use super::*;
use crate::{CowPage, LoadPage};
use core::mem::MaybeUninit;

#[derive(Debug)]
pub(super) struct PageCursor<K: ?Sized, V: ?Sized, P: BTreePage<K, V>> {
    pub page: CowPage,
    pub cursor: P::Cursor,
}

// This is 1 + the maximal depth of a tree.
//
// Since pages are of size 2^12, there are at most 2^52 addressable
// pages (potentially less depending on the platform). Since each page
// of a B tree below the root has at least 2 elements (because each
// page is at least half-full, and elements are at most 1/4th of a
// page), the arity is at least 3, except for the root. Since 3^33 is
// the smallest power of 3 larger than 2^52, the maximum depth is 33.
pub(crate) const N_CURSORS: usize = 33;

#[derive(Debug)]
/// A position in a B tree.
pub struct Cursor<K: ?Sized, V: ?Sized, P: BTreePage<K, V>> {
    /// Invariant: the first `len` items are initialised.
    stack: [core::mem::MaybeUninit<PageCursor<K, V, P>>; N_CURSORS],
    /// The length of the stack at the position of the first page
    /// shared with another tree. This definition is a little bit
    /// convoluted, but allows for efficient comparisons between
    /// `first_rc_len` and `len` to check whether a page is shared
    /// with another tree.
    first_rc_len: usize,
    /// Number of initialised items on the stack.
    len: usize,
}

impl<K: ?Sized + Storable, V: ?Sized + Storable, P: BTreePage<K, V>> Cursor<K, V, P> {
    /// Create a new cursor, initialised to the first entry of the B tree.
    pub fn new<T: LoadPage>(txn: &T, db: &Db_<K, V, P>) -> Result<Self, T::Error> {
        // Looking forward to getting array initialisation stabilised :)
        let mut stack = [
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
            core::mem::MaybeUninit::uninit(),
        ];
        let page = txn.load_page(db.db)?;
        stack[0] = MaybeUninit::new(PageCursor {
            cursor: P::cursor_before(&page),
            page,
        });
        Ok(Cursor {
            stack,
            first_rc_len: N_CURSORS,
            len: 1,
        })
    }

    pub(super) fn push(&mut self, p: PageCursor<K, V, P>) {
        self.stack[self.len] = MaybeUninit::new(p);
        self.len += 1;
    }

    pub(super) fn cur(&self) -> &PageCursor<K, V, P> {
        assert!(self.len > 0);
        unsafe { &*self.stack[self.len - 1].as_ptr() }
    }

    pub(super) fn len(&self) -> usize {
        self.len
    }

    pub(super) fn first_rc_len(&self) -> usize {
        self.first_rc_len
    }

    pub(super) fn pop(&mut self) -> Option<PageCursor<K, V, P>> {
        if self.len > 0 {
            self.len -= 1;
            let result = core::mem::replace(&mut self.stack[self.len], MaybeUninit::uninit());
            Some(unsafe { result.assume_init() })
        } else {
            None
        }
    }

    pub(super) fn current_mut(&mut self) -> &mut PageCursor<K, V, P> {
        assert!(self.len > 0);
        unsafe { &mut *self.stack[self.len - 1].as_mut_ptr() }
    }

    /// Push the leftmost path starting at page `left_page` onto the
    /// stack.
    pub(super) fn set_first_leaf<T: LoadPage>(
        &mut self,
        txn: &T,
        mut left_page: u64,
    ) -> Result<(), T::Error> {
        while left_page > 0 {
            if self.first_rc_len >= N_CURSORS && txn.rc(left_page)? >= 2 {
                self.first_rc_len = self.len + 1
            }
            let page = txn.load_page(left_page)?;
            let curs = P::cursor_first(&page);
            left_page = P::left_child(page.as_page(), &curs);
            self.push(PageCursor { page, cursor: curs });
        }
        Ok(())
    }

    /// Reset the cursor to the first element of the database.
    pub fn reset<'a, T: LoadPage>(&mut self) {
        self.len = 1;
        let init = unsafe { &mut *self.stack[0].as_mut_ptr() };
        init.cursor = P::cursor_before(&init.page);
    }

    // An invariant of cursors, fundamental to understanding the
    // `next` and `prev` functions below, is that the lower levels (in
    // the tree, upper levels on the stack) are the left children of
    // the cursor's position on a page.

    /// Set the cursor to the first position larger than or equal to
    /// the specified key and value.
    pub fn set<'a, T: LoadPage>(
        &mut self,
        txn: &'a T,
        k: &K,
        v: Option<&V>,
    ) -> Result<Option<(&'a K, &'a V)>, T::Error> {
        // Set the "cursor stack" by setting a cursor in each page
        // on a path from the root to the appropriate leaf.

        // Start from the bottom of the stack, which is also the root
        // of the tree.
        self.len = 1;
        self.first_rc_len = N_CURSORS;
        let init = unsafe { &mut *self.stack[0].as_mut_ptr() };
        init.cursor = P::cursor_before(&init.page);

        let mut last_matching_page = N_CURSORS;
        let mut last_match = None;
        while self.len < N_CURSORS {
            let current = unsafe { &mut *self.stack.get_unchecked_mut(self.len - 1).as_mut_ptr() };
            if self.first_rc_len >= N_CURSORS && txn.rc(current.page.offset)? >= 2 {
                self.first_rc_len = self.len
            }
            let ref mut cursor = current.cursor;
            if let Ok((kk, vv, _)) = P::set_cursor(txn, current.page.as_page(), cursor, k, v) {
                if v.is_some() {
                    return Ok(Some((kk, vv)));
                }
                last_match = Some((kk, vv));
                last_matching_page = self.len
            }
            let next_page = P::left_child(current.page.as_page(), cursor);
            if next_page > 0 {
                let page = txn.load_page(next_page)?;
                self.push(PageCursor {
                    cursor: P::cursor_before(&page),
                    page,
                });
            } else {
                break;
            }
        }
        if last_matching_page < N_CURSORS {
            self.len = last_matching_page;
            Ok(last_match)
        } else {
            Ok(None)
        }
    }

    /// Set the cursor after the last element, so that [`Self::next`]
    /// returns `None`, and [`Self::prev`] returns the last element.
    pub fn set_last<'a, T: LoadPage>(
        &mut self,
        txn: &'a T,
    ) -> Result<(), T::Error> {
        self.len = 1;
        self.first_rc_len = N_CURSORS;
        let current = unsafe { &mut *self.stack[self.len - 1].as_mut_ptr() };
        current.cursor = P::cursor_after(&current.page);
        loop {
            let current = unsafe { &mut *self.stack[self.len - 1].as_mut_ptr() };
            if self.first_rc_len >= N_CURSORS && txn.rc(current.page.offset)? >= 2 {
                self.first_rc_len = self.len
            }
            let l = P::left_child(current.page.as_page(), &current.cursor);
            if l > 0 {
                let page = txn.load_page(l)?;
                self.push(PageCursor {
                    cursor: P::cursor_after(&page),
                    page,
                })
            } else {
                break;
            }
        }
        Ok(())
    }

    /// Return the current position of the cursor.
    pub fn current<'a, T: LoadPage>(
        &mut self,
        txn: &'a T,
    ) -> Result<Option<(&'a K, &'a V)>, T::Error> {
        loop {
            let current = unsafe { &mut *self.stack[self.len - 1].as_mut_ptr() };
            if P::is_init(&current.cursor) {
                // The cursor hasn't been set.
                return Ok(None)
            } else if let Some((k, v, _)) = P::current(txn, current.page.as_page(), &current.cursor)
            {
                unsafe {
                    return Ok(Some((core::mem::transmute(k), core::mem::transmute(v))));
                }
            } else if self.len > 1 {
                self.len -= 1
            } else {
                // We're past the last element at the root.
                return Ok(None);
            }
        }
    }

    /// Return the current position of the cursor, and move the cursor
    /// to the next position.
    pub fn next<'a, T: LoadPage>(
        &mut self,
        txn: &'a T,
    ) -> Result<Option<(&'a K, &'a V)>, T::Error> {
        loop {
            let current = unsafe { &mut *self.stack[self.len - 1].as_mut_ptr() };
            if P::is_empty(&current.cursor) {
                if self.len > 1 {
                    if self.first_rc_len == self.len {
                        self.first_rc_len = N_CURSORS
                    }
                    self.len -= 1
                } else {
                    return Ok(None);
                }
            } else {
                let (cur_entry, r) = if let Some((k, v, r)) = P::current(txn, current.page.as_page(), &current.cursor) {
                    (Some((k, v)), r)
                } else {
                    (None, P::right_child(current.page.as_page(), &current.cursor))
                };
                P::move_next(&mut current.cursor);
                if r != 0 {
                    let page = txn.load_page(r)?;
                    self.push(PageCursor {
                        cursor: P::cursor_before(&page),
                        page,
                    });
                    if self.first_rc_len >= N_CURSORS && txn.rc(r)? >= 2 {
                        self.first_rc_len = self.len
                    }
                }
                if let Some((k, v)) = cur_entry {
                    unsafe {
                        return Ok(Some((core::mem::transmute(k), core::mem::transmute(v))));
                    }
                }
            }
        }
    }

    /// Move the cursor to the previous entry, and return the entry
    /// that was current before the move. If the cursor is initially
    /// after all the entries, this moves it back by two steps.
    pub fn prev<'a, T: LoadPage>(
        &mut self,
        txn: &'a T,
    ) -> Result<Option<(&'a K, &'a V)>, T::Error> {
        loop {
            let current = unsafe { &mut *self.stack[self.len - 1].as_mut_ptr() };

            if P::is_init(&current.cursor) {
                if self.len > 1 {
                    if self.first_rc_len == self.len {
                        self.first_rc_len = N_CURSORS
                    }
                    self.len -= 1;
                    let current = unsafe { &mut *self.stack[self.len - 1].as_mut_ptr() };
                    P::move_prev(&mut current.cursor);
                } else {
                    return Ok(None);
                }
            } else {
                let cur_entry = P::current(txn, current.page.as_page(), &current.cursor);
                let left = P::left_child(current.page.as_page(), &current.cursor);
                if left != 0 {
                    let page = txn.load_page(left)?;
                    self.push(PageCursor {
                        cursor: P::cursor_after(&page),
                        page,
                    });
                    if self.first_rc_len >= N_CURSORS && txn.rc(left)? >= 2 {
                        self.first_rc_len = self.len
                    }
                } else {
                    // We are at a leaf.
                    P::move_prev(&mut current.cursor);
                }
                if let Some((k, v, _)) = cur_entry {
                    unsafe {
                        return Ok(Some((core::mem::transmute(k), core::mem::transmute(v))));
                    }
                }
            }
        }
    }
}

pub struct Iter<'a, T: LoadPage, K: Storable + ?Sized, V: Storable + ?Sized, P: BTreePage<K, V>> {
    txn: &'a T,
    cursor: Cursor<K, V, P>,
}

pub fn iter<'a, T, K, V, P>(
    txn: &'a T,
    db: &super::Db_<K, V, P>,
    origin: Option<(&K, Option<&V>)>,
) -> Result<Iter<'a, T, K, V, P>, T::Error>
where
    T: LoadPage,
    K: Storable + ?Sized,
    V: Storable + ?Sized,
    P: BTreePage<K, V>,
{
    let mut cursor = Cursor::new(txn, db)?;
    if let Some((k, v)) = origin {
        cursor.set(txn, k, v)?;
    }
    Ok(Iter { cursor, txn })
}

impl<
        'a,
        T: LoadPage,
        K: Storable + ?Sized + 'a,
        V: Storable + ?Sized + 'a,
        P: BTreePage<K, V> + 'a,
    > Iterator for Iter<'a, T, K, V, P>
{
    type Item = Result<(&'a K, &'a V), T::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        self.cursor.next(self.txn).transpose()
    }
}

pub struct RevIter<'a, T: LoadPage, K: Storable + ?Sized, V: Storable + ?Sized, P: BTreePage<K, V>>
{
    txn: &'a T,
    cursor: Cursor<K, V, P>,
}

pub fn rev_iter<'a, T, K, V, P>(
    txn: &'a T,
    db: &super::Db_<K, V, P>,
    origin: Option<(&K, Option<&V>)>,
) -> Result<RevIter<'a, T, K, V, P>, T::Error>
where
    T: LoadPage,
    K: Storable + ?Sized,
    V: Storable + ?Sized,
    P: BTreePage<K, V>,
{
    let mut cursor = Cursor::new(txn, db)?;
    if let Some((k, v)) = origin {
        cursor.set(txn, k, v)?;
    } else {
        cursor.set_last(txn)?;
    }
    Ok(RevIter { cursor, txn })
}

impl<
        'a,
        T: LoadPage,
        K: Storable + ?Sized + 'a,
        V: Storable + ?Sized + 'a,
        P: BTreePage<K, V> + 'a,
    > Iterator for RevIter<'a, T, K, V, P>
{
    type Item = Result<(&'a K, &'a V), T::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        self.cursor.prev(self.txn).transpose()
    }
}
