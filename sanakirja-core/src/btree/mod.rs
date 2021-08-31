//! An implementation of B trees. The core operations on B trees
//! (lookup, iterate, put and del) are generic in the actual
//! implementation of nodes, via the [`BTreePage`] and
//! [`BTreeMutPage`]. This allows for a simpler code for the
//! high-level functions, as well as specialised, high-performance
//! implementations for the nodes.
//!
//! Two different implementations are supplied: one in [`page`] for
//! types with a size known at compile-time, which yields denser
//! leaves, and hence shallower trees (if the values are really using
//! the space). The other one, in [`page_unsized`], is for
//! dynamic-sized types, or types whose representation is dynamic, for
//! example enums that are `Sized` in Rust, but whose cases vary
//! widely in size.
use crate::*;
#[doc(hidden)]
pub mod cursor;
pub use cursor::{iter, rev_iter, Cursor, Iter, RevIter};
pub mod del;
pub use del::del;
pub mod put;
pub use put::put;
pub mod page;
pub mod page_unsized;

pub trait BTreePage<K: ?Sized, V: ?Sized>: Sized {
    type Cursor: Clone + Copy + core::fmt::Debug;

    /// Whether this cursor is at the end of the page.
    fn is_empty(c: &Self::Cursor) -> bool;

    /// Whether this cursor is strictly before the first element.
    fn is_init(c: &Self::Cursor) -> bool;

    /// Returns a cursor set before the first element of the page
    /// (i.e. set to -1).
    fn cursor_before(p: &CowPage) -> Self::Cursor;

    /// Returns a cursor set to the first element of the page
    /// (i.e. 0). If the page is empty, the returned cursor might be
    /// empty.
    fn cursor_first(p: &CowPage) -> Self::Cursor {
        let mut c = Self::cursor_before(p);
        Self::move_next(&mut c);
        c
    }

    /// Returns a cursor set after the last element of the page
    /// (i.e. to element n)
    fn cursor_after(p: &CowPage) -> Self::Cursor;

    /// Returns a cursor set to the last element of the page. If the
    /// cursor is empty, this is the same as `cursor_before`.
    fn cursor_last(p: &CowPage) -> Self::Cursor {
        let mut c = Self::cursor_after(p);
        Self::move_prev(&mut c);
        c
    }

    /// Return the element currently pointed to by the cursor (if the
    /// cursor is not before or after the elements of the page), and
    /// move the cursor to the next element.
    fn next<'b, T: LoadPage>(
        txn: &T,
        p: Page<'b>,
        c: &mut Self::Cursor,
    ) -> Option<(&'b K, &'b V, u64)> {
        if let Some((k, v, r)) = Self::current(txn, p, c) {
            Self::move_next(c);
            Some((k, v, r))
        } else {
            None
        }
    }

    /// Move the cursor to the previous element, and return that
    /// element. Note that this is not the symmetric of `next`.
    fn prev<'b, T: LoadPage>(
        txn: &T,
        p: Page<'b>,
        c: &mut Self::Cursor,
    ) -> Option<(&'b K, &'b V, u64)> {
        if Self::move_prev(c) {
            Self::current(txn, p, c)
        } else {
            None
        }
    }

    /// Move the cursor to the next position. Returns whether the
    /// cursor was actually moved (i.e. `true` if and only if the
    /// cursor isn't already after the last element).
    fn move_next(c: &mut Self::Cursor) -> bool;

    /// Move the cursor to the previous position. Returns whether the
    /// cursor was actually moved (i.e. `true` if and only if the
    /// cursor isn't strictly before the page).
    fn move_prev(c: &mut Self::Cursor) -> bool;

    /// Returns the current element, if the cursor is pointing at one.
    fn current<'a, T: LoadPage>(
        txn: &T,
        p: Page<'a>,
        c: &Self::Cursor,
    ) -> Option<(&'a K, &'a V, u64)>;

    /// Returns the left child of the entry pointed to by the cursor.
    fn left_child(p: Page, c: &Self::Cursor) -> u64;

    /// Returns the right child of the entry pointed to by the cursor.
    fn right_child(p: Page, c: &Self::Cursor) -> u64;

    /// Sets the cursor to the last element less than or equal to `k0`
    /// if `v0.is_none()`, and to `(k0, v0)` if `v0.is_some()`.  If a
    /// match is found (on `k0` only if `v0.is_none()`, on `(k0, v0)`
    /// else), return the match along with the right child.
    ///
    /// Else (in the `Err` case of the `Result`), return the position
    /// at which `(k0, v0)` can be inserted.
    fn set_cursor<'a, T: LoadPage>(
        txn: &'a T,
        page: Page,
        c: &mut Self::Cursor,
        k0: &K,
        v0: Option<&V>,
    ) -> Result<(&'a K, &'a V, u64), usize>;

    /// Splits the cursor into two cursors: the elements strictly
    /// before the current position, and the elements greater than or
    /// equal the current element.
    fn split_at(c: &Self::Cursor) -> (Self::Cursor, Self::Cursor);
}

pub struct PageIterator<'a, T: LoadPage, K: ?Sized, V: ?Sized, P: BTreePage<K, V>> {
    cursor: P::Cursor,
    txn: &'a T,
    page: Page<'a>,
}

impl<'a, T: LoadPage, K: ?Sized + 'a, V: ?Sized + 'a, P: BTreePage<K, V>> Iterator
    for PageIterator<'a, T, K, V, P>
{
    type Item = (&'a K, &'a V, u64);
    fn next(&mut self) -> Option<Self::Item> {
        P::next(self.txn, self.page, &mut self.cursor)
    }
}

pub trait BTreeMutPage<K: ?Sized, V: ?Sized>: BTreePage<K, V> + core::fmt::Debug {
    /// Initialise a page.
    fn init(page: &mut MutPage);

    /// Add an entry to the page, possibly splitting the page in the
    /// process.
    ///
    /// Makes the assumption that `k1v1.is_some()` implies
    /// `replace`. When `k1v1.is_some()`, we insert both `(k0, v0)`
    /// (as a replacement), followed by `(k1, v1)`. This is only ever
    /// used when deleting, and when the right child of a deleted
    /// entry (in an internal node) has split while we were looking
    /// for a replacement for the deleted entry.
    ///
    /// Since we only look for replacements in the right child, the
    /// left child of the insertion isn't modified, in which case `l`
    /// and `r` are interpreted as the left and right child of the new
    /// entry, `k1v1`.
    fn put<'a, T: AllocPage>(
        txn: &mut T,
        page: CowPage,
        mutable: bool,
        replace: bool,
        c: &Self::Cursor,
        k0: &'a K,
        v0: &'a V,
        k1v1: Option<(&'a K, &'a V)>,
        l: u64,
        r: u64,
    ) -> Result<crate::btree::put::Put<'a, K, V>, T::Error>;

    /// Add an entry to `page`, at position `c`. Does not check
    /// whether there is enough space to do so. This method is mostly
    /// useful for cloning pages.
    #[allow(unused_variables)]
    unsafe fn put_mut(
        page: &mut MutPage,
        c: &mut Self::Cursor,
        k0: &K,
        v0: &V,
        r: u64,
    );

    #[allow(unused_variables)]
    unsafe fn set_left_child(
        page: &mut MutPage,
        c: &Self::Cursor,
        l: u64
    );


    /// Update the left child of the position pointed to by the
    /// cursor.
    fn update_left_child<T: AllocPage>(
        txn: &mut T,
        page: CowPage,
        mutable: bool,
        c: &Self::Cursor,
        r: u64,
    ) -> Result<crate::btree::put::Ok, T::Error>;

    type Saved;

    /// Save a leaf entry as a replacement, when we delete at an
    /// internal node. This can be a pointer to the leaf if the leaf
    /// isn't mutated, or the actual value, or something else.
    fn save_deleted_leaf_entry(k: &K, v: &V) -> Self::Saved;

    /// Recover the saved value.
    unsafe fn from_saved<'a>(s: &Self::Saved) -> (&'a K, &'a V);

    /// Delete an entry on the page, returning the resuting page along
    /// with the offset of the freed page (or 0 if no page was freed,
    /// i.e. if `page` is mutable).
    fn del<T: AllocPage>(
        txn: &mut T,
        page: CowPage,
        mutable: bool,
        c: &Self::Cursor,
        l: u64,
    ) -> Result<(MutPage, u64), T::Error>;

    /// Merge, rebalance or update a concatenation.
    fn merge_or_rebalance<'a, 'b, T: AllocPage>(
        txn: &mut T,
        m: del::Concat<'a, K, V, Self>,
    ) -> Result<del::Op<'a, T, K, V>, T::Error>;
}

/// A database, which is essentially just a page offset along with markers.
#[derive(Debug)]
pub struct Db_<K: ?Sized, V: ?Sized, P: BTreePage<K, V>> {
    pub db: u64,
    pub k: core::marker::PhantomData<K>,
    pub v: core::marker::PhantomData<V>,
    pub p: core::marker::PhantomData<P>,
}

/// A database of sized values.
pub type Db<K, V> = Db_<K, V, page::Page<K, V>>;

/// A database of unsized values.
pub type UDb<K, V> = Db_<K, V, page_unsized::Page<K, V>>;

impl<K: ?Sized, V: ?Sized, P: BTreePage<K, V>> Db_<K, V, P> {
    /// Load a database from a page offset.
    pub fn from_page(db: u64) -> Self {
        Db_ {
            db,
            k: core::marker::PhantomData,
            v: core::marker::PhantomData,
            p: core::marker::PhantomData,
        }
    }
}

/// Create a database with an arbitrary page implementation.
pub fn create_db_<T: AllocPage, K: ?Sized, V: ?Sized, P: BTreeMutPage<K, V>>(
    txn: &mut T,
) -> Result<Db_<K, V, P>, T::Error> {
    let mut page = txn.alloc_page()?;
    P::init(&mut page);
    Ok(Db_ {
        db: page.0.offset,
        k: core::marker::PhantomData,
        v: core::marker::PhantomData,
        p: core::marker::PhantomData,
    })
}

/// Create a database for sized keys and values.
pub fn create_db<T: AllocPage, K: Storable, V: Storable>(
    txn: &mut T,
) -> Result<Db_<K, V, page::Page<K, V>>, T::Error> {
    create_db_(txn)
}

/// Fork a database.
pub fn fork_db<T: AllocPage, K: Storable + ?Sized, V: Storable + ?Sized, P: BTreeMutPage<K, V>>(
    txn: &mut T,
    db: &Db_<K, V, P>,
) -> Result<Db_<K, V, P>, T::Error> {
    txn.incr_rc(db.db)?;
    Ok(Db_ {
        db: db.db,
        k: core::marker::PhantomData,
        v: core::marker::PhantomData,
        p: core::marker::PhantomData,
    })
}

/// Get the first entry of a database greater than or equal to `k` (or
/// to `(k, v)` if `v.is_some()`).
pub fn get<'a, T: LoadPage, K: Storable + ?Sized, V: Storable + ?Sized, P: BTreePage<K, V>>(
    txn: &'a T,
    db: &Db_<K, V, P>,
    k: &K,
    v: Option<&V>,
) -> Result<Option<(&'a K, &'a V)>, T::Error> {
    // Set the "cursor stack" by setting a skip list cursor in
    // each page from the root to the appropriate leaf.
    let mut last_match = None;
    let mut page = txn.load_page(db.db)?;
    // This is a for loop, to allow the compiler to unroll (maybe).
    for _ in 0..cursor::N_CURSORS {
        let mut cursor = P::cursor_before(&page);
        if let Ok((kk, vv, _)) = P::set_cursor(txn, page.as_page(), &mut cursor, k, v) {
            if v.is_some() {
                return Ok(Some((kk, vv)));
            }
            last_match = Some((kk, vv));
        } else if let Some((k, v, _)) = P::current(txn, page.as_page(), &cursor) {
            // Here, Rust says that `k` and `v` have the same lifetime
            // as `page`, but we actually know that they're alive for
            // as long as `txn` doesn't change, so we can safely
            // extend their lifetimes:
            unsafe { last_match = Some((core::mem::transmute(k), core::mem::transmute(v))) }
        }
        // The cursor is set to the first element greater than or
        // equal to the (k, v) we're looking for, so we need to
        // explore the left subtree.
        let next_page = P::left_child(page.as_page(), &cursor);
        if next_page > 0 {
            page = txn.load_page(next_page)?;
        } else {
            break;
        }
    }
    Ok(last_match)
}

/// Drop a database recursively, dropping all referenced keys and
/// values that aren't shared with other databases.
pub fn drop<T: AllocPage, K: Storable + ?Sized, V: Storable + ?Sized, P: BTreePage<K, V>>(
    txn: &mut T,
    db: Db_<K, V, P>,
) -> Result<(), T::Error> {
    // In order to make this function tail-recursive, we simulate a
    // stack with the following:
    use core::mem::MaybeUninit;
    let mut stack: [MaybeUninit<cursor::PageCursor<K, V, P>>; cursor::N_CURSORS] = [
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
        MaybeUninit::uninit(),
    ];
    let mut ptr = 0;

    // Push the root page of `db` onto the stack.
    let page = txn.load_page(db.db)?;
    stack[0] = MaybeUninit::new(cursor::PageCursor {
        cursor: P::cursor_before(&page),
        page,
    });

    // Then perform a DFS:
    loop {
        // Look at the top element of the stack.
        let cur = unsafe { &mut *stack[ptr].as_mut_ptr() };
        // If it needs to be dropped (i.e. if its RC is <= 1), iterate
        // its cursor and drop all its referenced pages.
        let rc = txn.rc(cur.page.offset)?;
        if rc <= 1 {
            // if there's a current element in the cursor (i.e. we
            // aren't before or after the elements), decrease its RC.
            if let Some((k, v, _)) = P::current(txn, cur.page.as_page(), &cur.cursor) {
                for o in k.page_references().chain(v.page_references()) {
                    txn.decr_rc(o)?;
                }
            }
            // In all cases, move next and push the left child onto
            // the stack. This works because pushed cursors are
            // initially set to before the page's elements.
            if P::move_next(&mut cur.cursor) {
                let r = P::left_child(cur.page.as_page(), &cur.cursor);
                if r > 0 {
                    ptr += 1;
                    let page = txn.load_page(r)?;
                    stack[ptr] = MaybeUninit::new(cursor::PageCursor {
                        cursor: P::cursor_before(&page),
                        page,
                    })
                }
                continue;
            }
        }
        // Here, either rc > 1 (in which case the only thing we need
        // to do in this iteration is to decrement the RC), or else
        // `P::move_next` returned `false`, meaning that the cursor is
        // after the last element (in which case we are done with this
        // page, and also need to decrement its RC, in order to free
        // it).
        if cur.page.is_dirty() {
            txn.decr_rc_owned(cur.page.offset)?;
        } else {
            txn.decr_rc(cur.page.offset)?;
        }
        // If this was the bottom element of the stack, stop, else, pop.
        if ptr == 0 {
            break;
        } else {
            ptr -= 1;
        }
    }
    Ok(())
}
