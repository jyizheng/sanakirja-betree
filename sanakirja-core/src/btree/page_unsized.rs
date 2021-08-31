//! Implementation of B tree pages for Unsized types, or types with an
//! dynamically-sized representation (for example enums with widely
//! different sizes).
//!
//! This module follows the same organisation as the sized
//! implementation, and contains types shared between the two
//! implementations.
//!
//! The types that can be used with this implementation must implement
//! the [`UnsizedStorable`] trait, which essentially replaces the
//! [`core::mem`] functions for determining the size and alignment of
//! values.
//!
//! One key difference is the implementation of leaves (internal nodes
//! have the same format): indeed, in this implementation, leaves have
//! almost the same format as internal nodes, except that their
//! offsets are written on the page as little-endian-encoded [`u16`]
//! (with only the 12 LSBs used, i.e. 4 bits unused).

use super::*;
use crate::btree::del::*;
use crate::btree::put::*;
use core::cmp::Ordering;

// The header is the same as for the sized implementation, so we share
// it here.
pub(super) mod header;

// Like in the sized implementation, we have the same three submodules.
mod alloc;

// This is a common module with the sized implementation.
pub(super) mod cursor;

mod put;
pub(super) mod rebalance;
use alloc::*;
use cursor::*;
use header::*;
use rebalance::*;

#[derive(Debug)]
pub struct Page<K: ?Sized, V: ?Sized> {
    k: core::marker::PhantomData<K>,
    v: core::marker::PhantomData<V>,
}

// Many of these functions are the same as in the Sized implementations.
impl<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized> super::BTreePage<K, V>
    for Page<K, V>
{
    fn is_empty(c: &Self::Cursor) -> bool {
        c.cur >= c.total as isize
    }

    fn is_init(c: &Self::Cursor) -> bool {
        c.cur < 0
    }
    type Cursor = PageCursor;
    fn cursor_before(p: &crate::CowPage) -> Self::Cursor {
        PageCursor::new(p, -1)
    }
    fn cursor_after(p: &crate::CowPage) -> Self::Cursor {
        PageCursor::after(p)
    }

    // Split a cursor, returning two cursors `(a, b)` where b is the
    // same as `c`, and `a` is a cursor running from the first element
    // of the page to `c` (excluding `c`).
    fn split_at(c: &Self::Cursor) -> (Self::Cursor, Self::Cursor) {
        (
            PageCursor {
                cur: 0,
                total: c.cur.max(0) as usize,
                is_leaf: c.is_leaf,
            },
            *c,
        )
    }

    fn move_next(c: &mut Self::Cursor) -> bool {
        if c.cur < c.total as isize {
            c.cur += 1;
            true
        } else {
            false
        }
    }
    fn move_prev(c: &mut Self::Cursor) -> bool {
        if c.cur > 0 {
            c.cur -= 1;
            true
        } else {
            c.cur = -1;
            false
        }
    }

    // This function is the same as the sized implementation for
    // internal nodes, since the only difference between leaves and
    // internal nodes in this implementation is the size of offsets (2
    // bytes for leaves, 8 bytes for internal nodes).
    fn current<'a, T: LoadPage>(
        txn: &T,
        page: crate::Page<'a>,
        c: &Self::Cursor,
    ) -> Option<(&'a K, &'a V, u64)> {
        if c.cur < 0 || c.cur >= c.total as isize {
            None
        } else if c.is_leaf {
            unsafe {
                let off =
                    u16::from_le(*(page.data.as_ptr().add(HDR + c.cur as usize * 2) as *const u16));
                let (k, v) = read::<T, K, V>(txn, page.data.as_ptr().add(off as usize));
                Some((
                    K::from_raw_ptr(txn, k as *const u8),
                    V::from_raw_ptr(txn, v as *const u8),
                    0,
                ))
            }
        } else {
            unsafe {
                let off =
                    u64::from_le(*(page.data.as_ptr().add(HDR + c.cur as usize * 8) as *const u64));
                let (k, v) = read::<T, K, V>(txn, page.data.as_ptr().add((off & 0xfff) as usize));
                Some((
                    K::from_raw_ptr(txn, k as *const u8),
                    V::from_raw_ptr(txn, v as *const u8),
                    off & !0xfff,
                ))
            }
        }
    }

    // These methods are the same as in the sized implementation.
    fn left_child(page: crate::Page, c: &Self::Cursor) -> u64 {
        assert!(c.cur >= 0);
        if c.is_leaf {
            0
        } else {
            assert!(c.cur >= 0 && HDR as isize + c.cur * 8 - 8 <= 4088);
            let off =
                unsafe { *(page.data.as_ptr().offset(HDR as isize + c.cur * 8 - 8) as *const u64) };
            u64::from_le(off) & !0xfff
        }
    }
    fn right_child(page: crate::Page, c: &Self::Cursor) -> u64 {
        assert!(c.cur < c.total as isize);
        if c.is_leaf {
            0
        } else {
            assert!(c.cur < c.total as isize && HDR as isize + c.cur * 8 - 8 <= 4088);
            let off = unsafe { *(page.data.as_ptr().offset(HDR as isize + c.cur * 8) as *const u64) };
            u64::from_le(off) & !0xfff
        }
    }

    fn set_cursor<'a, T: LoadPage>(
        txn: &'a T,
        page: crate::Page,
        c: &mut PageCursor,
        k0: &K,
        v0: Option<&V>,
    ) -> Result<(&'a K, &'a V, u64), usize> {
        unsafe {
            // `lookup` has the same semantic as
            // `core::slice::binary_search`, i.e. it returns either
            // `Ok(n)`, where `n` is the position where `(k0, v0)` was
            // found, or `Err(n)` where `n` is the position where
            // `(k0, v0)` can be inserted to preserve the order.
            match lookup(txn, page, c, k0, v0) {
                Ok(n) => {
                    c.cur = n as isize;
                    if c.is_leaf {
                        let off =
                            u16::from_le(*(page.data.as_ptr().add(HDR + n * 2) as *const u16));
                        let (k, v) = read::<T, K, V>(txn, page.data.as_ptr().add(off as usize));
                        Ok((K::from_raw_ptr(txn, k), V::from_raw_ptr(txn, v), 0))
                    } else {
                        let off =
                            u64::from_le(*(page.data.as_ptr().add(HDR + n * 8) as *const u64));
                        let (k, v) =
                            read::<T, K, V>(txn, page.data.as_ptr().add(off as usize & 0xfff));
                        Ok((
                            K::from_raw_ptr(txn, k),
                            V::from_raw_ptr(txn, v),
                            off & !0xfff,
                        ))
                    }
                }
                Err(n) => {
                    c.cur = n as isize;
                    Err(n)
                }
            }
        }
    }
}

// There quite some duplicated code in the following function, because
// we're forming a slice of offsets, and the using the core library's
// `binary_search_by` method on slices.
unsafe fn lookup<T: LoadPage, K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
    txn: &T,
    page: crate::Page,
    c: &mut PageCursor,
    k0: &K,
    v0: Option<&V>,
) -> Result<usize, usize> {
    let hdr = header(page);
    c.total = hdr.n() as usize;
    c.is_leaf = hdr.is_leaf();
    if c.is_leaf {
        let s = core::slice::from_raw_parts(
            page.data.as_ptr().add(HDR) as *const u16,
            hdr.n() as usize,
        );
        if let Some(v0) = v0 {
            s.binary_search_by(|&off| {
                let off = u16::from_le(off);
                let (k, v) = read::<T, K, V>(txn, page.data.as_ptr().offset(off as isize));
                let k = K::from_raw_ptr(txn, k as *const u8);
                match k.compare(txn, k0) {
                    Ordering::Equal => {
                        let v = V::from_raw_ptr(txn, v as *const u8);
                        v.compare(txn, v0)
                    }
                    cmp => cmp,
                }
            })
        } else {
            s.binary_search_by(|&off| {
                let off = u16::from_le(off);
                let (k, _) = read::<T, K, V>(txn, page.data.as_ptr().offset(off as isize));
                let k = K::from_raw_ptr(txn, k);
                k.compare(txn, k0)
            })
        }
    } else {
        let s = core::slice::from_raw_parts(
            page.data.as_ptr().add(HDR) as *const u64,
            hdr.n() as usize,
        );
        if let Some(v0) = v0 {
            s.binary_search_by(|&off| {
                let off = u64::from_le(off) & 0xfff;
                let (k, v) = read::<T, K, V>(txn, page.data.as_ptr().offset(off as isize & 0xfff));
                let k = K::from_raw_ptr(txn, k);
                match k.compare(txn, k0) {
                    Ordering::Equal => {
                        let v = V::from_raw_ptr(txn, v);
                        v.compare(txn, v0)
                    }
                    cmp => cmp,
                }
            })
        } else {
            s.binary_search_by(|&off| {
                let off = u64::from_le(off) & 0xfff;
                let (k, _) = read::<T, K, V>(txn, page.data.as_ptr().offset(off as isize & 0xfff));
                let k = K::from_raw_ptr(txn, k);
                k.compare(txn, k0)
            })
        }
    }
}

impl<
        K: UnsizedStorable + ?Sized + core::fmt::Debug,
        V: UnsizedStorable + ?Sized + core::fmt::Debug,
    > super::BTreeMutPage<K, V> for Page<K, V>
{
    // The init function is straightforward.
    fn init(page: &mut MutPage) {
        let h = header_mut(page);
        h.init();
    }

    // Deletions in internal nodes of a B tree need to replace the
    // deleted value with a value from a leaf.
    //
    // In this implementation of pages, we never actually wipe any
    // data from pages, we're even only appending data, or cloning the
    // pages to compact them. Therefore, raw pointers to leaves are
    // always valid for as long as the page isn't freed, which can
    // only happen at the very last step of an insertion or deletion.
    type Saved = (*const K, *const V);
    fn save_deleted_leaf_entry(k: &K, v: &V) -> Self::Saved {
        (k as *const K, v as *const V)
    }

    unsafe fn from_saved<'a>(s: &Self::Saved) -> (&'a K, &'a V) {
        (&*s.0, &*s.1)
    }

    // As in the sized implementation, `put` is split into its own submodule.
    fn put<'a, T: AllocPage>(
        txn: &mut T,
        page: CowPage,
        mutable: bool,
        replace: bool,
        c: &PageCursor,
        k0: &'a K,
        v0: &'a V,
        k1v1: Option<(&'a K, &'a V)>,
        l: u64,
        r: u64,
    ) -> Result<crate::btree::put::Put<'a, K, V>, T::Error> {
        debug_assert!(c.cur >= 0);
        debug_assert!(k1v1.is_none() || replace);
        if r == 0 {
            put::put::<_, _, _, Leaf>(
                txn,
                page,
                mutable,
                replace,
                c.cur as usize,
                k0,
                v0,
                k1v1,
                0,
                0,
            )
        } else {
            put::put::<_, _, _, Internal>(
                txn,
                page,
                mutable,
                replace,
                c.cur as usize,
                k0,
                v0,
                k1v1,
                l,
                r,
            )
        }
    }

    unsafe fn put_mut(
        page: &mut MutPage,
        c: &mut Self::Cursor,
        k0: &K,
        v0: &V,
        r: u64,
    ) {
        let mut n = c.cur;
        if r == 0 {
            Leaf::alloc_write(page, k0, v0, 0, r, &mut n);
        } else {
            Internal::alloc_write(page, k0, v0, 0, r, &mut n);
        }
        c.total += 1;
    }

    unsafe fn set_left_child(
        page: &mut MutPage,
        c: &Self::Cursor,
        l: u64
    ) {
        let off = (page.0.data.add(HDR) as *mut u64).offset(c.cur - 1);
        *off = (l | (u64::from_le(*off) & 0xfff)).to_le();
    }

    // Update the left child of the entry pointed to by cursor `c`.
    fn update_left_child<T: AllocPage>(
        txn: &mut T,
        page: CowPage,
        mutable: bool,
        c: &Self::Cursor,
        l: u64,
    ) -> Result<crate::btree::put::Ok, T::Error> {
        assert!(!c.is_leaf);
        let freed;
        let page = if mutable && page.is_dirty() {
            // If the page is dirty (allocated by this transaction)
            // and isn't shared, just make it mutable.
            freed = 0;
            MutPage(page)
        } else {
            // Else, clone the page:
            let mut new = txn.alloc_page()?;
            <Page<K, V> as BTreeMutPage<K, V>>::init(&mut new);
            // Copy the left child
            let l = header(page.as_page()).left_page() & !0xfff;
            let hdr = header_mut(&mut new);
            hdr.set_left_page(l);
            // Copy all the entries
            let s = Internal::offset_slice(page.as_page());
            clone::<K, V, Internal>(page.as_page(), &mut new, s, &mut 0);
            // Mark the old version for freeing.
            freed = page.offset | if page.is_dirty() { 1 } else { 0 };
            new
        };
        // Finally, update the left children of the cursor. We know
        // that all valid positions of a cursor except the leftmost
        // one (-1) have a left child.
        assert!(c.cur >= 0);
        unsafe {
            let off = (page.0.data.add(HDR) as *mut u64).offset(c.cur as isize - 1);
            *off = (l | (u64::from_le(*off) & 0xfff)).to_le();
        }
        Ok(Ok { page, freed })
    }

    // Here is how deletions work: if the page is dirty and mutable,
    // we "unlink" the value by moving the end of the offset array to
    // the left by one offset (2 bytes in leaves, 8 bytes in internal
    // nodes).
    fn del<T: AllocPage>(
        txn: &mut T,
        page: crate::CowPage,
        mutable: bool,
        c: &PageCursor,
        l: u64,
    ) -> Result<(MutPage, u64), T::Error> {
        // Check that the cursor is at a valid position for a deletion.
        debug_assert!(c.cur >= 0 && c.cur < c.total as isize);
        if mutable && page.is_dirty() {
            let p = page.data;
            let mut page = MutPage(page);
            let hdr = header_mut(&mut page);
            let n = hdr.n();
            if c.is_leaf {
                unsafe {
                    let ptr = p.add(HDR + c.cur as usize * 2) as *mut u16;
                    // Get the offset in the page of the key/value data.
                    let off = u16::from_le(*ptr);
                    assert_eq!(off & 0xf000, 0);
                    // Erase the offset by shifting the last (`n -
                    // c.cur - 1`) offsets. The reasoning against
                    // "off-by-one errors" is that if the cursor is
                    // positioned on the first element (`c.cur == 0`),
                    // there are `n-1` elements to shift.
                    core::ptr::copy(ptr.offset(1), ptr, n as usize - c.cur as usize - 1);
                    // Remove the size of the actualy key/value, plus
                    // 2 bytes (the offset).
                    hdr.decr(2 + entry_size::<K, V>(p.add(off as usize)));
                }
            } else {
                unsafe {
                    let ptr = p.add(HDR + c.cur as usize * 8) as *mut u64;
                    // Offset to the key/value data.
                    let off = u64::from_le(*ptr);
                    // Shift the offsets like in the leaf case above.
                    core::ptr::copy(ptr.offset(1), ptr, n as usize - c.cur as usize - 1);
                    if l > 0 {
                        // In an internal node, we may have to update
                        // the left child of the current
                        // position. After the move, the current
                        // offset is at `ptr`, so we need to find the
                        // offset one step to the left.
                        let p = ptr.offset(-1);
                        *p = (l | (u64::from_le(*p) & 0xfff)).to_le();
                    }
                    // Remove the size of the key/value, plus 8 bytes
                    // (the offset).
                    hdr.decr(8 + entry_size::<K, V>(p.add((off & 0xfff) as usize)));
                }
            };
            hdr.set_n(n - 1);
            // Return the page, and 0 for "nothing was freed".
            Ok((page, 0))
        } else {
            // If the page cannot be mutated, we allocate a new page and clone.
            let mut new = txn.alloc_page()?;
            <Page<K, V> as BTreeMutPage<K, V>>::init(&mut new);
            if c.is_leaf {
                // In a leaf, this is just a matter of getting the
                // offset slice, removing the current position and
                // cloning.
                let s = Leaf::offset_slice(page.as_page());
                let (s0, s1) = s.split_at(c.cur as usize);
                let (_, s1) = s1.split_at(1);
                let mut n = 0;
                clone::<K, V, Leaf>(page.as_page(), &mut new, s0, &mut n);
                clone::<K, V, Leaf>(page.as_page(), &mut new, s1, &mut n);
            } else {
                // In an internal node, things are a bit trickier,
                // since we might need to update the left child.
                //
                // First, clone the leftmost child of the page.
                let hdr = header(page.as_page());
                let left = hdr.left_page() & !0xfff;
                unsafe {
                    *(new.0.data.add(HDR) as *mut u64).offset(-1) = left.to_le();
                }
                // Then, clone the first half of the page.
                let s = Internal::offset_slice(page.as_page());
                let (s0, s1) = s.split_at(c.cur as usize);
                let (_, s1) = s1.split_at(1);
                let mut n = 0;
                clone::<K, V, Internal>(page.as_page(), &mut new, s0, &mut n);
                // Update the left child, which was written by the
                // call to `clone` as the right child of the last
                // entry in `s0`.
                if l > 0 {
                    unsafe {
                        let off = (new.0.data.add(HDR) as *mut u64).offset(n - 1);
                        *off = (l | (u64::from_le(*off) & 0xfff)).to_le();
                    }
                }
                // Then, clone the second half of the page.
                clone::<K, V, Internal>(page.as_page(), &mut new, s1, &mut n);
            }
            // Return the new page, and the offset of the freed page.
            Ok((new, page.offset))
        }
    }

    // Decide what to do with the concatenation of two neighbouring
    // pages, with a middle element.
    //
    // This is highly similar to the sized case.
    fn merge_or_rebalance<'a, T: AllocPage>(
        txn: &mut T,
        m: Concat<'a, K, V, Self>,
    ) -> Result<Op<'a, T, K, V>, T::Error> {
        // First evaluate the size of the middle element on a
        // page. Contrarily to the sized case, the offsets are
        // aligned, so the header is always the same size (no
        // padding).
        let mid_size = if m.modified.c0.is_leaf {
            2 + alloc_size::<K, V>(m.mid.0, m.mid.1)
        } else {
            8 + alloc_size::<K, V>(m.mid.0, m.mid.1)
        };

        // Evaluate the size of the modified page of the concatenation
        // (which includes the header).
        let mod_size = size::<K, V>(&m.modified);
        // Add the "occupied" size (which excludes the header).
        let occupied = {
            let hdr = header(m.other.as_page());
            (hdr.left_page() & 0xfff) as usize
        };
        if mod_size + mid_size + occupied <= PAGE_SIZE {
            // If the concatenation fits on a page, merge.
            return if m.modified.c0.is_leaf {
                merge::<_, _, _, _, Leaf>(txn, m)
            } else {
                merge::<_, _, _, _, Internal>(txn, m)
            };
        }

        // If we can't merge, evaluate the size of the first binding
        // on the other page, to see if we can rebalance.
        let first_other = PageCursor::new(&m.other, 0);
        let first_other_size = current_size::<K, V>(m.other.as_page(), &first_other);

        // If the modified page is at least half-full, or if removing
        // the first entry on the other page would make that other
        // page less than half-full, don't rebalance. See the Sized
        // implementation to see cases where this happens.
        if mod_size >= PAGE_SIZE / 2 || HDR + occupied - first_other_size < PAGE_SIZE / 2 {
            if let Some((k, v)) = m.modified.ins {
                return Ok(Op::Put(Self::put(
                    txn,
                    m.modified.page,
                    m.modified.mutable,
                    m.modified.skip_first,
                    &m.modified.c1,
                    k,
                    v,
                    m.modified.ins2,
                    m.modified.l,
                    m.modified.r,
                )?));
            } else if m.modified.skip_first {
                debug_assert!(m.modified.ins2.is_none());
                let (page, freed) = Self::del(
                    txn,
                    m.modified.page,
                    m.modified.mutable,
                    &m.modified.c1,
                    m.modified.l,
                )?;
                return Ok(Op::Put(Put::Ok(Ok { page, freed })));
            } else {
                let mut c1 = m.modified.c1.clone();
                let mut l = m.modified.l;
                if l == 0 {
                    Self::move_next(&mut c1);
                    l = m.modified.r;
                }
                return Ok(Op::Put(Put::Ok(Self::update_left_child(
                    txn,
                    m.modified.page,
                    m.modified.mutable,
                    &c1,
                    l,
                )?)));
            }
        }
        // Finally, if we're here, we can rebalance. There are four
        // (relatively explicit) cases, see the `rebalance` submodule
        // to see how this is done.
        if m.mod_is_left {
            if m.modified.c0.is_leaf {
                rebalance_left::<_, _, _, Leaf>(txn, m)
            } else {
                rebalance_left::<_, _, _, Internal>(txn, m)
            }
        } else {
            rebalance_right::<_, _, _, Self>(txn, m)
        }
    }
}

/// Size of a modified page (including the header).
fn size<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
    m: &ModifiedPage<K, V, Page<K, V>>,
) -> usize {
    let mut total = {
        let hdr = header(m.page.as_page());
        (hdr.left_page() & 0xfff) as usize
    };
    total += HDR;

    // Extra size for the offsets.
    let extra = if m.c1.is_leaf { 2 } else { 8 };
    if let Some((k, v)) = m.ins {
        total += extra + alloc_size(k, v) as usize;
        if let Some((k, v)) = m.ins2 {
            total += extra + alloc_size(k, v) as usize;
        }
    }
    if m.skip_first {
        total -= current_size::<K, V>(m.page.as_page(), &m.c1) as usize;
    }
    total
}

// Size of a pair of type `(K, V)`. This is computed in the same way
// as a struct with fields of type `K` and `V` in C.
fn alloc_size<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(k: &K, v: &V) -> usize {
    let s = ((k.size() + V::ALIGN - 1) & !(V::ALIGN - 1)) + v.size();
    let al = K::ALIGN.max(V::ALIGN);
    (s + al - 1) & !(al - 1)
}

// Total size of the entry for that cursor position, including the
// offset size.
fn current_size<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
    page: crate::Page,
    c: &PageCursor,
) -> usize {
    if c.is_leaf {
        Leaf::current_size::<K, V>(page, c.cur)
    } else {
        Internal::current_size::<K, V>(page, c.cur)
    }
}

pub(super) trait AllocWrite<K: ?Sized, V: ?Sized> {
    fn alloc_write(new: &mut MutPage, k0: &K, v0: &V, l: u64, r: u64, n: &mut isize);
    fn set_left_child(new: &mut MutPage, n: isize, l: u64);
}

/// Perform the modifications on a page, by copying it onto page `new`.
fn modify<T: LoadPage, K: core::fmt::Debug + ?Sized, V: core::fmt::Debug + ?Sized, P: BTreeMutPage<K, V>, L: AllocWrite<K, V>>(
    txn: &T,
    new: &mut MutPage,
    m: &mut ModifiedPage<K, V, P>,
    n: &mut isize,
) {
    let mut l = P::left_child(m.page.as_page(), &m.c0);
    while let Some((k, v, r)) = P::next(txn, m.page.as_page(), &mut m.c0) {
        L::alloc_write(new, k, v, l, r, n);
        l = 0;
    }
    let mut rr = m.r;
    if let Some((k, v)) = m.ins {
        if let Some((k2, v2)) = m.ins2 {
            L::alloc_write(new, k, v, l, m.l, n);
            L::alloc_write(new, k2, v2, 0, m.r, n);
        } else if m.l > 0 {
            L::alloc_write(new, k, v, m.l, m.r, n);
        } else {
            L::alloc_write(new, k, v, l, m.r, n);
        }
        l = 0;
        rr = 0;
    } else if m.l > 0 {
        l = m.l
    }
    let mut c1 = m.c1.clone();
    if m.skip_first {
        P::move_next(&mut c1);
    }
    // Here's a confusing thing: if the first element of `c1` is the
    // last element of a page, we may be updating its right child (in
    // which case m.r > 0) rather than its left child like for all
    // other elements.
    //
    // This case only ever happens for this function when we're
    // updating the last child of a page p, and then merging p with
    // its right neighbour.
    while let Some((k, v, r)) = P::next(txn, m.page.as_page(), &mut c1) {
        if rr > 0 {
            L::alloc_write(new, k, v, l, rr, n);
            rr = 0;
        } else {
            L::alloc_write(new, k, v, l, r, n);
        }
        l = 0;
    }
    if l != 0 {
        // The while loop above didn't run, i.e. the insertion
        // happened at the end of the page. In this case, we haven't
        // had a chance to update the left page, so do it now.
        L::set_left_child(new, *n, l)
    }
}

/// The very unsurprising `merge` function
pub(super) fn merge<
    'a,
    T: AllocPage + LoadPage,
    K: ?Sized + core::fmt::Debug,
    V: ?Sized + core::fmt::Debug,
    P: BTreeMutPage<K, V>,
    L: AllocWrite<K, V>,
>(
    txn: &mut T,
    mut m: Concat<K, V, P>,
) -> Result<Op<'a, T, K, V>, T::Error> {
    // Here, we first allocate a page, then clone both pages onto it,
    // in a different order depending on whether the modified page is
    // the left or the right child.
    //
    // Note that in the case that this merge happens immediately after
    // a put that reallocated the two sides of the merge in order to
    // split (not all splits do that), we could be slightly more
    // efficient, but with considerably more code.
    let mut new = txn.alloc_page()?;
    P::init(&mut new);

    let mut n = 0;
    if m.mod_is_left {
        modify::<_, _, _, _, L>(txn, &mut new, &mut m.modified, &mut n);
        let mut rc = P::cursor_first(&m.other);
        let l = P::left_child(m.other.as_page(), &rc);
        L::alloc_write(&mut new, m.mid.0, m.mid.1, 0, l, &mut n);
        while let Some((k, v, r)) = P::next(txn, m.other.as_page(), &mut rc) {
            L::alloc_write(&mut new, k, v, 0, r, &mut n);
        }
    } else {
        let mut rc = P::cursor_first(&m.other);
        let mut l = P::left_child(m.other.as_page(), &rc);
        while let Some((k, v, r)) = P::next(txn, m.other.as_page(), &mut rc) {
            L::alloc_write(&mut new, k, v, l, r, &mut n);
            l = 0;
        }
        L::alloc_write(&mut new, m.mid.0, m.mid.1, 0, 0, &mut n);
        modify::<_, _, _, _, L>(txn, &mut new, &mut m.modified, &mut n);
    }

    let b0 = if m.modified.page.is_dirty() { 1 } else { 0 };
    let b1 = if m.other.is_dirty() { 1 } else { 0 };
    Ok(Op::Merged {
        page: new,
        freed: [m.modified.page.offset | b0, m.other.offset | b1],
        marker: core::marker::PhantomData,
    })
}

fn clone<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized, L: Alloc>(
    page: crate::Page,
    new: &mut MutPage,
    s: Offsets<L::Offset>,
    n: &mut isize,
) {
    for off in s.0.iter() {
        let (r, off): (u64, usize) = (*off).into();
        unsafe {
            let ptr = page.data.as_ptr().add(off);
            let size = entry_size::<K, V>(ptr);
            // Reserve the space on the page
            let hdr = header_mut(new);
            let data = hdr.data() as u16;
            let off_new = data - size as u16;
            hdr.set_data(off_new);
            hdr.set_n(hdr.n() + 1);
            if hdr.is_leaf() {
                hdr.incr(2 + size);
                let ptr = new.0.data.offset(HDR as isize + *n * 2) as *mut u16;
                *ptr = (off_new as u16).to_le();
            } else {
                hdr.incr(8 + size);
                // Set the offset to this new entry in the offset
                // array, along with the right child page.
                let ptr = new.0.data.offset(HDR as isize + *n * 8) as *mut u64;
                *ptr = (r | off_new as u64).to_le();
            }
            core::ptr::copy_nonoverlapping(ptr, new.0.data.offset(off_new as isize), size);
        }
        *n += 1;
    }
}
