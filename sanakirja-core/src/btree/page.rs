//! Implementation of B tree pages for Sized types, i.e. types whose
//! representation has a size known at compile time (and the same as
//! [`core::mem::size_of()`]).
//!
//! The details of the implementation are as follows:
//!
//! - The page starts with a 16 bytes header of the following form
//! (where all the fields are encoded in Little-Endian):
//!
//!     ```
//!     #[repr(C)]
//!     pub struct Header {

//!         /// Offset to the first entry in the page, shifted 3 bits
//!         /// to the right to allow for the dirty bit (plus two
//!         /// extra bits, zero for now), as explained in the
//!         /// documentation of CowPage, at the root of this
//!         /// crate. This is 4096 for empty pages, and it is unused
//!         /// for leaves. Moreover, this field can't be increased:
//!         /// when it reaches the bottom, the page must be cloned.
//!         data: u16,
//!         /// Number of entries on the page.
//!         n: u16,
//!         /// CRC (if used).
//!         crc: u32,

//!         /// The 52 most significant bits are the left child of
//!         /// this page (0 for leaves), while the 12 LSBs represent
//!         /// the space this page would take when cloned from scratch,
//!         /// minus the header. The reason for this is that entries
//!         /// in internal nodes aren't really removed when deleted,
//!         /// they're only "unlinked" from the array of offsets (see
//!         /// below). Therefore, we must have a way to tell when a
//!         /// page can be "compacted" to reclaim space.

//!         left_page: u64,
//!     }
//!     ```

//! - For leaves, the rest of the page has the same representation as
//! an array of length `n`, of elements of type `Tuple<K, V>`:
//!   ```
//!   #[repr(C)]
//!   struct Tuple<K, V> {
//!       k: K,
//!       v: V,
//!   }
//!   ```
//!   If the alignment of that structure is more than 16 bytes, we
//!   need to add some padding between the header and that array.

//! - For internal nodes, the rest of the page starts with an array of
//! length `n` of Little-Endian-encoded [`u64`], where the 12 least
//! significant bits of each [`u64`] are an offset to a `Tuple<K, V>` in
//! the page, and the 52 other bits are an offset in the file to the
//! right child of the entry.
//!
//!   Moreover, the offset represented by the 12 LSBs is after (or at)
//!   `header.data`.

//!   We say we can "allocate" in the page if the `data` of the header
//!   is greater than or equal to the position of the last "offset",
//!   plus the size we want to allocate (note that since we allocate
//!   from the end of the page, `data` is always a multiple of the
//!   alignment of `Tuple<K, V>`).

use super::*;
use crate::btree::del::*;
use crate::btree::put::*;
use core::cmp::Ordering;

mod alloc; // The "alloc" trait, to provide common methods for leaves and internal nodes.

mod put; // Inserting a new value onto a page (possibly splitting the page).

mod rebalance; // Rebalance two sibling pages to the left or to the right.

use super::page_unsized::{cursor::PageCursor, header};
use alloc::*;
use header::*;
use rebalance::*;

/// This struct is used to allocate a pair `(K, V)` on the stack, and
/// copy it from a C pointer from a page.
///
/// This is also used to form slices of pairs in order to use
/// functions from the core library.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
struct Tuple<K, V> {
    k: K,
    v: V,
}

/// Empty type implementing `BTreePage` and `BTreeMutPage`.
#[derive(Debug)]
pub struct Page<K, V> {
    k: core::marker::PhantomData<K>,
    v: core::marker::PhantomData<V>,
}

impl<K: Storable, V: Storable> super::BTreePage<K, V> for Page<K, V> {
    // Cursors are quite straightforward. One non-trivial thing is
    // that they represent both a position on a page and the interval
    // from that position to the end of the page, as is apparent in
    // their `split_at` method.
    //
    // Another thing to note is that -1 and `c.total` are valid
    // positions for a cursor `c`. The reason for this is that
    // position `-1` has a right child (which is the first element's
    // left child).

    type Cursor = PageCursor;

    fn is_empty(c: &Self::Cursor) -> bool {
        c.cur >= c.total as isize
    }

    fn is_init(c: &Self::Cursor) -> bool {
        c.cur < 0
    }

    fn cursor_before(p: &crate::CowPage) -> Self::Cursor {
        PageCursor::new(p, -1)
    }

    fn cursor_after(p: &crate::CowPage) -> Self::Cursor {
        PageCursor::after(p)
    }

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
        if c.cur >= c.total as isize {
            return false;
        }
        c.cur += 1;
        true
    }
    fn move_prev(c: &mut Self::Cursor) -> bool {
        if c.cur < 0 {
            return false;
        }
        c.cur -= 1;
        true
    }

    fn current<'a, T: LoadPage>(
        _txn: &T,
        page: crate::Page<'a>,
        c: &Self::Cursor,
    ) -> Option<(&'a K, &'a V, u64)> {
        // First, there's no current entry if the cursor is outside
        // the range of entries.
        if c.cur < 0 || c.cur >= c.total as isize {
            None
        } else if c.is_leaf {
            // Else, if this is a leaf, the elements are packed
            // together in a contiguous array.
            //
            // This means that the header may be followed by padding
            // (in order to align the entries). These are constants
            // known at compile-time, so `al` and `hdr` are optimised
            // away by the compiler.
            let al = core::mem::align_of::<Tuple<K, V>>();

            // The following is a way to compute the first multiple of
            // `al` after `HDR`, assuming `al` is a power of 2 (which
            // is always the case since we get it from `align_of`).
            let hdr = (HDR + al - 1) & !(al - 1);

            // The position of the `Tuple<K, V>` we're looking for is
            // `f * cur` bytes after the padded header (because
            // `size_of` includes alignment padding).
            let f = core::mem::size_of::<Tuple<K, V>>();
            let kv = unsafe {
                &*(page.data.as_ptr().add(hdr + c.cur as usize * f) as *const Tuple<K, V>)
            };
            Some((&kv.k, &kv.v, 0))
        } else {
            // Internal nodes have an extra level of indirection: we
            // first need to find `off`, the offset in the page, in
            // the initial array of offsets. Since these offsets are
            // `u64`, and the header is of size 16 bytes, the array is
            // already aligned.
            unsafe {
                let off =
                    u64::from_le(*(page.data.as_ptr().add(HDR + 8 * c.cur as usize) as *const u64));
                // Check that we aren't reading outside of the page
                // (for example because of a malformed offset).
                assert!((off as usize & 0xfff) + core::mem::size_of::<Tuple<K, V>>() <= 4096);

                // Once we have the offset, cast its 12 LSBs to a
                // position in the page, and read the `Tuple<K, V>` at
                // that position.
                let kv = &*(page.data.as_ptr().add((off as usize) & 0xfff) as *const Tuple<K, V>);
                Some((&kv.k, &kv.v, off & !0xfff))
            }
        }
    }

    // The left and right child methods aren't really surprising. One
    // thing to note is that cursors are always in positions between
    // `-1` and `c.total` (bounds included), so we only have to check
    // one side of the bound in the assertions.
    //
    // We also check, before entering the `unsafe` sections, that
    // we're only reading data that is on a page.
    fn left_child(page: crate::Page, c: &Self::Cursor) -> u64 {
        if c.is_leaf {
            0
        } else {
            assert!(c.cur >= 0 && HDR as isize + c.cur * 8 - 8 <= 4088);
            let off =
                unsafe { *(page.data.as_ptr().offset((HDR as isize + c.cur * 8) - 8) as *const u64) };
            u64::from_le(off) & !0xfff
        }
    }
    fn right_child(page: crate::Page, c: &Self::Cursor) -> u64 {
        if c.is_leaf {
            0
        } else {
            assert!(c.cur < c.total as isize && HDR as isize + c.cur * 8 <= 4088);
            let off =
                unsafe { *(page.data.as_ptr().offset(HDR as isize + c.cur * 8) as *const u64) };
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
                    // Just read the tuple and return it.
                    if c.is_leaf {
                        let f = core::mem::size_of::<Tuple<K, V>>();
                        let al = core::mem::align_of::<Tuple<K, V>>();
                        let hdr_size = (HDR + al - 1) & !(al - 1);
                        let tup =
                            &*(page.data.as_ptr().add(hdr_size + f * n) as *const Tuple<K, V>);
                        Ok((&tup.k, &tup.v, 0))
                    } else {
                        let off =
                            u64::from_le(*(page.data.as_ptr().add(HDR + n * 8) as *const u64));
                        let tup =
                            &*(page.data.as_ptr().add(off as usize & 0xfff) as *const Tuple<K, V>);
                        Ok((&tup.k, &tup.v, off & !0xfff))
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

impl<K: Storable + core::fmt::Debug, V: Storable + core::fmt::Debug> super::BTreeMutPage<K, V>
    for Page<K, V>
{
    // Once again, this is quite straightforward.
    fn init(page: &mut MutPage) {
        let h = header_mut(page);
        h.init();
    }

    // When deleting from internal nodes, we take a replacement from
    // one of the leaves (in our current implementation, the leftmost
    // entry of the right subtree). This method copies an entry from
    // the leaf onto the program stack, which is necessary since
    // deletions in leaves overwrites entries.
    //
    // Another design choice would have been to do the same as for the
    // unsized implementation, but in this case this would have meant
    // copying the saved value to the end of the leaf, potentially
    // preventing merges, and not even saving a memory copy.
    type Saved = (K, V);

    fn save_deleted_leaf_entry(k: &K, v: &V) -> Self::Saved {
        unsafe {
            let mut k0 = core::mem::MaybeUninit::uninit();
            let mut v0 = core::mem::MaybeUninit::uninit();
            core::ptr::copy_nonoverlapping(k, k0.as_mut_ptr(), 1);
            core::ptr::copy_nonoverlapping(v, v0.as_mut_ptr(), 1);
            (k0.assume_init(), v0.assume_init())
        }
    }

    unsafe fn from_saved<'a>(s: &Self::Saved) -> (&'a K, &'a V) {
        (core::mem::transmute(&s.0), core::mem::transmute(&s.1))
    }

    // `put` inserts one or two entries onto a node (internal or
    // leaf). This is implemented in the `put` module.
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
    ) -> Result<super::put::Put<'a, K, V>, T::Error> {
        assert!(c.cur >= 0);
        // In the sized case, deletions can never cause a split, so we
        // never have to insert two elements at the same position.
        assert!(k1v1.is_none());
        if r == 0 {
            put::put::<_, _, _, Leaf>(txn, page, mutable, replace, c.cur as usize, k0, v0, 0, 0)
        } else {
            put::put::<_, _, _, Internal>(txn, page, mutable, replace, c.cur as usize, k0, v0, l, r)
        }
    }

    unsafe fn put_mut(page: &mut MutPage, c: &mut Self::Cursor, k0: &K, v0: &V, r: u64) {
        use super::page_unsized::AllocWrite;
        let mut n = c.cur;
        if r == 0 {
            Leaf::alloc_write(page, k0, v0, 0, r, &mut n);
        } else {
            Internal::alloc_write(page, k0, v0, 0, r, &mut n);
        }
        c.total += 1;
    }

    unsafe fn set_left_child(page: &mut MutPage, c: &Self::Cursor, l: u64) {
        let off = (page.0.data.add(HDR) as *mut u64).offset(c.cur - 1);
        *off = (l | (u64::from_le(*off) & 0xfff)).to_le();
    }

    // This function updates an internal node, setting the left child
    // of the cursor to `l`.
    fn update_left_child<T: AllocPage>(
        txn: &mut T,
        page: CowPage,
        mutable: bool,
        c: &Self::Cursor,
        l: u64,
    ) -> Result<crate::btree::put::Ok, T::Error> {
        assert!(!c.is_leaf && c.cur >= 0 && (c.cur as usize) <= c.total);
        let freed;
        let page = if mutable && page.is_dirty() {
            // If the page is mutable (dirty), just convert it to a
            // mutable page, and update.
            freed = 0;
            MutPage(page)
        } else {
            // Else, clone the page.
            let mut new = txn.alloc_page()?;
            <Page<K, V> as BTreeMutPage<K, V>>::init(&mut new);
            // First clone the left child of the page.
            let l = header(page.as_page()).left_page() & !0xfff;
            let hdr = header_mut(&mut new);
            hdr.set_left_page(l);
            // And then the rest of the page.
            let s = Internal::offset_slice::<T, K, V>(page.as_page());
            clone::<K, V, Internal>(page.as_page(), &mut new, s, &mut 0);
            // Mark the former version of the page as free.
            freed = page.offset | if page.is_dirty() { 1 } else { 0 };
            new
        };
        // Finally, update the left child of the cursor.
        unsafe {
            let off = (page.0.data.add(HDR) as *mut u64).offset(c.cur - 1);
            *off = (l | (u64::from_le(*off) & 0xfff)).to_le();
        }
        Ok(Ok { page, freed })
    }

    fn del<T: AllocPage>(
        txn: &mut T,
        page: crate::CowPage,
        mutable: bool,
        c: &PageCursor,
        l: u64,
    ) -> Result<(MutPage, u64), T::Error> {
        assert!(c.cur >= 0 && (c.cur as usize) < c.total);
        if mutable && page.is_dirty() {
            // In the mutable case, we just need to move some memory
            // around.
            let p = page.data;
            let mut page = MutPage(page);
            let hdr = header_mut(&mut page);
            let f = core::mem::size_of::<Tuple<K, V>>();
            if c.is_leaf {
                // In leaves, we need to move the n - c - 1 elements
                // that are strictly after the cursor, by `f` (the
                // size of an entry).
                //
                // Here's the reasoning to avoid off-by-one errors: if
                // `c` is 0 (i.e. we're deleting the first element on
                // the page), we remove one entry, so there are n - 1
                // remaining entries.
                let n = hdr.n() as usize;
                let hdr_size = {
                    // As usual, header + padding
                    let al = core::mem::align_of::<Tuple<K, V>>();
                    (HDR + al - 1) & !(al - 1)
                };
                let off = hdr_size + c.cur as usize * f;
                unsafe {
                    core::ptr::copy(p.add(off + f), p.add(off), f * (n - c.cur as usize - 1));
                }
                // Removing `f` bytes from the page.
                hdr.decr(f);
            } else {
                // Internal nodes are easier to deal with, as we just
                // have to move the offsets.
                unsafe {
                    let ptr = p.add(HDR + c.cur as usize * 8) as *mut u64;
                    core::ptr::copy(ptr.offset(1), ptr, hdr.n() as usize - c.cur as usize - 1);
                }
                // Removing `f` bytes from the page (the tuple), plus
                // one 8-bytes offset.
                hdr.decr(f + 8);

                // Updating the left page if necessary.
                if l > 0 {
                    unsafe {
                        let off = (p.add(HDR) as *mut u64).offset(c.cur as isize - 1);
                        *off = (l | (u64::from_le(*off) & 0xfff)).to_le();
                    }
                }
            }
            hdr.set_n(hdr.n() - 1);
            // Returning the mutable page itself, and 0 (for "no page freed")
            Ok((page, 0))
        } else {
            // Immutable pages need to be cloned. The strategy is the
            // same in both cases: get an "offset slice", split it at
            // the cursor, remove the first entry of the second half,
            // and clone.
            let mut new = txn.alloc_page()?;
            <Page<K, V> as BTreeMutPage<K, V>>::init(&mut new);
            if c.is_leaf {
                let s = Leaf::offset_slice::<T, K, V>(page.as_page());
                let (s0, s1) = s.split_at(c.cur as usize);
                let (_, s1) = s1.split_at(1);
                let mut n = 0;
                clone::<K, V, Leaf>(page.as_page(), &mut new, s0, &mut n);
                clone::<K, V, Leaf>(page.as_page(), &mut new, s1, &mut n);
            } else {
                // Internal nodes a bit trickier, since the left child
                // is not counted in the "offset slice", so we need to
                // clone it separately. Also, the `l` argument to this
                // function might be non-zero in this case.
                let s = Internal::offset_slice::<T, K, V>(page.as_page());
                let (s0, s1) = s.split_at(c.cur as usize);
                let (_, s1) = s1.split_at(1);

                // First, clone the left child of the page.
                let hdr = header(page.as_page());
                let left = hdr.left_page() & !0xfff;
                unsafe { *(new.0.data.add(HDR - 8) as *mut u64) = left.to_le() };

                // Then, clone the entries strictly before the cursor
                // (i.e. clone `s0`).
                let mut n = 0;
                clone::<K, V, Internal>(page.as_page(), &mut new, s0, &mut n);

                // If we need to update the left child of the deleted
                // item, do it.
                if l > 0 {
                    unsafe {
                        let off = new.0.data.offset(HDR as isize + (n - 1) * 8) as *mut u64;
                        *off = (l | (u64::from_le(*off) & 0xfff)).to_le();
                    }
                }

                // Finally, clone the right half of the page (`s1`).
                clone::<K, V, Internal>(page.as_page(), &mut new, s1, &mut n);
            }
            Ok((new, page.offset))
        }
    }

    // Decide what to do with the concatenation of two neighbouring
    // pages, with a middle element.
    fn merge_or_rebalance<'a, T: AllocPage>(
        txn: &mut T,
        m: Concat<'a, K, V, Self>,
    ) -> Result<Op<'a, T, K, V>, T::Error> {
        // First evaluate the size of the middle element on a page.
        let (hdr_size, mid_size) = if m.modified.c0.is_leaf {
            let al = core::mem::align_of::<Tuple<K, V>>();
            (
                (HDR + al - 1) & !(al - 1),
                core::mem::size_of::<Tuple<K, V>>(),
            )
        } else {
            (HDR, 8 + core::mem::size_of::<Tuple<K, V>>())
        };

        // Evaluate the size of the modified half of the concatenation
        // (which includes the header).
        let mod_size = size::<K, V>(&m.modified);
        // Add the "occupied" size (which excludes the header).
        let occupied = {
            let hdr = header(m.other.as_page());
            (hdr.left_page() & 0xfff) as usize
        };

        // One surprising observation here is that adding the sizes
        // works. This is surprising because of alignment and
        // padding. It works because we can split the sizes into an
        // offset part (always 8 bytes) and a data part (of a constant
        // alignment), and thus we never need any padding anywhere on
        // the page.
        if mod_size + mid_size + occupied <= PAGE_SIZE {
            // If the concatenation fits on a page, merge.
            return if m.modified.c0.is_leaf {
                super::page_unsized::merge::<_, _, _, _, Leaf>(txn, m)
            } else {
                super::page_unsized::merge::<_, _, _, _, Internal>(txn, m)
            };
        }
        // If the modified page is large enough, or if the other page
        // has only just barely the minimum number of elements to be
        // at least half-full, return.
        //
        // The situation where the other page isn't full enough might
        // happen for example if elements occupy exactly 1/5th of a
        // page + 1 byte, and the modified page has 2 of them after
        // the deletion, while the other page has 3.
        if mod_size >= PAGE_SIZE / 2 || hdr_size + occupied - mid_size < PAGE_SIZE / 2 {
            if let Some((k, v)) = m.modified.ins {
                // Perform the required modification and return.
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
                // `ins2` is only ever used when the page immediately
                // below a deletion inside an internal node has split,
                // and we need to replace the deleted value, *and*
                // insert the middle entry of the split.
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
            super::page_unsized::rebalance::rebalance_right::<_, _, _, Self>(txn, m)
        }
    }
}

/// Size of a modified page (including the header).
fn size<K: Storable, V: Storable>(m: &ModifiedPage<K, V, Page<K, V>>) -> usize {
    let mut total = {
        let hdr = header(m.page.as_page());
        (hdr.left_page() & 0xfff) as usize
    };
    if m.c1.is_leaf {
        let al = core::mem::align_of::<Tuple<K, V>>();
        total += (HDR + al - 1) & (!al - 1);
    } else {
        total += HDR
    };

    // Extra size for the offsets.
    let extra = if m.c1.is_leaf { 0 } else { 8 };

    if m.ins.is_some() {
        total += extra + core::mem::size_of::<Tuple<K, V>>();
        if m.ins2.is_some() {
            total += extra + core::mem::size_of::<Tuple<K, V>>()
        }
    }
    // If we skip the first entry of `m.c1`, remove its size.
    if m.skip_first {
        total -= extra + core::mem::size_of::<Tuple<K, V>>()
    }
    total
}

/// Linear search, leaf version. This is relatively straightforward.
fn leaf_linear_search<T: LoadPage, K: Storable, V: Storable>(
    txn: &T,
    k0: &K,
    v0: Option<&V>,
    s: &[Tuple<K, V>],
) -> Result<usize, usize> {
    let mut n = 0;
    for sm in s.iter() {
        match sm.k.compare(txn, k0) {
            Ordering::Less => n += 1,
            Ordering::Greater => return Err(n),
            Ordering::Equal => {
                if let Some(v0) = v0 {
                    match sm.v.compare(txn, v0) {
                        Ordering::Less => n += 1,
                        Ordering::Greater => return Err(n),
                        Ordering::Equal => return Ok(n),
                    }
                } else {
                    return Ok(n);
                }
            }
        }
    }
    Err(n)
}

/// An equivalent of `Ord::cmp` on `Tuple<K, V>` but using
/// `Storable::compare` instead of `Ord::cmp` on `K` and `V`.
fn cmp<T: LoadPage, K: Storable, V: Storable>(
    txn: &T,
    k0: &K,
    v0: Option<&V>,
    p: &[u8; 4096],
    off: u64,
) -> Ordering {
    let off = u64::from_le(off) & 0xfff;
    if off as usize + core::mem::size_of::<Tuple<K, V>>() > PAGE_SIZE {
        panic!(
            "off = {:?}, size = {:?}",
            off,
            core::mem::size_of::<Tuple<K, V>>()
        );
    }
    let tup = unsafe { &*(p.as_ptr().offset(off as isize & 0xfff) as *const Tuple<K, V>) };
    match tup.k.compare(txn, k0) {
        Ordering::Equal => {
            if let Some(v0) = v0 {
                tup.v.compare(txn, v0)
            } else {
                Ordering::Equal
            }
        }
        o => o,
    }
}

/// Linear search for internal nodes. Does what it says.
unsafe fn internal_search<T: LoadPage, K: Storable, V: Storable>(
    txn: &T,
    k0: &K,
    v0: Option<&V>,
    s: &[u64],
    p: &[u8; 4096],
) -> Result<usize, usize> {
    for (n, off) in s.iter().enumerate() {
        match cmp(txn, k0, v0, p, *off) {
            Ordering::Less => {}
            Ordering::Greater => return Err(n),
            Ordering::Equal => return Ok(n),
        }
    }
    Err(s.len())
}

/// Lookup just forms slices of offsets (for internal nodes) or values
/// (for leaves), and runs an internal search on them.
unsafe fn lookup<T: LoadPage, K: Storable, V: Storable>(
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
        let al = core::mem::align_of::<Tuple<K, V>>();
        let hdr_size = (HDR + al - 1) & !(al - 1);
        let s = core::slice::from_raw_parts(
            page.data.as_ptr().add(hdr_size) as *const Tuple<K, V>,
            hdr.n() as usize,
        );
        leaf_linear_search(txn, k0, v0, s)
    } else {
        let s = core::slice::from_raw_parts(
            page.data.as_ptr().add(HDR) as *const u64,
            hdr.n() as usize,
        );
        internal_search(txn, k0, v0, s, page.data)
    }
}

/// Clone a slice of offsets onto a page. This essentially does what
/// it says. Note that the leftmost child of a page is not included in
/// the offset slices, so we don't have to handle it here.
///
/// This should really be in the `Alloc` trait, but Rust doesn't have
/// associated type constructors, so we can't have an associated type
/// that's sometimes a slice and sometimes a "Range".
fn clone<K: Storable, V: Storable, L: Alloc>(
    page: crate::Page,
    new: &mut MutPage,
    s: Offsets,
    n: &mut isize,
) {
    match s {
        Offsets::Slice(s) => {
            // We know we're in an internal node here.
            let size = core::mem::size_of::<Tuple<K, V>>();
            for off in s.iter() {
                let off = u64::from_le(*off);
                let r = off & !0xfff;
                let off = off & 0xfff;
                unsafe {
                    let ptr = page.data.as_ptr().add(off as usize);

                    // Reserve the space on the page
                    let hdr = header_mut(new);
                    let data = hdr.data() as u16;
                    let off_new = data - size as u16;
                    hdr.set_data(off_new);

                    // Copy the entry from the original page to its
                    // position on the new page.
                    core::ptr::copy_nonoverlapping(ptr, new.0.data.add(off_new as usize), size);

                    // Set the offset to this new entry in the offset
                    // array, along with the right child page.
                    let ptr = new.0.data.offset(HDR as isize + *n * 8) as *mut u64;
                    *ptr = (r | off_new as u64).to_le();
                }
                *n += 1;
            }
            let hdr = header_mut(new);
            hdr.set_n(hdr.n() + s.len() as u16);
            hdr.incr((8 + size) * s.len());
        }
        Offsets::Range(r) => {
            let size = core::mem::size_of::<Tuple<K, V>>();
            let a = core::mem::align_of::<Tuple<K, V>>();
            let header_size = (HDR + a - 1) & !(a - 1);
            let len = r.len();
            for off in r {
                unsafe {
                    let ptr = page.data.as_ptr().add(header_size + off * size);
                    let new_ptr = new.0.data.add(header_size + (*n as usize) * size);
                    core::ptr::copy_nonoverlapping(ptr, new_ptr, size);
                }
                *n += 1;
            }
            // On leaves, we do have to update everything manually,
            // because we're simply copying stuff.
            let hdr = header_mut(new);
            hdr.set_n(hdr.n() + len as u16);
            hdr.incr(size * len);
        }
    }
}
