use super::*;

/// This trait contains methods common to leaves and internal
/// nodes. These methods are meant to be just a few lines long each,
/// and avoid duplicating code in higher-level functions where just a
/// few constants change between internal nodes and leaves.
pub(crate) trait Alloc {
    /// Is there enough room to add one entry into this page (without cloning)?
    fn can_alloc<K: Storable, V: Storable>(hdr: &Header) -> bool;

    /// If we clone the page, will there be enough room for one entry?
    fn can_compact<K: Storable, V: Storable>(hdr: &Header) -> bool;

    /// Remove the leftmost `n` elements from the page. On leaves,
    /// this moves the last truncated element to the end of the page
    /// and returns a pointer to that element (this function is only
    /// used in `crate::btree::put`, and the pointer becomes invalid
    /// at the end of the `crate::btree::put`).
    ///
    /// Returning the last deleted element isn't required for internal
    /// nodes, since the entries are still valid there.
    fn truncate_left<K: Storable, V: Storable>(
        page: &mut MutPage,
        n: usize,
    ) -> Option<(*const K, *const V)>;

    /// Allocate a new entry (size inferred), and return the offset on
    /// the page where the new entry can be copied.
    fn alloc_insert<K: Storable, V: Storable>(new: &mut MutPage, n: &mut isize, r: u64) -> usize;

    /// Set the right child of the `n`th entry to `r`. If `n == -1`,
    /// this method can be used to set the leftmost child of a page.
    fn set_right_child(new: &mut MutPage, n: isize, r: u64);

    /// "Slices" of offsets, which aren't really slices in the case of
    /// leaves, but just intervals or "ranges".
    fn offset_slice<'a, T: LoadPage, K: Storable, V: Storable>(
        page: crate::Page<'a>,
    ) -> Offsets<'a>;

    /// First element of a slice offset. For the sake of code
    /// simplicity, we return a `u64` even for leaves. In internal
    /// nodes, the 52 MSBs encode a child page, and the 12 LSBs encode
    /// an offset in the page.
    fn first<'a, K, V>(off: &Offsets<'a>) -> u64;

    /// The tuple and right child at offset `off`.
    fn kv<'a, K: Storable, V: Storable>(page: crate::Page, off: u64) -> (&'a K, &'a V, u64);
}

/// The type of offsets.
#[derive(Debug, Clone)]
pub enum Offsets<'a> {
    /// Slices of child pages and offset-in-page for internal nodes,
    Slice(&'a [u64]),
    /// Ranges for leaves.
    Range(core::ops::Range<usize>),
}

impl<'a> Offsets<'a> {
    /// Splitting an offset slice, with the same semantics as
    /// `split_at` for slices, except if `mid` is equal to the length,
    /// in which case we return `(self, &[])`.
    pub fn split_at(&self, mid: usize) -> (Self, Self) {
        match self {
            Offsets::Slice(s) if mid < s.len() => {
                let (a, b) = s.split_at(mid);
                (Offsets::Slice(a), Offsets::Slice(b))
            }
            Offsets::Slice(s) => {
                debug_assert_eq!(mid, s.len());
                (Offsets::Slice(s), Offsets::Slice(&[][..]))
            }
            Offsets::Range(r) => (
                Offsets::Range(r.start..r.start + mid),
                Offsets::Range(r.start + mid..r.end),
            ),
        }
    }
}

pub struct Leaf {}
pub struct Internal {}

impl Alloc for Leaf {
    // Checking if there's enough room is just bookkeeping.
    fn can_alloc<K: Storable, V: Storable>(hdr: &Header) -> bool {
        let f = core::mem::size_of::<Tuple<K, V>>();
        let al = core::mem::align_of::<Tuple<K, V>>();
        let header_size = (HDR + al - 1) & !(al - 1);
        header_size + (hdr.n() as usize + 1) * f <= PAGE_SIZE
    }

    /// There's no possible compaction on leaves, it's the same as allocating.
    fn can_compact<K: Storable, V: Storable>(hdr: &Header) -> bool {
        Self::can_alloc::<K, V>(hdr)
    }

    fn set_right_child(_: &mut MutPage, _: isize, _: u64) {}

    fn offset_slice<'a, T: LoadPage, K: Storable, V: Storable>(
        page: crate::Page<'a>,
    ) -> Offsets<'a> {
        let hdr = header(page);
        Offsets::Range(0..(hdr.n() as usize))
    }

    /// This returns an offset on the page, so we need to compute that.
    fn first<'a, K, V>(off: &Offsets<'a>) -> u64 {
        match off {
            Offsets::Slice(_) => unreachable!(),
            Offsets::Range(r) => {
                let size = core::mem::size_of::<Tuple<K, V>>();
                let al = core::mem::align_of::<Tuple<K, V>>();
                let hdr_size = (HDR + al - 1) & !(al - 1);
                (hdr_size + r.start * size) as u64
            }
        }
    }

    fn kv<'a, K: Storable, V: Storable>(page: crate::Page, off: u64) -> (&'a K, &'a V, u64) {
        unsafe {
            let tup = &*(page.data.as_ptr().add(off as usize) as *const Tuple<K, V>);
            (&tup.k, &tup.v, 0)
        }
    }

    /// Here, we just move `total - *n` elements to the right, and
    /// increase the bookkeeping values (occupied bytes and number of
    /// elements).
    fn alloc_insert<K: Storable, V: Storable>(new: &mut MutPage, n: &mut isize, _: u64) -> usize {
        let f = core::mem::size_of::<Tuple<K, V>>();
        let al = core::mem::align_of::<Tuple<K, V>>();
        let hdr_size = (HDR + al - 1) & !(al - 1);
        let hdr_n = header_mut(new).n();
        unsafe {
            core::ptr::copy(
                new.0.data.add(hdr_size + (*n as usize) * f),
                new.0.data.add(hdr_size + (*n as usize) * f + f),
                (hdr_n as usize - (*n as usize)) * f,
            );
        }
        let hdr = header_mut(new);
        hdr.set_n(hdr.n() + 1);
        hdr.incr(f);
        hdr_size + (*n as usize) * f
    }

    fn truncate_left<K: Storable, V: Storable>(
        page: &mut MutPage,
        n: usize,
    ) -> Option<(*const K, *const V)> {
        let f = core::mem::size_of::<Tuple<K, V>>();
        let al = core::mem::align_of::<Tuple<K, V>>();
        let hdr_size = (HDR + al - 1) & !(al - 1);
        let hdr = header_mut(page);
        let hdr_n = hdr.n();
        hdr.set_n(hdr_n - n as u16);
        hdr.decr(n * f);

        // Now, this is a bit trickier. This performs a rotation by 1
        // without all the rotation machinery from the Rust core
        // library.
        //
        // Indeed, since we're in a leaf, we are effectively erasing
        // the split entry. There is a choice to be made here, between
        // passing the entry by value or by reference. Because splits
        // might cascade with the same middle entry, passing it by
        // value may be significantly worse if the tree is deep, and
        // is never significantly better (we'll end up copying this
        // entry twice anyway).
        unsafe {
            let mut swap: core::mem::MaybeUninit<Tuple<K, V>> = core::mem::MaybeUninit::uninit();
            core::ptr::copy(
                page.0.data.add(hdr_size + (n - 1) * f),
                swap.as_mut_ptr() as *mut u8,
                f,
            );
            core::ptr::copy(
                page.0.data.add(hdr_size + n * f),
                page.0.data.add(hdr_size),
                (hdr_n as usize - n) * f,
            );
            core::ptr::copy(
                swap.as_ptr() as *mut u8,
                page.0.data.add(hdr_size + (hdr_n as usize - n) * f),
                f,
            );
            let tup =
                &*(page.0.data.add(hdr_size + (hdr_n as usize - n) * f) as *const Tuple<K, V>);
            Some((&tup.k, &tup.v))
        }
    }
}

impl Alloc for Internal {
    fn can_alloc<K: Storable, V: Storable>(hdr: &Header) -> bool {
        (HDR as usize) + (hdr.n() as usize + 1) * 8 + core::mem::size_of::<Tuple<K, V>>()
            < hdr.data() as usize
    }

    fn can_compact<K: Storable, V: Storable>(hdr: &Header) -> bool {
        (HDR as usize)
            + ((hdr.left_page() & 0xfff) as usize)
            + 8
            + core::mem::size_of::<Tuple<K, V>>()
            <= PAGE_SIZE
    }

    /// Set the right-hand child in the offset array, preserving the
    /// current offset.
    fn set_right_child(page: &mut MutPage, n: isize, r: u64) {
        unsafe {
            debug_assert_eq!(r & 0xfff, 0);
            let ptr = page.0.data.offset(HDR as isize + n * 8) as *mut u64;
            let off = u64::from_le(*ptr) & 0xfff;
            *ptr = (r | off as u64).to_le();
        }
    }

    fn offset_slice<'a, T, K: Storable, V: Storable>(page: crate::Page<'a>) -> Offsets<'a> {
        let hdr = header(page);
        unsafe {
            Offsets::Slice(core::slice::from_raw_parts(
                page.data.as_ptr().add(HDR) as *const u64,
                hdr.n() as usize,
            ))
        }
    }

    fn first<'a, K, V>(off: &Offsets<'a>) -> u64 {
        match off {
            Offsets::Slice(s) => s[0],
            Offsets::Range(_) => unreachable!(),
        }
    }

    fn kv<'a, K: Storable, V: Storable>(page: crate::Page, off: u64) -> (&'a K, &'a V, u64) {
        unsafe {
            let tup = &*(page.data.as_ptr().add((off & 0xfff) as usize) as *const Tuple<K, V>);
            (&tup.k, &tup.v, off & !0xfff)
        }
    }

    // Much simpler than in leaves, because we just need to move the
    // offsets. There's a little bit of bookkeeping involved though.
    fn truncate_left<K: Storable, V: Storable>(
        page: &mut MutPage,
        n: usize,
    ) -> Option<(*const K, *const V)> {
        let hdr_n = header_mut(page).n();
        unsafe {
            // We want to copy the left child of the first entry that
            // will be kept alive as the left child of the page.
            core::ptr::copy(
                page.0.data.add(HDR + (n - 1) * 8),
                page.0.data.add(HDR - 8),
                // We're removing n entries, so we need to copy the
                // remaining `hdr_n - n`, plus the leftmost child
                // (hence the + 1).
                (hdr_n as usize - n + 1) * 8,
            );
        }
        // Remaining occupied size on the page (minus the header).
        let size = (8 + core::mem::size_of::<Tuple<K, V>>()) * (hdr_n as usize - n);
        let hdr = header_mut(page);
        hdr.set_n(hdr_n - n as u16);
        // Because the leftmost child has been copied from an entry
        // containing an offset, its 12 LBSs are still enconding an
        // offset on the page, whereas it should encode the occupied
        // bytes on the page. Reset it.
        hdr.set_occupied(size as u64);
        None
    }

    fn alloc_insert<K: Storable, V: Storable>(new: &mut MutPage, n: &mut isize, r: u64) -> usize {
        let hdr = header_mut(new);

        // Move the `data` field one entry to the left.
        let data = hdr.data() as u16;
        let off_new = data - core::mem::size_of::<Tuple<K, V>>() as u16;
        hdr.set_data(off_new);

        // Increment the number of entries, add the newly occupied size.
        hdr.set_n(hdr.n() + 1);
        hdr.incr(8 + core::mem::size_of::<Tuple<K, V>>());

        let hdr_n = hdr.n();
        unsafe {
            // Make space in the offset array by moving the last
            // `hdr_n - *n` elements.
            core::ptr::copy(
                new.0.data.add(HDR + (*n as usize) * 8),
                new.0.data.add(HDR + (*n as usize) * 8 + 8),
                (hdr_n as usize - (*n as usize)) * 8,
            );
            // Add the offset.
            let ptr = new.0.data.offset(HDR as isize + *n * 8) as *mut u64;
            *ptr = (r | off_new as u64).to_le();
        }
        off_new as usize
    }
}

impl<K: Storable, V: Storable> crate::btree::page_unsized::AllocWrite<K, V> for Internal {
    fn alloc_write(new: &mut MutPage, k0: &K, v0: &V, l: u64, r: u64, n: &mut isize) {
        alloc_write::<K, V, Self>(new, k0, v0, l, r, n)
    }
    fn set_left_child(new: &mut MutPage, n: isize, l: u64) {
        if l > 0 {
            Internal::set_right_child(new, n - 1, l);
        }
    }
}

impl<K: Storable, V: Storable> crate::btree::page_unsized::AllocWrite<K, V> for Leaf {
    fn alloc_write(new: &mut MutPage, k0: &K, v0: &V, l: u64, r: u64, n: &mut isize) {
        alloc_write::<K, V, Self>(new, k0, v0, l, r, n)
    }
    fn set_left_child(_new: &mut MutPage, _n: isize, l: u64) {
        debug_assert_eq!(l, 0);
    }
}

/// Simply allocate an entry in the page, copy it, and set its right
/// and left children.
fn alloc_write<K: Storable, V: Storable, L: Alloc>(
    new: &mut MutPage,
    k0: &K,
    v0: &V,
    l: u64,
    r: u64,
    n: &mut isize,
) {
    let off_new = L::alloc_insert::<K, V>(new, n, r);
    unsafe {
        let new_ptr = &mut *(new.0.data.add(off_new as usize) as *mut Tuple<K, V>);
        core::ptr::copy_nonoverlapping(k0, &mut new_ptr.k, 1);
        core::ptr::copy_nonoverlapping(v0, &mut new_ptr.v, 1);
    }
    if l > 0 {
        L::set_right_child(new, *n - 1, l);
    }
    *n += 1;
}
