use super::header::{header, header_mut, Header, HDR};
use super::*;

/// We'd love to share this trait with the sized implementation, but
/// unfortunately, the type parameters of almost all methods are
/// different.
pub(crate) trait Alloc {
    const OFFSET_SIZE: usize;

    /// Size (including the offset size) of the entry at position
    /// `cur`.
    fn current_size<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
        page: crate::Page,
        cur: isize,
    ) -> usize;

    /// Can we allocate an entry of `size` bytes, where `size` doesn't
    /// include the offset bytes?
    fn can_alloc(hdr: &Header, size: usize, n: usize) -> bool {
        (HDR as usize) + (hdr.n() as usize) * Self::OFFSET_SIZE + n * Self::OFFSET_SIZE + size
            <= hdr.data() as usize
    }

    /// If we cloned the page, could we allocate an entry of `size`
    /// bytes, where `size` doesn't include the offset bytes?
    fn can_compact(hdr: &Header, size: isize, n: usize) -> bool {
        (HDR as isize)
            + ((hdr.left_page() & 0xfff) as isize)
            + (n * Self::OFFSET_SIZE) as isize
            + size
            <= PAGE_SIZE as isize
    }

    /// Set the right child of the `n`th entry to `r`. If `n == -1`,
    /// this method can be used to set the leftmost child of a page.
    fn set_right_child(_new: &mut MutPage, _n: isize, _r: u64) {}

    /// Set the n^th offset on the page to `r`, which encodes a page
    /// offset in its 52 MSBs, and an offset on the page in its 12 LSBs.
    fn set_offset(new: &mut MutPage, n: isize, r: u64);

    /// The type of offsets, u64 in internal nodes, u16 in leaves.
    type Offset: Into<(u64, usize)> + Copy + core::fmt::Debug;

    fn offset_slice<'a>(page: crate::Page<'a>) -> Offsets<'a, Self::Offset>;
}

#[derive(Debug, Clone, Copy)]
pub struct Offsets<'a, A>(pub &'a [A]);

impl<'a, A: Copy> Offsets<'a, A> {
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        if mid < self.0.len() {
            let (a, b) = self.0.split_at(mid);
            (Offsets(a), Offsets(b))
        } else {
            debug_assert_eq!(mid, self.0.len());
            (self, Offsets(&[][..]))
        }
    }
}

pub struct Leaf {}
pub struct Internal {}

impl Alloc for Leaf {
    const OFFSET_SIZE: usize = 2;

    // Note: the size returned by this function includes the offset.
    fn current_size<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
        page: crate::Page,
        cur: isize,
    ) -> usize {
        // Find the offset of the current position, get its size.
        unsafe {
            debug_assert!(cur >= 0);
            let off = *(page.data.as_ptr().add(HDR + 2 * cur as usize) as *const u16);
            Self::OFFSET_SIZE
                + entry_size::<K, V>(page.data.as_ptr().add(u16::from_le(off) as usize))
        }
    }

    fn set_offset(new: &mut MutPage, n: isize, off: u64) {
        unsafe {
            let ptr = new.0.data.offset(HDR as isize + n * 2) as *mut u16;
            *ptr = (off as u16).to_le();
        }
    }

    type Offset = LeafOffset;

    fn offset_slice<'a>(page: crate::Page<'a>) -> Offsets<'a, Self::Offset> {
        let hdr_n = header(page).n();
        unsafe {
            Offsets(core::slice::from_raw_parts(
                page.data.as_ptr().add(HDR) as *const LeafOffset,
                hdr_n as usize,
            ))
        }
    }
}

impl Alloc for Internal {
    const OFFSET_SIZE: usize = 8;
    fn current_size<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
        page: crate::Page,
        cur: isize,
    ) -> usize {
        unsafe {
            8 + entry_size::<K, V>(page.data.as_ptr().add(
                (u64::from_le(*(page.data.as_ptr().add(HDR) as *const u64).offset(cur)) & 0xfff)
                    as usize,
            ))
        }
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

    fn set_offset(new: &mut MutPage, n: isize, off: u64) {
        unsafe {
            let ptr = new.0.data.offset(HDR as isize + n * 8) as *mut u64;
            *ptr = off.to_le();
        }
    }

    type Offset = InternalOffset;

    fn offset_slice<'a>(page: crate::Page<'a>) -> Offsets<'a, Self::Offset> {
        let hdr_n = header(page).n() as usize;
        unsafe {
            Offsets(core::slice::from_raw_parts(
                page.data.as_ptr().add(HDR) as *const InternalOffset,
                hdr_n,
            ))
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct LeafOffset(u16);

impl Into<(u64, usize)> for LeafOffset {
    fn into(self) -> (u64, usize) {
        (0, self.0 as usize)
    }
}

impl Into<usize> for LeafOffset {
    fn into(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct InternalOffset(u64);

impl Into<(u64, usize)> for InternalOffset {
    fn into(self) -> (u64, usize) {
        (self.0 & !0xfff, (self.0 & 0xfff) as usize)
    }
}

impl Into<usize> for InternalOffset {
    fn into(self) -> usize {
        self.0 as usize
    }
}

impl<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized> AllocWrite<K, V> for Leaf {
    fn alloc_write(new: &mut MutPage, k0: &K, v0: &V, l: u64, r: u64, n: &mut isize) {
        alloc_write::<K, V, Self>(new, k0, v0, l, r, n)
    }
    fn set_left_child(_new: &mut MutPage, _n: isize, l: u64) {
        debug_assert_eq!(l, 0);
    }
}

impl<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized> AllocWrite<K, V> for Internal {
    fn alloc_write(new: &mut MutPage, k0: &K, v0: &V, l: u64, r: u64, n: &mut isize) {
        alloc_write::<K, V, Self>(new, k0, v0, l, r, n)
    }
    fn set_left_child(new: &mut MutPage, n: isize, l: u64) {
        if l > 0 {
            Internal::set_right_child(new, n - 1, l);
        }
    }
}

// Allocate a new entry and copy (k0, v0) into the new slot.
fn alloc_write<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized, L: Alloc>(
    new: &mut MutPage,
    k0: &K,
    v0: &V,
    l: u64,
    r: u64,
    n: &mut isize,
) {
    let size = alloc_size(k0, v0);
    let off_new = alloc_insert::<K, V, L>(new, n, size, r);
    unsafe {
        let new_ptr = new.0.data.add(off_new);
        k0.write_to_page(new_ptr);
        let ks = k0.size();
        let v_ptr = new_ptr.add((ks + V::ALIGN - 1) & !(V::ALIGN - 1));
        v0.write_to_page(v_ptr);
    }
    if l > 0 {
        L::set_right_child(new, *n - 1, l);
    }
    *n += 1;
}

/// Reserve space on the page for `size` bytes of data (i.e. not
/// counting the offset), set the right child of the new position
/// to `r`, add the offset to the new data to the offset array,
/// and return the new offset.
fn alloc_insert<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized, L: Alloc>(
    new: &mut MutPage,
    n: &mut isize,
    size: usize,
    r: u64,
) -> usize {
    let hdr = header_mut(new);
    let data = hdr.data();
    // If we're here, the following assertion has been checked by the
    // `can_alloc` method.
    debug_assert!(HDR + (hdr.n() as usize + 1) * L::OFFSET_SIZE + size <= data as usize);
    hdr.set_data(data - size as u16);
    hdr.set_n(hdr.n() + 1);
    hdr.incr(L::OFFSET_SIZE + size);
    let off_new = data - size as u16;
    let hdr_n = hdr.n();

    // Making space for the new offset
    unsafe {
        core::ptr::copy(
            new.0.data.add(HDR + (*n as usize) * L::OFFSET_SIZE),
            new.0
                .data
                .add(HDR + (*n as usize) * L::OFFSET_SIZE + L::OFFSET_SIZE),
            (hdr_n as usize - (*n as usize)) * L::OFFSET_SIZE,
        );
    }
    L::set_offset(new, *n, r | (off_new as u64));
    off_new as usize
}
