#![no_std]

//! This crate defines tools to implement datastructures that can live
//! in main memory or on-disk, meaning that their natural habitat is
//! memory-mapped files, but if that environment is threatened, they
//! might seek refuge in lower-level environments.
//!
//! One core building block of this library is the notion of virtual
//! memory pages, which are allocated and freed by an
//! externally-provided allocator (see how the `sanakirja` crate does
//! this). The particular implementation used here is meant to allow a
//! transactional system with readers reading the structures
//! concurrently with one writer at a time.
//!
//! At the moment, only B trees are implemented, as well as the
//! following general traits:
//!
//! - [`LoadPage`] is a trait used to get a pointer to a page. In the
//! most basic version, this may just return a pointer to the file,
//! offset by the requested offset. In more sophisticated versions,
//! this can be used to encrypt and compress pages.
//! - [`AllocPage`] allocates and frees pages, because as
//! datastructures need to be persisted on disk, we can't rely on
//! Rust's memory management to do it for us. Users of this crate
//! don't have to worry about this though.
//!
//! Moreover, two other traits can be used to store things on pages:
//! [`Storable`] is a simple trait that all `Sized + Ord` types
//! without references can readily implement (the [`direct_repr!`]
//! macro does that). For types containing references to pages
//! allocated in the database, the comparison function can be
//! customised. Moreover, these types must supply an iterator over
//! these references, in order for reference-counting to work properly
//! when the datastructures referencing these types are forked.
//!
//! Dynamically-sized types, or types that need to be represented in a
//! dynamically-sized way, can use the [`UnsizedStorable`] format.

pub mod btree;

/// There's a hard-coded assumption that pages have 4K bytes. This is
/// true for normal memory pages on almost all platforms.
pub const PAGE_SIZE: usize = 4096;

/// Types that can be stored on disk. This trait may be used in
/// conjunction with `Sized` in order to determine the on-disk size,
/// or with [`UnsizedStorable`] when special arrangements are needed.
pub trait Storable: core::fmt::Debug {
    /// This is required for B trees, not necessarily for other
    /// structures. The default implementation panics.
    fn compare<T: LoadPage>(&self, _txn: &T, _b: &Self) -> core::cmp::Ordering {
        unimplemented!()
    }

    /// If this value is an offset to another page at offset `offset`,
    /// return `Some(offset)`. Return `None` else.
    fn page_references(&self) -> Self::PageReferences;

    /// An iterator over the offsets to pages contained in this
    /// value. Only values from this crate can generate non-empty
    /// iterators, but combined values (like tuples) must chain the
    /// iterators returned by method `page_offsets`.
    type PageReferences: Iterator<Item = u64>;
}

/// A macro to implement [`Storable`] on "plain" types,
/// i.e. fixed-sized types that are `repr(C)` and don't hold
/// references.
#[macro_export]
macro_rules! direct_repr {
    ($t: ty) => {
        impl Storable for $t {
            type PageReferences = core::iter::Empty<u64>;
            fn page_references(&self) -> Self::PageReferences {
                core::iter::empty()
            }
            fn compare<T>(&self, _: &T, b: &Self) -> core::cmp::Ordering {
                self.cmp(b)
            }
        }
        impl UnsizedStorable for $t {
            const ALIGN: usize = core::mem::align_of::<$t>();

            /// If `Self::SIZE.is_some()`, this must return the same
            /// value. The default implementation is `Self;:SIZE.unwrap()`.
            fn size(&self) -> usize {
                core::mem::size_of::<Self>()
            }

            /// Read the size from an on-page entry.
            unsafe fn onpage_size(_: *const u8) -> usize {
                core::mem::size_of::<Self>()
            }

            /// Write to a page. Must not overwrite the allocated size, but
            /// this isn't checked (which is why it's unsafe).
            unsafe fn write_to_page(&self, p: *mut u8) {
                core::ptr::copy_nonoverlapping(self, p as *mut Self, 1)
            }

            unsafe fn from_raw_ptr<'a, T>(_: &T, p: *const u8) -> &'a Self {
                &*(p as *const Self)
            }
        }
    };
}

direct_repr!(());
direct_repr!(u8);
direct_repr!(i8);
direct_repr!(u16);
direct_repr!(i16);
direct_repr!(u32);
direct_repr!(i32);
direct_repr!(u64);
direct_repr!(i64);
direct_repr!([u8; 16]);

#[cfg(feature = "std")]
extern crate std;
#[cfg(feature = "std")]
direct_repr!(std::net::Ipv4Addr);
#[cfg(feature = "std")]
direct_repr!(std::net::Ipv6Addr);
#[cfg(feature = "std")]
direct_repr!(std::net::IpAddr);
#[cfg(feature = "std")]
direct_repr!(std::net::SocketAddr);
#[cfg(feature = "std")]
direct_repr!(std::time::SystemTime);
#[cfg(feature = "std")]
direct_repr!(std::time::Duration);
#[cfg(feature = "uuid")]
direct_repr!(uuid::Uuid);
#[cfg(feature = "ed25519")]
direct_repr!(ed25519_zebra::VerificationKeyBytes);

/// Types that can be stored on disk.
pub trait UnsizedStorable: Storable {
    const ALIGN: usize;

    /// If `Self::SIZE.is_some()`, this must return the same
    /// value. The default implementation is `Self;:SIZE.unwrap()`.
    fn size(&self) -> usize;

    /// Read the size from an on-page entry. If `Self::SIZE.is_some()`
    /// this must be the same value.
    unsafe fn onpage_size(_: *const u8) -> usize;

    /// Write to a page. Must not overwrite the allocated size, but
    /// this isn't checked (which is why it's unsafe).
    unsafe fn write_to_page(&self, p: *mut u8);

    unsafe fn from_raw_ptr<'a, T>(_: &T, p: *const u8) -> &'a Self;
}

impl Storable for [u8] {
    type PageReferences = core::iter::Empty<u64>;
    fn page_references(&self) -> Self::PageReferences {
        core::iter::empty()
    }
    fn compare<T>(&self, _: &T, b: &Self) -> core::cmp::Ordering {
        self.cmp(b)
    }
}

impl UnsizedStorable for [u8] {
    const ALIGN: usize = 2;
    fn size(&self) -> usize {
        2 + self.len()
    }
    unsafe fn from_raw_ptr<'a, T>(_: &T, p: *const u8) -> &'a Self {
        let len = u16::from_le(*(p as *const u16));
        assert_ne!(len, 0);
        assert_eq!(len & 0xf000, 0);
        core::slice::from_raw_parts(p.add(2), len as usize)
    }
    unsafe fn onpage_size(p: *const u8) -> usize {
        let len = u16::from_le(*(p as *const u16));
        2 + len as usize
    }
    unsafe fn write_to_page(&self, p: *mut u8) {
        assert!(self.len() <= 510);
        *(p as *mut u16) = (self.len() as u16).to_le();
        core::ptr::copy_nonoverlapping(self.as_ptr(), p.add(2), self.len())
    }
}

unsafe fn read<T: LoadPage, K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
    _txn: &T,
    k: *const u8,
) -> (*const u8, *const u8) {
    let s = K::onpage_size(k);
    let v = k.add(s);
    let al = v.align_offset(V::ALIGN);
    let v = v.add(al);
    (k, v)
}

unsafe fn entry_size<K: UnsizedStorable + ?Sized, V: UnsizedStorable + ?Sized>(
    k: *const u8,
) -> usize {
    assert_eq!(k.align_offset(K::ALIGN), 0);
    let ks = K::onpage_size(k);
    // next multiple of va, assuming va is a power of 2.
    let v_off = (ks + V::ALIGN - 1) & !(V::ALIGN - 1);
    let v_ptr = k.add(v_off);
    let vs = V::onpage_size(v_ptr);
    let ka = K::ALIGN.max(V::ALIGN);
    let size = v_off + vs;
    (size + ka - 1) & !(ka - 1)
}

/// Representation of a mutable or shared page. This is an owned page
/// (like `Vec` in Rust's std), but we do not know whether we can
/// mutate it or not.
///
/// The least-significant bit of the first byte of each page is 1 if
/// and only if the page was allocated by the current transaction (and
/// hence isn't visible to any other transaction, meaning we can write
/// on it).
#[derive(Debug)]
#[repr(C)]
pub struct CowPage {
    pub data: *mut u8,
    pub offset: u64,
}

/// Representation of a borrowed, or immutable page, like a slice in
/// Rust.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct Page<'a> {
    pub data: &'a [u8; PAGE_SIZE],
    pub offset: u64,
}

impl CowPage {
    /// Borrows the page.
    pub fn as_page(&self) -> Page {
        Page {
            data: unsafe { &*(self.data as *const [u8; PAGE_SIZE]) },
            offset: self.offset,
        }
    }

    #[cfg(feature = "crc32")]
    pub fn crc(&self, hasher: &crc32fast::Hasher) -> u32 {
        let mut hasher = hasher.clone();
        hasher.reset();
        // Hash the beginning and the end of the page (i.e. remove
        // the CRC).
        unsafe {
            // Remove the dirty bit.
            let x = [(*self.data) & 0xfe];
            hasher.update(&x[..]);
            hasher.update(core::slice::from_raw_parts(self.data.add(1), 3));
            hasher.update(core::slice::from_raw_parts(
                self.data.add(8),
                PAGE_SIZE - 8,
            ));
        }
        hasher.finalize()
    }

    #[cfg(feature = "crc32")]
    pub fn crc_check(&self, hasher: &crc32fast::Hasher) -> bool {
        let crc = unsafe { u32::from_le(*(self.data as *const u32).add(1)) };
        self.crc(hasher) == crc
    }
}

/// An owned page on which we can write. This is just a wrapper around
/// `CowPage` to avoid checking the "dirty" bit at runtime.
#[derive(Debug)]
pub struct MutPage(pub CowPage);

impl MutPage {
    #[cfg(not(feature = "crc32"))]
    pub fn clear_dirty(&mut self) {
        unsafe { *self.0.data &= 0xfe }
    }

    #[cfg(feature = "crc32")]
    pub fn clear_dirty(&mut self, hasher: &crc32fast::Hasher) {
        unsafe {
            *self.0.data &= 0xfe;
            let crc = (self.0.data as *mut u32).add(1);
            *crc = self.0.crc(hasher)
        }
    }
}

unsafe impl Sync for CowPage {}
unsafe impl Send for CowPage {}

impl CowPage {
    /// Checks the dirty bit of a page.
    pub fn is_dirty(&self) -> bool {
        unsafe { (*self.data) & 1 != 0 }
    }
}

/// Trait for loading a page.
pub trait LoadPage {
    type Error;
    /// Loading a page.
    fn load_page(&self, off: u64) -> Result<CowPage, Self::Error>;

    /// Reference-counting. Since reference-counts are designed to be
    /// storable into B trees by external allocators, pages referenced
    /// once aren't stored, and hence are indistinguishable from pages
    /// that are never referenced. The default implementation returns
    /// 0.
    ///
    /// This has the extra benefit of requiring less disk space, and
    /// isn't more unsafe than storing the reference count, since we
    /// aren't supposed to hold a reference to a page with "logical
    /// RC" 0, so storing "1" for that page would be redundant anyway.
    fn rc(&self, _off: u64) -> Result<u64, Self::Error> {
        Ok(0)
    }
}

/// Trait for allocating and freeing pages.
pub trait AllocPage: LoadPage {
    /// Allocate a new page.
    fn alloc_page(&mut self) -> Result<MutPage, Self::Error>;
    /// Increment the page's reference count.
    fn incr_rc(&mut self, off: u64) -> Result<usize, Self::Error>;
    /// Decrement the page's reference count, assuming the page was
    /// first allocated by another transaction. If the RC reaches 0,
    /// free the page. Must return the new RC (0 if freed).
    fn decr_rc(&mut self, off: u64) -> Result<usize, Self::Error>;
    /// Same as [`Self::decr_rc`], but for pages allocated by the current
    /// transaction. This is an important distinction, as pages
    /// allocated by the current transaction can be reused immediately
    /// after being freed.
    fn decr_rc_owned(&mut self, off: u64) -> Result<usize, Self::Error>;
}
