use crate::Error;
#[cfg(feature = "mmap")]
use fs2::FileExt;
use parking_lot::lock_api::{RawMutex, RawRwLock};
use parking_lot::Mutex;

use sanakirja_core::{CowPage, Storable};

use std::borrow::Borrow;
#[cfg(feature = "mmap")]
use std::fs::OpenOptions;
#[cfg(not(feature = "mmap"))]
use std::path::Path;
#[cfg(feature = "mmap")]
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use log::*;

mod muttxn;
pub use muttxn::*;
mod global_header;
pub(crate) use global_header::*;

pub use sanakirja_core::PAGE_SIZE;
pub(crate) const PAGE_SIZEU64: u64 = PAGE_SIZE as u64;
const CURRENT_VERSION: u16 = 3;

/// A chunk of memory, possibly of a memory-mapped file, or allocated
/// with `std::alloc`.
#[derive(Debug)]
pub(crate) struct Map {
    pub(crate) ptr: *mut u8,
    #[cfg(feature = "mmap")]
    mmap: memmap::MmapMut,
    #[cfg(not(feature = "mmap"))]
    layout: std::alloc::Layout,
    length: u64,
}

impl Map {
    #[cfg(feature = "mmap")]
    fn flush(&self) -> Result<(), Error> {
        Ok(self.mmap.flush()?)
    }
    #[cfg(not(feature = "mmap"))]
    fn flush(&self) -> Result<(), Error> {
        Ok(())
    }
    #[cfg(feature = "mmap")]
    fn flush_range(&self, a: usize, b: usize) -> Result<(), Error> {
        Ok(self.mmap.flush_range(a, b)?)
    }
    #[cfg(not(feature = "mmap"))]
    fn flush_range(&self, a: usize, b: usize) -> Result<(), Error> {
        Ok(())
    }
}

/// An environment, which may be either a memory-mapped file, or
/// memory allocated with [`std::alloc`].
pub struct Env {
    #[cfg(feature = "mmap")]
    file: Option<std::fs::File>,

    pub(crate) mmaps: Mutex<Vec<Map>>,
    mut_txn_lock: parking_lot::RawMutex,

    pub(crate) roots: Vec<RootLock>,
}

unsafe impl Send for Env {}
unsafe impl Sync for Env {}

#[cfg(not(feature = "mmap"))]
impl Drop for Env {
    fn drop(&mut self) {
        let mut mmaps = self.mmaps.lock();
        for map in mmaps.drain(..) {
            unsafe { std::alloc::dealloc(map.ptr, map.layout) }
        }
    }
}

/// A lock on a root page for this process only, because taking
/// multiple locks on the same file from a single process isn't
/// cross-platform (or even properly defined).
///
/// Usage is as follows:
///
/// - For read-only transactions, we first take a read lock on the `rw`
/// field, and increment `n_txn`, locking the file if the former value
/// is 0.
///
/// - For read-write transactions, we first take a write lock on the
/// `rw` field, and then take an exclusive lock on the file (this is
/// valid since only one read-write transaction can be active in a
/// process at the same time).
///
pub(crate) struct RootLock {
    /// It is undefined behavior to have a file mmapped for than once.
    #[cfg(feature = "mmap")]
    lock_file: Option<std::fs::File>,

    /// Read-write lock.
    rw: parking_lot::RawRwLock,

    /// Count of read-only transactions.
    n_txn: AtomicUsize,
}

impl Env {
    /// Same as [`new`](#new), but does not create any lock on the
    /// file system.
    ///
    /// The database is very likely to get corrupted if an environment
    /// is opened from multiple processes, or more than once by the
    /// same process, if at least one of these instances can start a
    /// mutable transaction.
    ///
    /// The `n_roots` argument is ignored if the database already
    /// exists, and is used to initialise the first `n_roots` pages of
    /// the file else.
    #[cfg(feature = "mmap")]
    pub unsafe fn new_nolock<P: AsRef<Path>>(
        path: P,
        length: u64,
        n_roots: usize,
    ) -> Result<Self, Error> {
        let meta = std::fs::metadata(&path);
        let length = if let Ok(ref meta) = meta {
            std::cmp::max(meta.len(), length)
        } else {
            std::cmp::max(length, PAGE_SIZEU64)
        };
        // Find the next multiple of PAGE_SIZE greater than or equal
        // to `length`.
        let length = (length + PAGE_SIZEU64 - 1) & !(PAGE_SIZEU64 - 1);

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .truncate(false)
            .create(true)
            .open(&path)?;
        file.set_len(length)?;
        let mmap = memmap::MmapMut::map_mut(&file)?;
        Self::new_nolock_(Some(file), length, mmap, meta.is_err(), n_roots)
    }

    /// Create an environment from a file, without creating any lock
    /// on the filesystem.
    #[cfg(feature = "mmap")]
    unsafe fn new_nolock_(
        file: Option<std::fs::File>,
        length: u64,
        mut mmap: memmap::MmapMut,
        initialise: bool,
        n_roots: usize,
    ) -> Result<Self, Error> {
        assert!(n_roots >= 1);
        assert!(n_roots <= ((length >> 12) as usize));
        assert!(n_roots < 256);
        let map = mmap.as_mut_ptr();
        let n_roots = if initialise {
            // Initialise the first `n_roots` pages at the start of
            // the file.
            init(map, n_roots);
            // Since the first `n_roots` pages are occupied by roots,
            // the first unused page is found at offset `n_roots *
            // PAGE_SIZE`.
            n_roots
        } else {
            // Read the root and number of roots from the first page's
            // header.
            let g = &*(map as *const GlobalHeader);
            assert_eq!(g.version, CURRENT_VERSION);
            g.n_roots as usize
        };

        // Finally, create the environment.
        let env = Env {
            file,
            mmaps: Mutex::new(vec![Map {
                ptr: map,
                mmap,
                length,
            }]),
            mut_txn_lock: RawMutex::INIT,

            // Initialise a different `RootLock` for each root page.
            roots: (0..n_roots)
                .map(|_| RootLock {
                    rw: RawRwLock::INIT,
                    n_txn: AtomicUsize::new(0),
                    lock_file: None,
                })
                .collect(),
        };
        Ok(env)
    }

    /// No-mmap version of the same thing.
    #[cfg(not(feature = "mmap"))]
    unsafe fn new_nolock_(length: u64, initialise: bool, n_roots: usize) -> Result<Env, Error> {
        assert!(n_roots >= 1);
        assert!(n_roots <= ((length >> 12) as usize));
        assert!(n_roots < 256);
        assert!(initialise);
        let layout = std::alloc::Layout::from_size_align(length as usize, 64).unwrap();
        let map = std::alloc::alloc(layout);
        init(map, n_roots);
        let env = Env {
            mmaps: Mutex::new(vec![Map {
                ptr: map,
                layout,
                length,
            }]),
            mut_txn_lock: RawMutex::INIT,
            // Initialise a different `RootLock` for each root page.
            roots: (0..n_roots)
                .map(|_| RootLock {
                    rw: RawRwLock::INIT,
                    n_txn: AtomicUsize::new(0),
                })
                .collect(),
        };
        Ok(env)
    }
}

unsafe fn init(map: *mut u8, n_roots: usize) {
    for i in 0..n_roots {
        *(map.offset((i * PAGE_SIZE) as isize) as *mut GlobalHeader) = (GlobalHeader {
            version: CURRENT_VERSION,
            root: 0,
            n_roots: n_roots as u8,
            crc: 0,
            length: n_roots as u64 * PAGE_SIZE as u64,
            free_db: 0,
            rc_db: 0,
        })
        .to_le();
        set_crc(map.add(i * PAGE_SIZE));
    }
}

impl Env {
    /// Initialize an environment. If `length` is not a multiple of
    /// `4096`, it is rounded to the next multiple of the page size
    /// (4096 bytes).
    ///
    /// The `n_roots` parameter is the maximum number of versions that
    /// can be alive at the same time, before `mut_txn_begin` must
    /// wait for old readers to stop.
    ///
    /// If `n_roots` is 1, mutable transactions exclude all readers.
    #[cfg(feature = "mmap")]
    pub fn new<P: AsRef<Path>>(path: P, length: u64, n_roots: usize) -> Result<Env, Error> {
        assert!(n_roots < 256);
        let path = path.as_ref();
        let mut env = unsafe { Self::new_nolock(path, length, n_roots)? };
        for (n, l) in env.roots.iter_mut().enumerate() {
            l.lock_file = Some(
                OpenOptions::new()
                    .read(true)
                    .write(true)
                    .truncate(false)
                    .create(true)
                    .open(path.with_extension(&format!("lock{}", n)))?,
            );
        }
        Ok(env)
    }

    /// Create a new anonymous database, backed by memory. The length
    /// is the total size in bytes of the database.
    #[cfg(feature = "mmap")]
    pub fn new_anon(length: u64, n_roots: usize) -> Result<Env, Error> {
        let length =
            (std::cmp::max(length, PAGE_SIZEU64) + (PAGE_SIZEU64 - 1)) & !(PAGE_SIZEU64 - 1);
        let mmap = memmap::MmapMut::map_anon(length as usize)?;
        unsafe { Self::new_nolock_(None, length, mmap, true, n_roots) }
    }

    /// Create a new anonymous database, backed by memory. The length
    /// is the total size in bytes of the database.
    #[cfg(not(feature = "mmap"))]
    pub fn new_anon(length: u64, n_roots: usize) -> Result<Env, Error> {
        let length =
            (std::cmp::max(length, PAGE_SIZEU64) + (PAGE_SIZEU64 - 1)) & !(PAGE_SIZEU64 - 1);
        unsafe { Self::new_nolock_(length, true, n_roots) }
    }

    /// Now, here is how databases grow: when we run out of space, we
    /// allocate a new chunk of memory/disk space, of a size twice as
    /// large as the last chunk. The size of the first chunk is the
    /// size of the file when we first opened the environment.

    /// Allocate the memory of the appropriate size and offest for the
    /// `i`th chunk.
    #[cfg(not(feature = "mmap"))]
    fn open_mmap(&self, i: usize, length0: u64) -> Result<Map, Error> {
        let length = length0 << i;
        let layout = std::alloc::Layout::from_size_align(length as usize, 64).unwrap();
        let map = unsafe { std::alloc::alloc(layout) };
        Ok(Map {
            ptr: map,
            layout,
            length,
        })
    }

    /// The same, but for memory-mapped file. If we're doing that, it
    /// means we need to grow the file.
    #[cfg(feature = "mmap")]
    fn open_mmap(&self, i: usize, length0: u64) -> Result<Map, Error> {
        let length = length0 << i;
        let offset = (length0 << i) - length0;
        if let Some(ref file) = self.file {
            file.set_len(offset + length)?;
            fallocate(file, offset + length)?;
            let mut mmap = unsafe {
                memmap::MmapOptions::new()
                    .offset(offset)
                    .len(length as usize)
                    .map_mut(&file)?
            };
            Ok(Map {
                ptr: mmap.as_mut_ptr(),
                mmap,
                length,
            })
        } else {
            let mut mmap = memmap::MmapMut::map_anon(length as usize)?;
            Ok(Map {
                ptr: mmap.as_mut_ptr(),
                mmap,
                length,
            })
        }
    }

    /// Find an offset in a file, possibly mapping more of the file if
    /// necessary (for example if the file has been grown by another
    /// process since we openend this environment).
    unsafe fn find_offset(&self, mut offset: u64) -> Result<*mut u8, Error> {
        let mut i = 0;
        let mut mmaps = self.mmaps.lock();
        loop {
            if i >= mmaps.len() {
                let length0 = mmaps[0].length;
                info!("find_offset, i = {:?}/{:?}, extending, offset = {:?}, length0 = {:?}", i, mmaps.len(), offset, length0);
                mmaps.push(self.open_mmap(i, length0)?);
            }
            if offset < mmaps[i].length {
                return Ok(mmaps[i].ptr.add(offset as usize));
            }
            offset -= mmaps[i].length;
            i += 1
        }
    }

    /// Close this repository.
    ///
    /// The safe alternative to this method is to use an `Option<Env>`
    /// instead of an `Env`.
    #[cfg(not(feature = "mmap"))]
    pub unsafe fn close(&mut self) {
        let mut mmaps = self.mmaps.lock();
        for m in mmaps.drain(..) {
            std::alloc::dealloc(m.ptr, m.layout)
        }
    }

    /// If the CRC feature is disabled, we're not checking CRCs.
    #[cfg(not(feature = "crc32"))]
    fn check_crc(&self, _root: usize) -> Result<(), crate::CRCError> {
        Ok(())
    }

    /// Else, we are checking CRCs, so return a CRC error if the check
    /// fails (the CRC is a 32 bit integer encoded little-endian at
    /// bytes [8,12[ of the root pages).
    #[cfg(feature = "crc32")]
    fn check_crc(&self, root: usize) -> Result<(), crate::CRCError> {
        unsafe {
            let maps = self.mmaps.lock();
            check_crc(maps[0].ptr.add(root * PAGE_SIZE))
        }
    }
}

#[cfg(feature = "mmap")]
fn fallocate(file: &std::fs::File, length: u64) -> Result<(), Error> {
    file.allocate(length)?;
    Ok(())
}

#[cfg(not(feature = "mmap"))]
fn fallocate(&self, length: u64) -> Result<(), Error> {
    Ok(())
}

#[cfg(feature = "crc32")]
use lazy_static::*;

#[cfg(feature = "crc32")]
lazy_static! {
    static ref HASHER: crc32fast::Hasher = crc32fast::Hasher::new();
}

#[cfg(feature = "mmap")]
#[test]
#[should_panic]
fn nroots_test() {
    let path = tempfile::tempdir().unwrap();
    let path = path.path().join("db");
    let l0 = 1 << 15; // 8 pages
    Env::new(&path, l0, 19).unwrap();
}

#[cfg(feature = "mmap")]
#[test]
fn mmap_growth_test() {
    let path = tempfile::tempdir().unwrap();
    let path = path.path().join("db");
    let l0 = 1 << 15; // 8 pages
    {
        let env = Env::new(&path, l0, 2).unwrap();
        let map1 = env.open_mmap(0, l0).unwrap();
        println!("{:?}", map1);
        let map2 = env.open_mmap(1, l0).unwrap();
        println!("{:?}", map2);
        map1.flush().unwrap();
        map2.flush().unwrap();
    }
    let len = std::fs::metadata(&path).unwrap().len();
    assert_eq!(len, (l0 << 2) - l0);
}

#[cfg(not(feature = "crc32"))]
fn set_crc(_ptr: *mut u8) {}

#[cfg(feature = "crc32")]
fn set_crc(ptr: *mut u8) {
    unsafe {
        let root_page = std::slice::from_raw_parts(ptr.add(8), PAGE_SIZE - 8);
        let mut h = HASHER.clone();
        h.update(root_page);
        let globptr = ptr as *mut GlobalHeader;
        (&mut *globptr).crc = h.finalize().to_le();
        debug!("SETTING CRC {:?}", (&*globptr).crc);
    }
}

/// An immutable transaction.
pub struct Txn<E: Borrow<Env>> {
    pub(crate) env: E,
    pub(crate) root: usize,
}


impl<E: Borrow<Env>> Txn<E> {
  /// Borrow env
  pub fn env_borrow(&self) -> &Env {
    self.env.borrow()
  }
}

impl Env {
    /// Start a read-only transaction.
    pub fn txn_begin<E: Borrow<Self>>(env: E) -> Result<Txn<E>, Error> {
        let env_ = env.borrow();
        let root = {
            // Find the youngest committed version and lock it. Note
            // that there may be processes incrementing the version
            // number in parallel to this process. If that happens,
            // then since we take a shared file lock on a root page
            // (at the end of this function), the only thing that may
            // happen is that we don't open the very last version.
            let cur_mut_root =
                unsafe { (&*(env_.mmaps.lock()[0].ptr as *const GlobalHeader)).root as usize };
            // Last committed root page.
            let root = (cur_mut_root + env_.roots.len() - 1) % env_.roots.len();
            env_.roots[root].rw.lock_shared();
            // Increase the read-only transaction count for that root,
            // and if the previous value is 0, take a file lock.
            let old_n_txn = env_.roots[root].n_txn.fetch_add(1, Ordering::SeqCst);
            if old_n_txn == 0 {
                env_.lock_shared(root)?
            }
            root
        };
        env_.check_crc(root)?;
        Ok(Txn { env, root })
    }

    #[cfg(feature = "mmap")]
    fn lock_shared(&self, root: usize) -> Result<(), Error> {
        if let Some(ref f) = self.roots[root].lock_file {
            f.lock_shared()?;
        }
        Ok(())
    }

    #[cfg(not(feature = "mmap"))]
    fn lock_shared(&self, _root: usize) -> Result<(), Error> {
        Ok(())
    }

    #[cfg(feature = "mmap")]
    fn lock_exclusive(&self, root: usize) -> Result<(), Error> {
        if let Some(ref f) = self.roots[root].lock_file {
            f.lock_exclusive()?;
        }
        Ok(())
    }

    #[cfg(not(feature = "mmap"))]
    fn lock_exclusive(&self, _root: usize) -> Result<(), Error> {
        Ok(())
    }

    #[cfg(feature = "mmap")]
    fn unlock(&self, root: usize) -> Result<(), Error> {
        if let Some(ref f) = self.roots[root].lock_file {
            f.unlock()?
        }
        Ok(())
    }

    #[cfg(not(feature = "mmap"))]
    fn unlock(&self, _root: usize) -> Result<(), Error> {
        Ok(())
    }
}

impl<E: Borrow<Env>> Drop for Txn<E> {
    fn drop(&mut self) {
        let env = self.env.borrow();
        unsafe { env.roots[self.root].rw.unlock_shared() }
        let old_n_txn = env.roots[self.root].n_txn.fetch_sub(1, Ordering::SeqCst);
        if old_n_txn == 1 {
            env.unlock(self.root).unwrap_or(())
        }
    }
}

impl<E: Borrow<Env>> sanakirja_core::LoadPage for Txn<E> {
    type Error = Error;

    /// Find the appropriate map segment
    fn load_page(&self, off: u64) -> Result<CowPage, Self::Error> {
        unsafe {
            let data = self.env.borrow().find_offset(off)?;
            Ok(CowPage { data, offset: off })
        }
    }
    fn rc(&self, _: u64) -> Result<u64, Self::Error> {
        Ok(0)
    }
}

/// Access the root page of a transaction.
pub trait RootPage {
    /// The root page of this transaction.
    unsafe fn root_page(&self) -> &[u8; 4064];
}

impl<E: Borrow<Env>> RootPage for Txn<E> {
    unsafe fn root_page(&self) -> &[u8; 4064] {
        let env = self.env.borrow();
        let maps = env.mmaps.lock();
        let ptr = maps[0].ptr.add(self.root * PAGE_SIZE + GLOBAL_HEADER_SIZE);
        &*(ptr as *const [u8; 4064])
    }
}

/// The trait, implemented by [`Txn`] and [`MutTxn`], for treating the
/// 4064 bytes after the header of root pages as pointers to B trees
/// (well, actually `Option` of pointers to databases, where `None` is
/// encoded by 0).
pub trait RootDb {
    /// Return the database stored in the root page of the current
    /// transaction at index `n`, if any.
    fn root_db<K: Storable + ?Sized, V: Storable + ?Sized, P: crate::btree::BTreePage<K, V>>(
        &self,
        n: usize,
    ) -> Option<sanakirja_core::btree::Db_<K, V, P>>;
}

impl<E: Borrow<Env>> RootDb for Txn<E> {
    /// This is a straightforward implementation of just accessing index `n`.
    fn root_db<K: Storable + ?Sized, V: Storable + ?Sized, P: crate::btree::BTreePage<K, V>>(
        &self,
        n: usize,
    ) -> Option<sanakirja_core::btree::Db_<K, V, P>> {
        unsafe {
            let env = self.env.borrow();
            let db = {
                let maps = env.mmaps.lock();
                *(maps[0]
                    .ptr
                    .add(self.root * PAGE_SIZE + GLOBAL_HEADER_SIZE + 8 * n)
                    as *mut u64)
            };
            if db != 0 {
                Some(sanakirja_core::btree::Db_::from_page(db))
            } else {
                None
            }
        }
    }
}

impl<E: Borrow<Env>> Txn<E> {
    /// A "raw" version of the `root_db` method, useful to store
    /// things other than databases.
    pub fn root(&self, n: usize) -> u64 {
        assert!(n <= (4096 - GLOBAL_HEADER_SIZE) / 8);
        unsafe {
            let env = self.env.borrow();
            let maps = env.mmaps.lock();
            *(maps[0]
              .ptr
              .add(self.root * PAGE_SIZE + GLOBAL_HEADER_SIZE + 8 * n)
              as *mut u64)
        }
    }
}

#[cfg(feature = "crc32")]
unsafe fn check_crc(p: *const u8) -> Result<(), crate::CRCError> {
    let globptr = p as *mut GlobalHeader;
    let crc = u32::from_le((&*globptr).crc);
    let mut h = crc32fast::Hasher::new();
    let data = std::slice::from_raw_parts(p.offset(8), PAGE_SIZE - 8);
    h.update(data);
    let crc_ = h.finalize();
    debug!("CHECKING CRC {:?} {:?}", crc_, crc);
    if crc_ == crc {
        Ok(())
    } else {
        Err(crate::CRCError {})
    }
}
