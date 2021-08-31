use super::*;
use sanakirja_core::{btree, CowPage, MutPage};
use std::borrow::Borrow;

impl<E: Borrow<Env>, T> std::fmt::Debug for MutTxn<E, T> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "MutTxn {{ }}")
    }
}

/// A mutable transaction.
pub struct MutTxn<E: Borrow<Env>, T> {
    pub(crate) env: E,
    /// The root page of this transaction, which is 1 + the root
    /// written on page 0. The root written on page 0 changes at
    /// commit time.
    pub(crate) root: usize,
    parent: Option<T>,
    pub(crate) length: u64,

    /// Offset to the root of the B tree of free pages.
    pub(crate) free: u64,

    /// Reference counts use a strange encoding, meant to avoid code
    /// bloat: indeed, the list of free pages uses `Db<u64, ()>`, so
    /// we're just reusing the same code here, encoding the reference
    /// counts in the 12 least significant bits of the keys, and the
    /// actual pages in the 52 most significant bits.
    pub(crate) rc: Option<btree::Db<u64, ()>>,

    /// Offsets of pages that were allocated by this transaction, and
    /// have not been freed since.
    pub(crate) occupied_owned_pages: Vec<MutPage>,

    /// Offsets of pages that were allocated by this transaction, and
    /// then freed.
    pub(crate) free_owned_pages: Vec<u64>,

    /// Offsets of old pages freed by this transaction. These were
    /// *not* allocated by this transaction.
    ///
    /// Since we can't reuse them in the same transaction, another
    /// option would be to put them directly into the table of free
    /// pages. However, since calls to `put` may allocate and free
    /// pages, this could recurse infinitely, which is why we store
    /// them outside of the file.
    pub(crate) free_pages: Vec<u64>,
    roots: Vec<u64>,
}

impl<E: Borrow<Env>, T> MutTxn<E, T> {
  /// Borrow env
  pub fn env_borrow(&self) -> &Env {
    self.env.borrow()
  }
}

/// When dropping a transaction, we need to unlock the read-write
/// locks internal to this process, and possibly the file locks.
impl<E: Borrow<Env>, T> Drop for MutTxn<E, T> {
    fn drop(&mut self) {
        if self.parent.is_none() {
            let env = self.env.borrow();
            unsafe {
                env.mut_txn_unlock().unwrap_or(());
                env.roots[self.root].rw.unlock_exclusive();
                env.unlock(self.root).unwrap_or(())
            }
        }
    }
}

/// Transactions that can be committed. This trait is an abstraction
/// over mutable transactions and their subtransactions.
pub trait Commit {
    /// Commit the transaction.
    fn commit(self) -> Result<(), Error>;
}

/// The following is very easy, we're just extending all values of the
/// current transaction with values of the subtransaction.
impl<'a, E: Borrow<Env>, T> Commit for MutTxn<E, &'a mut MutTxn<E, T>> {
    fn commit(mut self) -> Result<(), Error> {
        let parent = self.parent.as_mut().unwrap();
        parent.length = self.length;
        parent.free = self.free;
        parent.rc = self.rc.take();
        parent
            .occupied_owned_pages
            .extend(self.occupied_owned_pages.drain(..));
        parent.free_owned_pages.extend(self.free_owned_pages.iter());
        parent.free_pages.extend(self.free_pages.iter());
        for (u, v) in self.roots.iter().enumerate() {
            if *v != 0 {
                parent.roots[u] = *v
            }
        }
        for (n, &r) in self.roots.iter().enumerate() {
            if r > 0 {
                if parent.roots.get(n).is_none() {
                    parent.roots.resize(n + 1, 0u64)
                }
                parent.roots[n] = r
            }
        }
        Ok(())
    }
}

impl Env {
    #[cfg(feature = "mmap")]
    fn mut_txn_lock(&self) -> Result<(), Error> {
        self.mut_txn_lock.lock();
        if let Some(ref f) = self.file {
            f.lock_exclusive()?;
        }
        Ok(())
    }

    #[cfg(not(feature = "mmap"))]
    fn mut_txn_lock(&self) -> Result<(), Error> {
        self.mut_txn_lock.lock();
        Ok(())
    }

    #[cfg(feature = "mmap")]
    fn mut_txn_unlock(&self) -> Result<(), Error> {
        unsafe {
            self.mut_txn_lock.unlock();
        }
        if let Some(ref f) = self.file {
            f.unlock()?
        }
        Ok(())
    }

    #[cfg(not(feature = "mmap"))]
    fn mut_txn_unlock(&self) -> Result<(), Error> {
        unsafe {
            self.mut_txn_lock.unlock();
        }
        Ok(())
    }

    /// Start a mutable transaction. Mutable transactions that go out
    /// of scope are automatically aborted.
    pub fn mut_txn_begin<E: Borrow<Self>>(env: E) -> Result<MutTxn<E, ()>, Error> {
        unsafe {
            let env_ = env.borrow();

            // First, take an exclusive file lock on the whole file to
            // make sure that no other process is starting a mutable
            // transaction at the same time. The worst that can happen
            // here is if the other process commits while we're still
            // waiting for a lock on the current page, because if that
            // happens, this new transaction will erase the
            // transaction in the other process.
            env_.mut_txn_lock()?;

            // Then, we can lock the root page of this transaction.
            let maps = env_.mmaps.lock()[0].ptr;
            let root = (&*(maps as *const GlobalHeader)).root as usize;
            debug!("BEGIN_TXN root = {:?}", root);
            env_.roots[root].rw.lock_exclusive();
            env_.lock_exclusive(root)?;
            // Root of the last MutTxn.
            let v0 = (root + env_.roots.len() - 1) % env_.roots.len();
            env_.check_crc(v0)?;
            // Copy the root page of the last transaction onto this
            // one.
            let page_ptr = maps.offset((v0 * PAGE_SIZE) as isize);
            let next_page_ptr = maps.offset((root * PAGE_SIZE) as isize);
            std::ptr::copy_nonoverlapping(page_ptr.add(8), next_page_ptr.add(8), PAGE_SIZE - 8);

            // Finally, read the header and start the transaction.
            let header = GlobalHeader::from_le(&*(next_page_ptr as *const GlobalHeader));
            debug!("n_roots = {:?}", header.n_roots);
            Ok(MutTxn {
                env,
                root,
                parent: None,
                rc: if header.rc_db == 0 {
                    None
                } else {
                    Some(btree::Db::from_page(header.rc_db))
                },
                length: if header.length == 0 {
                    (PAGE_SIZE as u64) * (header.n_roots as u64)
                } else {
                    header.length
                },
                free: header.free_db,
                occupied_owned_pages: Vec::with_capacity(100),
                free_owned_pages: Vec::new(),
                free_pages: Vec::new(),
                roots: Vec::new(),
            })
        }
    }
}

#[cfg(feature = "crc32")]
fn clear_dirty(p: &mut MutPage) {
    p.clear_dirty(&HASHER)
}

#[cfg(not(feature = "crc32"))]
fn clear_dirty(p: &mut MutPage) {
    p.clear_dirty()
}

impl<E: Borrow<Env>> Commit for MutTxn<E, ()> {
    fn commit(mut self) -> Result<(), Error> {
        debug!("COMMIT");

        // If there's no tree of free pages, and no pages to free,
        // don't bother with free pages at all (don't even allocate a
        // tree).
        let free_db =
            if self.free == 0 && self.free_owned_pages.is_empty() && self.free_pages.is_empty() {
                None
            } else {
                // Else, allocate or load the tree of free pages.
                let mut free_db: btree::Db<u64, ()> = if self.free == 0 {
                    btree::create_db(&mut self)?
                } else {
                    btree::Db::from_page(self.free)
                };
                debug!("free_db = {:?}", free_db);
                // Adding all the pages freed during the transaction to the
                // tree of free pages. If this call to `btree::put` frees
                // pages, add them again. This converges in at most log n
                // iterations (where n is the total number of free pages).

                // First, set the free table to 0 in this transaction, to
                // avoid recursing in the calls to `put` below (indeed,
                // the table of free pages is used when allocating new
                // pages, which may happen in a call to `put`).
                self.free = 0;

                // Then, while there are pages to free, free them. Since
                // the calls to `put` below might free pages (and add
                // pages to these two vectors), the (outer) loop might run
                // for more than one iteration.
                while !self.free_pages.is_empty() || !self.free_owned_pages.is_empty() {
                    while let Some(p) = self.free_pages.pop() {
                        let p = p & !0xfff;
                        btree::put(&mut self, &mut free_db, &p.to_le(), &())?;
                    }
                    while let Some(p) = self.free_owned_pages.pop() {
                        let p = p & !0xfff;
                        btree::put(&mut self, &mut free_db, &p.to_le(), &())?;
                    }
                }
                Some(free_db)
            };
        // Clear the dirty bit of all pages we've touched. If they've
        // been freed and have already been flushed by the kernel, we
        // don't want to resurrect them to the main memory, so we
        // check that.
        let mut occ = std::mem::replace(&mut self.occupied_owned_pages, Vec::new());
        for p in occ.iter_mut() {
            if let Some(ref free_db) = free_db {
                if let Some((pp, ())) = btree::get(&self, free_db, &p.0.offset, None)? {
                    if *pp == p.0.offset {
                        continue;
                    }
                }
            }
            clear_dirty(p);
        }

        let env = self.env.borrow();
        let mut maps = env.mmaps.lock();

        // Flush all the maps.
        for m in maps.iter_mut() {
            m.flush()?
        }

        // Get this transaction's root page.
        let globptr =
            unsafe { &mut *(maps[0].ptr.add(self.root * PAGE_SIZE) as *mut GlobalHeader) };
        // Set the length and free database.
        globptr.length = self.length.to_le();
        if let Some(free_db) = free_db {
            debug!("COMMIT: free_db = 0x{:x}", free_db.db);
            globptr.free_db = free_db.db.to_le();
        }
        if let Some(ref rc_db) = self.rc {
            debug!("COMMIT: rc_db = 0x{:x}", rc_db.db);
            globptr.rc_db = rc_db.db.to_le();
        }
        // Set the "root databases" modified by this transaction.
        let root_dbs = unsafe {
            std::slice::from_raw_parts_mut(
                maps[0].ptr.add(self.root * PAGE_SIZE + GLOBAL_HEADER_SIZE) as *mut u64,
                N_ROOTS,
            )
        };
        for (&r, rr) in self.roots.iter().zip(root_dbs.iter_mut()) {
            debug!("root_db: {:?}", rr);
            debug!("committing root: {:?} {:?}", r, rr);
            if r > 0 {
                *rr = r
            }
        }

        // Set the root page's CRC.
        unsafe {
            set_crc(maps[0].ptr.add(self.root * PAGE_SIZE));
        }

        // Move the current global root page by one page on page 0.
        unsafe {
            (&mut *(maps[0].ptr as *mut GlobalHeader)).root =
                (self.root as u8 + 1) % (env.roots.len() as u8);
        }

        // Flush all the maps.
        maps[0].flush_range(0, env.roots.len() * PAGE_SIZE)?;

        // And finally, unlock the root page in the environment.
        debug!("commit: unlock {:?}", self.root);
        unsafe { env.roots[self.root].rw.unlock_exclusive() };
        // Unlock the root page on the file lock (if relevant).
        env.unlock(self.root)?;

        // And unlock the global mutable transaction mutex.
        env.mut_txn_unlock()?;
        debug!("/COMMIT");
        Ok(())
    }
}

impl<E: Borrow<Env>, T> MutTxn<E, T> {
    /// Setting the `num`th element of the initial page, treated as a
    /// `[u64; 510]`, to `value`. This doesn't actually write anything
    /// to that page, since that page is written during the commit.
    ///
    /// In the current implementation, `value` is probably going to be
    /// the offset in the file of the root page of a B tree.
    pub fn set_root(&mut self, num: usize, value: u64) {
        if self.roots.get(num).is_none() {
            self.roots.resize(num + 1, 0u64);
        }
        self.roots[num] = value;
    }

    /// Setting the `num`th element of the initial page, treated as a
    /// [u64; 510].
    pub fn remove_root(&mut self, num: usize) {
        if self.roots.get(num).is_none() {
            self.roots.resize(num + 1, 0u64);
        }
        self.roots[num] = 0;
    }

    /// Add the page at offset `offset` to the list of free pages that
    /// were allocated by this `MutTxn` (and hence can be reallocated
    /// by the same transaction).
    fn free_owned_page(&mut self, offset: u64) {
        debug!("FREEING OWNED PAGE {:?} {:x}", offset, offset);
        assert_ne!(offset, 0);
        self.free_owned_pages.push(offset);
    }

    /// Add the page at offset `offset` to the list of free pages
    /// allocated by a previous transaction, and hence may still be
    /// accessible by other transactions.
    fn free_page(&mut self, offset: u64) {
        debug!("FREEING PAGE {:?} {:x}", offset, offset);
        assert_ne!(offset, 0);
        self.free_pages.push(offset)
    }

    /// Pop a free page from the B tree of free pages.
    fn free_pages_pop(&mut self) -> Result<Option<u64>, Error> {
        if self.free == 0 {
            debug!("self.free = 0");
            return Ok(None);
        }
        let mut db: btree::Db<u64, ()> = btree::Db::from_page(self.free);
        let mut curs = btree::cursor::Cursor::new(self, &db)?;
        curs.set_last(self)?;
        let mut f = if let Some((f, ())) = curs.prev(self)? {
            *f
        } else {
            return Ok(None);
        };
        // Get the last page that is also free in all other versions.
        loop {
            debug!("trying 0x{:x}", f);
            if self.free_for_all(f)? {
                break;
            } else if let Some((f_, ())) = curs.prev(self)? {
                f = *f_
            } else {
                debug!("no more candidate");
                return Ok(None);
            }
        }

        self.free = 0;
        assert!(btree::del::del(self, &mut db, &f, None)?);

        self.free = db.db;
        Ok(Some(f))
    }

    // Check whether this page is also free for the other
    // versions.
    fn free_for_all(&self, f: u64) -> Result<bool, Error> {
        let env = self.env.borrow();
        // We already know it's free for the youngest previous
        // transaction and for the current one (because the tree of
        // free pages was copied from there), so we only have
        // `self.roots.len() - 2` root pages to check.
        for i in 1..env.roots.len() - 1 {
            debug!("free_for_all {:?}", i);
            let db: btree::Db<u64, ()> = unsafe {
                let p = &*(env.mmaps.lock()[0]
                    .ptr
                    .add(((self.root + i) % env.roots.len()) * PAGE_SIZE)
                    as *const GlobalHeader);
                if f >= u64::from_le(p.length) {
                    // Page `f` was allocated strictyl after
                    // transaction `i`.
                    continue;
                }
                if p.free_db == 0 {
                    // This version doesn't have any free page.
                    return Ok(false);
                }
                btree::Db::from_page(p.free_db)
            };
            if let Some((&f_, ())) = btree::get(self, &db, &f, None)? {
                if f_ != f {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}

impl<E: Borrow<Env>, T> sanakirja_core::AllocPage for MutTxn<E, T> {
    /// Allocate a single page.
    fn alloc_page(&mut self) -> Result<MutPage, Error> {
        // If we have allocated and freed a page in this transaction,
        // use it first.
        if let Some(offset) = self.free_owned_pages.pop() {
            assert_ne!(offset, 0);
            debug!("free owned pop 0x{:x}", offset);
            let data = unsafe { self.env.borrow().find_offset(offset)? };
            let page = MutPage(CowPage { data, offset });
            self.occupied_owned_pages
                .push(MutPage(CowPage { data, offset }));
            Ok(page)
        } else {
            // Else, if there are free pages, take one.
            if let Some(offset) = self.free_pages_pop()? {
                assert_ne!(offset, 0);
                debug!("free pages pop 0x{:x}", offset);
                let data = unsafe { self.env.borrow().find_offset(offset)? };
                self.occupied_owned_pages
                    .push(MutPage(CowPage { data, offset }));
                Ok(MutPage(CowPage { data, offset }))
            } else {
                // Else, allocate in the free space.
                debug!("allocate in the free space 0x{:x}", self.length);
                let offset = self.length;
                self.length += PAGE_SIZE as u64;
                let data = unsafe { self.env.borrow().find_offset(offset)? };
                self.occupied_owned_pages
                    .push(MutPage(CowPage { data, offset }));
                Ok(MutPage(CowPage { data, offset }))
            }
        }
    }

    /// Increment the reference count for page `off`.
    fn incr_rc(&mut self, off: u64) -> Result<usize, Error> {
        assert!(off > 0);
        if let Some(mut rc_) = self.rc.take() {
            let mut curs = btree::cursor::Cursor::new(self, &rc_)?;
            curs.set(self, &off, None)?;
            let rc = if let Some((rc, _)) = curs.current(self)? {
                if *rc & !0xfff == off {
                    *rc & 0xfff
                } else {
                    1
                }
            } else {
                1
            };
            if rc > 1 {
                btree::del::del_at_cursor(self, &mut rc_, &mut curs)?;
            }
            debug!("incr rc 0x{:x} {:?}", off, rc+1);
            assert!(rc + 1 <= 0xfff);
            btree::put(self, &mut rc_, &(off | (rc + 1)), &())?;
            self.rc = Some(rc_);
            Ok(rc as usize + 1)
        } else {
            let mut rc = btree::create_db(self)?;
            btree::put(self, &mut rc, &(off | 2), &())?;
            self.rc = Some(rc);
            Ok(2)
        }
    }

    fn decr_rc(&mut self, off: u64) -> Result<usize, Error> {
        let rc = self.decr_rc_(off)?;
        if rc == 0 {
            self.free_page(off);
        }
        Ok(rc)
    }

    fn decr_rc_owned(&mut self, off: u64) -> Result<usize, Error> {
        let rc = self.decr_rc_(off)?;
        if rc == 0 {
            self.free_owned_page(off);
        }
        Ok(rc)
    }
}

impl<E: Borrow<Env>, A> MutTxn<E, A> {
    /// Decrement the reference count of page `off`, freeing that page
    /// if the RC reaches 0 after decrementing it.
    fn decr_rc_(&mut self, off: u64) -> Result<usize, Error> {
        debug!("decr_rc 0x{:x} {:?}", off, self.rc);

        // If there's no RC table, free the page. Also, in order to
        // avoid infinite recursion (since `del` and `put` below might
        // free pages), we `take` the reference counter table.
        if let Some(mut rc_) = self.rc.take() {
            let mut curs = btree::cursor::Cursor::new(self, &rc_)?;
            curs.set(self, &off, None)?;
            // The reference count is stored as the 12 LSBs of the
            // keys. If the page isn't in the RC table, the count is
            // 1.
            let rc = if let Some((rc, ())) = curs.next(self)? {
                if *rc & !0xfff == off {
                    *rc
                } else {
                    1
                }
            } else {
                1
            };
            debug!("decr_rc, rc = 0x{:x}", rc);
            if rc > 1 {
                // If the reference count is strictly more than 2,
                // replace the reference count with a decremented
                // value.
                btree::del(self, &mut rc_, &rc, None)?;
                if rc & 0xfff > 2 {
                    btree::put(self, &mut rc_, &(rc - 1), &())?;
                    self.rc = Some(rc_);
                } else {
                    // Else, we don't free the page, but don't add the
                    // page back, since this is an implicit value of
                    // "1" for the reference count.
                    self.rc = Some(rc_)
                }
                return Ok((rc & 0xfff) as usize - 1);
            } else {
                self.rc = Some(rc_)
            }
        }
        Ok(0)
    }

    /// The root page of this transaction (use with caution, this page
    /// contains root databases).
    pub unsafe fn root_page_mut(&mut self) -> &mut [u8; 4064] {
        let env = self.env.borrow();
        let maps = env.mmaps.lock();
        let ptr = maps[0].ptr.add(self.root * PAGE_SIZE + GLOBAL_HEADER_SIZE);
        &mut *(ptr as *mut [u8; 4064])
    }

    /// The root page of this transaction.
    pub unsafe fn root_page(&mut self) -> &[u8; 4064] {
        let env = self.env.borrow();
        let maps = env.mmaps.lock();
        let ptr = maps[0].ptr.add(self.root * PAGE_SIZE + GLOBAL_HEADER_SIZE);
        &*(ptr as *const [u8; 4064])
    }
}

impl<E: Borrow<Env>, A> sanakirja_core::LoadPage for MutTxn<E, A> {
    type Error = Error;
    fn load_page(&self, off: u64) -> Result<CowPage, Self::Error> {
        unsafe {
            let data = self.env.borrow().find_offset(off)?;
            Ok(CowPage { data, offset: off })
        }
    }

    fn rc(&self, page: u64) -> Result<u64, Self::Error> {
        if let Some(ref rc) = self.rc {
            if let Some((rc, _)) = btree::get(self, rc, &page, None)? {
                if *rc & !0xfff == page {
                    let r = *rc & 0xfff;
                    if r >= 2 {
                        return Ok(r);
                    }
                }
            }
        }
        Ok(0)
    }
}

impl<E: Borrow<Env>, T> RootPage for MutTxn<E, T> {
    unsafe fn root_page(&self) -> &[u8; 4064] {
        let env = self.env.borrow();
        let maps = env.mmaps.lock();
        let ptr = maps[0].ptr.add(self.root * PAGE_SIZE + GLOBAL_HEADER_SIZE);
        &*(ptr as *const [u8; 4064])
    }
}

impl<E: Borrow<Env>, T> MutTxn<E, T> {
    /// Low-level method to get the root page number `n`, if that page
    /// isn't a B tree (use the [`RootDb`] trait else).
    pub fn root(&self, n: usize) -> Option<u64> {
        if let Some(db) = self.roots.get(n) {
            Some(*db)
        } else {
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
                    Some(db)
                } else {
                    None
                }
            }
        }
    }
}

impl<E: Borrow<Env>, T> RootDb for MutTxn<E, T> {
    // Just call method `root` and convert the result to a `Db`.
    fn root_db<K: Storable + ?Sized, V: Storable + ?Sized, P: crate::btree::BTreePage<K, V>>(
        &self,
        n: usize,
    ) -> Option<sanakirja_core::btree::Db_<K, V, P>> {
        if let Some(db) = self.root(n) {
            Some(sanakirja_core::btree::Db_::from_page(db))
        } else {
            None
        }
    }
}
