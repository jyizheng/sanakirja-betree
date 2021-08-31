#![deny(
    missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_qualifications
)]
//! Transactional, on-disk datastructures with concurrent readers and
//! writers (writers exclude each other).
//!
//! This crate is based on the no-std crate `sanakirja-core`, whose
//! goal is to implement different datastructures.
//!
//! Here's an example of how to use it (starting with 64 pages, 2
//! versions, see below for details about what that means). The file
//! grows automatically, as needed.
//!
//! ```
//! use sanakirja::*;
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("db");
//! let env = Env::new(&path, 1 << 20, 2).unwrap();
//! let mut txn = Env::mut_txn_begin(&env).unwrap();
//! let mut db = btree::create_db::<_, u64, u64>(&mut txn).unwrap();
//! for i in 0..100_000u64 {
//!     btree::put(&mut txn, &mut db, &i, &(i*i)).unwrap();
//! }
//! let root_db = 0;
//! txn.set_root(root_db, db.db);
//! txn.commit().unwrap();
//! let txn = Env::txn_begin(&env).unwrap();
//! let db: btree::Db<u64, u64> = txn.root_db(root_db).unwrap();
//! assert_eq!(btree::get(&txn, &db, &50_000, None).unwrap(), Some((&50_000, &(50_000 * 50_000))));
//! for entry in btree::iter(&txn, &db, None).unwrap() {
//!   let (k, v) = entry.unwrap();
//!   assert_eq!(*k * *k, *v)
//! }
//! ```
//!
//! The binary format of a Sanakirja database is the following:
//!
//! - There is a fixed number of "current versions", set at file
//! initialisation. If a file has n versions, then for all k between 0
//! and n-1 (included), the k^th page (i.e. the byte positions between
//! `k * 4096` and `(k+1) * 4096`, also written as `k << 12` and
//! `(k+1) << 12`) stores the data relative to that version, and is
//! called the "root page" of that version.
//!
//!   This is a way to handle concurrent access: indeed, mutable
//! transactions do not exclude readers, but readers that started
//! before the commit of a mutable transaction will keep reading the
//! database as it was before the commit. However, this means that
//! older versions of the database have to be kept "alive", and the
//! "number of current versions" here is the limit on the number of
//! versions that can be kept "alive" at the same time.
//!
//!   When a reader starts, it takes a shared file lock on the file
//! representing the youngest committed version. When a writer starts,
//! it takes an exclusive file lock on the file representing the
//! oldest committed version. This implies that if readers are still
//! reading that version, the writer will wait for the exclusive lock.
//!
//!   After taking a lock, the writer (also called "mutable
//! transaction" or [`MutTxn`]) copies the entire root page of the
//! youngest committed version onto the root page of the oldest
//! committed version, hence erasing the root page of the oldest
//! version.
//!
//! - Root pages have the following format: a 32-bytes header
//! (described below), followed by 4064 bytes, usable in a more or
//! less free format. The current implementation defines two methods
//! on [`MutTxn`], [`MutTxn::set_root`] and [`MutTxn::remove_root`],
//! treating that space as an array of type `[u64; 510]`. A reasonable
//! use for these is to point to different datastructures allocated in
//! the file, such as the offsets in the file to the root pages of B
//! trees.
//!
//!   Now, about the header, there's a version identifier on the first
//! 16 bytes, followed by two bytes: `root` is the version used by the
//! current mutable transaction (if there is current mutable
//! transaction), or by the next mutable transaction (else). The
//! `n_roots` field is the total number of versions.
//!
//!   ```
//!   #[repr(C)]
//!   pub struct GlobalHeader {
//!       /// Version of Sanakirja
//!       pub version: u16,
//!       /// Which page is currently the root page? (only valid for page 0).
//!       pub root: u8,
//!       /// Total number of versions (or "root pages")
//!       pub n_roots: u8,
//!       /// CRC of this page.
//!       pub crc: u32,
//!       /// First free page at the end of the file (only valid for page 0).
//!       pub length: u64,
//!       /// Offset of the free list.
//!       pub free_db: u64,
//!       /// Offset of the RC database.
//!       pub rc_db: u64,
//!   }
//!   ```

use thiserror::*;

mod environment;
pub use environment::{Commit, Env, MutTxn, RootDb, Txn, RootPage};
pub use sanakirja_core::{btree, direct_repr, LoadPage, AllocPage, Storable, UnsizedStorable, MutPage, CowPage, Page};

#[cfg(test)]
mod tests;

#[doc(hidden)]
pub mod debug;

/// Errors that can occur while transacting.
#[derive(Debug, Error)]
pub enum Error {
    /// IO errors, from the `std::io` module.
    #[error(transparent)]
    IO(#[from] std::io::Error),
    /// Lock poisoning error.
    #[error("Lock poisoning")]
    Poison,
    /// Version mismatch
    #[error("Version mismatch")]
    VersionMismatch,
    /// CRC check failed
    #[error(transparent)]
    CRC(#[from] CRCError),
}

/// A CRC check failed
#[derive(Debug, Error)]
#[error("CRC check failed")]
pub struct CRCError {}
