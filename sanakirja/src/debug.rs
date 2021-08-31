use log::*;
use sanakirja_core::btree::*;
use sanakirja_core::*;
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

pub fn debug<
    P: AsRef<Path>,
    T: LoadPage,
    K: Storable + ?Sized + std::fmt::Debug,
    V: Storable + ?Sized + std::fmt::Debug,
    PP: BTreePage<K, V>,
>(
    t: &T,
    db: &[&Db_<K, V, PP>],
    p: P,
    recurse: bool,
) where
    T::Error: std::fmt::Debug,
{
    let f = File::create(p.as_ref()).unwrap();
    let mut buf = BufWriter::new(f);
    writeln!(&mut buf, "digraph{{").unwrap();
    let mut h = HashSet::new();
    for db in db {
        print_page::<T, K, V, PP>(t, &mut h, &mut buf, &t.load_page(db.db).unwrap(), recurse);
    }
    writeln!(&mut buf, "}}").unwrap();
}

fn print_page<
    T: LoadPage,
    K: Storable + ?Sized + std::fmt::Debug,
    V: Storable + ?Sized + std::fmt::Debug,
    P: BTreePage<K, V>,
>(
    txn: &T,
    pages: &mut HashSet<u64>,
    buf: &mut BufWriter<File>,
    p: &CowPage,
    print_children: bool,
) where
    T::Error: std::fmt::Debug,
{
    if !pages.contains(&p.offset) {
        pages.insert(p.offset);

        writeln!(
            buf,
            "subgraph cluster{} {{\nlabel=\"Page {}, rc \
             {} {}\";\ncolor=black;",
            p.offset,
            p.offset,
            txn.rc(p.offset).unwrap(),
            unsafe { u64::from_le(*(p.data as *const u64).add(1)) & 0xfff }
        )
        .unwrap();
        let mut h = Vec::new();
        let mut edges = Vec::new();
        print_cursor::<T, K, V, P>(txn, buf, &mut edges, &mut h, p);

        writeln!(buf, "}}").unwrap();
        for p in edges.iter() {
            writeln!(buf, "{}", p).unwrap()
        }
        if print_children {
            for p in h.iter() {
                print_page::<T, K, V, P>(txn, pages, buf, &p, print_children)
            }
        }
    }
}

fn print_cursor<
    T: LoadPage,
    K: Storable + ?Sized + std::fmt::Debug,
    V: Storable + ?Sized + std::fmt::Debug,
    P: BTreePage<K, V>,
>(
    txn: &T,
    buf: &mut dyn Write,
    edges: &mut Vec<String>,
    pages: &mut Vec<CowPage>,
    p: &CowPage,
) where
    T::Error: std::fmt::Debug,
{
    let mut cursor = P::cursor_first(p);
    let mut i = 0;
    let l = P::left_child(p.as_page(), &cursor);
    if l > 0 {
        pages.push(txn.load_page(l).unwrap());
        edges.push(format!(
            "n_{}_{}->n_{}_0[color=\"ForestGreen\"];",
            p.offset, i, l
        ))
    }
    while let Some((key, val, r)) = P::next(txn, p.as_page(), &mut cursor) {
        if i > 0 {
            writeln!(
                buf,
                "n_{}_{}->n_{}_{}[color=\"blue\"];",
                p.offset,
                i - 1,
                p.offset,
                i
            )
            .unwrap();
        }
        writeln!(
            buf,
            "n_{}_{}[label=\"{}: {:?} -> {:?}\"];",
            p.offset, i, i, key, val
        )
        .unwrap();
        if r > 0 {
            pages.push(txn.load_page(r).unwrap());
            edges.push(format!("n_{}_{}->n_{}_0[color=\"red\"];", p.offset, i, r))
        };
        i += 1
    }
}

type B = btree::page::Page<u64, ()>;

pub fn check_free_mut(
    txn: &crate::MutTxn<&crate::Env, ()>,
    refs: &std::collections::BTreeMap<u64, usize>,
) {
    let db_free = if txn.free > 0 {
        let db_free = Db::from_page(txn.free);
        let mut curs: Cursor<_, _, B> = btree::cursor::Cursor::new(txn, &db_free).unwrap();
        while let Some((k, _)) = curs.next(txn).unwrap() {
            assert!(refs.get(k).is_none())
        }
        Some(db_free)
    } else {
        None
    };
    debug!("{:?}", db_free);
    for (r, _) in refs.iter() {
        assert!(*r < txn.length)
    }
    let env = txn.env;
    let len = txn.length;

    for i in env.roots.len() as u64..(len >> 12) {
        let page = i << 12;
        if refs.contains_key(&page) {
            continue;
        } else if let Some(ref f) = db_free {
            if let Some((x, _)) = get(txn, f, &page, None).unwrap() {
                if *x == page {
                    continue;
                }
            }
        } else if txn.free_owned_pages.iter().any(|x| *x == page) {
            continue;
        } else if txn.free_pages.iter().any(|x| *x == page) {
            continue;
        }
        panic!("page not found: 0x{:x} (total length 0x{:x})", page, len);
    }
}

pub fn check_free<B: std::borrow::Borrow<crate::Env>>(
    txn: &crate::Txn<B>,
    refs: &std::collections::BTreeMap<u64, usize>,
) {
    let env = txn.env.borrow();
    let (db_free, length): (Option<Db<u64, ()>>, _) = unsafe {
        let hdr = &*(env.mmaps.lock()[0].ptr.add(txn.root * PAGE_SIZE)
            as *const crate::environment::GlobalHeader);
        (
            if hdr.free_db != 0 {
                Some(Db::from_page(u64::from_le(hdr.free_db)))
            } else {
                None
            },
            u64::from_le(hdr.length),
        )
    };
    debug!("db_free: {:?}", db_free);
    for (r, _) in refs.iter() {
        debug!("r = 0x{:x}, length = 0x{:x}", r, length);
        assert!(*r < length)
    }
    for i in env.roots.len() as u64..(length >> 12) {
        let page = i << 12;
        if refs.contains_key(&page) {
            continue;
        } else if let Some(ref f) = db_free {
            if let Some((x, _)) = get(txn, f, &page, None).unwrap() {
                if *x == page {
                    continue;
                }
            }
        }
        panic!("page not found: 0x{:x} (total length 0x{:x})", page, length);
    }
}

pub fn add_refs<T: LoadPage, K: Storable + Ord + ?Sized + std::fmt::Debug, V: Storable + Ord + ?Sized + std::fmt::Debug, P: BTreePage<K, V>>(
    txn: &T,
    db: &Db_<K, V, P>,
    pages: &mut std::collections::BTreeMap<u64, usize>,
) -> Result<(), T::Error>
where
    T::Error: std::fmt::Debug
{
    use std::collections::btree_map::Entry;
    let mut stack = vec![db.db];
    while let Some(p) = stack.pop() {
        match pages.entry(p) {
            Entry::Vacant(e) => {
                debug!("add_refs: 0x{:x}", p);
                e.insert(1);
                let p = txn.load_page(p)?;
                let mut c = P::cursor_first(&p);
                let l = P::left_child(p.as_page(), &c);
                if l > 0 {
                    stack.push(l);
                }
                let mut kv = None;
                while let Some((k, v, r)) = P::next(txn, p.as_page(), &mut c) {
                    debug!("{:?} {:?} {:?}", k, v, kv);
                    if let Some((k_, v_)) = kv {
                        debug!("{:?} {:?} {:?}", k_ > k, k_ == k, v_ > v);
                        if k_ > k || (k_ == k && v_ > v) {
                            debug(txn, &[db], "debug_ord", true);
                            panic!("{:?} {:?} {:?} {:?} {:?}", kv, k_, v_, k_>k, v_>v);
                        }
                    }
                    kv = Some((k, v));
                    if r > 0 {
                        stack.push(r);
                    }
                }
            }
            Entry::Occupied(mut e) => {
                e.insert(e.get() + 1);
            }
        }
    }
    Ok(())
}

pub fn add_free_refs<B: std::borrow::Borrow<crate::Env>>(
    txn: &crate::Txn<B>,
    pages: &mut std::collections::BTreeMap<u64, usize>,
) -> Result<(), crate::Error> {
    let env = txn.env.borrow();
    unsafe {
        let p = &*(env.mmaps.lock()[0].ptr.add(txn.root * PAGE_SIZE)
            as *const crate::environment::GlobalHeader);
        if p.free_db != 0 {
            debug!("add_free_refs: free = 0x{:x}", p.free_db);
            let free_db: Db<u64, ()> = btree::Db::from_page(p.free_db);
            add_refs(txn, &free_db, pages)?;
        }
        if p.rc_db != 0 {
            debug!("add_free_refs: rc = 0x{:x}", p.rc_db);
            let rc_db: Db<u64, ()> = btree::Db::from_page(p.rc_db);
            add_refs(txn, &rc_db, pages)?;
        }
    };
    Ok(())
}

pub fn add_free_refs_mut<B: std::borrow::Borrow<crate::Env>, T>(
    txn: &crate::MutTxn<B, T>,
    pages: &mut std::collections::BTreeMap<u64, usize>,
) -> Result<(), crate::Error> {
    if txn.free != 0 {
        debug!("add_free_refs: free = 0x{:x}", txn.free);
        let free_db: Db<u64, ()> = btree::Db::from_page(txn.free);
        add_refs(txn, &free_db, pages)?;
    }
    if let Some(ref rc) = txn.rc {
        debug!("add_free_refs: rc = 0x{:x}", rc.db);
        add_refs(txn, &rc, pages)?;
    }
    Ok(())
}

pub fn check_refs<B: std::borrow::Borrow<crate::Env>, T>(txn: &crate::MutTxn<B, T>, refs: &std::collections::BTreeMap<u64, usize>) {
    for (p, r) in refs.iter() {
        if *r >= 2 {
            assert_eq!(txn.rc(*p).unwrap(), *r as u64);
        } else {
            assert_eq!(txn.rc(*p).unwrap(), 0);
        }
    }
}
