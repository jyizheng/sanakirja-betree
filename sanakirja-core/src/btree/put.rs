//! Insertions into a B tree.
use super::cursor::*;
use super::*;
/// The representation of the update to a page.
#[derive(Debug)]
pub struct Ok {
    /// The new page, possibly the same as the previous version.
    pub page: MutPage,
    /// The freed page, or 0 if no page was freed.
    pub freed: u64,
}

/// The result of an insertion, i.e. either an update or a split.
#[derive(Debug)]
pub enum Put<'a, K: ?Sized, V: ?Sized> {
    Ok(Ok),
    Split {
        split_key: &'a K,
        split_value: &'a V,
        left: MutPage,
        right: MutPage,
        freed: u64,
    },
}

/// Insert an entry into a database, returning `false` if and only if
/// the exact same entry (key *and* value) was already in the
/// database.
pub fn put<
    T: AllocPage,
    K: Storable + ?Sized + core::fmt::Debug,
    V: Storable + ?Sized + core::fmt::Debug,
    P: BTreeMutPage<K, V>,
>(
    txn: &mut T,
    db: &mut Db_<K, V, P>,
    key: &K,
    value: &V,
) -> Result<bool, T::Error> {
    // Set the cursor to the first element larger than or equal to
    // `(key, value)`. We will insert at that position (where "insert"
    // is meant in the sense of Rust's `Vec::insert`.
    let mut cursor = Cursor::new(txn, db)?;
    if cursor.set(txn, key, Some(value))?.is_some() {
        // If `(key, value)` already exists in the tree, return.
        return Ok(false);
    }
    // Else, we are at a leaf, since cursors that don't find an
    // element go all the way to the leaves.
    //
    // We put on the leaf page, resulting in a `Put`, i.e. either
    // `Put::Ok` or `Put::Split`.
    let p = cursor.len(); // Save the position of the leaf cursor.
    let is_owned = p < cursor.first_rc_len();

    // Insert the key and value at the leaf, i.e. pop the top level of
    // the stack (the leaf) and insert in there.
    let cur = cursor.pop().unwrap();
    let put = P::put(
        txn,
        cur.page,
        is_owned,
        false,
        &cur.cursor,
        key,
        value,
        None,
        0,
        0,
    )?;

    // In both cases (`Ok` and `Split`), we need to walk up the tree
    // and update each node.

    // Moreover, since the middle elements of the splits may be on
    // pages that must be freed at the end of this call, we collect
    // them in the `free` array below, and free them only at the end
    // of this function.
    //
    // If we didn't hold on to these pages, they could be reallocated
    // in subsequent splits, and the middle element could be
    // lost. This is important when the middle element climbs up more
    // than one level (i.e. the middle element of the split of a leaf
    // is also the middle element of the split of the leaf's parent,
    // etc).
    let mut free = [0; N_CURSORS];
    db.db = put_cascade(txn, &mut cursor, put, &mut free)?.0.offset;
    for f in &free[..p] {
        if *f & 1 != 0 {
            txn.decr_rc_owned((*f) ^ 1)?;
        } else if *f > 0 {
            txn.decr_rc(*f)?;
        }
    }
    Ok(true)
}

fn put_cascade<
    T: AllocPage,
    K: Storable + ?Sized + core::fmt::Debug,
    V: Storable + ?Sized + core::fmt::Debug,
    P: BTreeMutPage<K, V>,
>(
    txn: &mut T,
    cursor: &mut Cursor<K, V, P>,
    mut put: Put<K, V>,
    free: &mut [u64; N_CURSORS],
) -> Result<MutPage, T::Error> {
    loop {
        match put {
            Put::Split {
                split_key,
                split_value,
                left,
                right,
                freed,
            } => {
                // Here, we are copying all children of the freed
                // page, except possibly the last freed page (which is
                // a child of the current node, if we aren't at a
                // leaf). This includes the split key/value, also
                // incremented in the following call:
                incr_descendants::<T, K, V, P>(txn, cursor, free, freed)?;
                // Then, insert the split key/value in the relevant page:
                let is_owned = cursor.len() < cursor.first_rc_len();
                if let Some(cur) = cursor.pop() {
                    // In this case, there's a page above the page
                    // that just split (since we can pop the stack),
                    // so the page that just split isn't the root (but
                    // `cur` might be).
                    put = P::put(
                        txn,
                        cur.page,
                        is_owned,
                        false,
                        &cur.cursor,
                        split_key,
                        split_value,
                        None,
                        left.0.offset,
                        right.0.offset,
                    )?;
                } else {
                    // No page above the split, so the root has just
                    // split. Insert the split key/value into a new
                    // page above the entire tree.
                    let mut p = txn.alloc_page()?;
                    let cursor = P::cursor_first(&p.0);
                    P::init(&mut p);
                    if let Put::Ok(p) = P::put(
                        txn,
                        p.0,
                        true,
                        false,
                        &cursor,
                        split_key,
                        split_value,
                        None,
                        left.0.offset,
                        right.0.offset,
                    )? {
                        // Return the new root.
                        return Ok(p.page);
                    } else {
                        unreachable!()
                    }
                }
            }
            Put::Ok(Ok { page, freed }) => {
                // Same as above: increment the relevant reference
                // counters.
                incr_descendants::<T, K, V, P>(txn, cursor, free, freed)?;
                // And update the left child of the current cursor,
                // since the main invariant of cursors is that we're
                // always visiting the left child (if we're visiting
                // the last child of a page, the cursor is set to the
                // position strictly after the entries).
                let is_owned = cursor.len() < cursor.first_rc_len();
                if let Some(curs) = cursor.pop() {
                    // If we aren't at the root, just update the child.
                    put = Put::Ok(P::update_left_child(
                        txn,
                        curs.page,
                        is_owned,
                        &curs.cursor,
                        page.0.offset,
                    )?)
                } else {
                    // If we are at the root, `page` is the updated root.
                    return Ok(page);
                }
            }
        }
    }
}

/// This function does all the memory management for `put`.
fn incr_descendants<
    T: AllocPage + LoadPage,
    K: Storable + ?Sized,
    V: Storable + ?Sized,
    P: BTreePage<K, V>,
>(
    txn: &mut T,
    cursor: &mut Cursor<K, V, P>,
    free: &mut [u64; N_CURSORS],
    mut freed: u64,
) -> Result<(), T::Error> {
    // The freed page is on the page below.
    if cursor.len() < cursor.first_rc_len() {
        // If a page has split or was immutable (allocated by a
        // previous transaction) and has been updated, we need to free
        // the old page.
        free[cursor.len()] = freed;
    } else {
        // This means that the new version of the page (either split
        // or not) contains references to all the children of the
        // freed page, except the last freed page (because the new
        // version of that page isn't shared).
        let cur = cursor.cur();

        // Start a cursor at the leftmost position and increase the
        // leftmost child page's RC (if we aren't at a leaf, and if
        // that child isn't the last freed page).
        let mut c = P::cursor_first(&cur.page);
        let left = P::left_child(cur.page.as_page(), &c);
        if left != 0 {
            if left != (freed & !1) {
                txn.incr_rc(left)?;
            } else if cursor.len() == cursor.first_rc_len() {
                freed = 0
            }
        }
        // Then, for each entry of the page, increase the RCs of
        // references contained in the keys and values, and increase
        // the RC of the right child.
        while let Some((k, v, r)) = P::next(txn, cur.page.as_page(), &mut c) {
            for o in k.page_references().chain(v.page_references()) {
                txn.incr_rc(o)?;
            }
            if r != 0 {
                if r != (freed & !1) {
                    txn.incr_rc(r)?;
                } else if cursor.len() == cursor.first_rc_len() {
                    freed = 0
                }
            }
        }
        // Else, the "freed" page is shared with another tree, and
        // hence we just need to decrement its RC.
        if freed > 0 && cursor.len() == cursor.first_rc_len() {
            free[cursor.len()] = freed;
        }
    }
    Ok(())
}
