//! Deletions from a B tree.
use super::cursor::*;
use super::put::{Ok, Put};
use super::*;
use crate::LoadPage;

/// Represents the result of a merge or rebalance, without touching
/// the parent of the merge/rebalance.
#[derive(Debug)]
pub enum Op<'a, T, K: ?Sized, V: ?Sized> {
    Merged {
        // New merged page.
        page: MutPage,
        // Pages freed by the merge (0 meaning "no page").
        freed: [u64; 2],
        marker: core::marker::PhantomData<T>,
    },
    Rebalanced {
        // New middle key.
        k: &'a K,
        // New middle value.
        v: &'a V,
        // New left page.
        l: u64,
        // New right page.
        r: u64,
        // Pages freed by the rebalance (0 meaning "no page").
        freed: [u64; 2],
    },
    Put(crate::btree::put::Put<'a, K, V>),
}

/// Represents a page with modifications from a merge.
#[derive(Debug)]
pub struct ModifiedPage<'a, K: ?Sized, V: ?Sized, P: BTreePage<K, V>> {
    pub page: CowPage,
    // Whether the page is mutable with another tree.
    pub mutable: bool,
    // Start copying c0 (keep `page`'s left child).
    pub c0: P::Cursor,
    // If > 0, replace the right child of c0's last element with `l`.
    pub l: u64,
    // If > 0, replace the left child of c1's last element with `r`.
    pub r: u64,
    // Possibly insert a new binding.
    pub ins: Option<(&'a K, &'a V)>,
    // If a rebalance causes a split, we might need to insert an entry
    // after the replacement.
    pub ins2: Option<(&'a K, &'a V)>,
    // The first element of c1 is to be deleted, the others must be copied.
    pub c1: P::Cursor,
    // Whether to skip `c1`'s first element.
    pub skip_first: bool,
    // Whether the page we just modified is `self.l`.
    pub mod_is_left: bool,
}

/// Represents the concatenation of a modified page and one of its
/// sibling (left or right).
#[derive(Debug)]
pub struct Concat<'a, K: ?Sized, V: ?Sized, P: BTreePage<K, V>> {
    /// Modified page.
    pub modified: ModifiedPage<'a, K, V, P>,
    /// Middle element.
    pub mid: (&'a K, &'a V),
    /// Sibling of the modified page.
    pub other: CowPage,
    /// Is the modified field on the left or on the right of the
    /// concatenation?
    pub mod_is_left: bool,
    /// Is the other page owned by this tree? If not, it means `other`
    /// is shared with another tree, and hence we need to increase the
    /// reference count of entries coming from `other`.
    pub other_is_mutable: bool,
}

/// If `value` is `None`, delete the first entry for `key` from the
/// database, if present. Else, delete the entry for `(key, value)`,
/// if present.
pub fn del<
    T: AllocPage + LoadPage + core::fmt::Debug,
    K: Storable + ?Sized + core::fmt::Debug + PartialEq,
    V: Storable + ?Sized + core::fmt::Debug + PartialEq,
    P: BTreeMutPage<K, V> + core::fmt::Debug,
>(
    txn: &mut T,
    db: &mut Db_<K, V, P>,
    key: &K,
    value: Option<&V>,
) -> Result<bool, T::Error> {
    let mut cursor = Cursor::new(txn, db)?;
    // If the key and value weren't found, return.
    match (cursor.set(txn, key, value)?, value) {
        (Some((k, v)), Some(value)) if k == key && v == value => {}
        (Some((k, _)), None) if k == key => {}
        _ => return Ok(false),
    }
    // Else, the cursor is set on `(key, value)` if `value.is_some()`
    // or on the first entry with key `key` else.
    //
    // We delete that position, which might be in a leaf or in an
    // internal node.
    del_at_cursor(txn, db, &mut cursor)
}

/// Delete the entry pointed to by `cursor`. The cursor can't be used
/// after this.
#[doc(hidden)]
pub fn del_at_cursor<
    T: AllocPage + LoadPage + core::fmt::Debug,
    K: Storable + ?Sized + core::fmt::Debug + PartialEq,
    V: Storable + ?Sized + core::fmt::Debug,
    P: BTreeMutPage<K, V> + core::fmt::Debug,
>(
    txn: &mut T,
    db: &mut Db_<K, V, P>,
    cursor: &mut Cursor<K, V, P>,
) -> Result<bool, T::Error> {
    let p0 = cursor.len();

    // If p0 < cursor.first_rc_level, the page containing the deleted
    // element is not shared with another table. Therefore, the RC of
    // the pages referenced by the deleted element needs to be
    // decreased.
    //
    // Else, that RC doesn't need to be changed, since it's still
    // referenced by the same pages as before, just not by the pages
    // that are cloned by this deletion.
    if p0 < cursor.first_rc_len() {
        let (delk, delv, _) = {
            let cur = cursor.cur();
            P::current(txn, cur.page.as_page(), &cur.cursor).unwrap()
        };
        for o in delk.page_references().chain(delv.page_references()) {
            txn.decr_rc(o)?;
        }
    }

    // Find the leftmost page in the right subtree of the deleted
    // element, in order to find a replacement.
    let cur = cursor.cur();
    let right_subtree = P::right_child(cur.page.as_page(), &cur.cursor);
    cursor.set_first_leaf(txn, right_subtree)?;
    let leaf_is_shared = cursor.len() >= cursor.first_rc_len();

    // In the leaf, mark the replacement for deletion, and keep a
    // reference to it in k0v0 if the deletion happens in an internal
    // node (k0v0 is `Option::None` else).
    let (mut last_op, k0v0) = leaf_delete(txn, cursor, p0)?;

    // If the leaf is shared with another tree, then since we're
    // cloning the leaf, update the reference counts of all the
    // references contained in the leaf.
    if leaf_is_shared {
        modify_rc(txn, &last_op)?;
    }

    let mut free = [[0, 0]; N_CURSORS];

    // Then, climb up the stack, performing the operations lazily. At
    // each step, we are one level above the page that we plan to
    // modify, since `last_op` is the result of popping the
    // stack.
    //
    // We iterate up to the root. The last iteration builds a modified
    // page for the root, but doesn't actually execute it.
    while cursor.len() > 0 {
        // Prepare a plan for merging the current modified page (which
        // is stored in `last_op`) with one of its neighbours.
        let concat = concat(txn, cursor, p0, &k0v0, last_op)?;
        let mil = concat.mod_is_left;

        let incr_page = if !concat.other_is_mutable {
            Some(CowPage {
                offset: concat.other.offset,
                data: concat.other.data,
            })
        } else {
            None
        };
        let incr_mid = if cursor.len() >= cursor.first_rc_len() {
            Some(concat.mid)
        } else {
            None
        };

        // Execute the modification plan, resulting in one of four
        // different outcomes (described in the big match in
        // `handle_merge`). This mutates or clones the current
        // modified page, returning an `Op` describing what happened
        // (between update, merge, rebalance and split).
        let merge = P::merge_or_rebalance(txn, concat)?;
        // Prepare a description (`last_op`) of the next page
        // modification, without mutating nor cloning that page.
        last_op = handle_merge(txn, cursor, p0, &k0v0, incr_page, incr_mid, mil, merge, &mut free)?;
        // If the modified page is shared with another tree, we will
        // clone it in the next round. Therefore, update the reference
        // counts of all the references in the modified page.
        //
        // Since `handle_merge` pops the stack, the modified page is
        // at level `cursor.len() + 1`.
        if cursor.len() + 1 >= cursor.first_rc_len() {
            modify_rc(txn, &last_op)?;
        }
    }

    // The last modification plan was on the root, and still needs to
    // be executed.
    let root_is_shared = cursor.first_rc_len() == 1;
    update_root(txn, db, last_op, k0v0, root_is_shared, &mut free)?;

    // Finally, free all the pages marked as free during the deletion,
    // now that we don't need to read them anymore.
    for p in free.iter() {
        if p[0] & 1 == 1 {
            txn.decr_rc_owned(p[0] ^ 1)?;
        } else if p[0] > 0 {
            txn.decr_rc(p[0])?;
        }
        if p[1] & 1 == 1 {
            txn.decr_rc_owned(p[1] ^ 1)?;
        } else if p[1] > 0 {
            txn.decr_rc(p[1])?;
        }
    }
    Ok(true)
}

/// Preparing a modified page for the leaf.
fn leaf_delete<
    'a,
    T: AllocPage + LoadPage,
    K: Storable + ?Sized,
    V: Storable + ?Sized,
    P: BTreeMutPage<K, V> + 'a,
>(
    txn: &mut T,
    cursor: &mut Cursor<K, V, P>,
    p0: usize,
) -> Result<(ModifiedPage<'a, K, V, P>, Option<P::Saved>), T::Error> {
    let is_rc = cursor.len() >= cursor.first_rc_len();
    let del_at_internal = p0 < cursor.len();
    let curs0 = cursor.pop().unwrap();
    let (c0, c1) = P::split_at(&curs0.cursor);
    let mut deleted = None;
    if del_at_internal {
        // In this case, we need to save the replacement, and if this
        // leaf is shared with another tree, we also need increment
        // the replacement's references, since we are copying it.
        let (k, v, _) = P::current(txn, curs0.page.as_page(), &c1).unwrap();
        if is_rc {
            for o in k.page_references().chain(v.page_references()) {
                txn.incr_rc(o)?;
            }
        }
        deleted = Some(P::save_deleted_leaf_entry(k, v))
    }
    Ok((
        ModifiedPage {
            page: curs0.page,
            mutable: !is_rc,
            c0,
            c1,
            skip_first: true,
            l: 0,
            r: 0,
            ins: None,
            ins2: None,
            // The following (`mod_is_left`) is meaningless in this
            // context, and isn't actually used: indeed, the only
            // place where this field is used is when modifying the
            // root, when `ins.is_some()`.
            mod_is_left: true,
        },
        deleted,
    ))
}

/// From a cursor at level `p = cursor.len()`, form the
/// concatenation of `last_op` (which is a modified page at level p +
/// 1`, and its left or right sibling, depending on the case.
fn concat<
    'a,
    T: AllocPage + LoadPage,
    K: Storable + ?Sized,
    V: Storable + ?Sized,
    P: BTreeMutPage<K, V> + core::fmt::Debug,
>(
    txn: &mut T,
    cursor: &mut Cursor<K, V, P>,
    p0: usize,
    k0v0: &Option<P::Saved>,
    last_op: ModifiedPage<'a, K, V, P>,
) -> Result<Concat<'a, K, V, P>, T::Error> {
    let p = cursor.len();
    let rc_level = cursor.first_rc_len();
    let curs = cursor.current_mut();

    if p == p0 {
        // Here, p == p0, meaning that we're deleting at an internal
        // node. If that's the case, k0v0 is `Some`, hence we can
        // safely unwrap the replacement.
        let (k0, v0) = unsafe { P::from_saved(k0v0.as_ref().unwrap()) };

        // Since we've picked the leftmost entry of the right child of
        // the deleted entry, the other page to consider in the
        // concatenation is the left child of the deleted entry.
        let other = txn.load_page(P::left_child(curs.page.as_page(), &curs.cursor))?;
        // Then, if the page at level `p` or one of its ancestor, is
        // pointed at least twice (i.e. if `p >= rc_level`, or
        // alternatively if `other` is itself pointed at least twice,
        // the page is immutable, meaning that we can't delete on it
        // when rebalancing.
        let other_is_mutable = (p < rc_level) && txn.rc(other.offset)? < 2;
        Ok(Concat {
            modified: last_op,
            mid: (k0, v0),
            other,
            mod_is_left: false,
            other_is_mutable,
        })
    } else {
        // Here, `p` is not a leaf (but `last_op` might be), and does
        // not contain the deleted entry.

        // In this case, the visited page at level `p+1` is always on
        // the left-hand side of the cursor at level `p` (this is an
        // invariant of cursors). However, if the cursor at level `p`
        // is past the end of the page, we need to move one step back
        // to find a middle element for the concatenation, in which
        // case the visited page becomes the right-hand side of the
        // cursor.
        let ((k, v, r), mod_is_left) =
            if let Some(x) = P::current(txn, curs.page.as_page(), &curs.cursor) {
                // Not the last element of the page.
                (x, true)
            } else {
                // Last element of the page.
                let (k, v, _) = P::prev(txn, curs.page.as_page(), &mut curs.cursor).unwrap();
                let l = P::left_child(curs.page.as_page(), &curs.cursor);
                ((k, v, l), false)
            };
        let other = txn.load_page(r)?;
        let other_is_mutable = (p < rc_level) && txn.rc(other.offset)? < 2;
        Ok(Concat {
            modified: last_op,

            // The middle element comes from the page above this
            // concatenation, and hence has the same lifetime as that
            // page. However, our choice of lifetimes can't express
            // this, but we also know that we are not going to mutate
            // the parent before rebalancing or merging the
            // concatenation, and hence this pointer will be alive
            // during these operations (i.e. during the merge or
            // rebalance).
            mid: unsafe { (core::mem::transmute(k), core::mem::transmute(v)) },

            other,
            mod_is_left,
            other_is_mutable,
        })
    }
}

/// Prepare a modified version of the page at the current level `p =
/// cursor.len()`.
fn handle_merge<
    'a,
    T: AllocPage + LoadPage,
    K: Storable + ?Sized + PartialEq,
    V: Storable + ?Sized,
    P: BTreeMutPage<K, V>,
>(
    txn: &mut T,
    cursor: &mut Cursor<K, V, P>,
    p0: usize,
    k0v0: &Option<P::Saved>,
    incr_other: Option<CowPage>,
    incr_mid: Option<(&K, &V)>,

    mod_is_left: bool,    // The modified page in the `merge` is the left one.

    merge: Op<'a, T, K, V>,
    free: &mut [[u64; 2]; N_CURSORS],
) -> Result<ModifiedPage<'a, K, V, P>, T::Error> {
    let mutable = cursor.len() < cursor.first_rc_len();
    let mut last_op = {
        // Beware, a stack pop happens here, all subsequent references
        // to the pointer must be updated.
        let curs = cursor.pop().unwrap();
        let (c0, c1) = P::split_at(&curs.cursor);
        ModifiedPage {
            page: curs.page,
            mutable,
            c0,
            l: 0,
            r: 0,
            ins: None,
            ins2: None,
            c1,
            skip_first: true,
            mod_is_left,
        }
    };

    // For merges and rebalances, take care of the reference counts of
    // pages and key/values.
    match merge {
        Op::Merged {.. } | Op::Rebalanced { .. } => {
            // Increase the RC of the "other page's" descendants. In
            // the case of a rebalance, this has the effect of
            // increasing the RC of the new middle entry if that entry
            // comes from a shared page, which is what we want.
            if let Some(other) = incr_other {
                let mut curs = P::cursor_first(&other);
                let left = P::left_child(other.as_page(), &curs);
                if left > 0 {
                    txn.incr_rc(left)?;
                }
                while let Some((k0, v0, r)) = P::next(txn, other.as_page(), &mut curs) {
                    for o in k0.page_references().chain(v0.page_references()) {
                        txn.incr_rc(o)?;
                    }
                    if r != 0 {
                        txn.incr_rc(r)?;
                    }
                }
            }

            // If the middle element comes from a shared page,
            // increment its references.
            if let Some((ref k, ref v)) = incr_mid {
                for o in k.page_references().chain(v.page_references()) {
                    txn.incr_rc(o)?;
                }
            }
        }
        _ => {}
    }

    // Here, we match on `merge`, the operation that just happened at
    // level `cursor.len() + 1`, and build the modification plan
    // for the page at the current level (i.e. at level
    // `cursor.len()`).
    let freed = match merge {
        Op::Merged {
            page,
            freed,
            marker: _,
        } => {
            // If we're deleting at an internal node, the
            // replacement has already been included in the merged
            // page.
            last_op.l = page.0.offset;
            freed
        }
        Op::Rebalanced {
            k,
            v,
            l,
            r,
            freed,
        } => {
            // If we're deleting at an internal node, the
            // replacement is already in pages `l` or `r`.
            last_op.l = l;
            last_op.r = r;
            last_op.ins = Some((k, v));
            freed
        }
        Op::Put(Put::Ok(Ok { page, freed })) => {
            // No merge, split or rebalance has happened. If we're
            // deleting at an internal node (i.e. if cursor.len ==
            // p0), we need to mark the replacement here.
            if cursor.len() + 1 == p0 {
                // We have already incremented the references of the
                // replacement at the leaf.
                if let Some(k0v0) = k0v0 {
                    last_op.ins = Some(unsafe { P::from_saved(k0v0) });
                }
                last_op.r = page.0.offset;
            } else {
                last_op.skip_first = false;
                if mod_is_left {
                    last_op.l = page.0.offset;
                } else {
                    last_op.r = page.0.offset;
                }
            }
            [freed, 0]
        }
        Op::Put(Put::Split {
            left,
            right,
            split_key,
            split_value,
            freed,
        }) => {
            // This case only happens if `(K, V)` is not `Sized`, when
            // either (1) a rebalance replaces a key/value pair with a
            // larger one or (2) another split has happened in a page
            // below.
            let split_key_is_k0 = if cursor.len() == p0 {
                // In this case, ins2 comes after ins, since the
                // replacement is in the right child of the deleted
                // key.
                if let Some(k0v0) = k0v0 {
                    last_op.ins = Some(unsafe { P::from_saved(k0v0) });
                }
                last_op.ins2 = Some((split_key, split_value));
                false
            } else {
                last_op.ins = Some((split_key, split_value));
                last_op.skip_first = false;

                // If the page modified in the last step is the one on
                // the right of the current entry, move right one step
                // before inserting the split key/value.
                //
                // (remember that we popped the stack upon entering
                // this function).
                //
                // We need to do this because the split key/value is
                // inserted immediately *before* the current cursor
                // position, which is incorrect if the split key/value
                // comes from the right-hand side of the current
                // cursor position.
                //
                // This can happen in exactly two situations:
                // - when the element we are deleting is the one we are
                //   skipping here.
                // - when we are deleting in the rightmost child of a
                //   page.
                if cursor.len() > 0 && !mod_is_left {
                    P::move_next(&mut last_op.c1);
                }
                // If the split key is the replacement element, we have
                // already increased its counter when we deleted it from
                // its original position at the bottom of the tree.
                //
                // This can happen if we replaced an element and that
                // replacement caused a split with the replacement as the
                // middle element.
                if let Some(k0v0) = k0v0 {
                    assert!(cursor.len() + 1 < p0);
                    let (k0, _) = unsafe { P::from_saved(k0v0) };
                    core::ptr::eq(k0, split_key)
                } else {
                    false
                }
            };
            // The `l` and `r` fields are relative to `ins2` if
            // `ins2.is_some()` or to `ins` else.
            last_op.l = left.0.offset;
            last_op.r = right.0.offset;
            if cursor.len() + 2 >= cursor.first_rc_len() && !split_key_is_k0 {
                for o in split_key
                    .page_references()
                    .chain(split_value.page_references())
                {
                    txn.incr_rc(o)?;
                }
            }
            [freed, 0]
        }
    };
    // Free the page(s) at level `cursor.len() + 1` if it isn't
    // shared with another tree, or if it is the first level shared
    // with another tree.
    if cursor.len() + 1 < cursor.first_rc_len() {
        free[cursor.len() + 1] = freed;
    }
    Ok(last_op)
}

// This function modifies the reference counts of references of the
// modified page, which is the page *about to be* modified.
//
// This function is always called when `m` is an internal node.
fn modify_rc<
    T: AllocPage + LoadPage,
    K: Storable + ?Sized,
    V: Storable + ?Sized,
    P: BTreePage<K, V>,
>(
    txn: &mut T,
    m: &ModifiedPage<K, V, P>,
) -> Result<(), T::Error> {
    let mut c0 = m.c0.clone();
    let mut c1 = m.c1.clone();
    let mut left = P::left_child(m.page.as_page(), &c0);
    while let Some((k, v, r)) = P::next(txn, m.page.as_page(), &mut c0) {
        for o in k.page_references().chain(v.page_references()) {
            txn.incr_rc(o)?;
        }
        if left != 0 {
            txn.incr_rc(left)?;
        }
        left = r;
    }
    // The insertions are taken care of in `handle_merge` above,
    // so we can directly move to the `c1` part of the
    // modification.
    if m.skip_first {
        P::move_next(&mut c1);
    }
    // If we are not updating the left child of c1's first
    // element, increment that left child.
    if m.l == 0 {
        if left != 0 {
            txn.incr_rc(left)?;
        }
    }

    // If we are not updating the right child of the first
    // element of `c1`, increment that right child's RC.
    if let Some((k, v, r)) = P::next(txn, m.page.as_page(), &mut c1) {
        for o in k.page_references().chain(v.page_references()) {
            txn.incr_rc(o)?;
        }
        // If `m.skip_first`, we have already skipped the entry above,
        // so this `r` has nothing to do with any update.
        //
        // Else, if we aren't skipping, but also aren't updating the
        // right child of the current entry, also increase the RC.
        if (m.skip_first || m.r == 0) && r != 0 {
            txn.incr_rc(r)?;
        }
    }
    // Finally, increment the RCs of all other elements in `c1`.
    while let Some((k, v, r)) = P::next(txn, m.page.as_page(), &mut c1) {
        for o in k.page_references().chain(v.page_references()) {
            txn.incr_rc(o)?;
        }
        if r != 0 {
            txn.incr_rc(r)?;
        }
    }
    Ok(())
}

fn update_root<
    T: AllocPage + LoadPage + core::fmt::Debug,
    K: Storable + ?Sized + core::fmt::Debug,
    V: Storable + ?Sized + core::fmt::Debug,
    P: BTreeMutPage<K, V> + core::fmt::Debug,
>(
    txn: &mut T,
    db: &mut Db_<K, V, P>,
    last_op: ModifiedPage<K, V, P>,
    k0v0: Option<P::Saved>,
    is_rc: bool,
    free: &mut [[u64; 2]; N_CURSORS],
) -> Result<(), T::Error> {
    if let Some(d) = single_child(&last_op) {
        // If the root had only one element, and the last operation
        // was a merge, this decreases the depth of the tree.
        //
        // We don't do this if the table is empty (i.e. if `d == 0`),
        // in order to be consistent with put and drop.
        if d > 0 {
            if last_op.page.is_dirty() {
                txn.decr_rc_owned(last_op.page.offset)?;
            } else {
                txn.decr_rc(last_op.page.offset)?;
            }
            db.db = d;
        } else {
            // The page becomes empty.
            let (page, freed) = P::del(txn, last_op.page, last_op.mutable, &last_op.c1, d)?;
            free[0][0] = freed;
            db.db = page.0.offset
        }
        return Ok(());
    }

    // Else, the last operation `last_op` was relative to the root,
    // but it hasn't been applied yet. We apply it now:
    match modify::<_, K, V, P>(txn, last_op)? {
        Put::Ok(Ok { page, freed }) => {
            // Here, the root was simply updated (i.e. some elements
            // might have been deleted/inserted/updated), so we just
            // need to update the Db.
            free[0][0] = freed;
            db.db = page.0.offset
        }
        Put::Split {
            split_key: k,
            split_value: v,
            left: MutPage(CowPage { offset: l, .. }),
            right: MutPage(CowPage { offset: r, .. }),
            freed,
        } => {
            // Else, the root has split, and we need to allocate a new
            // page to hold the split key/value and the two sides of
            // the split.
            free[0][0] = freed;
            let mut page = txn.alloc_page()?;
            P::init(&mut page);
            let mut c = P::cursor_before(&page.0);
            P::move_next(&mut c);
            let page = if let Put::Ok(p) = P::put(txn, page.0, true, false, &c, k, v, None, l, r)? {
                p.page
            } else {
                unreachable!()
            };
            let split_key_is_k0 = if let Some(ref k0v0) = k0v0 {
                let (k0, _) = unsafe { P::from_saved(k0v0) };
                core::ptr::eq(k0, k)
            } else {
                false
            };
            // If the root isn't shared with another tree, and the
            // split key is different from the replacement, increment
            // the RCs of the references contained in the split
            // key/value.
            //
            // The replacement need not be incremented again, since it
            // was already increment when we took it from the page in
            // `leaf_delete`.
            if is_rc && !split_key_is_k0 {
                for o in k.page_references().chain(v.page_references()) {
                    txn.incr_rc(o)?;
                }
            }
            // Finally, update the database.
            db.db = page.0.offset
        }
    }
    Ok(())
}

fn single_child<K: Storable + ?Sized, V: Storable + ?Sized, P: BTreeMutPage<K, V>>(
    m: &ModifiedPage<K, V, P>,
) -> Option<u64> {
    let mut c1 = m.c1.clone();
    if m.skip_first {
        P::move_next(&mut c1);
    }
    if P::is_empty(&m.c0) && m.ins.is_none() && P::is_empty(&c1) {
        Some(m.l)
    } else {
        None
    }
}

/// Apply the modifications to a page. This is exclusively used for
/// the root page, because other modifications are applied during a
/// merge/rebalance attempts.
fn modify<'a, T: AllocPage, K: Storable + ?Sized, V: Storable + ?Sized, P: BTreeMutPage<K, V>>(
    txn: &mut T,
    m: ModifiedPage<'a, K, V, P>,
) -> Result<super::put::Put<'a, K, V>, T::Error> {
    if let Some((k, v)) = m.ins {
        // The following call might actually replace the first element
        // of `m.c1` if `m.skip_first`.
        let mut c1 = m.c1.clone();
        if !m.skip_first && !m.mod_is_left {
            // This means that the page below just split, since we
            // have to insert an extra entry on the root page.
            //
            // However, the extra entry is to be inserted (by
            // `P::put`) *before* `c1`'s first element, which is
            // incorrect since the page that split is the right child
            // of `c1`'s first element. Therefore, we need to move
            // `c1` one notch to the right.
            assert!(m.ins2.is_none());
            P::move_next(&mut c1);
        }
        P::put(
            txn,
            m.page,
            m.mutable,
            m.skip_first,
            &c1,
            k,
            v,
            m.ins2,
            m.l,
            m.r,
        )
    } else {
        // If there's no insertion to do, we might still need to
        // delete elements, or update children.
        if m.skip_first {
            let (page, freed) = P::del(txn, m.page, m.mutable, &m.c1, m.l)?;
            Ok(Put::Ok(Ok { freed, page }))
        } else if m.l > 0 {
            // If the left page of the current entry has changed,
            // update it.
            Ok(Put::Ok(P::update_left_child(
                txn, m.page, m.mutable, &m.c1, m.l,
            )?))
        } else {
            // If there's no insertion, and `m.l == 0`, we need to
            // update the right child of the current entry. The
            // following moves one step to the right and updates the
            // left child:
            let mut c1 = m.c1.clone();
            P::move_next(&mut c1);
            Ok(Put::Ok(P::update_left_child(
                txn, m.page, m.mutable, &c1, m.r,
            )?))
        }
    }
}
