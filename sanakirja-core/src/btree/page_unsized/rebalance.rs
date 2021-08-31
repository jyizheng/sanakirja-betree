use super::cursor::*;
use super::*;

// The implementation here is mostly the same as in the sized case,
// except for leaves, which makes it hard to refactor.
pub(crate) fn rebalance_left<
    'a,
    T: AllocPage,
    K: UnsizedStorable + ?Sized + core::fmt::Debug,
    V: UnsizedStorable + ?Sized + core::fmt::Debug,
    L: Alloc,
>(
    txn: &mut T,
    m: Concat<'a, K, V, Page<K, V>>,
) -> Result<Op<'a, T, K, V>, T::Error> {
    assert!(m.mod_is_left);
    // First element of the right page. We'll rotate it to the left
    // page, i.e. return a middle element, and append the current
    // middle element to the left page.
    let rc = super::cursor::PageCursor::new(&m.other, 0);
    let rl = <Page<K, V>>::left_child(m.other.as_page(), &rc);
    let (k, v, r) = <Page<K, V>>::current(txn, m.other.as_page(), &rc).unwrap();

    let mut freed_ = [0, 0];

    // First, perform the modification on the modified page, which we
    // know is the left page, and return the resulting mutable page
    // (the modified page may or may not be mutable before we do this).
    let new_left = if let Some((k, v)) = m.modified.ins {
        let is_dirty = m.modified.page.is_dirty();
        let new_left = if let Put::Ok(Ok { page, freed }) = <Page<K, V>>::put(
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
        )? {
            if freed > 0 {
                let b = if is_dirty { 1 } else { 0 };
                freed_[0] = freed | b;
            }
            page
        } else {
            unreachable!()
        };
        // Append the middle element of the concatenation at the end
        // of the left page. We know the left page to be mutable by
        // now, and we also know there's enough space to do this.
        let lc = PageCursor::after(&new_left.0);
        if let Put::Ok(Ok { freed, page }) = <Page<K, V>>::put(
            txn, new_left.0, true, false, &lc, m.mid.0, m.mid.1, None, 0, rl,
        )? {
            if freed > 0 {
                let b = if is_dirty { 1 } else { 0 };
                freed_[0] = freed | b;
            }
            page
        } else {
            unreachable!()
        }
    } else if m.modified.skip_first {
        let is_dirty = m.modified.page.is_dirty();
        let (page, freed) = <Page<K, V>>::del(
            txn,
            m.modified.page,
            m.modified.mutable,
            &m.modified.c1,
            m.modified.l,
        )?;
        if freed > 0 {
            let b = if is_dirty { 1 } else { 0 };
            freed_[0] = freed | b;
        }

        // Append the middle element of the concatenation at the end
        // of the left page. We know the left page to be mutable by
        // now, and we also know there's enough space to do this.
        let lc = PageCursor::after(&page.0);
        if let Put::Ok(Ok { freed, page }) =
            <Page<K, V>>::put(txn, page.0, true, false, &lc, m.mid.0, m.mid.1, None, 0, rl)?
        {
            if freed > 0 {
                let b = if is_dirty { 1 } else { 0 };
                freed_[0] = freed | b;
            }
            page
        } else {
            unreachable!()
        }
    } else {
        // Append the middle element of the concatenation at the end
        // of the left page. We know the left page to be mutable by
        // now, and we also know there's enough space to do this.
        let is_dirty = m.modified.page.is_dirty();
        let lc = PageCursor::after(&m.modified.page);
        if let Put::Ok(Ok { freed, page }) = <Page<K, V>>::put(
            txn,
            m.modified.page,
            m.modified.mutable,
            false,
            &lc,
            m.mid.0,
            m.mid.1,
            None,
            0,
            rl,
        )? {
            if m.modified.l > 0 {
                assert_eq!(m.modified.r, 0);
                unsafe {
                    let off = (page.0.data.add(HDR) as *mut u64).offset(m.modified.c1.cur - 1);
                    *off = (m.modified.l | (u64::from_le(*off) & 0xfff)).to_le();
                }
            } else if m.modified.r > 0 {
                unsafe {
                    let off = (page.0.data.add(HDR) as *mut u64).offset(m.modified.c1.cur);
                    *off = (m.modified.r | (u64::from_le(*off) & 0xfff)).to_le();
                }
            }
            if freed > 0 {
                let b = if is_dirty { 1 } else { 0 };
                freed_[0] = freed | b;
            }
            page
        } else {
            unreachable!()
        }
    };

    // We extend the pointer's lifetime here, because we know the
    // current deletion (we only rebalance during deletions) won't
    // touch this page anymore after this.
    let k = unsafe { core::mem::transmute(k) };
    let v = unsafe { core::mem::transmute(v) };

    // If this frees the old "other" page, add it to the "freed"
    // array.
    let is_dirty = m.other.is_dirty();
    let (new_right, freed) = <Page<K, V>>::del(txn, m.other, m.other_is_mutable, &rc, r)?;
    if freed > 0 {
        freed_[1] = if is_dirty { freed | 1 } else { freed }
    }
    Ok(Op::Rebalanced {
        l: new_left.0.offset,
        r: new_right.0.offset,
        k,
        v,
        freed: freed_,
    })
}

// Surprisingly, the `rebalance_right` function is simpler,
// since:
//
// - if we call it to rebalance two internal nodes, we're in the easy
// case of rebalance_left.
//
// - Else, the middle element is the last one on the left page, and
// isn't erased be leaf deletions, because these just move entries to
// the left.
//
// This implementation is shared with the sized one.
pub(crate) fn rebalance_right<
    'a,
    T: AllocPage,
    K: ?Sized,
    V: ?Sized,
    P: BTreeMutPage<K, V, Cursor = super::PageCursor>,
>(
    txn: &mut T,
    m: Concat<'a, K, V, P>,
) -> Result<Op<'a, T, K, V>, T::Error> {
    assert!(!m.mod_is_left);
    // Take the last element of the left page.
    let lc = P::cursor_last(&m.other);
    let (k0, v0, r0) = P::current(txn, m.other.as_page(), &lc).unwrap();

    let mut freed_ = [0, 0];

    // Perform the modification on the modified page.
    let new_right = if let Some((k, v)) = m.modified.ins {
        let is_dirty = m.modified.page.is_dirty();
        let new_right = if let Put::Ok(Ok { page, freed }) = P::put(
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
        )? {
            if freed > 0 {
                freed_[0] = if is_dirty { freed | 1 } else { freed };
            }
            page
        } else {
            unreachable!()
        };
        // Add the middle element of the concatenation as the first
        // element of the right page. We know the right page is
        // mutable, since we just modified it (hence the
        // `assert_eq!(freed, 0)`.

        // First element of the right page (after potential
        // modification by `put` above).
        let rc = P::cursor_first(&new_right.0);
        let rl = P::left_child(new_right.0.as_page(), &rc);
        if let Put::Ok(Ok { freed, page }) = P::put(
            txn,
            new_right.0,
            true,
            false,
            &rc,
            m.mid.0,
            m.mid.1,
            None,
            r0,
            rl,
        )? {
            debug_assert_eq!(freed, 0);
            page
        } else {
            unreachable!()
        }
    } else if m.modified.skip_first {
        let is_dirty = m.modified.page.is_dirty();
        let (page, freed) = P::del(
            txn,
            m.modified.page,
            m.modified.mutable,
            &m.modified.c1,
            m.modified.l,
        )?;
        if freed > 0 {
            freed_[0] = if is_dirty { freed | 1 } else { freed };
        }
        // Add the middle element of the concatenation as the first
        // element of the right page. We know the right page is
        // mutable, since we just modified it. Moreover, if it is
        // compacted by the `put` below, we know that the `del` didn't
        // free anything, hence we can reuse the slot 0..

        // First element of the right page (after potential
        // modification by `del` above).
        let rc = P::cursor_first(&page.0);
        let rl = P::left_child(page.0.as_page(), &rc);
        if let Put::Ok(Ok { freed, page }) = P::put(
            txn, page.0, true, false, &rc, m.mid.0, m.mid.1, None, r0, rl,
        )? {
            if freed > 0 {
                freed_[0] = if is_dirty { freed | 1 } else { freed };
            }
            page
        } else {
            unreachable!()
        }
    } else {
        let is_dirty = m.modified.page.is_dirty();
        let rc = P::cursor_first(&m.modified.page);
        let rl = P::left_child(m.modified.page.as_page(), &rc);
        if let Put::Ok(Ok { freed, page }) = P::put(
            txn,
            m.modified.page,
            m.modified.mutable,
            false,
            &rc,
            m.mid.0,
            m.mid.1,
            None,
            r0,
            rl,
        )? {
            // Update the left and right offsets. We know that at
            // least one of them is 0, but it can be either one (or
            // both), depending on what happened on the page below.
            //
            // Since we inserted an entry at the beginning of the
            // page, we need to add 1 to the index given by
            // `m.modified.c1.cur`.
            if m.modified.l > 0 {
                assert_eq!(m.modified.r, 0);
                unsafe {
                    let off = (page.0.data.add(HDR) as *mut u64).offset(m.modified.c1.cur);
                    *off = (m.modified.l | (u64::from_le(*off) & 0xfff)).to_le();
                }
            } else if m.modified.r > 0 {
                unsafe {
                    let off = (page.0.data.add(HDR) as *mut u64).offset(m.modified.c1.cur + 1);
                    *off = (m.modified.r | (u64::from_le(*off) & 0xfff)).to_le();
                }
            }
            if freed > 0 {
                freed_[0] = if is_dirty { freed | 1 } else { freed };
            }
            page
        } else {
            unreachable!()
        }
    };

    // As explained in the general comment on this function, this
    // entry isn't erased by the deletion in `m.other` below, so we
    // can safely extend its lifetime.
    let k = unsafe { core::mem::transmute(k0) };
    let v = unsafe { core::mem::transmute(v0) };

    let is_dirty = m.other.is_dirty();
    let (new_left, freed) = P::del(txn, m.other, m.other_is_mutable, &lc, 0)?;
    if freed > 0 {
        freed_[1] = if is_dirty { freed | 1 } else { freed }
    }
    Ok(Op::Rebalanced {
        l: new_left.0.offset,
        r: new_right.0.offset,
        k,
        v,
        freed: freed_,
    })
}
