use super::*;
use core::mem::MaybeUninit;

pub(crate) fn rebalance_left<
    'a,
    T: AllocPage,
    K: Storable + core::fmt::Debug,
    V: Storable + core::fmt::Debug,
    L: Alloc,
>(
    txn: &mut T,
    m: Concat<'a, K, V, Page<K, V>>,
) -> Result<Op<'a, T, K, V>, T::Error> {
    assert!(m.mod_is_left);
    // First element of the right page. We'll rotate it to the left
    // page, i.e. return a middle element, and append the current
    // middle element to the left page.
    let rc = super::PageCursor::new(&m.other, 0);
    let rl = <Page<K, V>>::left_child(m.other.as_page(), &rc);
    let (k, v, r) = <Page<K, V>>::current(txn, m.other.as_page(), &rc).unwrap();

    let mut freed_ = [0, 0];

    // First, perform the modification on the modified page, which we
    // know is the left page, and return the resulting mutable page
    // (the modified page may or may not be mutable before we do this).
    let new_left = if let Some((k, v)) = m.modified.ins {
        let is_dirty = m.modified.page.is_dirty();
        let page = if let Put::Ok(Ok { page, freed }) = <Page<K, V>>::put(
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
        let lc = PageCursor::after(&page.0);
        if let Put::Ok(Ok { page, freed }) = <Page<K, V>>::put(
            txn, page.0, true, false, &lc, m.mid.0, m.mid.1, None, 0, rl,
        )? {
            if freed > 0 {
                let b = if is_dirty { 1 } else { 0 };
                // index 0 is ok here: if a page is freed, it means we
                // just compacted a page, which implies that the call
                // to `put` above didn't free.
                freed_[0] = freed | b
            }
            page
        } else {
            unreachable!()
        }
    } else if m.modified.skip_first {
        // Looking at module `super::del`, the only way we can be in
        // this case
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
            freed_[0] = freed | b
        }
        // Append the middle element of the concatenation at the end
        // of the left page. We know the left page to be mutable by
        // now, and we also know there's enough space to do this.
        let lc = PageCursor::after(&page.0);
        if let Put::Ok(Ok { page, freed }) = <Page<K, V>>::put(
            txn, page.0, true, false, &lc, m.mid.0, m.mid.1, None, 0, rl,
        )? {
            if freed > 0 {
                let b = if is_dirty { 1 } else { 0 };
                // index 0 is ok here: if we freed a page in the call
                // to `del` above, it is mutable and we can allocate
                // on it. Else, we just compacted a page, but that
                // also means `del` above didn't free.
                freed_[0] = freed | b
            }
            page
        } else {
            unreachable!()
        }
    } else {
        let is_dirty = m.modified.page.is_dirty();
        let lc = PageCursor::after(&m.modified.page);
        if let Put::Ok(Ok { page, freed }) = <Page<K, V>>::put(
            txn, m.modified.page, m.modified.mutable, false, &lc, m.mid.0, m.mid.1, None, 0, rl,
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
                freed_[0] = freed | b
            }
            page
        } else {
            unreachable!()
        }
    };

    let f = core::mem::size_of::<Tuple<K, V>>();
    let (new_right, k, v) = if r == 0 && m.other_is_mutable && m.other.is_dirty() {
        // Since `r == 0`, we know this is a leaf. Therefore, we need
        // to rewrite the deleted element to the end of the page, so
        // that the pointer to the new middle entry is valid when this
        // function returns.
        let data = m.other.data;
        let mut other = MutPage(m.other);
        let right_hdr = header_mut(&mut other);
        // Remove the space for one entry.
        let n = right_hdr.n() as usize;
        right_hdr.decr(f);
        right_hdr.set_n((n - 1) as u16);

        let al = core::mem::align_of::<Tuple<K, V>>();
        let hdr_size = (HDR + al - 1) & !(al - 1);
        let mut t: MaybeUninit<Tuple<K, V>> = MaybeUninit::uninit();
        unsafe {
            // Save the leftmost element (we can't directly copy it to
            // the end, because the page may be full).
            core::ptr::copy_nonoverlapping(
                data.add(hdr_size) as *mut Tuple<K, V>,
                t.as_mut_ptr(),
                1,
            );
            // Move the n - 1 last elements one entry to the left.
            core::ptr::copy(
                data.add(hdr_size + f) as *const Tuple<K, V>,
                data.add(hdr_size) as *mut Tuple<K, V>,
                n - 1,
            );
            // Copy the last element to the end of the page.
            let last = data.add(hdr_size + f * (n - 1)) as *mut Tuple<K, V>;
            core::ptr::copy_nonoverlapping(t.as_ptr(), last, 1);
            (other, &(&*last).k, &(&*last).v)
        }
    } else {
        // If this isn't a leaf, or isn't mutable, use the standard
        // deletion function, because we know this will leave the
        // pointer to the current entry valid.

        // We extend the pointer's lifetime here, because we know the
        // current deletion (we only rebalance during deletions) won't
        // touch this page anymore after this.
        let k = unsafe { core::mem::transmute(k) };
        let v = unsafe { core::mem::transmute(v) };

        // If this frees the old "other" page, add it to the "freed"
        // array.
        let is_dirty = m.other.is_dirty();
        let (page, freed) = <Page<K, V>>::del(txn, m.other, m.other_is_mutable, &rc, r)?;
        if freed > 0 {
            freed_[1] = if is_dirty { freed | 1 } else { freed };
        }
        (page, k, v)
    };
    Ok(Op::Rebalanced {
        l: new_left.0.offset,
        r: new_right.0.offset,
        k,
        v,
        freed: freed_,
    })
}
