use super::header::{header, header_mut, HDR};
use super::*;

pub(super) fn put<
    'a,
    T: AllocPage,
    K: UnsizedStorable + ?Sized + core::fmt::Debug,
    V: UnsizedStorable + ?Sized + core::fmt::Debug,
    L: Alloc + AllocWrite<K, V>,
>(
    txn: &mut T,
    page: CowPage,
    mutable: bool,
    replace: bool,
    u: usize,
    k0: &'a K,
    v0: &'a V,
    k1v1: Option<(&'a K, &'a V)>,
    l: u64,
    r: u64,
) -> Result<crate::btree::put::Put<'a, K, V>, T::Error> {
    // Size of the new insertions, not counting the offsets.
    let size = alloc_size(k0, v0)
        + if let Some((k1, v1)) = k1v1 {
            alloc_size(k1, v1)
        } else {
            0
        };
    // Sized occupied by the data in these insertions (not counting
    // the offsets), if we need to compact the page.
    let size_replaced = if replace {
        // We're always in an internal node if we replace.
        let cur_size = Internal::current_size::<K, V>(page.as_page(), u as isize);
        // Since `size` isn't counting the size of the 64-bit offset,
        // and `cur_size` is, we need to add 8.
        8 + size as isize - cur_size as isize
    } else {
        size as isize
    };
    // Number of extra offsets.
    let n_ins = {
        let n_ins = if k1v1.is_some() { 2 } else { 1 };
        if replace {
            n_ins - 1
        } else {
            n_ins
        }
    };
    let hdr = header(page.as_page());
    if mutable && page.is_dirty() && L::can_alloc(header(page.as_page()), size, n_ins) {
        // First, if the page is dirty and mutable, mark it mutable.
        let mut page = MutPage(page);
        let mut n = u as isize;

        // If we replace, we first need to "unlink" the previous
        // value, by erasing its offset.
        if replace {
            let p = page.0.data;
            let hdr = header_mut(&mut page);
            // In this case, we know we're not in a leaf, so offsets
            // are of size 8.
            assert!(!hdr.is_leaf());
            unsafe {
                let ptr = p.add(HDR + n as usize * 8) as *mut u64;
                let off = (u64::from_le(*ptr) & 0xfff) as usize;
                let kv_ptr = p.add(off);
                let size = entry_size::<K, V>(kv_ptr);
                core::ptr::copy(ptr.offset(1), ptr, hdr.n() as usize - n as usize - 1);
                // Decreasing these figures here, we'll increase them
                // again in the calls to `alloc_write` below.
                hdr.decr(8 + size);
                hdr.set_n(hdr.n() - 1);
            }
        }
        // Do the actual insertions.
        if let Some((k1, v1)) = k1v1 {
            L::alloc_write(&mut page, k0, v0, 0, 0, &mut n);
            L::alloc_write(&mut page, k1, v1, l, r, &mut n);
        } else {
            L::alloc_write(&mut page, k0, v0, l, r, &mut n);
        }
        // Return: no page was freed.
        Ok(Put::Ok(Ok { page, freed: 0 }))
    } else if L::can_compact(hdr, size_replaced, n_ins) {
        // Allocate a new page, split the offsets at the position of
        // the insertion, and each side of the split onto the new
        // page, with the insertion between them.
        let mut new = txn.alloc_page()?;
        <Page<K, V> as BTreeMutPage<K, V>>::init(&mut new);

        // Clone the leftmost child.
        L::set_right_child(&mut new, -1, hdr.left_page() & !0xfff);

        // Split the offsets.
        let s = L::offset_slice(page.as_page());
        let (s0, s1) = s.split_at(u as usize);
        // Drop the first element of `s1` if we're replacing it.
        let s1 = if replace { s1.split_at(1).1 } else { s1 };

        // Finally, clone and insert.
        let mut n = 0;
        clone::<K, V, L>(page.as_page(), &mut new, s0, &mut n);
        if let Some((k1, v1)) = k1v1 {
            L::alloc_write(&mut new, k0, v0, 0, l, &mut n);
            L::alloc_write(&mut new, k1, v1, 0, r, &mut n);
        } else {
            L::alloc_write(&mut new, k0, v0, l, r, &mut n);
        }
        clone::<K, V, L>(page.as_page(), &mut new, s1, &mut n);

        // And return, freeing the old version of the page.
        Ok(Put::Ok(Ok {
            page: new,
            freed: page.offset | if page.is_dirty() { 1 } else { 0 },
        }))
    } else {
        split_unsized::<_, _, _, L>(txn, page, replace, u, k0, v0, k1v1, l, r)
    }
}

// Surprisingly, the following function is simpler than in the sized
// case, because we can't be too efficient in this case, since we have
// to go through all the elements linearly anyway to get their sizes.
fn split_unsized<
    'a,
    T: AllocPage,
    K: UnsizedStorable + ?Sized + core::fmt::Debug,
    V: UnsizedStorable + ?Sized + core::fmt::Debug,
    L: Alloc + AllocWrite<K, V>,
>(
    txn: &mut T,
    page: CowPage,
    replace: bool,
    u: usize,
    k0: &'a K,
    v0: &'a V,
    k1v1: Option<(&'a K, &'a V)>,
    l0: u64,
    r0: u64,
) -> Result<crate::btree::put::Put<'a, K, V>, T::Error> {
    let hdr = header(page.as_page());
    let mut left = txn.alloc_page()?;
    <Page<K, V> as BTreeMutPage<K, V>>::init(&mut left);

    let mut right = txn.alloc_page()?;
    <Page<K, V> as BTreeMutPage<K, V>>::init(&mut right);

    // Clone the leftmost child. If we're inserting at position 0,
    // this means this leftmost child must, and will be replaced.
    let left_child = hdr.left_page() & !0xfff;
    L::set_right_child(&mut left, -1, left_child);

    // Pointer to the split key and value.
    let mut split = None;

    // We start filling the left page, and we will change to filling
    // the right page when the left one is at least half-full.
    let mut current_page = &mut left;

    // There are two synchronised counters here: `hdr.n()` and
    // `n`. The reason for this is that operations on `hdr.n()` are
    // somewhat cumbersome, as they might involve extra operations to
    // convert to/from the little-endian encoding of `hdr.n()`.
    let mut n = 0;
    let s = L::offset_slice(page.as_page());
    let mut total = HDR;
    for (uu, off) in s.0.iter().enumerate() {
        // If the current position of the cursor is the insertion,
        // (i.e. `uu == u`), insert.
        if uu == u {
            // The following is tricky and makes assumptions on the
            // rest of the code. If we are inserting two elements
            // (i.e. if `k1v1.is_some()`), this means we're replacing
            // one on the page.
            header_mut(current_page).set_n(n as u16);
            if let Some((k1, v1)) = k1v1 {
                // As explained in the documentation for `put` in the
                // definition of `BTreeMutPage`, `l0` and `r0` are the
                // left and right children of k1v1, since this means
                // the right child of a deleted entry has split, and
                // we must replace the deleted entry with `(k0, v0)`.
                L::alloc_write(current_page, k0, v0, 0, l0, &mut n);
                total += alloc_size(k0, v0) + L::OFFSET_SIZE;
                L::alloc_write(current_page, k1, v1, 0, r0, &mut n);
                total += alloc_size(k1, v1) + L::OFFSET_SIZE;

                // Replacing the next element:
                debug_assert!(replace);
                continue;
            } else {
                L::alloc_write(current_page, k0, v0, l0, r0, &mut n);
                total += alloc_size(k0, v0) + L::OFFSET_SIZE;
                if replace {
                    continue;
                }
            }
        }
        // Then, i.e. either if we're not at the position of an
        // insertion, or else if we're not replacing the current
        // position, just copy the current entry to the appropriate
        // page (left or right).
        let (r, off): (u64, usize) = (*off).into();
        assert_ne!(off, 0);
        unsafe {
            let ptr = page.data.add(off);
            let size = entry_size::<K, V>(ptr);

            // If the left side of the split is at least half-full, we
            // know that we can do all the insertions we need on the
            // right-hand side (even if there are two of them, and the
            // replaced value is of size 0), so we switch.
            if split.is_none() && total >= PAGE_SIZE / 2 {
                // Don't write the next entry onto any page, keep it
                // as the split entry.
                let (k, v) = read::<T, K, V>(txn, ptr);
                split = Some((K::from_raw_ptr(txn, k), V::from_raw_ptr(txn, v)));
                // Set the entry count for the current page, before
                // switching and resetting the counter.
                header_mut(current_page).set_n(n as u16);

                // And set the leftmost child of the right page to
                // `r`.
                L::set_right_child(&mut right, -1, r);

                // Then, switch page and reset the counter.
                current_page = &mut right;
                n = 0;
            } else {
                // Else, we're simply allocating a new entry on the
                // current page.
                let off_new = {
                    let hdr = header_mut(current_page);
                    let data = hdr.data();
                    assert!(
                        HDR + hdr.n() as usize * L::OFFSET_SIZE + L::OFFSET_SIZE + size
                            < data as usize
                    );
                    // Move the data pointer `size` bytes to the left.
                    hdr.set_data(data - size as u16);
                    // And increase the number of entries, and
                    // occupied size of the page.
                    hdr.incr(size + L::OFFSET_SIZE);
                    data - size as u16
                };
                // Copy the entry.
                core::ptr::copy_nonoverlapping(
                    ptr,
                    current_page.0.data.offset(off_new as isize),
                    size,
                );
                // And set the offset.
                L::set_offset(current_page, n, r | (off_new as u64));
                n += 1;
            }
            total += size + L::OFFSET_SIZE;
        }
    }
    header_mut(current_page).set_n(n as u16);

    // Finally, it is possible that we haven't had a chance to do the
    // insertions yet: this is the case iff we're inserting at the end
    // of all the entries, so handle this now.
    if u == s.0.len() {
        if let Some((k1, v1)) = k1v1 {
            L::alloc_write(current_page, k0, v0, 0, l0, &mut n);
            L::alloc_write(current_page, k1, v1, 0, r0, &mut n);
        } else {
            L::alloc_write(current_page, k0, v0, l0, r0, &mut n);
        }
    }
    let (split_key, split_value) = split.unwrap();
    Ok(Put::Split {
        split_key,
        split_value,
        left,
        right,
        freed: if page.is_dirty() {
            page.offset | 1
        } else {
            page.offset
        },
    })
}
