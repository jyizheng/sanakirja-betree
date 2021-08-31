use super::*;

pub(super) fn put<
    'a,
    T: AllocPage,
    K: Storable + core::fmt::Debug,
    V: Storable + core::fmt::Debug,
    L: Alloc + super::super::page_unsized::AllocWrite<K, V>,
>(
    txn: &mut T,
    page: CowPage,
    mutable: bool,
    replace: bool,
    u: usize,
    k0: &'a K,
    v0: &'a V,
    l: u64,
    r: u64,
) -> Result<crate::btree::put::Put<'a, K, V>, T::Error> {
    let hdr = header(page.as_page());
    let is_dirty = page.is_dirty();
    if mutable && is_dirty && L::can_alloc::<K, V>(hdr) {
        // If the page is mutable (i.e. not shared with another tree)
        // and dirty, here's what we do:
        let mut page = MutPage(page);
        let p = page.0.data;
        let hdr = header_mut(&mut page);
        let mut n = u as isize;
        if replace {
            // If we're replacing a value, this can't be in a leaf,
            // hence the only thing that needs to be done is erasing
            // the offset in the offset array. This is a bit naive,
            // since we're moving that array back and forth.
            assert!(!hdr.is_leaf());
            unsafe {
                let ptr = p.add(HDR + n as usize * 8) as *mut u64;
                core::ptr::copy(ptr.offset(1), ptr, hdr.n() as usize - n as usize - 1);
                hdr.decr(8 + core::mem::size_of::<Tuple<K, V>>());
                hdr.set_n(hdr.n() - 1);
            }
        }
        // Do the actual insertions.
        L::alloc_write(&mut page, k0, v0, l, r, &mut n);
        // No page was freed, return the page.
        Ok(Put::Ok(Ok { page, freed: 0 }))
    } else if replace || L::can_compact::<K, V>(hdr) {
        // Here, we could allocate if we cloned, so let's clone:
        let mut new = txn.alloc_page()?;
        <Page<K, V> as BTreeMutPage<K, V>>::init(&mut new);
        L::set_right_child(&mut new, -1, hdr.left_page() & !0xfff);

        // Take the offsets and split it at the cursor position.
        let s = L::offset_slice::<T, K, V>(page.as_page());
        let (s0, s1) = s.split_at(u as usize);

        // If we're replacing, remove the offset that needs to go.
        let s1 = if replace { s1.split_at(1).1 } else { s1 };

        // And then clone the page, inserting the new elements between
        // the two halves of the split offsets.
        let mut n = 0;
        clone::<K, V, L>(page.as_page(), &mut new, s0, &mut n);
        L::alloc_write(&mut new, k0, v0, l, r, &mut n);
        clone::<K, V, L>(page.as_page(), &mut new, s1, &mut n);
        Ok(Put::Ok(Ok {
            page: new,
            freed: if is_dirty {
                page.offset | 1
            } else {
                page.offset
            },
        }))
    } else {
        // Else, split the page.
        split::<_, _, _, L>(txn, page, mutable, u, k0, v0, l, r)
    }
}

fn split<
    'a,
    T: AllocPage,
    K: Storable + core::fmt::Debug,
    V: Storable + core::fmt::Debug,
    L: Alloc + super::super::page_unsized::AllocWrite<K, V>,
>(
    txn: &mut T,
    page: CowPage,
    mutable: bool,
    u: usize,
    k0: &'a K,
    v0: &'a V,
    l: u64,
    r: u64,
) -> Result<crate::btree::put::Put<'a, K, V>, T::Error> {
    let mut left;
    let hdr = header(page.as_page());

    let page_is_dirty = if page.is_dirty() { 1 } else { 0 };

    let mut n = hdr.n();
    let k = n / 2;
    n += 1;
    let s = L::offset_slice::<T, K, V>(page.as_page());
    let (s0, s1) = s.split_at(k as usize);

    // Find the split entry (i.e. the entry going up in the B
    // tree). Then, mid_child is the right child of the split
    // key/value, and `s1` is the offsets of the right side of the
    // split.
    let (mut split_key, mut split_value, mid_child, s1) = if u == k as usize {
        // The inserted element is exactly in the middle.
        (k0, v0, r, s1)
    } else {
        // Else, the split key is the first element of `s1`: set the
        // new, updated `s1`.
        let (s1a, s1b) = s1.split_at(1);
        let (k, v, r) = L::kv(page.as_page(), L::first::<K, V>(&s1a));
        (k, v, r, s1b)
    };
    let mut freed = 0;
    if u >= k as usize {
        // If we are here, u >= k, i.e. the insertion is in the
        // right-hand side of the split, or is the split entry itself.
        let mut right = txn.alloc_page()?;
        <Page<K, V> as BTreeMutPage<K, V>>::init(&mut right);
        if u > k as usize {
            // if we're inserting in the right-hand side, clone to the
            // newly allocated `right` page, by
            let mut n = 0;

            // Splitting the offsets to make space for an insertion,
            // and insert in the middle.
            //
            // Off-by-one error? Nope: since `k` is the split entry,
            // the right page starts at index `k + 1`, hence if `u ==
            // k + 1`, `kk` must be 0.
            let kk = u as usize - k as usize - 1;
            let (s1a, s1b) = s1.split_at(kk);
            L::set_right_child(&mut right, -1, mid_child);
            clone::<K, V, L>(page.as_page(), &mut right, s1a, &mut n);
            L::alloc_write(&mut right, k0, v0, l, r, &mut n);
            clone::<K, V, L>(page.as_page(), &mut right, s1b, &mut n);
        } else {
            // Else, just clone the page, we'll take care of returning
            // the split entry afterwards.
            clone::<K, V, L>(page.as_page(), &mut right, s1, &mut 0);
        }

        if mutable && page.is_dirty() {
            // (k0, v0) is to be inserted on the right-hand side of
            // the split, hence we don't have to clone the left-hand
            // side, we can just truncate it.
            left = MutPage(page);
            let hdr = header_mut(&mut left);
            hdr.set_n(k);
            hdr.decr((n - 1 - k) as usize * core::mem::size_of::<Tuple<K, V>>());
        } else {
            // Else, we need to clone the first `k-1` entries,
            // i.e. `s0`, onto a new left page.
            left = txn.alloc_page()?;
            <Page<K, V> as BTreeMutPage<K, V>>::init(&mut left);
            let mut n = 0;
            L::set_right_child(&mut left, -1, hdr.left_page() & !0xfff);
            clone::<K, V, L>(page.as_page(), &mut left, s0, &mut n);
            freed = page.offset | page_is_dirty
        }

        // Finally, if `u` is the middle element, its left and right
        // children become the leftmost child of the right page, and
        // the rightmost child of the left page, respectively.
        if u == k as usize {
            // Insertion in the middle:
            // - `l` becomes the right child of the last element on `left`.
            L::set_right_child(&mut left, k as isize - 1, l);
            // - `r` (i.e. `mid_child`) becomes the left child of `right`.
            L::set_right_child(&mut right, -1, mid_child);
        }
        Ok(Put::Split {
            split_key,
            split_value,
            left,
            right,
            freed,
        })
    } else {
        // Else, the insertion is in the new left page. We first clone
        // the left page, inserting (k,v) at its position:
        left = txn.alloc_page()?;
        <Page<K, V> as BTreeMutPage<K, V>>::init(&mut left);
        // Clone the leftmost page
        let ll = header(page.as_page()).left_page() & !0xfff;
        L::set_right_child(&mut left, -1, ll);
        // Clone the two sides, with an entry in between.
        let (s0a, s0b) = s0.split_at(u as usize);
        let mut n = 0;
        clone::<K, V, L>(page.as_page(), &mut left, s0a, &mut n);
        L::alloc_write(&mut left, k0, v0, l, r, &mut n);
        clone::<K, V, L>(page.as_page(), &mut left, s0b, &mut n);

        let mut right;
        let freed;
        // Then, for the right page:
        if mutable && page.is_dirty() {
            // If we can mutate the original page, remove the first
            // `k` entries, and return a pointer to the split key (at
            // position `k` on the page)
            right = MutPage(page);
            if let Some((k, v)) = L::truncate_left::<K, V>(&mut right, k as usize + 1) {
                unsafe {
                    split_key = &*k;
                    split_value = &*v;
                }
            }
            freed = 0;
        } else {
            // Else, clone the right page.
            right = txn.alloc_page()?;
            <Page<K, V> as BTreeMutPage<K, V>>::init(&mut right);
            // The left child of the right page is `mid_child`,
            // i.e. the right child of the split entry.
            L::set_right_child(&mut right, -1, mid_child);
            // Clone the rest of the page.
            let mut n = 0;
            clone::<K, V, L>(page.as_page(), &mut right, s1, &mut n);
            freed = page.offset | page_is_dirty
        }
        Ok(Put::Split {
            split_key,
            split_value,
            left,
            right,
            freed,
        })
    }
}
