use super::{header, Header};

#[derive(Debug, Clone, Copy)]
pub struct PageCursor {
    pub cur: isize,
    pub total: usize,
    pub is_leaf: bool,
}

impl PageCursor {
    /// Initialise a cursor on page `p` at position `cur`, checking
    /// that `cur` is a valid position.
    pub fn new(p: &crate::CowPage, cur: isize) -> Self {
        let hdr = unsafe { &*(p.data as *const Header) };
        assert!(cur >= -1 && cur < hdr.n() as isize);
        PageCursor {
            cur,
            total: hdr.n() as usize,
            is_leaf: hdr.is_leaf(),
        }
    }
    /// Initialise a cursor set after the last entry of page `p`.
    pub fn after(p: &crate::CowPage) -> Self {
        let hdr = unsafe { &*(p.data as *const Header) };
        let total = hdr.n();
        PageCursor {
            cur: total as isize,
            total: total as usize,
            is_leaf: hdr.is_leaf(),
        }
    }
    /// Initialise a cursor set on the last entry of page `p`.
    pub fn last(p: crate::Page) -> Self {
        let hdr = header(p);
        let total = hdr.n();
        PageCursor {
            cur: (total - 1) as isize,
            total: total as usize,
            is_leaf: hdr.is_leaf(),
        }
    }
}
