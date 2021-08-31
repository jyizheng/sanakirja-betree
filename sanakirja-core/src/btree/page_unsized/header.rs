use crate::PAGE_SIZE;

#[derive(Debug)]
#[repr(C)]
pub struct Header {
    data: u16,
    n: u16,
    crc: u32,
    left_page: u64,
}

impl Header {
    pub(crate) fn init(&mut self) {
        self.data = (((PAGE_SIZE as u16) << 3) | 1).to_le();
        self.n = 0;
        self.crc = 0;
        self.left_page = 0;
    }

    pub(crate) fn n(&self) -> u16 {
        u16::from_le(self.n)
    }

    pub(crate) fn set_n(&mut self, n: u16) {
        self.n = n.to_le();
    }

    pub fn left_page(&self) -> u64 {
        u64::from_le(self.left_page)
    }

    pub fn set_left_page(&mut self, l: u64) {
        self.left_page = l.to_le()
    }

    pub fn data(&self) -> u16 {
        u16::from_le(self.data) >> 3
    }

    pub fn set_data(&mut self, d: u16) {
        let dirty = u16::from_le(self.data) & 7;
        self.data = ((d << 3) | dirty).to_le()
    }

    pub fn decr(&mut self, s: usize) {
        self.left_page = (self.left_page() - s as u64).to_le();
    }

    pub fn set_occupied(&mut self, size: u64) {
        self.left_page = ((self.left_page() & !0xfff) | size).to_le()
    }

    pub fn incr(&mut self, s: usize) {
        self.left_page = (self.left_page() + s as u64).to_le();
    }

    pub fn is_leaf(&self) -> bool {
        u64::from_le(self.left_page) <= 0xfff
    }
}

pub const HDR: usize = core::mem::size_of::<Header>();

pub(crate) fn header<'a>(page: crate::Page<'a>) -> &'a Header {
    unsafe { &*(page.data.as_ptr() as *const Header) }
}

pub fn header_mut(page: &mut crate::MutPage) -> &mut Header {
    unsafe { &mut *(page.0.data as *mut Header) }
}
