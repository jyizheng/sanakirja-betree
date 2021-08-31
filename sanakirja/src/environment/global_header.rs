pub const GLOBAL_HEADER_SIZE: usize = 32;
pub const N_ROOTS: usize = 508;

#[derive(Debug)]
#[repr(C)]
pub struct GlobalHeader {
    /// Version of Sanakirja
    pub version: u16,
    /// Which page is currently the root page? (only valid for page 0)
    pub root: u8,
    pub n_roots: u8,
    /// CRC of this page
    pub crc: u32,

    /// First free page at the end of the file (only valid for page 0)
    pub length: u64,

    /// Offset of the free list
    pub free_db: u64,

    /// Offset of the RC db,
    pub rc_db: u64,
}

impl GlobalHeader {
    pub fn from_le(&self) -> Self {
        GlobalHeader {
            version: u16::from_le(self.version),
            root: self.root,
            n_roots: self.n_roots,
            crc: u32::from_le(self.crc),
            free_db: u64::from_le(self.free_db),
            length: u64::from_le(self.length),
            rc_db: u64::from_le(self.rc_db),
        }
    }
    pub fn to_le(&self) -> Self {
        GlobalHeader {
            version: self.version.to_le(),
            root: self.root,
            n_roots: self.n_roots,
            crc: self.crc.to_le(),
            free_db: self.free_db.to_le(),
            length: self.length.to_le(),
            rc_db: self.rc_db.to_le(),
        }
    }
}
