/// A C-compatible eight-byte element: two words, passed in two registers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(C)]
pub struct Pair {
    pub key: u32,
    pub value: u32,
}

/// Caller-owned vector storage with a C-compatible header.
#[repr(C)]
pub struct RawVec<T> {
    pub data: *mut T,
    pub length: u32,
    pub capacity: u32,
}

pub const OK: u32 = 0;
pub const FULL: u32 = 1;
pub const INDEX_OUT_OF_BOUNDS: u32 = 2;
pub const INVALID_LENGTH: u32 = 3;
