//! The `RawVec<u32>` insertion case that the ESP32-C3 firmware and the QEMU
//! harness share. Its five calls reach all five outcomes of the routine:
//! insertion before a suffix, append, full, invalid index, and invalid length.

use crate::header::{FULL, INDEX_OUT_OF_BOUNDS, INVALID_LENGTH, OK, RawVec};

/// The C ABI of `raw_vec_u32_insert` and of the calling shim that forwards to it.
pub type Insert = unsafe extern "C" fn(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;

/// Make the five calls through `insert`, assert every status and the final
/// memory, and return the statuses of the first four calls for the report.
///
/// # Safety
///
/// `insert` must have the contract of `raw_vec_u32_insert` in
/// `research/vec-ffi/linked/raw_vec.rs`.
#[inline(always)]
pub unsafe fn run(insert: Insert) -> [u32; 4] {
    let mut data = [111, 10, 30, 0, 0, 222];
    let mut vec = RawVec {
        data: data[1..5].as_mut_ptr(),
        length: 2,
        capacity: 4,
    };
    // SAFETY: The header and its four initialized backing slots are disjoint.
    // No other accesses to the header or array occur during these calls.
    let statuses = unsafe {
        let inserted = insert(&mut vec, 1, 20);
        let end = vec.length;
        let appended = insert(&mut vec, end, 40);
        let full = insert(&mut vec, 0, 99);
        let invalid_index = insert(&mut vec, 5, 99);
        [inserted, appended, full, invalid_index]
    };
    assert_eq!(statuses, [OK, OK, FULL, INDEX_OUT_OF_BOUNDS]);
    assert_eq!(vec.length, 4);
    assert_eq!(vec.capacity, 4);

    let mut invalid = RawVec { length: 5, ..vec };
    // SAFETY: The header is exclusive. Its length exceeds capacity, so this
    // call returns without accessing the backing array.
    assert_eq!(unsafe { insert(&mut invalid, 0, 99) }, INVALID_LENGTH);
    assert_eq!(invalid.length, 5);
    assert_eq!(data, [111, 10, 20, 30, 40, 222]);
    statuses
}
