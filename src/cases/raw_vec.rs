//! The `RawVec` insertion cases that the ESP32-C3 firmware and the QEMU
//! harness share. Each case's five calls reach all five outcomes of its
//! routine: insertion before a suffix, append, full, invalid index, and
//! invalid length.

use core::fmt::Arguments;

use crate::header::{FULL, INDEX_OUT_OF_BOUNDS, INVALID_LENGTH, OK, Pair, RawVec};

/// The C ABI of `raw_vec_u32_insert` and of the calling shim that forwards to it.
pub type InsertU32 = unsafe extern "C" fn(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;

/// The C ABI of `raw_vec_pair_insert` and of the calling shim that forwards to it.
pub type InsertPair = unsafe extern "C" fn(vec: *mut RawVec<Pair>, index: u32, value: Pair) -> u32;

/// Make the five `RawVec<u32>` calls through `insert`, assert every status and
/// the final memory, and report success through `print`.
///
/// # Safety
///
/// `insert` must have the contract of `raw_vec_u32_insert` in
/// `research/vec-ffi/linked/raw_vec.rs`.
pub unsafe fn insert_u32(insert: InsertU32, print: impl FnOnce(Arguments<'_>)) {
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
    print(format_args!(
        "RawVec<u32> PASS: [10, 20, 30, 40]; statuses {statuses:?}; invalid length rejected"
    ));
}

/// Make the five `RawVec<Pair>` calls through `insert`, assert every status
/// and the final memory, and report success through `print`.
///
/// # Safety
///
/// `insert` must have the contract of `raw_vec_pair_insert` in
/// `research/vec-ffi/linked/raw_vec.rs`.
pub unsafe fn insert_pair(insert: InsertPair, print: impl FnOnce(Arguments<'_>)) {
    let pair = |key, value| Pair { key, value };
    let mut data = [
        pair(111, 1110),
        pair(10, 100),
        pair(30, 300),
        pair(0, 0),
        pair(0, 0),
        pair(222, 2220),
    ];
    let mut vec = RawVec {
        data: data[1..5].as_mut_ptr(),
        length: 2,
        capacity: 4,
    };
    // SAFETY: The header and its four initialized backing slots are disjoint.
    // No other accesses to the header or array occur during these calls.
    let statuses = unsafe {
        let inserted = insert(&mut vec, 1, pair(20, 200));
        let end = vec.length;
        let appended = insert(&mut vec, end, pair(40, 400));
        let full = insert(&mut vec, 0, pair(99, 990));
        let invalid_index = insert(&mut vec, 5, pair(99, 990));
        [inserted, appended, full, invalid_index]
    };
    assert_eq!(statuses, [OK, OK, FULL, INDEX_OUT_OF_BOUNDS]);
    assert_eq!(vec.length, 4);
    assert_eq!(vec.capacity, 4);

    let mut invalid = RawVec { length: 5, ..vec };
    // SAFETY: The header is exclusive. Its length exceeds capacity, so this
    // call returns without accessing the backing array.
    assert_eq!(
        unsafe { insert(&mut invalid, 0, pair(99, 990)) },
        INVALID_LENGTH
    );
    assert_eq!(invalid.length, 5);
    assert_eq!(
        data,
        [
            pair(111, 1110),
            pair(10, 100),
            pair(20, 200),
            pair(30, 300),
            pair(40, 400),
            pair(222, 2220),
        ]
    );
    print(format_args!(
        "RawVec<Pair> PASS: [(10, 100), (20, 200), (30, 300), (40, 400)]; statuses {statuses:?}; invalid length rejected"
    ));
}
