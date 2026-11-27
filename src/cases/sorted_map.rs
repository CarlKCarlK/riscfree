//! The sorted-map cases that the ESP32-C3 firmware and a harness without
//! compressed instructions, such as the QEMU one, share. The firmware passes
//! the calling shims; the QEMU harness can pass the routines themselves.
//!
//! The calls reach every path of the four routines: both searches on an
//! empty map, before, between, at, and after every key; insertion into an
//! empty map, append, insertion in the middle and at the front, replacement in
//! a full map, a full map, and an invalid length; and removal of a missing key
//! (between keys, past the end, and in an empty map), of the last, a middle,
//! and the first entry, and an invalid length. Values are `10 * key` until a
//! replacement, so a routine that moved only keys would fail.

use core::{fmt::Arguments, ptr};

use crate::header::{ABSENT, FULL, INVALID_LENGTH, OK, Pair, REPLACED, RawVec};

/// The C ABI of `sorted_map_lower_bound` and `sorted_map_upper_bound`.
pub type Search = unsafe extern "C" fn(map: *const RawVec<Pair>, key: u32) -> u32;

/// The C ABI of `sorted_map_insert`.
pub type Insert = unsafe extern "C" fn(map: *mut RawVec<Pair>, entry: Pair) -> u32;

/// The C ABI of `sorted_map_remove`.
pub type Remove = unsafe extern "C" fn(map: *mut RawVec<Pair>, key: u32) -> u32;

fn entry(key: u32) -> Pair {
    Pair {
        key,
        value: 10 * key,
    }
}

/// Check both searches on an empty map and on the keys `[10, 20, 30]`, and
/// report success through `print`.
///
/// # Safety
///
/// `lower_bound` and `upper_bound` must have the contracts of
/// `sorted_map_lower_bound` and `sorted_map_upper_bound` in
/// `research/vec-ffi/linked/sorted_map.rs`.
pub unsafe fn search(lower_bound: Search, upper_bound: Search, mut print: impl FnMut(Arguments<'_>)) {
    // An empty map has no backing allocation: neither search reads `data`.
    let empty = RawVec {
        data: ptr::null_mut(),
        length: 0,
        capacity: 0,
    };
    // SAFETY: The header is valid, and its length is 0.
    let empty_bounds = unsafe { [lower_bound(&empty, 7), upper_bound(&empty, 7)] };
    assert_eq!(empty_bounds, [0, 0]);

    let mut data = [entry(111), entry(10), entry(20), entry(30), entry(222)];
    let map = RawVec {
        data: data[1..4].as_mut_ptr(),
        length: 3,
        capacity: 3,
    };
    let keys = [0, 5, 10, 15, 20, 30, 31, u32::MAX];
    let mut lower = [0; 8];
    let mut upper = [0; 8];
    for (position, key) in keys.into_iter().enumerate() {
        // SAFETY: The header is valid, and its three elements are initialized.
        unsafe {
            lower[position] = lower_bound(&map, key);
            upper[position] = upper_bound(&map, key);
        }
    }
    assert_eq!(lower, [0, 0, 0, 1, 1, 2, 3, 3]);
    assert_eq!(upper, [0, 0, 1, 1, 2, 3, 3, 3]);
    assert_eq!(map.length, 3);
    print(format_args!(
        "SortedMap search PASS: keys [10, 20, 30]; lower bounds {lower:?}; upper bounds {upper:?}; empty map {empty_bounds:?}"
    ));
}

/// Build the map `[10, 20, 30, 40]` with `insert`, then empty it with
/// `remove`, asserting every status, length, and the final memory, including
/// the guard elements on both sides of the backing slots, and report success
/// through `print`.
///
/// # Safety
///
/// `insert` and `remove` must have the contracts of `sorted_map_insert` and
/// `sorted_map_remove` in `research/vec-ffi/linked/sorted_map.rs`.
pub unsafe fn update(insert: Insert, remove: Remove, mut print: impl FnMut(Arguments<'_>)) {
    let mut data = [entry(111), entry(0), entry(0), entry(0), entry(0), entry(222)];
    let mut map = RawVec {
        data: data[1..5].as_mut_ptr(),
        length: 0,
        capacity: 4,
    };
    let mut lengths = [0; 6];
    // SAFETY: The header and its four backing slots are disjoint. No other
    // accesses to the header or array occur during these calls.
    let inserted = unsafe {
        let into_empty = insert(&mut map, entry(20));
        lengths[0] = map.length;
        let appended = insert(&mut map, entry(40));
        lengths[1] = map.length;
        let middle = insert(&mut map, entry(30));
        lengths[2] = map.length;
        let front = insert(&mut map, entry(10));
        lengths[3] = map.length;
        // The map is full, but replacing an existing key needs no spare slot.
        let replaced = insert(&mut map, Pair { key: 30, value: 333 });
        lengths[4] = map.length;
        let full = insert(&mut map, entry(50));
        lengths[5] = map.length;
        [into_empty, appended, middle, front, replaced, full]
    };
    assert_eq!(inserted, [OK, OK, OK, OK, REPLACED, FULL]);
    assert_eq!(lengths, [1, 2, 3, 4, 4, 4]);
    let replaced = Pair { key: 30, value: 333 };
    assert_eq!(
        data,
        [entry(111), entry(10), entry(20), replaced, entry(40), entry(222)]
    );

    let mut invalid = RawVec { length: 5, ..map };
    // SAFETY: The header is exclusive. Its length exceeds capacity, so these
    // calls return without accessing the backing array.
    let rejected = unsafe { [insert(&mut invalid, entry(5)), remove(&mut invalid, 10)] };
    assert_eq!(rejected, [INVALID_LENGTH, INVALID_LENGTH]);
    assert_eq!(invalid.length, 5);

    // SAFETY: As above.
    let removed = unsafe {
        let between = remove(&mut map, 25);
        lengths[0] = map.length;
        let middle = remove(&mut map, 20);
        lengths[1] = map.length;
        let last = remove(&mut map, 40);
        lengths[2] = map.length;
        let past_end = remove(&mut map, 99);
        lengths[3] = map.length;
        let first = remove(&mut map, 10);
        lengths[4] = map.length;
        let only = remove(&mut map, 30);
        lengths[5] = map.length;
        let empty = remove(&mut map, 30);
        [between, middle, last, past_end, first, only, empty]
    };
    assert_eq!(removed, [ABSENT, OK, OK, ABSENT, OK, OK, ABSENT]);
    assert_eq!(lengths, [4, 3, 2, 2, 1, 0]);
    assert_eq!(map.length, 0);
    assert_eq!(map.capacity, 4);
    // Removal leaves each vacated slot as it was: removing 20 shifted the
    // replaced 30 and 40 down, and removing 10 shifted the replaced 30 again.
    assert_eq!(
        data,
        [entry(111), replaced, replaced, entry(40), entry(40), entry(222)]
    );
    print(format_args!(
        "SortedMap update PASS: [] -> [10, 20, 30, 40] -> []; insert statuses {inserted:?}; remove statuses {removed:?}; invalid length rejected"
    ));
}
