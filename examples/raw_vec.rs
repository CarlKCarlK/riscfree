//! Exercise the linked RawVec and sorted-map routines on the ESP32-C3.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};
use esp_println::println;

#[path = "../research/vec-ffi/linked/header.rs"]
mod header;
use header::{FULL, INDEX_OUT_OF_BOUNDS, INVALID_LENGTH, OK, Pair, RawVec};
#[path = "../src/cases/raw_vec_remove.rs"]
mod raw_vec_remove_case;
#[path = "../src/cases/sorted_map.rs"]
mod sorted_map_case;

esp_bootloader_esp_idf::esp_app_desc!();
global_asm!(include_str!("../src/watchdog.S"));

// The shims in `raw_vec_call.S` are assembled into their own object, linked
// next to the routines (see `build.rs`).
unsafe extern "C" {
    fn call_raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
    fn call_raw_vec_pair_insert(vec: *mut RawVec<Pair>, index: u32, value: Pair) -> u32;
    // Removal shims, in `raw_vec_remove_call.S`.
    fn call_raw_vec_u32_remove(vec: *mut RawVec<u32>, index: u32) -> u32;
    fn call_raw_vec_pair_remove(vec: *mut RawVec<Pair>, index: u32) -> u32;
    // Sorted-map shims, in `sorted_map_call.S`.
    fn call_sorted_map_lower_bound(map: *const RawVec<Pair>, key: u32) -> u32;
    fn call_sorted_map_upper_bound(map: *const RawVec<Pair>, key: u32) -> u32;
    fn call_sorted_map_insert(map: *mut RawVec<Pair>, entry: Pair) -> u32;
    fn call_sorted_map_remove(map: *mut RawVec<Pair>, key: u32) -> u32;
    fn stop_boot_watchdogs();
}

#[esp_hal::main]
fn main() -> ! {
    // SAFETY: This firmware owns the RTC watchdogs and runs without interrupts.
    unsafe { stop_boot_watchdogs() };

    let mut data = [111, 10, 30, 0, 0, 222];
    let mut vec = RawVec {
        data: data[1..5].as_mut_ptr(),
        length: 2,
        capacity: 4,
    };
    // SAFETY: The header and its four initialized backing slots are disjoint.
    // No other accesses to the header or array occur during these calls.
    let statuses = unsafe {
        let inserted = call_raw_vec_u32_insert(&mut vec, 1, 20);
        let end = vec.length;
        let appended = call_raw_vec_u32_insert(&mut vec, end, 40);
        let full = call_raw_vec_u32_insert(&mut vec, 0, 99);
        let invalid_index = call_raw_vec_u32_insert(&mut vec, 5, 99);
        [inserted, appended, full, invalid_index]
    };
    assert_eq!(statuses, [OK, OK, FULL, INDEX_OUT_OF_BOUNDS]);
    assert_eq!(vec.length, 4);
    assert_eq!(vec.capacity, 4);

    let mut invalid = RawVec { length: 5, ..vec };
    // SAFETY: The header is exclusive. Its length exceeds capacity, so this
    // call returns without accessing the backing array.
    assert_eq!(
        unsafe { call_raw_vec_u32_insert(&mut invalid, 0, 99) },
        INVALID_LENGTH
    );
    assert_eq!(invalid.length, 5);
    assert_eq!(data, [111, 10, 20, 30, 40, 222]);
    println!("RawVec<u32> PASS: [10, 20, 30, 40]; statuses {statuses:?}; invalid length rejected");
    check_pairs();
    check_removal();
    // SAFETY: Each shim forwards to its routine, which has the contract the
    // case requires.
    unsafe {
        sorted_map_case::search(
            call_sorted_map_lower_bound,
            call_sorted_map_upper_bound,
            |line| println!("{line}"),
        );
        sorted_map_case::update(call_sorted_map_insert, call_sorted_map_remove, |line| {
            println!("{line}")
        });
    }
    idle()
}

fn check_removal() {
    // SAFETY: Each shim forwards to its routine, which has the contract of
    // `raw_vec_u32_remove` for its element type.
    let statuses = unsafe { raw_vec_remove_case::run(call_raw_vec_u32_remove, |word| word) };
    println!(
        "RawVec<u32> remove PASS: [10, 20, 30, 40] -> [30] -> []; statuses {statuses:?}; invalid length rejected"
    );
    // SAFETY: As above, with eight-byte elements.
    let statuses = unsafe {
        raw_vec_remove_case::run(call_raw_vec_pair_remove, |key| Pair {
            key,
            value: 10 * key,
        })
    };
    println!(
        "RawVec<Pair> remove PASS: [(10, 100), ..., (40, 400)] -> [(30, 300)] -> []; statuses {statuses:?}; invalid length rejected"
    );
}

fn check_pairs() {
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
        let inserted = call_raw_vec_pair_insert(&mut vec, 1, pair(20, 200));
        let end = vec.length;
        let appended = call_raw_vec_pair_insert(&mut vec, end, pair(40, 400));
        let full = call_raw_vec_pair_insert(&mut vec, 0, pair(99, 990));
        let invalid_index = call_raw_vec_pair_insert(&mut vec, 5, pair(99, 990));
        [inserted, appended, full, invalid_index]
    };
    assert_eq!(statuses, [OK, OK, FULL, INDEX_OUT_OF_BOUNDS]);
    assert_eq!(vec.length, 4);
    assert_eq!(vec.capacity, 4);

    let mut invalid = RawVec { length: 5, ..vec };
    // SAFETY: The header is exclusive. Its length exceeds capacity, so this
    // call returns without accessing the backing array.
    assert_eq!(
        unsafe { call_raw_vec_pair_insert(&mut invalid, 0, pair(99, 990)) },
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
    println!(
        "RawVec<Pair> PASS: [(10, 100), (20, 200), (30, 300), (40, 400)]; statuses {statuses:?}; invalid length rejected"
    );
}

#[panic_handler]
fn panic(info: &PanicInfo<'_>) -> ! {
    println!("RawVec FAIL: {info}");
    idle()
}

fn idle() -> ! {
    loop {
        spin_loop();
    }
}
