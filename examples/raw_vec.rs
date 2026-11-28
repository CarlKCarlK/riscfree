//! Exercise the linked RawVec and sorted-map routines on the ESP32-C3.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};
use esp_println::println;

#[path = "../research/vec-ffi/linked/header.rs"]
mod header;
#[path = "../src/cases/range_insert.rs"]
mod range_insert_case;
#[path = "../src/cases/raw_vec.rs"]
mod raw_vec_case;
#[path = "../src/cases/raw_vec_remove.rs"]
mod raw_vec_remove_case;
#[path = "../src/cases/sorted_map.rs"]
mod sorted_map_case;
use header::{Pair, RawVec};

esp_bootloader_esp_idf::esp_app_desc!();
global_asm!(include_str!("../src/watchdog.S"));

// The shims in `raw_vec_call.S` are assembled into their own object, linked
// next to the routines (see `build.rs`).
unsafe extern "C" {
    fn call_range_insert_u32(
        map: *mut RawVec<Pair>,
        length: *mut u64,
        start: u32,
        end: u32,
        scratch: *mut u32,
        scratch_capacity: u32,
    ) -> u32;
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

    // SAFETY: Each shim forwards to its routine with a word-aligned return
    // address and restores `ra` and `sp`, so it has the routine's contract.
    unsafe {
        raw_vec_case::insert_u32(call_raw_vec_u32_insert, |line| println!("{line}"));
        raw_vec_case::insert_pair(call_raw_vec_pair_insert, |line| println!("{line}"));
    }
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
    // SAFETY: The shim forwards the test's valid storage to the linked routine.
    unsafe { range_insert_case::run(call_range_insert_u32) };
    println!("Range insertion PASS");
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
