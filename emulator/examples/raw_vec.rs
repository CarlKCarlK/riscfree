//! Exercise the linked RawVec and sorted-map routines under QEMU.
//!
//! This harness has no compressed instructions, so every call leaves a
//! word-aligned return address and the routines are called without the
//! ESP32-C3 demo's shims.

#![no_std]
#![no_main]

#[path = "../../research/vec-ffi/linked/header.rs"]
mod header;
#[path = "../../src/cases/range_insert.rs"]
mod range_insert_case;
#[path = "../../src/cases/raw_vec.rs"]
mod raw_vec_case;
#[path = "../../src/cases/raw_vec_remove.rs"]
mod raw_vec_remove_case;
#[path = "../src/runtime.rs"]
mod runtime;
#[path = "../../src/cases/sorted_map.rs"]
mod sorted_map_case;
use header::{Pair, RawVec};

unsafe extern "C" {
    fn range_insert_u32(
        map: *mut RawVec<Pair>,
        length: *mut u64,
        start: u32,
        end: u32,
        scratch: *mut u32,
        scratch_capacity: u32,
    ) -> u32;
    fn raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
    fn raw_vec_pair_insert(vec: *mut RawVec<Pair>, index: u32, value: Pair) -> u32;
    fn raw_vec_u32_remove(vec: *mut RawVec<u32>, index: u32) -> u32;
    fn raw_vec_pair_remove(vec: *mut RawVec<Pair>, index: u32) -> u32;
    fn sorted_map_lower_bound(map: *const RawVec<Pair>, key: u32) -> u32;
    fn sorted_map_upper_bound(map: *const RawVec<Pair>, key: u32) -> u32;
    fn sorted_map_insert(map: *mut RawVec<Pair>, entry: Pair) -> u32;
    fn sorted_map_remove(map: *mut RawVec<Pair>, key: u32) -> u32;
}

fn main() {
    // SAFETY: Each case passes its routine's own contract to the routine.
    unsafe {
        raw_vec_case::insert_u32(raw_vec_u32_insert, runtime::println);
        raw_vec_case::insert_pair(raw_vec_pair_insert, runtime::println);
    }
    // SAFETY: Each routine has the contract of `raw_vec_u32_remove` for its
    // element type.
    let statuses = unsafe { raw_vec_remove_case::run(raw_vec_u32_remove, |word| word) };
    runtime::println(format_args!(
        "RawVec<u32> remove PASS: [10, 20, 30, 40] -> [30] -> []; statuses {statuses:?}; invalid length rejected"
    ));
    // SAFETY: As above, with eight-byte elements.
    let statuses = unsafe {
        raw_vec_remove_case::run(raw_vec_pair_remove, |key| Pair {
            key,
            value: 10 * key,
        })
    };
    runtime::println(format_args!(
        "RawVec<Pair> remove PASS: [(10, 100), ..., (40, 400)] -> [(30, 300)] -> []; statuses {statuses:?}; invalid length rejected"
    ));
    // SAFETY: Each routine has the contract the case requires.
    unsafe {
        sorted_map_case::search(
            sorted_map_lower_bound,
            sorted_map_upper_bound,
            runtime::println,
        );
        sorted_map_case::update(sorted_map_insert, sorted_map_remove, runtime::println);
    }
    // SAFETY: The test supplies the linked routine's storage contract.
    unsafe { range_insert_case::run(range_insert_u32) };
    runtime::println(format_args!("Range insertion PASS"));
}
