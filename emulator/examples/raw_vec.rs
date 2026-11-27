//! Exercise the linked RawVec insertion and removal routines under QEMU.
//!
//! This harness has no compressed instructions, so every call leaves a
//! word-aligned return address and the routines are called without the
//! ESP32-C3 demo's shims.

#![no_std]
#![no_main]

#[path = "../../research/vec-ffi/linked/header.rs"]
mod header;
#[path = "../../src/cases/raw_vec.rs"]
mod raw_vec_case;
#[path = "../../src/cases/raw_vec_remove.rs"]
mod raw_vec_remove_case;
#[path = "../src/runtime.rs"]
mod runtime;
use header::{Pair, RawVec};

unsafe extern "C" {
    fn raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
    fn raw_vec_pair_insert(vec: *mut RawVec<Pair>, index: u32, value: Pair) -> u32;
    fn raw_vec_u32_remove(vec: *mut RawVec<u32>, index: u32) -> u32;
    fn raw_vec_pair_remove(vec: *mut RawVec<Pair>, index: u32) -> u32;
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
}
