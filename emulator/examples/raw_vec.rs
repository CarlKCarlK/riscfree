//! Exercise the linked RawVec insertion routines under QEMU.
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
#[path = "../src/runtime.rs"]
mod runtime;
use header::{Pair, RawVec};

unsafe extern "C" {
    fn raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
    fn raw_vec_pair_insert(vec: *mut RawVec<Pair>, index: u32, value: Pair) -> u32;
}

fn main() {
    // SAFETY: Each case passes its routine's own contract to the routine.
    unsafe {
        raw_vec_case::insert_u32(raw_vec_u32_insert, runtime::println);
        raw_vec_case::insert_pair(raw_vec_pair_insert, runtime::println);
    }
}
