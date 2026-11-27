//! Exercise the linked RawVec insertion routine under QEMU.
//!
//! This harness has no compressed instructions, so every call leaves a
//! word-aligned return address and the routine is called without the
//! ESP32-C3 demo's shim.

#![no_std]
#![no_main]

#[path = "../../research/vec-ffi/linked/header.rs"]
mod header;
#[path = "../../src/cases/raw_vec.rs"]
mod raw_vec_case;
#[path = "../src/runtime.rs"]
mod runtime;
use header::RawVec;

unsafe extern "C" {
    fn raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
}

fn main() {
    // SAFETY: The case passes the contract of `raw_vec_u32_insert` to the
    // routine itself.
    let statuses = unsafe { raw_vec_case::run(raw_vec_u32_insert) };
    runtime::println(format_args!(
        "RawVec<u32> PASS: [10, 20, 30, 40]; statuses {statuses:?}; invalid length rejected"
    ));
}
