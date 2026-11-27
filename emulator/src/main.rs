//! Run one 128-bit assembly popcount under QEMU and report its result.
//! The `swar` feature selects the SWAR routine instead of the bit loop.

#![no_std]
#![no_main]

use core::arch::global_asm;

#[path = "../../src/cases/popcount.rs"]
mod popcount_case;
mod runtime;

global_asm!(include_str!("../../src/popcount.S"));
global_asm!(include_str!("../../src/popcount_swar.S"));

unsafe extern "C" {
    #[cfg(not(feature = "swar"))]
    fn popcount128(input: *const u32) -> u8;
    #[cfg(feature = "swar")]
    fn popcount128_swar(input: *const u32) -> u8;
}

fn main() {
    #[cfg(not(feature = "swar"))]
    let (name, popcount) = ("popcount", popcount128 as popcount_case::Popcount);
    #[cfg(feature = "swar")]
    let (name, popcount) = ("popcount_swar", popcount128_swar as popcount_case::Popcount);
    // SAFETY: Each assembly routine reads four aligned words through its
    // argument, never writes through it, and follows the C ABI. This harness
    // has no compressed instructions, so the return address is word-aligned.
    unsafe { popcount_case::run(name, popcount, runtime::println) };
}
