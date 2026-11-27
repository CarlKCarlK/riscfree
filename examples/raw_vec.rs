//! Exercise the linked RawVec insertion routines on the ESP32-C3.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};
use esp_println::println;

#[path = "../research/vec-ffi/linked/header.rs"]
mod header;
#[path = "../src/cases/raw_vec.rs"]
mod raw_vec_case;
use header::{Pair, RawVec};

esp_bootloader_esp_idf::esp_app_desc!();
global_asm!(include_str!("../src/watchdog.S"));

// The shims in `raw_vec_call.S` are assembled into their own object, linked
// next to the routines (see `build.rs`).
unsafe extern "C" {
    fn call_raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
    fn call_raw_vec_pair_insert(vec: *mut RawVec<Pair>, index: u32, value: Pair) -> u32;
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
    idle()
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
