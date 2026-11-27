//! Exercise the linked RawVec insertion routine on the ESP32-C3.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};
use esp_println::println;

#[path = "../research/vec-ffi/linked/header.rs"]
mod header;
#[path = "../src/cases/raw_vec.rs"]
mod raw_vec_case;
use header::RawVec;

esp_bootloader_esp_idf::esp_app_desc!();
global_asm!(include_str!("../src/watchdog.S"));
global_asm!(include_str!("raw_vec_call.S"));

unsafe extern "C" {
    fn call_raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
    fn stop_boot_watchdogs();
}

#[esp_hal::main]
fn main() -> ! {
    // SAFETY: This firmware owns the RTC watchdogs and runs without interrupts.
    unsafe { stop_boot_watchdogs() };

    // SAFETY: The shim forwards to the routine with a word-aligned return
    // address and restores `ra` and `sp`, so it has the routine's contract.
    let statuses = unsafe { raw_vec_case::run(call_raw_vec_u32_insert) };
    println!("RawVec<u32> PASS: [10, 20, 30, 40]; statuses {statuses:?}; invalid length rejected");
    idle()
}

#[panic_handler]
fn panic(info: &PanicInfo<'_>) -> ! {
    println!("RawVec<u32> FAIL: {info}");
    idle()
}

fn idle() -> ! {
    loop {
        spin_loop();
    }
}
