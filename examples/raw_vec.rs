//! Exercise the linked RawVec insertion routine on the ESP32-C3.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};
use esp_println::println;

#[path = "../research/vec-ffi/linked/header.rs"]
mod header;
use header::{FULL, INDEX_OUT_OF_BOUNDS, INVALID_LENGTH, OK, RawVec};

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
