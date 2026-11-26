//! Run the 128-bit assembly popcount and report its result.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};
use esp_println::println;

esp_bootloader_esp_idf::esp_app_desc!();

global_asm!(include_str!("popcount.S"));
global_asm!(include_str!("watchdog.S"));

static INPUT: u128 = 0xD3A5_7C19_02EF_B648_9D30_6A17_C2F5_804B;
const _: () = assert!(align_of::<u128>() >= align_of::<u32>());

unsafe extern "C" {
    fn popcount128(input: *const u32) -> u8;
    fn stop_boot_watchdogs();
}

#[esp_hal::main]
fn main() -> ! {
    const EXPECTED_COUNT: u8 = 61;

    // SAFETY: This firmware owns the RTC watchdogs and runs without interrupts.
    unsafe { stop_boot_watchdogs() };

    // SAFETY: INPUT provides 16 readable bytes at a 4-byte-aligned address.
    // The assembly reads four words and never writes through the pointer.
    let count = unsafe { popcount128((&raw const INPUT).cast()) };
    println!("popcount(0x{INPUT:032x}) = {count}");
    assert_eq!(count, EXPECTED_COUNT);

    idle()
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    idle()
}

fn idle() -> ! {
    loop {
        // Keep the CPU in a busy loop forever. This hint does not put it to sleep.
        spin_loop();
    }
}
