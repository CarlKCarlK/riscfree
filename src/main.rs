//! Run one 128-bit assembly popcount and report its result.
//! The `swar` feature selects the SWAR routine instead of the bit loop.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};
use esp_println::println;

#[path = "cases/popcount.rs"]
mod popcount_case;

esp_bootloader_esp_idf::esp_app_desc!();

global_asm!(include_str!("popcount.S"));
global_asm!(include_str!("popcount_swar.S"));
global_asm!(include_str!("watchdog.S"));

unsafe extern "C" {
    #[cfg(not(feature = "swar"))]
    fn popcount128(input: *const u32) -> u8;
    #[cfg(feature = "swar")]
    fn popcount128_swar(input: *const u32) -> u8;
    fn stop_boot_watchdogs();
}

#[esp_hal::main]
fn main() -> ! {
    // SAFETY: This firmware owns the RTC watchdogs and runs without interrupts.
    unsafe { stop_boot_watchdogs() };

    #[cfg(not(feature = "swar"))]
    let (name, popcount) = ("popcount", popcount128 as popcount_case::Popcount);
    #[cfg(feature = "swar")]
    let (name, popcount) = ("popcount_swar", popcount128_swar as popcount_case::Popcount);
    // SAFETY: Each assembly routine reads four aligned words through its
    // argument, never writes through it, and follows the C ABI.
    unsafe { popcount_case::run(name, popcount, |line| println!("{line}")) };

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
