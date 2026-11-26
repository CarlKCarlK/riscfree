//! Run one 128-bit assembly popcount and report its result.
//! The `swar` feature selects the SWAR routine instead of the bit loop.

#![no_std]
#![no_main]

use core::{
    arch::global_asm,
    hint::{black_box, spin_loop},
    panic::PanicInfo,
};
use esp_println::println;

esp_bootloader_esp_idf::esp_app_desc!();

global_asm!(include_str!("popcount.S"));
global_asm!(include_str!("popcount_swar.S"));
global_asm!(include_str!("watchdog.S"));

const INPUT: u128 = 0xD3A5_7C19_02EF_B648_9D30_6A17_C2F5_804B;
const _: () = assert!(align_of::<u128>() >= align_of::<u32>());

unsafe extern "C" {
    #[cfg(not(feature = "swar"))]
    fn popcount128(input: *const u32) -> u8;
    #[cfg(feature = "swar")]
    fn popcount128_swar(input: *const u32) -> u8;
    fn stop_boot_watchdogs();
}

#[esp_hal::main]
fn main() -> ! {
    const EXPECTED_COUNT: u8 = 61;

    // SAFETY: This firmware owns the RTC watchdogs and runs without interrupts.
    unsafe { stop_boot_watchdogs() };

    // Materialize the input on the stack in data RAM for the assembly call.
    let input = black_box(INPUT);
    let input_pointer = (&raw const input).cast();
    // SAFETY: The local provides 16 readable bytes at a 4-byte-aligned address.
    // The assembly reads four words and never writes through the pointer.
    #[cfg(not(feature = "swar"))]
    let (name, count) = ("popcount", unsafe { popcount128(input_pointer) });
    // SAFETY: The SWAR routine has the same contract as the bit loop.
    #[cfg(feature = "swar")]
    let (name, count) = ("popcount_swar", unsafe { popcount128_swar(input_pointer) });
    println!("{name}(0x{INPUT:032x}) = {count}");
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
