//! riscfree: Rust as an assembly launcher.

#![no_std]
#![no_main]

use core::{arch::global_asm, hint::spin_loop, panic::PanicInfo};

esp_bootloader_esp_idf::esp_app_desc!();

global_asm!(include_str!("blink.S"));

unsafe extern "C" {
    fn riscfree_start() -> !;
}

#[esp_hal::main]
fn main() -> ! {
    // SAFETY: The assembly entry takes no arguments, configures GPIO12 itself,
    // and loops forever. This board leaves GPIO12 free by using DIO flash.
    unsafe { riscfree_start() }
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {
        spin_loop();
    }
}
