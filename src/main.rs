//! riscfree: Blink GPIO12 using RISC-V assembly.

#![no_std]
#![no_main]

use core::{arch::global_asm, convert::Infallible};
use embassy_executor::Spawner;
use esp_backtrace as _;
use esp_hal::gpio::{Level, Output, OutputConfig};
use log::info;

use device_envoy_esp::{Result, init_and_start};

esp_bootloader_esp_idf::esp_app_desc!();

global_asm!(
    ".section .text.riscfree_blink, \"ax\"",
    ".balign 4",
    ".global riscfree_blink",
    ".type riscfree_blink, @function",
    ".option push",
    ".option norvc",
    ".option norelax",

    "riscfree_blink:",
    "    li t0, 0x60004000", // GPIO register base
    "    li t1, 4096",       // GPIO12 bit mask
    "    li t2, 20000000",   // Delay iterations

    "blink:",
    "    sw t1, 8(t0)",      // LED on
    "    mv t3, t2",
    "delay_on:",
    "    addi t3, t3, -1",
    "    bne t3, zero, delay_on",

    "    sw t1, 12(t0)",     // LED off
    "    mv t3, t2",
    "delay_off:",
    "    addi t3, t3, -1",
    "    bne t3, zero, delay_off",

    "    j blink",

    ".size riscfree_blink, . - riscfree_blink",
    ".option pop",
);

unsafe extern "C" {
    fn riscfree_blink() -> !;
}

#[esp_rtos::main]
async fn main(spawner: Spawner) -> ! {
    let err = inner_main(spawner).await.unwrap_err();
    panic!("{err:?}");
}

async fn inner_main(spawner: Spawner) -> Result<Infallible> {
    init_and_start!(p);

    esp_println::logger::init_logger(log::LevelFilter::Info);

    let _led = Output::new(
        p.GPIO12,
        Level::Low,
        OutputConfig::default(),
    );

    info!("Transferring control to riscfree assembly");

    unsafe { riscfree_blink() }
}