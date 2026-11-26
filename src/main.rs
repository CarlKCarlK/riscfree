//! riscfree Phase 1: Execute hand-written RISC-V assembly.

#![no_std]
#![no_main]

use core::{arch::global_asm, convert::Infallible, future::pending};
use embassy_executor::Spawner;
use esp_backtrace as _;
use log::info;

use device_envoy_esp::{Result, init_and_start};

esp_bootloader_esp_idf::esp_app_desc!();

global_asm!(
    ".section .text.riscfree_add, \"ax\"",
    ".balign 4",
    ".global riscfree_add",
    ".type riscfree_add, @function",
    ".option push",
    ".option norvc",
    ".option norelax",
    "riscfree_add:",
    "    add a0, a0, a1",
    "    jalr zero, 0(ra)",
    ".size riscfree_add, . - riscfree_add",
    ".option pop",
);

unsafe extern "C" {
    fn riscfree_add(a: u32, b: u32) -> u32;
}

#[esp_rtos::main]
async fn main(spawner: Spawner) -> ! {
    let err = inner_main(spawner).await.unwrap_err();
    panic!("{err:?}");
}

async fn inner_main(spawner: Spawner) -> Result<Infallible> {
    init_and_start!(_p);

    esp_println::logger::init_logger(log::LevelFilter::Info);
    info!("riscfree Phase 1 starting");

    let test_cases: [(u32, u32); 5] = [
        (20, 22),
        (0, 0),
        (u32::MAX, 0),
        (u32::MAX, 1),
        (u32::MAX, u32::MAX),
    ];

    for (a, b) in test_cases {
        let actual = unsafe { riscfree_add(a, b) };
        let expected = a.wrapping_add(b);

        info!("{a} + {b} = {actual}");
        assert_eq!(actual, expected);
    }

    info!("riscfree: All tests passed");

    pending().await
}
