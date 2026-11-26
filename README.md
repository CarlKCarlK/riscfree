# device-envoy-esp-blinky

[![GitHub](https://img.shields.io/badge/github-device--envoy--esp--blinky-8da0cb?style=flat&labelColor=555555&logo=github)](https://github.com/CarlKCarlK/device-envoy-esp-blinky)
[![crates.io](https://img.shields.io/crates/v/device-envoy-esp?style=flat&color=fc8d62&logo=rust)](https://crates.io/crates/device-envoy-esp)

Minimal blinky project using [`device-envoy-esp`](https://crates.io/crates/device-envoy-esp) and the onboard D4 LED on the LuatOS ESP32-C3 Core Board.

[Device Envoy](https://crates.io/crates/device-envoy-esp) makes Rust applications for ESP32 easier. It helps your program draw on touchscreens, animate LED strips, join WiFi, and more, without writing interrupt handlers, DMA setup, or background tasks yourself.

## What This Repo Contains

- `src/main.rs` blinks the active-high onboard D4 LED on `GPIO12`.
- `examples/<chip>/<board>/blinky.rs` contains chip- and board-specific variants.

What if your board is different from the default setup?

Find a matching example under `examples/<chip>/<board>/blinky.rs` and follow its wiring instructions.

**Feedback**: If you try this crate, I’d love to hear how it goes, whether it works well, fails to build, needs clearer docs, or does not fit your hardware. Please send feedback to carlk AT msn.com.
## Prerequisites

Before **Quick Start**, install the toolchain in [Toolchain](#toolchain), then return here.

## Quick Start

The [LuatOS ESP32-C3 Core Board](https://wiki.luatos.org/chips/esp32c3/board.html) uses external flash in DIO mode so `GPIO12` is available for the onboard LED.

Next, run:

```bash
cargo xtask run
```

This project defaults to ESP32-C3. To override it, pass `--chip` with one of `c2`, `c3`, `c5`, `c6`, `c61`, `h2`, `esp32`, `s2`, or `s3`.

*This `xtask run` always adds the `--release` option*.

## Setting the Default Chip

The default in `xtask/src/main.rs` is:

```rust
const DEFAULT_CHIP: Chip = Chip::C3;
```

## Main Commands

```bash
cargo xtask run
cargo xtask check
cargo xtask build
```

## Running Examples Directly

```bash
cargo xtask run --example blinky_c6_devkitc1_n8
cargo xtask check --example blinky_c6_devkitc1_n8
cargo xtask build --example blinky_c6_devkitc1_n8
```

Where examples are defined in `examples` and (if subfolders are used) in `Cargo.toml`.

## Toolchain

Install Rust from [rustup.rs](https://rustup.rs) if you haven't already.

Install Rust targets:

```bash
rustup target add riscv32imac-unknown-none-elf
rustup target add riscv32imc-unknown-none-elf
```

Xtensa chips (`esp32`, `s2`, `s3`) need ESP toolchain setup:

```bash
cargo install espup
espup install
```

Enable espup environment before building xtensa chips:

```bash
# Linux/macOS/WSL
source "$HOME/export-esp.sh"
# To make this permanent, add this line to your
# shell profile (e.g. ~/.bashrc or ~/.zshrc):
# source "$HOME/export-esp.sh"
```

```powershell
# Windows PowerShell
& "$env:USERPROFILE\export-esp.ps1"
# To make this permanent, run:
# if (!(Test-Path $PROFILE)) { New-Item -Type File -Path $PROFILE -Force }; Add-Content $PROFILE '& "$env:USERPROFILE\export-esp.ps1"'
```

Install flashing tool:

```bash
cargo install espflash
```

## License

Licensed under either:

- MIT license (see LICENSE-MIT)
- Apache License, Version 2.0 (see LICENSE-APACHE)

at your option.
