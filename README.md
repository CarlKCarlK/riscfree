# riscfree

ESP32-C3 firmware for the LuatOS Core Board. The app in `src/main.rs` blinks
SOS on the onboard D4 LED on GPIO12. This board uses external SPI flash in DIO
mode.

Install the Rust target and flashing tool:

```bash
rustup target add riscv32imc-unknown-none-elf
cargo install espflash --locked
```

In WSL 2, attach the board with `hey attach-esp` if the global recipe is installed.

```bash
just check   # Type-check the firmware
just build   # Build release firmware
just run     # Build, flash, and open the serial monitor
```

Licensed under either the [MIT](LICENSE-MIT) or [Apache 2.0](LICENSE-APACHE)
license, at your option.
