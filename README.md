# riscfree

ESP32-C3 firmware for the LuatOS Core Board. Rust passes a fixed `u128` to
`src/popcount.S` by address, then reports the returned `u8` over serial:

```text
popcount(0xd3a57c1902efb6489d306a17c2f5804b) = 61
```

The assembly routine reads four aligned 32-bit words and counts their set bits.
It leaves memory and callee-saved registers unchanged. The Rust harness supplies
the input, calls the routine, prints the result, and asserts that it equals 61.
The machine-code proof would take that harness as trusted and cover the assembly
routine for all inputs. After the assertion passes, the firmware runs
`src/blink.S` to blink the onboard D4 LED on GPIO12. This board uses external
SPI flash in DIO mode.

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
