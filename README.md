# riscfree

ESP32-C3 firmware for the LuatOS Core Board. Rust passes a fixed `u128` to
`src/popcount.S` by address, then reports the returned `u8` over serial:

```text
popcount(0xd3a57c1902efb6489d306a17c2f5804b) = 61
```

The assembly routine reads four aligned 32-bit words and counts their set bits.
It leaves memory and callee-saved registers unchanged. The Rust harness supplies
the input, calls the routine, prints the result, and asserts that it equals 61.
After the assertion passes, Rust idles indefinitely.

## Lean proof

Run `just prove` with Lean (via Elan) and GNU binutils installed. It builds the
firmware, checks the Lean proof, and compares the 56 bytes of the linked
`popcount128` symbol with the proof's instruction words.

The theorem covers every 128-bit input. Starting with four aligned, readable
32-bit words and an aligned return address, the modeled routine returns after
664 instructions with the population count in `a0`. It preserves memory and
all registers except `a0` and `t0`–`t4`.

The trusted base includes the Rust harness and the hand-written RV32I subset
in `proof/Popcount.lean`. The model assumes ordinary stable memory, executable
code, and uninterrupted execution. Its memory model returns readable words
and does not represent byte permissions, alignment faults, or MMIO. This is
not a general proof of hardware memory safety. Correspondence with official
Sail semantics and the hardware are outside the proof.

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
