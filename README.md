# riscfree

ESP32-C3 firmware for the LuatOS Core Board. Rust places a fixed `u128` on the
stack in data RAM, passes its address to `src/popcount.S`, and reports the
returned `u8` over serial:

```text
popcount(0xd3a57c1902efb6489d306a17c2f5804b) = 61
```

The assembly routine reads four aligned 32-bit words and counts their set bits.
It leaves memory and callee-saved registers unchanged. The Rust harness supplies
the input, calls the routine, prints the result, and asserts that it equals 61.
After the assertion passes, Rust idles indefinitely.

## Lean proof

Run `just prove` with Elan and GNU binutils installed. It builds the firmware,
checks `popcount128SailCorrect`, prints its axiom dependencies, and compares all
56 linked `popcount128` bytes with the words decoded by Sail. Lake uses the
pinned Pico FV and Sail dependencies in `lake-manifest.json` and Lean 4.28.0-rc1.

The theorem covers every 128-bit input. The routine returns after 664 Sail
instructions with the population count in `a0`. It preserves byte memory and
all registers outside `a0` and `t0`–`t4`, with the expected update to the PC and
Sail's internal `nextPC`. The sections in `proof/Popcount.lean` follow the proof
from the mathematical specification and linked instruction words through the
Sail steps, loop invariants, and ELF byte check. The reusable RV32 lemmas live
under `proof/Riscfree/RV32/`.

The theorem's `entry` premise and the `Platform` section specify the starting
state and execution conditions. The code mapping supplies the linked halfwords to Sail's
instruction fetch. The four data words occupy naturally aligned, readable RAM
and agree with the little-endian input bytes. The hart runs in machine mode
with `MPRV` clear, the host interface and landing-pad checks disabled, and a
four-byte-aligned return address. The model steps each instruction and commits
the PC. Interrupt delivery and hardware counters are outside that model. The
proof trusts the Rust harness and ESP32-C3 hardware.

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
