# Running the verified routines under QEMU

Readers without an ESP32-C3 can run the same linked machine code under
[QEMU](https://www.qemu.org). The emulator is an alternative execution and
testing environment. It is not part of the formal proof or its trusted base.
The proofs, their premises, and the hardware harness are unchanged.

```bash
just prove            # Unchanged: proofs, then the linked-byte checks for both environments
just emulate          # Bit-loop popcount under QEMU
just emulate swar     # SWAR popcount under QEMU
just emulate-raw-vec  # RawVec<u32> insertion, all five outcomes, under QEMU
```

Expected output:

```text
popcount(0xd3a57c1902efb6489d306a17c2f5804b) = 61
popcount_swar(0xd3a57c1902efb6489d306a17c2f5804b) = 61
emulator/target/riscv32im-unknown-none-elf/release/examples/raw_vec: no compressed instructions (EF_RISCV_RVC clear)
raw_vec_u32_insert: verified all 120 linked bytes (30 instructions)
RawVec<u32> PASS: [10, 20, 30, 40]; statuses [0, 0, 1, 2]; invalid length rejected
```

Each run exits with status 0 on success, 1 on a failed assertion, and 2 on an
unexpected trap. A `timeout` of 60 seconds stops a run that hangs.

## Installation

The emulator needs only stable Rust, the prebuilt `riscv32im` target, and
QEMU's RISC-V system emulator. It needs no new Rust crates, no C toolchain,
and no RISC-V Linux sysroot.

```bash
rustup target add riscv32im-unknown-none-elf
sudo apt install qemu-system-misc      # Debian, Ubuntu, and WSL 2
# sudo dnf install qemu-system-riscv   # Fedora
# brew install qemu                    # macOS
```

The harness has been run with QEMU 6.2 (Ubuntu 22.04 under WSL 2). `just
prove` builds the QEMU harness but does not run it, so it does not need QEMU.

## Layout

- `emulator/`: a separate Cargo package with no dependencies. Its
  `.cargo/config.toml` selects `riscv32im-unknown-none-elf` and makes QEMU the
  `cargo run` runner.
- `emulator/src/runtime.rs`: the whole platform layer, in about 100 lines.
  It sets the stack and trap vector, writes lines to the board's 16550 UART,
  reports traps, and exits through QEMU's SiFive test device.
- `emulator/src/main.rs` and `emulator/examples/raw_vec.rs`: the popcount and
  RawVec harnesses, mirroring `src/main.rs` and `examples/raw_vec.rs`.
- `src/cases/popcount.rs` and `src/cases/raw_vec.rs`: the test cases. Both
  the ESP32-C3 firmware and the QEMU harness include these files, so the
  inputs, the calls, and the assertions are written once.
- `research/vec-ffi/linked/compile.rs`: the RawVec compilation step, shared
  by both build scripts.

## Relationship between the two environments' machine code

| | ESP32-C3 firmware | QEMU harness |
| --- | --- | --- |
| Rust target | `riscv32imc-unknown-none-elf` | `riscv32im-unknown-none-elf` |
| `popcount128`, `popcount128_swar` | assembled from `src/popcount*.S` | the same sources |
| `raw_vec_u32_insert` | `raw_vec.rs`, compiled by rustc for `riscv32im` at `opt-level=1` | the same command |
| RawVec caller | through the shim `call_raw_vec_u32_insert` | calls the routine directly |
| Code addresses | flash, near `0x4200_0000` | RAM, from `0x8000_0000` |
| Return addresses | may have bit 1 set | always word-aligned |

The routines' bytes are identical in both environments, but their addresses
differ. The proofs are stated for any code base address. `just prove` checks
each environment's ELF against the same Lean instruction tables: the 56 bytes
of `popcount128`, the 112 bytes of `popcount128_swar`, and the 120 bytes of
`raw_vec_u32_insert`. Two files that each match the same table match each
other, so the emulator executes exactly the bytes that Lean verifies.
`just emulate-raw-vec` also runs `check_elf.py`, the quick Python version
of the RawVec check, before starting QEMU.

`just prove` also runs `Riscfree.verifyUncompressed` on each QEMU ELF. It
requires `EF_RISCV_RVC` to be clear in the ELF header. The linker sets that
flag when any input object enables compressed instructions.

## Decisions

### Bare-metal QEMU `virt`

Options considered:

- **QEMU system mode, `virt` board (chosen).** The ELF is loaded with
  `-bios none`, so the hart starts in machine mode at `0x8000_0000` with no
  firmware, no PMP entries, and interrupts disabled. That is the state the
  theorems assume. The board's UART and test device are the only peripherals
  used. QEMU is mature, maintained, and packaged for every major Linux
  distribution, macOS, and Windows. The same command works under WSL 2.
- **QEMU user mode (`qemu-riscv32`).** It runs a Linux RV32 executable in
  user mode and translates its system calls. It works only on Linux hosts, and
  the routine would run in user mode rather than the machine mode the proofs
  assume. A no-`std` harness could make raw Linux system calls. It would
  avoid about 15 lines of UART and exit code but nothing else.
- **A Rust harness for RV32 Linux.** The `riscv32gc-unknown-linux-gnu` and
  `riscv32gc-unknown-linux-musl` targets are Tier 3. `rustup` offers no
  prebuilt `std` for them, so a reader would need nightly Rust, `-Zbuild-std`,
  and an RV32 Linux C toolchain and sysroot, which distributions rarely
  package. These targets also enable compressed instructions. This route
  costs much more setup than it saves.
- **Other emulators.** Spike, the RISC-V reference ISA simulator, is not
  packaged by Ubuntu 22.04 and must be built from source. Sail's own C
  emulator runs the formal model itself. It would need a separate download
  or build, and its configuration would differ from the pinned Lean
  translation. Either could be a later cross-check. Neither is simpler than
  QEMU.

### No compressed instructions, so no shim

The QEMU harness is compiled entirely for `riscv32im`. Every instruction is a
32-bit word in a word-aligned section, so every `jal` or `jalr` leaves a
word-aligned return address. That is exactly the premise the pinned Sail model
needs for each routine's final `ret`. The ESP32-C3 demo uses the shim only to
satisfy that premise, so the QEMU harness calls `raw_vec_u32_insert` directly.
In the current build, the five calls return to `0x8000252c`, `0x80002544`,
`0x8000255c`, `0x80002574`, and `0x800025d8`.

So under QEMU, all five calls meet the return-address premise of
`rawVecU32InsertSailCorrect`, whose guarantee extends through the routine's
`ret`. The popcount calls meet the same premise of their theorems. On the
board, the final shim `ret` of three calls is trusted to the hardware. The
other premises, listed in [rawvec-assurance.md](rawvec-assurance.md), remain
trusted in both environments.

QEMU's CPU runs with the C extension disabled (`-cpu rv32,c=false`), as in the
pinned Sail configuration. A jump to an address with bit 1 set then raises an
instruction-address-misaligned exception, which the runtime reports as a trap,
so a misaligned return would fail the run. That is a dynamic cross-check, not
a proof.

The ESP32-C3 firmware still needs the shim, because it is compiled for
`riscv32imc`. Building the firmware without compressed instructions might
remove the shim there too. That has not been tried with `esp-hal`.

### One set of tests

The cases live in `src/cases/`. Each harness supplies only what differs:
the routine to call, the output device, and startup. The popcount case
takes a print function. The RawVec case returns its statuses and each
harness prints the result line itself. Moving the print into the shared
case changed the ESP32-C3 demo's layout by 28 bytes. The shim's `call`
immediates and `routineOffset` in `proof/RawVec/Shim.lean` would then have
needed to change. With the line in each harness, the shim, the routine, and
the five return addresses stay at their recorded addresses.

## Limitations

- QEMU is not the ESP32-C3. It models a generic RV32 hart and executes each
  instruction by translating it to host code. Its agreement with the Sail
  model is tested, not proved.
- Passing runs show that these five calls and two popcounts behave as
  expected on QEMU. The guarantee for all inputs still comes only from the
  Lean theorems.
- The memory facts, such as disjoint header and buffer and initialized
  elements, are established by Rust's types and `unsafe` contracts, as on the
  board. The proof does not check them.
- The `EF_RISCV_RVC` check relies on the toolchain setting the flag honestly.
  The dynamic check is QEMU's misaligned-jump exception.
- The QEMU harness is not timing-accurate and models no watchdogs, GPIO, or
  ESP32-C3 peripherals. None of the routines uses them.
