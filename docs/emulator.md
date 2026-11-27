# Running the verified routines under QEMU

Readers without an ESP32-C3 can run the same linked machine code under
[QEMU](https://www.qemu.org). The emulator is an alternative execution and
testing environment. It is not part of the formal proof or its trusted base.
The proofs, their premises, and the hardware harness are unchanged.

```bash
just prove            # Unchanged: proofs, then the linked-byte checks for both environments
just emulate          # Bit-loop popcount under QEMU
just emulate swar     # SWAR popcount under QEMU
just emulate-raw-vec  # RawVec<u32> and RawVec<Pair> insertion, all five outcomes each, under QEMU
```

Expected output:

```text
popcount(0xd3a57c1902efb6489d306a17c2f5804b) = 61
popcount_swar(0xd3a57c1902efb6489d306a17c2f5804b) = 61
emulator/target/riscv32im-unknown-none-elf/release/examples/raw_vec: no compressed instructions (EF_RISCV_RVC clear)
raw_vec_u32_insert: verified all 120 linked bytes (30 instructions)
raw_vec_pair_insert: verified all 132 linked bytes (33 instructions)
RawVec<u32> PASS: [10, 20, 30, 40]; statuses [0, 0, 1, 2]; invalid length rejected
RawVec<Pair> PASS: [(10, 100), (20, 200), (30, 300), (40, 400)]; statuses [0, 0, 1, 2]; invalid length rejected
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
| `raw_vec_u32_insert`, `raw_vec_pair_insert` | `raw_vec.rs`, compiled by rustc for `riscv32im` at `opt-level=1` | the same command |
| RawVec caller | through the shims in `examples/raw_vec_call.S` | calls the routines directly |
| Code addresses | flash, near `0x4200_0000` | RAM, from `0x8000_0000` |
| Return addresses | may have bit 1 set | always word-aligned |

The routines' bytes are identical in both environments, but their addresses
differ. The proofs are stated for any code base address. `just prove` checks
each environment's ELF against the same Lean instruction tables: the 56 bytes
of `popcount128`, the 112 bytes of `popcount128_swar`, the 120 bytes of
`raw_vec_u32_insert`, and the 132 bytes of `raw_vec_pair_insert`. Two files that each match the same table match each
other, so the emulator executes exactly the bytes that Lean verifies.
`just emulate-raw-vec` also runs `check_elf.py`, the quick Python version
of the RawVec checks, before starting QEMU.

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
needs for each routine's final `ret`. The ESP32-C3 demo uses the shims only to
satisfy that premise, so the QEMU harness calls `raw_vec_u32_insert` and
`raw_vec_pair_insert` directly. In the current build, the ten calls return to
`0x80002e90`, `0x80002ea8`, `0x80002ec0`, `0x80002ed8`, and `0x80002f3c`
(u32), and `0x80003050`, `0x8000306c`, `0x80003088`, `0x800030a4`, and
`0x8000310c` (pair).

So under QEMU, all ten calls meet the return-address premise of
`rawVecU32InsertSailCorrect` and `rawVecPairInsertSailCorrect`, whose
guarantees extend through the routine's `ret`. The popcount calls meet the
same premise of their theorems. On the board, the final shim `ret` of two
`RawVec<u32>` calls is trusted to the hardware, and the pair shim has no
proof. The other premises, listed in [rawvec-assurance.md](rawvec-assurance.md),
remain trusted in both environments.

QEMU's CPU runs with the C extension disabled (`-cpu rv32,c=false`), as in the
pinned Sail configuration. A jump to an address with bit 1 set then raises an
instruction-address-misaligned exception, which the runtime reports as a trap,
so a misaligned return would fail the run. That is a dynamic cross-check, not
a proof.

The ESP32-C3 firmware still needs the shims, because it is compiled for
`riscv32imc`. Building the firmware without compressed instructions might
remove them there too. That has not been tried with `esp-hal`.

### One set of tests

The cases live in `src/cases/`. Each harness supplies only what differs:
the routines to call, the output device, and startup. Each case takes a
print function for its result line. The ESP32-C3 build links the shims in
their own object directly before the routines, so changes to the shared
cases do not move the u32 shim's verified `call` offset (0xbc).
`just prove` checks that offset.

## Limitations

- QEMU is not the ESP32-C3. It models a generic RV32 hart and executes each
  instruction by translating it to host code. Its agreement with the Sail
  model is tested, not proved.
- Passing runs show that these ten calls and two popcounts behave as
  expected on QEMU. The guarantee for all inputs still comes only from the
  Lean theorems.
- The memory facts, such as disjoint header and buffer and initialized
  elements, are established by Rust's types and `unsafe` contracts, as on the
  board. The proof does not check them.
- The `EF_RISCV_RVC` check relies on the toolchain setting the flag honestly.
  The dynamic check is QEMU's misaligned-jump exception.
- The QEMU harness is not timing-accurate and models no watchdogs, GPIO, or
  ESP32-C3 peripherals. None of the routines uses them.
