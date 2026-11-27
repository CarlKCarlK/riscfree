# Bounded-vector machine-code experiment

This standalone `no_std` crate compares `heapless::Vec` with a C-compatible
runtime-capacity vector header for RV32 machine-code verification. It is
deliberately outside the riscfree firmware crate and has its own Cargo
workspace and lockfile.

Install the target and disassembly tools once:

```bash
rustup target add riscv32im-unknown-none-elf
rustup component add llvm-tools-preview
```

Run the host tests and regenerate all checked-in assembly, object, ELF
attribute, and disassembly files:

```bash
cargo test --target x86_64-unknown-linux-gnu
clang --target=riscv32-unknown-none-elf -march=rv32im -mabi=ilp32 \
    -ffreestanding -fsyntax-only tests/ffi_header.c
./scripts/build-rv32.sh
```

The explicit host target is necessary because riscfree configures an embedded
target by default. See [REPORT.md](REPORT.md) for the findings and recommendation.

## Linked ESP32-C3 demo

From the repository root, run:

```bash
just build-raw-vec
just run-raw-vec
```

The [generic Rust implementation](linked/raw_vec.rs) is compiled at
`opt-level=1` for RV32IM and linked into the ESP32-C3 firmware. The byte check
reads each function directly from the linked ELF and compares it with its
recorded instruction words ([u32](linked/raw_vec_u32.words),
[Pair](linked/raw_vec_pair.words), and the two removal routines below). To disassemble the linked routines with the
compiler's LLVM tools:

```bash
host=$(rustc -vV | sed -n 's/^host: //p')
"$(rustc --print sysroot)/lib/rustlib/$host/bin/llvm-objdump" \
    --disassemble-symbols=raw_vec_u32_insert,raw_vec_pair_insert,raw_vec_u32_remove,raw_vec_pair_remove \
    target/riscv32imc-unknown-none-elf/release/examples/raw_vec
```

With Rust 1.100.0, the linked function has 30 four-byte instructions and no
calls or stack frame. The earlier research routine has a different loop and
29 static instructions. For the linked routine, append takes 14 instructions.
Inserting before a suffix of `m > 0` elements takes `18 + 6m` instructions,
including the return. Invalid length, invalid index, and full capacity take
5, 6, and 7 instructions respectively.

The `RawVec<Pair>` instance, `raw_vec_pair_insert`, has 33 instructions. As
predicted, it shifts by 3 instead of 2 and moves each pair with two loads and
two stores. Register allocation also differs: the length is in `a4`, the loop
counter in `a6`, and the moved pair passes through `a7` and `t0`. Append takes
15 instructions and insertion before `m > 0` pairs takes `19 + 8m`.

Removal ([raw_vec_remove.rs](linked/raw_vec_remove.rs)) is one generic
`RawVec<T>::remove` with a forward copy loop and the same two instances. It
is compiled the same way into a separate object, linked after the insertion
routines so that it does not move them. `raw_vec_u32_remove` has 23
instructions and `raw_vec_pair_remove` 25. Both keep the length in `a3`, walk a
pointer in `a1` up to an end pointer in `a3`, and differ only in the shift
(2 or 3), the pointer step (4 or 8), and the extra load and store for the pair's
second word. Removing the last element takes 9 instructions, and removing
before `m > 0` later elements takes `15 + 4m` (`u32`) or `15 + 6m` (`Pair`).
Invalid length and invalid index take 5 and 6. The words are recorded in
[raw_vec_u32_remove.words](linked/raw_vec_u32_remove.words) and
[raw_vec_pair_remove.words](linked/raw_vec_pair_remove.words).

The removal test case, [src/cases/raw_vec_remove.rs](../../src/cases/raw_vec_remove.rs),
is written once for both element types and takes the routine as a function
pointer, so a harness without compressed instructions can pass the routines
themselves.

On an ESP32-C3 revision v0.4, the demo printed:

```text
RawVec<u32> PASS: [10, 20, 30, 40]; statuses [0, 0, 1, 2]; invalid length rejected
```

On November 26, 2026, the build with both removal routines printed, on the
same board:

```text
RawVec<u32> PASS: [10, 20, 30, 40]; statuses [0, 0, 1, 2]; invalid length rejected
RawVec<Pair> PASS: [(10, 100), (20, 200), (30, 300), (40, 400)]; statuses [0, 0, 1, 2]; invalid length rejected
RawVec<u32> remove PASS: [10, 20, 30, 40] -> [30] -> []; statuses [0, 0, 0, 2, 0, 2]; invalid length rejected
RawVec<Pair> remove PASS: [(10, 100), ..., (40, 400)] -> [(30, 300)] -> []; statuses [0, 0, 0, 2, 0, 2]; invalid length rejected
```

The demo now calls the routine through the shim in
[examples/raw_vec_call.S](../../examples/raw_vec_call.S), which gives it the
word-aligned return address the proof requires. The shim is itself proved in
`proof/RawVec/Shim.lean`. On November 26, 2026, the shim
build passed the same board test with identical output.

The demo asserts the final contents and checks guard words on both sides of the
backing buffer. The linked-byte check and board run are the inputs to a future
Lean correctness proof.
