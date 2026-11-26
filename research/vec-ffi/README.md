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
reads the function directly from the linked ELF and compares it with the
[recorded instruction words](linked/raw_vec_u32.words). To disassemble the
linked routine with the compiler's LLVM tools:

```bash
host=$(rustc -vV | sed -n 's/^host: //p')
"$(rustc --print sysroot)/lib/rustlib/$host/bin/llvm-objdump" \
    --disassemble-symbols=raw_vec_u32_insert \
    target/riscv32imc-unknown-none-elf/release/examples/raw_vec
```

With Rust 1.100.0, the linked function has 30 four-byte instructions and no
calls or stack frame. The earlier research routine has a different loop and
29 static instructions. For the linked routine, append takes 14 instructions.
Inserting before a suffix of `m > 0` elements takes `18 + 6m` instructions,
including the return. Invalid length, invalid index, and full capacity take
5, 6, and 7 instructions respectively.

On an ESP32-C3 revision v0.4, the demo printed:

```text
RawVec<u32> PASS: [10, 20, 30, 40]; statuses [0, 0, 1, 2]; invalid length rejected
```

That run predates the call shim in
[examples/raw_vec_call.S](../../examples/raw_vec_call.S), which gives the
routine the word-aligned return address the proof requires. The demo with the
shim has not yet been run on the board.

The demo asserts the final contents and checks guard words on both sides of the
backing buffer. The linked-byte check and board run are the inputs to a future
Lean correctness proof.
