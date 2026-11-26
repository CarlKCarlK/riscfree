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
