run:
    cargo run --locked --release

check:
    cargo check --locked

build:
    cargo build --locked --release

prove: build
    lake build
    lake env lean -DwarningAsError=true --run proof/VerifyElf.lean target/riscv32imc-unknown-none-elf/release/riscfree
