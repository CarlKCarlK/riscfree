run:
    cargo run --locked --release

check:
    cargo check --locked

build:
    cargo build --locked --release

prove: build
    lean -DwarningAsError=true --run proof/Popcount.lean target/riscv32imc-unknown-none-elf/release/riscfree
