run:
    cargo run --locked --release

check:
    cargo check --locked

build:
    cargo build --locked --release

prove: build
    lake build
    printf '%s\n' 'import Popcount' '#eval Riscfree.verifyElf "target/riscv32imc-unknown-none-elf/release/riscfree"' | lake env lean -DwarningAsError=true --stdin
