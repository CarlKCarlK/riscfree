# Flash and monitor one popcount routine: `just run` (bit loop) or `just run swar`.
run algorithm="loop":
    cargo run --locked --release {{ if algorithm == "loop" { "" } else if algorithm == "swar" { "--features swar" } else { error("algorithm must be loop or swar") } }}

check:
    cargo check --locked

build:
    cargo build --locked --release

# Check the Lean proofs, then compare each routine's linked bytes in the firmware that calls it.
prove:
    lake build
    cargo build --locked --release
    just verify-elf Popcount
    cargo build --locked --release --features swar
    just verify-elf PopcountSwar

[private]
verify-elf module:
    printf '%s\n' 'import {{module}}' \
        '#eval Riscfree.{{module}}.verifyElf "target/riscv32imc-unknown-none-elf/release/riscfree"' \
        | lake env lean -DwarningAsError=true --stdin
