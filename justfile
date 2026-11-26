# Flash and monitor one popcount routine: `just run` (bit loop) or `just run swar`.
run algorithm="loop":
    cargo run --locked --release {{ if algorithm == "loop" { "" } else if algorithm == "swar" { "--features swar" } else { error("algorithm must be loop or swar") } }}

check:
    cargo check --locked

build:
    cargo build --locked --release

# Check the Lean proofs and their axioms, then compare each routine's linked bytes in the firmware that calls it.
prove:
    python3 scripts/check_proof_sources.py
    lake build
    lake env lean --run scripts/AxiomAudit.lean
    cargo build --locked --release
    just verify-elf Popcount
    cargo build --locked --release --features swar
    just verify-elf PopcountSwar

# Optional: replay every proof module through Lean's kernel with leanchecker. Not part of `prove`.
# One module at a time: checking them all in one process runs out of memory.
kernel-check:
    lake build
    for module in $(find proof -name '*.lean' | sed -e 's|^proof/||' -e 's|\.lean$||' -e 's|/|.|g' | sort); do echo "leanchecker $module"; lake env leanchecker "$module" || exit 1; done

[private]
verify-elf module:
    printf '%s\n' 'import {{module}}' \
        '#eval Riscfree.{{module}}.verifyElf "target/riscv32imc-unknown-none-elf/release/riscfree"' \
        | lake env lean -DwarningAsError=true --stdin
