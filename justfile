emulator_release := "emulator/target/riscv32im-unknown-none-elf/release"

# Flash and monitor one popcount routine: `just run` (bit loop) or `just run swar`.
run algorithm="loop":
    cargo run --locked --release {{ if algorithm == "loop" { "" } else if algorithm == "swar" { "--features swar" } else { error("algorithm must be loop or swar") } }}

check:
    cargo check --locked
    cd emulator && cargo check --locked --bins --examples

build:
    cargo build --locked --release

# Build the ESP32-C3 RawVec demo and check the linked insertion instructions of both routines.
build-raw-vec:
    cargo build --locked --release --example raw_vec --features raw-vec-demo
    python3 research/vec-ffi/linked/check_elf.py target/riscv32imc-unknown-none-elf/release/examples/raw_vec

# Flash the checked RawVec demo and print its UART assertions.
run-raw-vec: build-raw-vec
    espflash flash --monitor target/riscv32imc-unknown-none-elf/release/examples/raw_vec

# Run one popcount routine under QEMU instead of on the board: `just emulate` (bit loop) or `just emulate swar`.
emulate algorithm="loop":
    cd emulator && cargo run --locked --release {{ if algorithm == "loop" { "" } else if algorithm == "swar" { "--features swar" } else { error("algorithm must be loop or swar") } }}

# Build the QEMU RawVec harness and check its linked insertion instructions and that it has no compressed code.
build-emulator-raw-vec:
    cd emulator && cargo build --locked --release --example raw_vec
    python3 research/vec-ffi/linked/check_elf.py --uncompressed {{emulator_release}}/examples/raw_vec

# Run the checked RawVec harness under QEMU.
emulate-raw-vec: build-emulator-raw-vec
    cd emulator && cargo run --locked --release --example raw_vec

# Check the Lean proofs and their axioms, then compare each routine's linked bytes in the firmware and the QEMU harness that call it.
prove:
    python3 scripts/check_proof_sources.py
    lake build
    lake env lean --run scripts/AxiomAudit.lean
    just axiom-paths
    cargo build --locked --release
    just verify-elf Popcount
    cargo build --locked --release --features swar
    just verify-elf PopcountSwar
    just build-raw-vec
    just verify-elf RawVec.Shim target/riscv32imc-unknown-none-elf/release/examples/raw_vec
    just verify-elf RawVec.PairInsert target/riscv32imc-unknown-none-elf/release/examples/raw_vec
    cd emulator && cargo build --locked --release
    just verify-emulator-elf Popcount {{emulator_release}}/riscfree-emulator
    cd emulator && cargo build --locked --release --features swar
    just verify-emulator-elf PopcountSwar {{emulator_release}}/riscfree-emulator
    just build-emulator-raw-vec
    just verify-emulator-elf RawVec {{emulator_release}}/examples/raw_vec
    just verify-emulator-elf RawVec.PairInsert {{emulator_release}}/examples/raw_vec

# Explain each axiom the RawVec and shim theorems reach, and fail unless the executed instructions reach only the expected ones.
axiom-paths:
    lake env lean --run scripts/AxiomPaths.lean RawVec.Shim Riscfree.RawVec.rawVecU32InsertSailCorrect \
        Riscfree.RawVec.callRawVecU32InsertSailCorrect {{ axiom-path-flags }}
    lake env lean --run scripts/AxiomPaths.lean RawVec.PairInsert \
        Riscfree.RawVec.PairInsert.rawVecPairInsertSailCorrect {{ axiom-path-flags }}

axiom-path-flags := "--block LeanRV32D.Functions.execute " + \
    prepend("--root LeanRV32D.Functions.execute_", "LOAD STORE BTYPE ITYPE RTYPE SHIFTIOP JALR UTYPE") + " " + \
    prepend("--expect ", "propext Quot.sound Classical.choice load_reservation match_reservation plat_term_write sys_enable_experimental_extensions")

# Optional: replay every proof module through Lean's kernel with leanchecker's replay. Not part of `prove`.
# Each replay reports 6–7 GB resident, but that is mostly the memory-mapped Sail `.olean` files, which
# all jobs share. With 16 jobs, physical memory in use peaked at 21 GB (5 GB idle).
kernel-check jobs="16":
    lake build
    find proof -name '*.lean' | sed -e 's|^proof/||' -e 's|\.lean$||' -e 's|/|.|g' | sort | \
        xargs -P {{ jobs }} -I {} sh -c '/usr/bin/time -f "replayed {} in %e s, peak %M KB" lake env lean --run scripts/KernelCheck.lean {} > /dev/null'

[private]
verify-elf module elf="target/riscv32imc-unknown-none-elf/release/riscfree":
    printf '%s\n' 'import {{module}}' \
        '#eval Riscfree.{{module}}.verifyElf "{{elf}}"' \
        | lake env lean -DwarningAsError=true --stdin

# Like verify-elf, and also require that the QEMU harness has no compressed instructions.
[private]
verify-emulator-elf module elf:
    printf '%s\n' 'import {{module}}' \
        '#eval Riscfree.{{module}}.verifyElf "{{elf}}"' \
        '#eval Riscfree.verifyUncompressed "{{elf}}"' \
        | lake env lean -DwarningAsError=true --stdin
