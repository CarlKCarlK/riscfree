emulator_release := "emulator/target/riscv32im-unknown-none-elf/release"
firmware_release := "target/riscv32imc-unknown-none-elf/release"
# The popcount variants share one output path, so each build is copied here.
linked := "target/linked"

# Flash and monitor one popcount routine: `just run` (bit loop) or `just run swar`.
run algorithm="loop":
    cargo run --locked --release {{ if algorithm == "loop" { "" } else if algorithm == "swar" { "--features swar" } else { error("algorithm must be loop or swar") } }}

check:
    cargo check --locked
    cd emulator && cargo check --locked --bins --examples

build:
    cargo build --locked --release

# Build the ESP32-C3 RawVec demo and check the linked instructions of all four routines.
build-raw-vec:
    cargo build --locked --release --example raw_vec --features raw-vec-demo
    python3 research/vec-ffi/linked/check_elf.py target/riscv32imc-unknown-none-elf/release/examples/raw_vec

# Flash the checked RawVec demo and print its UART assertions.
run-raw-vec: build-raw-vec
    espflash flash --monitor target/riscv32imc-unknown-none-elf/release/examples/raw_vec

# Run one popcount routine under QEMU instead of on the board: `just emulate` (bit loop) or `just emulate swar`.
emulate algorithm="loop":
    cd emulator && cargo run --locked --release {{ if algorithm == "loop" { "" } else if algorithm == "swar" { "--features swar" } else { error("algorithm must be loop or swar") } }}

# Build the QEMU RawVec harness and check the linked instructions of all four routines and that it has no compressed code.
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
    just build-linked
    just corrupt-linked
    { cat scripts/LinkedBytes.lean; printf '%s\n' '#eval linkedBytes [' \
        '"popcount", "{{linked}}/firmware-popcount.elf",' \
        '"popcount-swar", "{{linked}}/firmware-popcount-swar.elf",' \
        '"raw-vec", "{{firmware_release}}/examples/raw_vec",' \
        '"raw-vec-shim", "{{firmware_release}}/examples/raw_vec",' \
        '"sorted-map", "{{firmware_release}}/examples/raw_vec",' \
        '"popcount", "{{linked}}/emulator-popcount.elf",' \
        '"uncompressed", "{{linked}}/emulator-popcount.elf",' \
        '"popcount-swar", "{{linked}}/emulator-popcount-swar.elf",' \
        '"uncompressed", "{{linked}}/emulator-popcount-swar.elf",' \
        '"raw-vec", "{{emulator_release}}/examples/raw_vec",' \
        '"sorted-map", "{{emulator_release}}/examples/raw_vec",' \
        '"uncompressed", "{{emulator_release}}/examples/raw_vec",' \
        '"reject-popcount", "{{linked}}/negative/popcount.elf",' \
        '"reject-popcount-swar", "{{linked}}/negative/popcount-swar.elf",' \
        '"reject-raw-vec", "{{linked}}/negative/raw-vec-u32.elf",' \
        '"reject-raw-vec", "{{linked}}/negative/raw-vec-pair.elf",' \
        '"reject-raw-vec", "{{linked}}/negative/raw-vec-u32-remove.elf",' \
        '"reject-raw-vec", "{{linked}}/negative/raw-vec-pair-remove.elf",' \
        '"reject-raw-vec-shim", "{{linked}}/negative/raw-vec-shim.elf",' \
        '"reject-sorted-map", "{{linked}}/negative/sorted-map-lower-bound.elf",' \
        '"reject-sorted-map", "{{linked}}/negative/sorted-map-upper-bound.elf",' \
        '"reject-uncompressed", "{{linked}}/negative/emulator-rvc.elf"' \
        ']'; } | lake env lean -DwarningAsError=true --stdin

# Explain each axiom the RawVec and shim theorems reach, and fail unless the executed instructions reach only the expected ones.
axiom-paths:
    lake env lean --run scripts/AxiomPaths.lean RawVec.Shim Riscfree.RawVec.rawVecU32InsertSailCorrect \
        Riscfree.RawVec.callRawVecU32InsertSailCorrect {{ axiom-path-flags }}
    lake env lean --run scripts/AxiomPaths.lean RawVec.PairInsert \
        Riscfree.RawVec.PairInsert.rawVecPairInsertSailCorrect {{ axiom-path-flags }}
    lake env lean --run scripts/AxiomPaths.lean RawVec.U32Remove \
        Riscfree.RawVec.U32Remove.rawVecU32RemoveSailCorrect {{ axiom-path-flags }}
    lake env lean --run scripts/AxiomPaths.lean RawVec.PairRemove \
        Riscfree.RawVec.PairRemove.rawVecPairRemoveSailCorrect {{ axiom-path-flags }}
    lake env lean --run scripts/AxiomPaths.lean SortedMap.Search.Correct \
        Riscfree.SortedMap.Search.sortedMapSearchSailCorrect {{ axiom-path-flags }}

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

# Build every firmware and QEMU ELF file that `prove` checks.
[private]
build-linked:
    mkdir -p {{linked}}
    cargo build --locked --release
    cp {{firmware_release}}/riscfree {{linked}}/firmware-popcount.elf
    cargo build --locked --release --features swar
    cp {{firmware_release}}/riscfree {{linked}}/firmware-popcount-swar.elf
    just build-raw-vec
    cd emulator && cargo build --locked --release
    cp {{emulator_release}}/riscfree-emulator {{linked}}/emulator-popcount.elf
    cd emulator && cargo build --locked --release --features swar
    cp {{emulator_release}}/riscfree-emulator {{linked}}/emulator-popcount-swar.elf
    just build-emulator-raw-vec

# Write corrupted copies of the linked ELF files, which `prove` requires the checker to reject.
[private]
corrupt-linked:
    mkdir -p {{linked}}/negative
    python3 scripts/corrupt_elf.py flip {{linked}}/firmware-popcount.elf popcount128 {{linked}}/negative/popcount.elf
    python3 scripts/corrupt_elf.py flip {{linked}}/emulator-popcount-swar.elf popcount128_swar {{linked}}/negative/popcount-swar.elf
    python3 scripts/corrupt_elf.py flip {{firmware_release}}/examples/raw_vec raw_vec_u32_insert {{linked}}/negative/raw-vec-u32.elf
    python3 scripts/corrupt_elf.py flip {{emulator_release}}/examples/raw_vec raw_vec_pair_insert {{linked}}/negative/raw-vec-pair.elf
    python3 scripts/corrupt_elf.py flip {{firmware_release}}/examples/raw_vec raw_vec_u32_remove {{linked}}/negative/raw-vec-u32-remove.elf
    python3 scripts/corrupt_elf.py flip {{emulator_release}}/examples/raw_vec raw_vec_pair_remove {{linked}}/negative/raw-vec-pair-remove.elf
    python3 scripts/corrupt_elf.py flip {{firmware_release}}/examples/raw_vec call_raw_vec_u32_insert {{linked}}/negative/raw-vec-shim.elf
    python3 scripts/corrupt_elf.py flip {{firmware_release}}/examples/raw_vec sorted_map_lower_bound {{linked}}/negative/sorted-map-lower-bound.elf
    python3 scripts/corrupt_elf.py flip {{emulator_release}}/examples/raw_vec sorted_map_upper_bound {{linked}}/negative/sorted-map-upper-bound.elf
    python3 scripts/corrupt_elf.py rvc {{emulator_release}}/examples/raw_vec {{linked}}/negative/emulator-rvc.elf
