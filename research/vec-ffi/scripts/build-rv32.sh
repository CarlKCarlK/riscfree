#!/usr/bin/env bash

set -euo pipefail

target="riscv32im-unknown-none-elf"
host="$(rustc --version --verbose | sed -n 's/^host: //p')"
llvm_objdump="$(rustc --print sysroot)/lib/rustlib/$host/bin/llvm-objdump"
heapless_manifest="$(
    cargo metadata --locked --offline --format-version 1 \
        | jq --raw-output '.packages[] | select(.name == "heapless") | .manifest_path'
)"
heapless_source="$(dirname "$heapless_manifest")"
export RUSTFLAGS="--remap-path-prefix=$PWD=/workspace/research/vec-ffi \
--remap-path-prefix=$heapless_source=/cargo/registry/heapless-0.9.3"

latest_artifact() {
    find "$1" -type f -name "$2" -printf '%T@ %p\n' \
        | sort --numeric-sort --reverse \
        | head --lines=1 \
        | cut --delimiter=' ' --fields=2-
}

for profile in release-1 release-3 release-s release-z; do
    cargo rustc --locked --target "$target" --profile "$profile" --lib -- \
        --emit=asm,obj

    profile_directory="target/$target/$profile"
    assembly_file="$(latest_artifact "$profile_directory" 'vec_ffi_research-*.s')"
    object_file="$(latest_artifact "$profile_directory" 'vec_ffi_research-*.o')"

    cp "$assembly_file" "generated/$profile.s"
    cp "$object_file" "generated/$profile.o"
    readelf -A "$object_file" > "generated/$profile.attributes.txt"
    "$llvm_objdump" --disassemble --reloc "$object_file" \
        > "generated/$profile.disassembly.txt"
done
