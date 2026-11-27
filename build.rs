use std::{
    env, fs,
    path::{Path, PathBuf},
};

#[path = "research/vec-ffi/linked/compile.rs"]
mod compile;

fn main() {
    if env::var_os("CARGO_FEATURE_RAW_VEC_DEMO").is_none() {
        return;
    }

    let shims = "examples/raw_vec_call.S";
    let remove_shims = "examples/raw_vec_remove_call.S";
    let map_shims = "examples/sorted_map_call.S";
    for source in [shims, remove_shims, map_shims] {
        println!("cargo:rerun-if-changed={source}");
    }
    assert_eq!(
        env::var("TARGET").expect("Cargo sets TARGET"),
        "riscv32imc-unknown-none-elf",
        "the RawVec demo targets the ESP32-C3"
    );
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let manifest =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"));
    let linked = Path::new("research/vec-ffi/linked");

    // The shims get their own object, linked directly before the routines, so
    // the linker's single `.text` rule places them next to each other. Each
    // shim's `call` offset then depends only on these two objects, not on the
    // demo's code. The proof of the u32 shim records that offset.
    //
    // The removal routines and their shims follow in two more objects, so
    // adding them moved neither the insertion routines nor that offset. The
    // sorted-map routines follow the removal routines directly, as in the QEMU
    // harness, so their calls into the RawVec routines have the same offsets in
    // both executables. All unproved shims come last.
    let objects = [
        assemble(&out, &manifest, shims, "raw_vec_shims"),
        compile::routine_object(linked, "raw_vec"),
        compile::routine_object(linked, "raw_vec_remove"),
        compile::routine_object(linked, "sorted_map"),
        assemble(&out, &manifest, remove_shims, "raw_vec_remove_shims"),
        assemble(&out, &manifest, map_shims, "sorted_map_shims"),
    ];
    for object in objects {
        println!("cargo:rustc-link-arg-examples={}", object.display());
    }
}

// Wrap an assembly file in a `no_std` crate and compile it to `<name>.o`.
fn assemble(out: &Path, manifest: &Path, shims: &str, name: &str) -> PathBuf {
    let source = out.join(format!("{name}.rs"));
    fs::write(
        &source,
        format!(
            "#![no_std]\ncore::arch::global_asm!(include_str!({:?}));\n",
            manifest.join(shims)
        ),
    )
    .unwrap_or_else(|error| panic!("write {}: {error}", source.display()));
    let object = out.join(format!("{name}.o"));
    compile::compile(&source, &object);
    object
}
