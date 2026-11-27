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
    println!("cargo:rerun-if-changed={shims}");
    assert_eq!(
        env::var("TARGET").expect("Cargo sets TARGET"),
        "riscv32imc-unknown-none-elf",
        "the RawVec demo targets the ESP32-C3"
    );
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let manifest =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"));

    // The shims get their own object, linked directly before the routines, so
    // the linker's single `.text` rule places them next to each other. Each
    // shim's `call` offset then depends only on these two objects, not on the
    // demo's code. The proof of the u32 shim records that offset.
    let shim_source = out.join("raw_vec_shims.rs");
    fs::write(
        &shim_source,
        format!(
            "#![no_std]\ncore::arch::global_asm!(include_str!({:?}));\n",
            manifest.join(shims)
        ),
    )
    .expect("write the RawVec shim crate");
    let shim_object = out.join("raw_vec_shims.o");
    compile::compile(&shim_source, &shim_object);
    let routine_object = compile::raw_vec_object(Path::new("research/vec-ffi/linked"));
    println!("cargo:rustc-link-arg-examples={}", shim_object.display());
    println!("cargo:rustc-link-arg-examples={}", routine_object.display());
}
