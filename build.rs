use std::{env, path::Path};

#[path = "research/vec-ffi/linked/compile.rs"]
mod compile;

fn main() {
    if env::var_os("CARGO_FEATURE_RAW_VEC_DEMO").is_none() {
        return;
    }

    assert_eq!(
        env::var("TARGET").expect("Cargo sets TARGET"),
        "riscv32imc-unknown-none-elf",
        "the RawVec demo targets the ESP32-C3"
    );
    let object = compile::raw_vec_object(Path::new("research/vec-ffi/linked"));
    println!("cargo:rustc-link-arg-examples={}", object.display());
}
