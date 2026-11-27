use std::{
    env,
    path::{Path, PathBuf},
};

#[path = "../research/vec-ffi/linked/compile.rs"]
mod compile;

fn main() {
    assert_eq!(
        env::var("TARGET").expect("Cargo sets TARGET"),
        "riscv32im-unknown-none-elf",
        "the QEMU harness must not contain compressed instructions"
    );
    let manifest_directory =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"));
    println!("cargo:rustc-link-search={}", manifest_directory.display());
    println!("cargo:rustc-link-arg=-Tlink.x");
    println!("cargo:rerun-if-changed=link.x");

    // The same routine objects as the ESP32-C3 demo, without its shims.
    let linked = Path::new("../research/vec-ffi/linked");
    for name in ["raw_vec", "raw_vec_remove"] {
        let object = compile::routine_object(linked, name);
        println!("cargo:rustc-link-arg-examples={}", object.display());
    }
}
