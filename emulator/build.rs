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

    let object = compile::raw_vec_object(Path::new("../research/vec-ffi/linked"));
    println!("cargo:rustc-link-arg-examples={}", object.display());
}
