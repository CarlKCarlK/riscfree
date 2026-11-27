//! Compile the RawVec routines for the build scripts of the ESP32-C3 firmware
//! and the QEMU harness, so both link the same object.

use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

/// Compile `raw_vec.rs` in `linked_directory`, which defines every verified
/// RawVec routine, to an object in `OUT_DIR` and return its path.
pub fn raw_vec_object(linked_directory: &Path) -> PathBuf {
    let source = linked_directory.join("raw_vec.rs");
    println!("cargo:rerun-if-changed={}", source.display());
    println!(
        "cargo:rerun-if-changed={}",
        linked_directory.join("header.rs").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        linked_directory.join("compile.rs").display()
    );
    let object =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR")).join("raw_vec.o");
    compile(&source, &object);
    object
}

/// Compile one source file to an object, isolated from the caller's
/// optimization settings and for an ISA without compressed instructions.
pub fn compile(source: &Path, object: &Path) {
    let status = Command::new(env::var_os("RUSTC").expect("Cargo sets RUSTC"))
        .args([
            "--edition",
            "2024",
            "--crate-type",
            "lib",
            "--emit",
            "obj",
            "--target",
            "riscv32im-unknown-none-elf",
            "-C",
            "opt-level=1",
            "-C",
            "panic=abort",
            "-o",
        ])
        .arg(object)
        .arg(source)
        .status()
        .unwrap_or_else(|error| panic!("start rustc for {}: {error}", source.display()));
    assert!(status.success(), "compile {}", source.display());
}
