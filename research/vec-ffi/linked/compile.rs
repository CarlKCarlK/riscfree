//! Compile the RawVec routines for the build scripts of the ESP32-C3 firmware
//! and the QEMU harness, so both link the same object.

use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

/// Compile `<name>.rs` in `linked_directory`, which defines verified RawVec
/// routines (`raw_vec` for insertion, `raw_vec_remove` for removal, `sorted_map`
/// for the sorted map), to
/// `<name>.o` in `OUT_DIR` and return its path.
pub fn routine_object(linked_directory: &Path, name: &str) -> PathBuf {
    let source = linked_directory.join(format!("{name}.rs"));
    println!("cargo:rerun-if-changed={}", source.display());
    println!(
        "cargo:rerun-if-changed={}",
        linked_directory.join("header.rs").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        linked_directory.join("compile.rs").display()
    );
    if name == "range_insert" {
        println!(
            "cargo:rerun-if-changed={}",
            linked_directory.join("range_insert_algorithm.rs").display()
        );
    }
    let object = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"))
        .join(format!("{name}.o"));
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
