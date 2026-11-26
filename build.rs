use std::{env, path::PathBuf, process::Command};

fn main() {
    if env::var_os("CARGO_FEATURE_RAW_VEC_DEMO").is_none() {
        return;
    }

    let source = "research/vec-ffi/linked/raw_vec.rs";
    println!("cargo:rerun-if-changed={source}");
    println!("cargo:rerun-if-changed=research/vec-ffi/linked/header.rs");
    assert_eq!(
        env::var("TARGET").expect("Cargo sets TARGET"),
        "riscv32imc-unknown-none-elf",
        "the RawVec demo targets the ESP32-C3"
    );
    let object =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR")).join("raw_vec_u32.o");
    // Isolate the proof target from the firmware's optimization settings and
    // compile it for an ISA without compressed instructions.
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
        .arg(&object)
        .arg(source)
        .status()
        .expect("start rustc for the RawVec routine");
    assert!(status.success(), "compile the RawVec routine");
    println!("cargo:rustc-link-arg-examples={}", object.display());
}
