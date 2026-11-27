use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

fn main() {
    if env::var_os("CARGO_FEATURE_RAW_VEC_DEMO").is_none() {
        return;
    }

    let routines = "research/vec-ffi/linked/raw_vec.rs";
    let shims = "examples/raw_vec_call.S";
    let remove_routines = "research/vec-ffi/linked/raw_vec_remove.rs";
    let remove_shims = "examples/raw_vec_remove_call.S";
    let map_routines = "research/vec-ffi/linked/sorted_map.rs";
    let map_shims = "examples/sorted_map_call.S";
    for source in [routines, shims, remove_routines, remove_shims, map_routines, map_shims] {
        println!("cargo:rerun-if-changed={source}");
    }
    println!("cargo:rerun-if-changed=research/vec-ffi/linked/header.rs");
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
    //
    // The removal routines and their shims follow in two more objects, so
    // adding them moved neither the insertion routines nor that offset. The
    // sorted-map routines and their shims come last, for the same reason.
    let objects = [
        assemble(&out, &manifest, shims, "raw_vec_shims"),
        compile_routines(&out, routines, "raw_vec"),
        compile_routines(&out, remove_routines, "raw_vec_remove"),
        assemble(&out, &manifest, remove_shims, "raw_vec_remove_shims"),
        compile_routines(&out, map_routines, "sorted_map"),
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
    compile(&source, &object);
    object
}

fn compile_routines(out: &Path, routines: &str, name: &str) -> PathBuf {
    let object = out.join(format!("{name}.o"));
    compile(Path::new(routines), &object);
    object
}

// Isolate the proof targets from the firmware's optimization settings and
// compile them for an ISA without compressed instructions.
fn compile(source: &Path, object: &Path) {
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
