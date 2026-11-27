//! The popcount case that the ESP32-C3 firmware and the QEMU harness share.

use core::{fmt::Arguments, hint::black_box};

/// The C ABI of `popcount128` and `popcount128_swar`.
pub type Popcount = unsafe extern "C" fn(input: *const u32) -> u8;

const INPUT: u128 = 0xD3A5_7C19_02EF_B648_9D30_6A17_C2F5_804B;
const EXPECTED_COUNT: u8 = 61;
const _: () = assert!(align_of::<u128>() >= align_of::<u32>());

/// Call `popcount` on the fixed input, report the count through `print`, and
/// then assert that it is correct.
///
/// # Safety
///
/// `popcount` must read only the 16 bytes at its 4-byte-aligned argument and
/// otherwise follow the C ABI.
pub unsafe fn run(name: &str, popcount: Popcount, print: impl FnOnce(Arguments<'_>)) {
    // Materialize the input on the stack in data RAM for the assembly call.
    let input = black_box(INPUT);
    let input_pointer = (&raw const input).cast();
    // SAFETY: The local provides 16 readable bytes at a 4-byte-aligned address.
    // The caller guarantees that the routine reads four words and never writes
    // through the pointer.
    let count = unsafe { popcount(input_pointer) };
    print(format_args!("{name}(0x{INPUT:032x}) = {count}"));
    assert_eq!(count, EXPECTED_COUNT);
}
