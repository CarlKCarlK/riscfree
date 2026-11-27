//! The RawVec removal case, written once for the `u32` and `Pair` routines.
//! The ESP32-C3 demo runs it through the calling shims. A harness without
//! compressed instructions, such as the QEMU one, can pass the routines
//! themselves. Its calls reach all four outcomes of the routine: removal
//! before a suffix, removal of the last element, invalid index (including an
//! empty vector), and invalid length.

use core::fmt::Debug;

use crate::header::{INDEX_OUT_OF_BOUNDS, INVALID_LENGTH, OK, RawVec};

/// The C ABI of `raw_vec_u32_remove` and `raw_vec_pair_remove`, and of the
/// calling shims that forward to them.
pub type Remove<T> = unsafe extern "C" fn(vec: *mut RawVec<T>, index: u32) -> u32;

/// The statuses of the six calls on the valid vector, in order.
pub const STATUSES: [u32; 6] = [OK, OK, OK, INDEX_OUT_OF_BOUNDS, OK, INDEX_OUT_OF_BOUNDS];

/// Make seven calls through `remove` on elements `element(10)`, `element(20)`, ...,
/// assert every status, length, and the final memory, including the guard
/// elements on both sides of the backing slots, and return the statuses of
/// the first six calls for the report.
///
/// # Safety
///
/// `remove` must have the contract of `raw_vec_u32_remove` in
/// `research/vec-ffi/linked/raw_vec_remove.rs` for elements of type `T`.
#[inline(always)]
pub unsafe fn run<T: Copy + Debug + PartialEq>(
    remove: Remove<T>,
    element: fn(u32) -> T,
) -> [u32; 6] {
    let mut data = [111, 10, 20, 30, 40, 222].map(element);
    let mut vec = RawVec {
        data: data[1..5].as_mut_ptr(),
        length: 4,
        capacity: 4,
    };
    let mut lengths = [0; 6];
    // SAFETY: The header and its four initialized backing slots are disjoint.
    // No other accesses to the header or array occur during these calls.
    let statuses = unsafe {
        // [10, 20, 30, 40] -> [10, 30, 40]: shift two elements.
        let shifted = remove(&mut vec, 1);
        lengths[0] = vec.length;
        // [10, 30, 40] -> [10, 30]: remove the last element, shifting none.
        let last = remove(&mut vec, 2);
        lengths[1] = vec.length;
        // [10, 30] -> [30]: shift one element.
        let front = remove(&mut vec, 0);
        lengths[2] = vec.length;
        // Index 1 is not below length 1.
        let invalid_index = remove(&mut vec, 1);
        lengths[3] = vec.length;
        // [30] -> []: remove the only element.
        let only = remove(&mut vec, 0);
        lengths[4] = vec.length;
        // No index of an empty vector is valid.
        let empty = remove(&mut vec, 0);
        lengths[5] = vec.length;
        [shifted, last, front, invalid_index, only, empty]
    };
    assert_eq!(statuses, STATUSES);
    assert_eq!(lengths, [3, 2, 1, 1, 0, 0]);
    assert_eq!(vec.capacity, 4);

    let mut invalid = RawVec { length: 5, ..vec };
    // SAFETY: The header is exclusive. Its length exceeds capacity, so this
    // call returns without accessing the backing array.
    assert_eq!(unsafe { remove(&mut invalid, 0) }, INVALID_LENGTH);
    assert_eq!(invalid.length, 5);
    // Each removal leaves the vacated last slot as it was: after the first
    // call, slot 3 still holds 40, and after the third, slot 1 still holds 30.
    assert_eq!(data, [111, 30, 30, 40, 40, 222].map(element));
    statuses
}
