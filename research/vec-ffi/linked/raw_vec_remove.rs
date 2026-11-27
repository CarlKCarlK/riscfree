#![no_std]

//! Removal from a `RawVec<T>`, with C entry points for `u32` and `Pair`.
//!
//! This crate is compiled into its own object, linked after the insertion
//! routines in `raw_vec.rs` (see `build.rs`), so adding it does not move them
//! or the verified calling shim's `call` offset.

pub mod header;

use header::{INDEX_OUT_OF_BOUNDS, INVALID_LENGTH, OK, Pair, RawVec};

/// Remove the word at `index`, moving each later word one slot toward the
/// front.
///
/// Returns `OK` after removing it and decrementing `length`,
/// `INDEX_OUT_OF_BOUNDS` if `index >= length` (including every index of an
/// empty vector), and `INVALID_LENGTH` if `length > capacity`. On either
/// error, the routine writes no memory. The removed word is not returned;
/// a caller that needs it reads `data[index]` first. The slot at the old
/// `length - 1` keeps its old value, outside the new live prefix.
///
/// The routine reads the three header words. On success it also reads the
/// elements after `index`, writes the elements from `index` to the old
/// `length - 2`, and writes the length word. It writes no other memory and
/// makes no calls.
///
/// # Safety
///
/// The header must be valid, aligned and exclusively accessible. If
/// `index < length <= capacity`, the data pointer must identify an aligned,
/// exclusively accessible allocation with the first `length` elements
/// initialized, disjoint from the header.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_vec_u32_remove(vec: *mut RawVec<u32>, index: u32) -> u32 {
    // SAFETY: The caller supplies an exclusive header and the backing allocation
    // required by remove.
    unsafe { (&mut *vec).remove(index) }
}

/// Remove the pair at `index`, moving each later pair one slot toward the
/// front.
///
/// # Safety
///
/// The same contract, results, and memory accesses as `raw_vec_u32_remove`,
/// with eight-byte elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_vec_pair_remove(vec: *mut RawVec<Pair>, index: u32) -> u32 {
    // SAFETY: The caller supplies an exclusive header and the backing allocation
    // required by remove.
    unsafe { (&mut *vec).remove(index) }
}

impl<T: Copy> RawVec<T> {
    #[inline(always)]
    unsafe fn remove(&mut self, index: u32) -> u32 {
        if self.length > self.capacity {
            return INVALID_LENGTH;
        }
        if index >= self.length {
            return INDEX_OUT_OF_BOUNDS;
        }

        // `length >= 1` here, because `index < length`.
        let new_length = self.length - 1;
        let mut destination_index = index;
        while destination_index < new_length {
            // SAFETY: The source, `destination_index + 1`, is below length and
            // initialized. The destination is below length too.
            unsafe {
                let moved = self.data.add(destination_index as usize + 1).read();
                self.data.add(destination_index as usize).write(moved);
            }
            destination_index += 1;
        }
        self.length = new_length;
        OK
    }
}
