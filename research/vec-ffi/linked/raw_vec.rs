#![no_std]

mod header;

use header::{FULL, INDEX_OUT_OF_BOUNDS, INVALID_LENGTH, OK, RawVec};

/// Insert a word at `index`. Inserting at `length` appends it.
///
/// # Safety
///
/// The header must be valid, aligned and exclusively accessible. If
/// `index <= length < capacity`, the data pointer must identify an aligned,
/// exclusively accessible allocation for `capacity` elements, disjoint from
/// the header, with the first `length` elements initialized.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32 {
    // SAFETY: The caller supplies an exclusive header and the backing allocation
    // required by insert.
    unsafe { (&mut *vec).insert(index, value) }
}

impl<T: Copy> RawVec<T> {
    #[inline(always)]
    unsafe fn insert(&mut self, index: u32, value: T) -> u32 {
        if self.length > self.capacity {
            return INVALID_LENGTH;
        }
        if index > self.length {
            return INDEX_OUT_OF_BOUNDS;
        }
        if self.length == self.capacity {
            return FULL;
        }

        let mut source_index = self.length;
        while source_index > index {
            source_index -= 1;
            // SAFETY: The initialized source is below length. The destination
            // is at most length, and there is at least one spare slot.
            unsafe {
                let moved = self.data.add(source_index as usize).read();
                self.data.add(source_index as usize + 1).write(moved);
            }
        }
        // SAFETY: index <= length < capacity, and the caller supplies the array.
        unsafe { self.data.add(index as usize).write(value) };
        self.length += 1;
        OK
    }
}
