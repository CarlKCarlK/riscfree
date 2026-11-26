#![no_std]

use core::{
    ffi::c_void,
    mem::{align_of, size_of},
    ptr,
};

use heapless::{Vec, VecView};

pub const OK: u32 = 0;
pub const FULL: u32 = 1;
pub const INDEX_OUT_OF_BOUNDS: u32 = 2;
pub const INVALID_LENGTH: u32 = 3;

const HEAPLESS_CAPACITY: usize = 16;

type HeaplessU32 = Vec<u32, HEAPLESS_CAPACITY, u32>;
type HeaplessPair = Vec<Pair, HEAPLESS_CAPACITY, u32>;

/// A C-compatible eight-byte ordered-map entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(C)]
pub struct Pair {
    pub key: u32,
    pub value: u32,
}

/// Runtime-capacity vector header for four-byte elements.
///
/// The caller must provide writable, aligned storage for `capacity` elements.
/// `length <= capacity` is checked by every operation, but pointer validity and
/// the allocation size remain FFI preconditions.
#[repr(C)]
pub struct U32Vec {
    pub data: *mut u32,
    pub length: u32,
    pub capacity: u32,
}

/// Runtime-capacity vector header for eight-byte elements.
///
/// The caller must provide writable, aligned storage for `capacity` elements.
/// `length <= capacity` is checked by every operation, but pointer validity and
/// the allocation size remain FFI preconditions.
#[repr(C)]
pub struct PairVec {
    pub data: *mut Pair,
    pub length: u32,
    pub capacity: u32,
}

#[unsafe(no_mangle)]
pub extern "C" fn heapless_u32_size() -> usize {
    size_of::<HeaplessU32>()
}

#[unsafe(no_mangle)]
pub extern "C" fn heapless_u32_align() -> usize {
    align_of::<HeaplessU32>()
}

/// Initializes opaque storage returned by a C allocator with the size and
/// alignment reported above.
///
/// # Safety
///
/// `storage` must point to writable, aligned, uninitialized storage of at
/// least `heapless_u32_size()` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn heapless_u32_init(storage: *mut c_void) {
    // SAFETY: The function's contract provides storage for a `HeaplessU32`.
    unsafe { storage.cast::<HeaplessU32>().write(HeaplessU32::new()) };
}

/// # Safety
///
/// `storage` must point to a live value initialized by `heapless_u32_init` and
/// must be exclusively borrowed for the duration of this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn heapless_u32_push(storage: *mut c_void, value: u32) -> u32 {
    // SAFETY: The function's contract provides an exclusive live vector.
    let vec = unsafe { &mut *storage.cast::<HeaplessU32>() };
    if vec.push(value).is_ok() { OK } else { FULL }
}

/// # Safety
///
/// `storage` must point to a live value initialized by `heapless_u32_init` and
/// must be exclusively borrowed for the duration of this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn heapless_u32_insert(storage: *mut c_void, index: u32, value: u32) -> u32 {
    // SAFETY: The function's contract provides an exclusive live vector.
    let vec = unsafe { &mut *storage.cast::<HeaplessU32>() };
    if index > vec.len() as u32 {
        return INDEX_OUT_OF_BOUNDS;
    }
    if vec.insert(index as usize, value).is_ok() {
        OK
    } else {
        FULL
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn heapless_pair_size() -> usize {
    size_of::<HeaplessPair>()
}

#[unsafe(no_mangle)]
pub extern "C" fn heapless_pair_align() -> usize {
    align_of::<HeaplessPair>()
}

/// # Safety
///
/// `storage` must point to writable, aligned, uninitialized storage of at
/// least `heapless_pair_size()` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn heapless_pair_init(storage: *mut c_void) {
    // SAFETY: The function's contract provides storage for a `HeaplessPair`.
    unsafe { storage.cast::<HeaplessPair>().write(HeaplessPair::new()) };
}

/// # Safety
///
/// `storage` must point to a live value initialized by `heapless_pair_init` and
/// must be exclusively borrowed for the duration of this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn heapless_pair_push(storage: *mut c_void, value: Pair) -> u32 {
    // SAFETY: The function's contract provides an exclusive live vector.
    let vec = unsafe { &mut *storage.cast::<HeaplessPair>() };
    if vec.push(value).is_ok() { OK } else { FULL }
}

/// # Safety
///
/// `storage` must point to a live value initialized by `heapless_pair_init` and
/// must be exclusively borrowed for the duration of this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn heapless_pair_insert(
    storage: *mut c_void,
    index: u32,
    value: Pair,
) -> u32 {
    // SAFETY: The function's contract provides an exclusive live vector.
    let vec = unsafe { &mut *storage.cast::<HeaplessPair>() };
    if index > vec.len() as u32 {
        return INDEX_OUT_OF_BOUNDS;
    }
    if vec.insert(index as usize, value).is_ok() {
        OK
    } else {
        FULL
    }
}

/// Capacity-erased `heapless` insertion using Rust's fat-pointer ABI.
///
/// This symbol is deliberately not `extern "C"`: `VecView` is unsized, and
/// its capacity is fat-pointer metadata whose representation is not a C ABI.
#[unsafe(no_mangle)]
pub fn heapless_view_u32_insert_rust_abi(
    vec: &mut VecView<u32, u32>,
    index: u32,
    value: u32,
) -> u32 {
    if index > vec.len() as u32 {
        return INDEX_OUT_OF_BOUNDS;
    }
    if vec.insert(index as usize, value).is_ok() {
        OK
    } else {
        FULL
    }
}

/// Calls a capacity-erased `VecView` implementation through a concrete C ABI
/// wrapper. The view itself is not C ABI compatible because it is unsized.
///
/// # Safety
///
/// `storage` must satisfy the contract of `heapless_u32_insert`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn heapless_view_u32_insert_cap16(
    storage: *mut c_void,
    index: u32,
    value: u32,
) -> u32 {
    // SAFETY: The function's contract provides an exclusive live vector.
    let vec = unsafe { &mut *storage.cast::<HeaplessU32>() };
    heapless_view_u32_insert_rust_abi(vec, index, value)
}

/// # Safety
///
/// `vec` and its backing allocation must satisfy the documented `U32Vec`
/// invariants and must be exclusively borrowed for this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn custom_u32_push(vec: *mut U32Vec, value: u32) -> u32 {
    // SAFETY: The function's contract provides an exclusive live header.
    let vec = unsafe { &mut *vec };
    if vec.length > vec.capacity {
        return INVALID_LENGTH;
    }
    if vec.length == vec.capacity {
        return FULL;
    }

    // SAFETY: `length < capacity`, and the caller guarantees the allocation.
    unsafe { vec.data.add(vec.length as usize).write(value) };
    vec.length += 1;
    OK
}

/// # Safety
///
/// `vec` and its backing allocation must satisfy the documented `U32Vec`
/// invariants and must be exclusively borrowed for this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn custom_u32_insert(vec: *mut U32Vec, index: u32, value: u32) -> u32 {
    // SAFETY: The function's contract provides an exclusive live header.
    let vec = unsafe { &mut *vec };
    if vec.length > vec.capacity {
        return INVALID_LENGTH;
    }
    if index > vec.length {
        return INDEX_OUT_OF_BOUNDS;
    }
    if vec.length == vec.capacity {
        return FULL;
    }

    let moved = (vec.length - index) as usize;
    // SAFETY: Both ranges are inside the allocation because `length < capacity`.
    // `ptr::copy` permits the one-element overlap between them.
    unsafe {
        let insertion = vec.data.add(index as usize);
        ptr::copy(insertion, insertion.add(1), moved);
        insertion.write(value);
    }
    vec.length += 1;
    OK
}

/// Inserts using an explicit reverse-copy loop instead of a `memmove` call.
///
/// # Safety
///
/// `vec` and its backing allocation must satisfy the documented `U32Vec`
/// invariants and must be exclusively borrowed for this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn custom_u32_insert_loop(vec: *mut U32Vec, index: u32, value: u32) -> u32 {
    // SAFETY: The function's contract provides an exclusive live header.
    let vec = unsafe { &mut *vec };
    if vec.length > vec.capacity {
        return INVALID_LENGTH;
    }
    if index > vec.length {
        return INDEX_OUT_OF_BOUNDS;
    }
    if vec.length == vec.capacity {
        return FULL;
    }

    let mut source_index = vec.length;
    while source_index > index {
        source_index -= 1;
        // SAFETY: The source is initialized and the destination is no greater
        // than the spare element at `length` because `length < capacity`.
        unsafe {
            let moved = vec.data.add(source_index as usize).read();
            vec.data.add(source_index as usize + 1).write(moved);
        }
    }
    // SAFETY: `index <= length < capacity` puts the write inside the allocation.
    unsafe { vec.data.add(index as usize).write(value) };
    vec.length += 1;
    OK
}

/// # Safety
///
/// `vec` and its backing allocation must satisfy the documented `PairVec`
/// invariants and must be exclusively borrowed for this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn custom_pair_push(vec: *mut PairVec, value: Pair) -> u32 {
    // SAFETY: The function's contract provides an exclusive live header.
    let vec = unsafe { &mut *vec };
    if vec.length > vec.capacity {
        return INVALID_LENGTH;
    }
    if vec.length == vec.capacity {
        return FULL;
    }

    // SAFETY: `length < capacity`, and the caller guarantees the allocation.
    unsafe { vec.data.add(vec.length as usize).write(value) };
    vec.length += 1;
    OK
}

/// # Safety
///
/// `vec` and its backing allocation must satisfy the documented `PairVec`
/// invariants and must be exclusively borrowed for this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn custom_pair_insert(vec: *mut PairVec, index: u32, value: Pair) -> u32 {
    // SAFETY: The function's contract provides an exclusive live header.
    let vec = unsafe { &mut *vec };
    if vec.length > vec.capacity {
        return INVALID_LENGTH;
    }
    if index > vec.length {
        return INDEX_OUT_OF_BOUNDS;
    }
    if vec.length == vec.capacity {
        return FULL;
    }

    let moved = (vec.length - index) as usize;
    // SAFETY: Both ranges are inside the allocation because `length < capacity`.
    // `ptr::copy` permits the one-element overlap between them.
    unsafe {
        let insertion = vec.data.add(index as usize);
        ptr::copy(insertion, insertion.add(1), moved);
        insertion.write(value);
    }
    vec.length += 1;
    OK
}

/// Inserts using an explicit reverse-copy loop instead of a `memmove` call.
///
/// # Safety
///
/// `vec` and its backing allocation must satisfy the documented `PairVec`
/// invariants and must be exclusively borrowed for this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn custom_pair_insert_loop(
    vec: *mut PairVec,
    index: u32,
    value: Pair,
) -> u32 {
    // SAFETY: The function's contract provides an exclusive live header.
    let vec = unsafe { &mut *vec };
    if vec.length > vec.capacity {
        return INVALID_LENGTH;
    }
    if index > vec.length {
        return INDEX_OUT_OF_BOUNDS;
    }
    if vec.length == vec.capacity {
        return FULL;
    }

    let mut source_index = vec.length;
    while source_index > index {
        source_index -= 1;
        // SAFETY: The source is initialized and the destination is no greater
        // than the spare element at `length` because `length < capacity`.
        unsafe {
            let moved = vec.data.add(source_index as usize).read();
            vec.data.add(source_index as usize + 1).write(moved);
        }
    }
    // SAFETY: `index <= length < capacity` puts the write inside the allocation.
    unsafe { vec.data.add(index as usize).write(value) };
    vec.length += 1;
    OK
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;

    #[test]
    fn heapless_opaque_wrappers_insert_and_report_full() {
        let mut vec = HeaplessU32::new();
        let storage = ptr::from_mut(&mut vec).cast::<c_void>();

        // SAFETY: `storage` points to the live, exclusively borrowed `vec`.
        assert_eq!(unsafe { heapless_u32_push(storage, 10) }, OK);
        // SAFETY: `storage` points to the live, exclusively borrowed `vec`.
        assert_eq!(unsafe { heapless_u32_push(storage, 30) }, OK);
        // SAFETY: `storage` points to the live, exclusively borrowed `vec`.
        assert_eq!(unsafe { heapless_u32_insert(storage, 1, 20) }, OK);
        assert_eq!(vec.as_slice(), &[10, 20, 30]);

        for value in 3..HEAPLESS_CAPACITY {
            // SAFETY: `storage` points to the live, exclusively borrowed `vec`.
            assert_eq!(unsafe { heapless_u32_push(storage, value as u32) }, OK);
        }
        // SAFETY: `storage` points to the live, exclusively borrowed `vec`.
        assert_eq!(unsafe { heapless_u32_push(storage, 99) }, FULL);
    }

    #[test]
    fn custom_u32_operations_and_failures() {
        let mut data = [10, 30, 0];
        let mut vec = U32Vec {
            data: data.as_mut_ptr(),
            length: 2,
            capacity: 3,
        };

        // SAFETY: `vec` points to the three-element `data` allocation.
        assert_eq!(unsafe { custom_u32_insert(&mut vec, 1, 20) }, OK);
        assert_eq!(&data, &[10, 20, 30]);
        assert_eq!(vec.length, 3);
        // SAFETY: The same valid vector remains live and exclusively borrowed.
        assert_eq!(unsafe { custom_u32_push(&mut vec, 40) }, FULL);
        // SAFETY: The same valid vector remains live and exclusively borrowed.
        assert_eq!(
            unsafe { custom_u32_insert(&mut vec, 4, 40) },
            INDEX_OUT_OF_BOUNDS
        );
    }

    #[test]
    fn custom_pair_operations() {
        let mut data = [
            Pair { key: 10, value: 1 },
            Pair { key: 30, value: 3 },
            Pair { key: 0, value: 0 },
        ];
        let mut vec = PairVec {
            data: data.as_mut_ptr(),
            length: 2,
            capacity: 3,
        };

        // SAFETY: `vec` points to the three-element `data` allocation.
        assert_eq!(
            unsafe { custom_pair_insert(&mut vec, 1, Pair { key: 20, value: 2 }) },
            OK
        );
        assert_eq!(data[1], Pair { key: 20, value: 2 });
        assert_eq!(data[2], Pair { key: 30, value: 3 });
    }

    #[test]
    fn explicit_loops_shift_every_successor() {
        let mut u32_data = [10, 20, 30, 0];
        let mut u32_vec = U32Vec {
            data: u32_data.as_mut_ptr(),
            length: 3,
            capacity: 4,
        };
        // SAFETY: `u32_vec` points to the four-element `u32_data` allocation.
        assert_eq!(unsafe { custom_u32_insert_loop(&mut u32_vec, 1, 15) }, OK);
        assert_eq!(u32_data, [10, 15, 20, 30]);

        let mut pair_data = [
            Pair { key: 10, value: 1 },
            Pair { key: 20, value: 2 },
            Pair { key: 30, value: 3 },
            Pair { key: 0, value: 0 },
        ];
        let mut pair_vec = PairVec {
            data: pair_data.as_mut_ptr(),
            length: 3,
            capacity: 4,
        };
        // SAFETY: `pair_vec` points to the four-element `pair_data` allocation.
        assert_eq!(
            unsafe { custom_pair_insert_loop(&mut pair_vec, 1, Pair { key: 15, value: 4 }) },
            OK
        );
        assert_eq!(pair_data[1], Pair { key: 15, value: 4 });
        assert_eq!(pair_data[2], Pair { key: 20, value: 2 });
        assert_eq!(pair_data[3], Pair { key: 30, value: 3 });
    }

    #[test]
    fn invalid_length_is_reported_before_memory_access() {
        let mut vec = U32Vec {
            data: ptr::null_mut(),
            length: 1,
            capacity: 0,
        };

        // SAFETY: The invalid length is detected before the null data pointer is used.
        assert_eq!(unsafe { custom_u32_push(&mut vec, 1) }, INVALID_LENGTH);
    }
}
