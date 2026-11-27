#![no_std]

//! A sorted map over `RawVec<Pair>`, with C entry points.
//!
//! The map's entries are the live elements of a `RawVec<Pair>`, ordered by
//! strictly increasing, unique keys. Lookup is a linear scan. Insertion and
//! removal find the entry with that scan and then call the verified
//! `raw_vec_pair_insert` and `raw_vec_pair_remove` to shift the suffix, so this
//! crate contains no shifting loop of its own.
//!
//! The four routines are what RangeSetBlaze's insertion algorithm needs from
//! an ordered map (see `docs/sorted-map.md`):
//!
//! | Routine | `BTreeMap` operation it backs |
//! | --- | --- |
//! | `sorted_map_lower_bound(map, key)` | position of `range(key..)` |
//! | `sorted_map_upper_bound(map, key)` | position after `range(..=key)` |
//! | `sorted_map_insert(map, entry)` | `insert(key, value)` |
//! | `sorted_map_remove(map, key)` | `remove(&key)` |
//!
//! Value updates and forward iteration from a position need no routine: the
//! caller reads and writes `data[index]` directly.
//!
//! This crate is compiled into its own object, linked after the RawVec
//! removal shims (see `build.rs`), so adding it moves none of the verified
//! RawVec routines or the verified calling shim's `call` offset.

pub mod header;

use header::{ABSENT, INVALID_LENGTH, Pair, REPLACED, RawVec};

unsafe extern "C" {
    fn raw_vec_pair_insert(vec: *mut RawVec<Pair>, index: u32, value: Pair) -> u32;
    fn raw_vec_pair_remove(vec: *mut RawVec<Pair>, index: u32) -> u32;
}

/// Return the number of leading entries whose key is less than `key`.
///
/// For a sorted map this is the index of the first entry with a key at least
/// `key`, or `length` if there is none. The routine reads the length word,
/// and, if the length is positive, the data pointer and the keys it compares.
/// It writes no memory and makes no calls.
///
/// # Safety
///
/// The header must be valid and aligned. If `length > 0`, the data pointer
/// must identify an aligned allocation with the first `length` elements
/// initialized. The routine does not read `capacity` and does not check
/// `length <= capacity`.
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn sorted_map_lower_bound(map: *const RawVec<Pair>, key: u32) -> u32 {
    // SAFETY: The caller supplies a valid header and its initialized prefix.
    unsafe { (&*map).partition_point(|entry| entry.key < key) }
}

/// Return the number of leading entries whose key is at most `key`.
///
/// For a sorted map, the entry before this index, if any, is the one with the
/// greatest key at most `key`: `BTreeMap::range(..=key).next_back()`.
///
/// # Safety
///
/// The same contract and memory accesses as `sorted_map_lower_bound`.
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn sorted_map_upper_bound(map: *const RawVec<Pair>, key: u32) -> u32 {
    // SAFETY: The caller supplies a valid header and its initialized prefix.
    unsafe { (&*map).partition_point(|entry| entry.key <= key) }
}

/// Insert `entry`, or replace the value of the entry with the same key.
///
/// Returns `INVALID_LENGTH` if `length > capacity`, without writing memory.
/// Otherwise it finds the insertion point with `sorted_map_lower_bound`. If
/// the entry there has the same key, it overwrites that entry and returns
/// `REPLACED`, even when the map is full. Otherwise it returns the status of
/// `raw_vec_pair_insert` at that index: `OK` after inserting, or `FULL`
/// without writing the map.
///
/// The routine saves five registers on the stack, below the caller's `sp`.
///
/// # Safety
///
/// The header must be valid, aligned and exclusively accessible. If
/// `length <= capacity`, the data pointer must identify an aligned,
/// exclusively accessible allocation for `capacity` elements, disjoint from
/// the header, with the first `length` elements initialized.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sorted_map_insert(map: *mut RawVec<Pair>, entry: Pair) -> u32 {
    // SAFETY: The caller supplies an exclusive header and its allocation.
    unsafe { RawVec::map_insert(map, entry) }
}

/// Remove the entry with `key`.
///
/// Returns `INVALID_LENGTH` if `length > capacity`, and `ABSENT` if no entry
/// has the key, both without writing the map. Otherwise it returns the status
/// of `raw_vec_pair_remove` at the entry's index, `OK`.
///
/// The routine saves four registers on the stack, below the caller's `sp`.
///
/// # Safety
///
/// The same contract as `sorted_map_insert`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sorted_map_remove(map: *mut RawVec<Pair>, key: u32) -> u32 {
    // SAFETY: The caller supplies an exclusive header and its allocation.
    unsafe { RawVec::map_remove(map, key) }
}

/// An element ordered by a key, with the verified routines for its vector.
///
/// The generic map code below calls these routines instead of inlining them,
/// so its machine code makes real calls to the verified instances.
pub trait Entry: Copy {
    type Key: Ord + Copy;

    fn key(&self) -> Self::Key;

    /// # Safety
    ///
    /// The contract of `sorted_map_lower_bound`.
    unsafe fn lower_bound(map: *const RawVec<Self>, key: Self::Key) -> u32;

    /// # Safety
    ///
    /// The contract of `raw_vec_pair_insert`.
    unsafe fn vec_insert(map: *mut RawVec<Self>, index: u32, entry: Self) -> u32;

    /// # Safety
    ///
    /// The contract of `raw_vec_pair_remove`.
    unsafe fn vec_remove(map: *mut RawVec<Self>, index: u32) -> u32;
}

impl Entry for Pair {
    type Key = u32;

    #[inline(always)]
    fn key(&self) -> u32 {
        self.key
    }

    #[inline(always)]
    unsafe fn lower_bound(map: *const RawVec<Self>, key: u32) -> u32 {
        // SAFETY: Forwarded from the caller.
        unsafe { sorted_map_lower_bound(map, key) }
    }

    #[inline(always)]
    unsafe fn vec_insert(map: *mut RawVec<Self>, index: u32, entry: Self) -> u32 {
        // SAFETY: Forwarded from the caller.
        unsafe { raw_vec_pair_insert(map, index, entry) }
    }

    #[inline(always)]
    unsafe fn vec_remove(map: *mut RawVec<Self>, index: u32) -> u32 {
        // SAFETY: Forwarded from the caller.
        unsafe { raw_vec_pair_remove(map, index) }
    }
}

impl<T: Entry> RawVec<T> {
    /// The number of leading elements for which `before` holds. A linear
    /// scan: no binary search, so the result does not depend on sortedness.
    #[inline(always)]
    unsafe fn partition_point(&self, before: impl Fn(&T) -> bool) -> u32 {
        let mut index = 0;
        while index < self.length {
            // SAFETY: `index < length`, and the first `length` elements are
            // initialized.
            if !before(unsafe { &*self.data.add(index as usize) }) {
                break;
            }
            index += 1;
        }
        index
    }

    #[inline(always)]
    unsafe fn map_insert(map: *mut Self, entry: T) -> u32 {
        // SAFETY: The caller supplies an exclusive header. The element reads
        // and the write are below `length <= capacity`.
        unsafe {
            if (*map).length > (*map).capacity {
                return INVALID_LENGTH;
            }
            let index = T::lower_bound(map, entry.key());
            if index < (*map).length {
                let slot = (*map).data.add(index as usize);
                if (*slot).key() == entry.key() {
                    slot.write(entry);
                    return REPLACED;
                }
            }
            T::vec_insert(map, index, entry)
        }
    }

    #[inline(always)]
    unsafe fn map_remove(map: *mut Self, key: T::Key) -> u32 {
        // SAFETY: The caller supplies an exclusive header. The element read
        // is below `length <= capacity`.
        unsafe {
            if (*map).length > (*map).capacity {
                return INVALID_LENGTH;
            }
            let index = T::lower_bound(map, key);
            if index < (*map).length && (*(*map).data.add(index as usize)).key() == key {
                return T::vec_remove(map, index);
            }
            ABSENT
        }
    }
}
