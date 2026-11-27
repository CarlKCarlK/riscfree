#![no_std]

mod header;
mod range_insert_algorithm;

use core::{iter::Copied, marker::PhantomData, mem::MaybeUninit, slice};
use header::{OK, Pair, RawVec};
use range_insert_algorithm::{DeletionKeys, Map, internal_add_baseline};

unsafe extern "C" {
    fn raw_vec_u32_insert(vec: *mut RawVec<u32>, index: u32, value: u32) -> u32;
    fn sorted_map_lower_bound(map: *const RawVec<Pair>, key: u32) -> u32;
    fn sorted_map_upper_bound(map: *const RawVec<Pair>, key: u32) -> u32;
    fn sorted_map_insert(map: *mut RawVec<Pair>, entry: Pair) -> u32;
    fn sorted_map_remove(map: *mut RawVec<Pair>, key: u32) -> u32;
}

/// Insert into an inclusive range set with caller-owned map and scratch storage.
///
/// # Safety
///
/// The map header and its allocation must satisfy the sorted-map routines'
/// contracts. Its initialized prefix must consist of canonical ranges.
/// `length` must point to an aligned, initialized `u64` equal to the set's
/// cardinality. `scratch` must
/// point to an aligned allocation for `scratch_capacity` words (or be aligned
/// and nonnull at zero capacity). The two allocations must meet the Rust slice
/// size bounds. The headers and allocations must be mutually disjoint and
/// exclusively accessible for the call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn range_insert_u32(
    map: *mut RawVec<Pair>,
    length: *mut u64,
    start: u32,
    end: u32,
    scratch: *mut u32,
    scratch_capacity: u32,
) {
    // SAFETY: The caller supplies the exclusive map, cache, and scratch storage.
    unsafe {
        let scratch = slice::from_raw_parts_mut(
            scratch.cast::<MaybeUninit<u32>>(),
            scratch_capacity as usize,
        );
        internal_add_baseline(
            &mut BoundedMap(&mut *map),
            &mut *length,
            start..=end,
            BoundedKeys::new(scratch),
        );
    }
}

struct BoundedMap<'a>(&'a mut RawVec<Pair>);

impl Map<u32> for BoundedMap<'_> {
    fn predecessor(&mut self, key: u32) -> Option<(&u32, &mut u32)> {
        // SAFETY: The map header and its initialized prefix are valid. A
        // nonzero upper-bound rank is at most the length.
        unsafe {
            let rank = sorted_map_upper_bound(self.0, key);
            if rank == 0 {
                return None;
            }
            let entry = &mut *self.0.data.add((rank - 1) as usize);
            Some((&entry.key, &mut entry.value))
        }
    }

    fn suffix(&mut self, key: u32) -> impl Iterator<Item = (&u32, &mut u32)> {
        // SAFETY: The lower-bound rank is at most length, so the slice
        // consists of the initialized suffix and borrows the map exclusively.
        let entries = unsafe {
            let rank = sorted_map_lower_bound(self.0, key);
            slice::from_raw_parts_mut(
                self.0.data.add(rank as usize),
                (self.0.length - rank) as usize,
            )
        };
        entries
            .iter_mut()
            .map(|entry| (&entry.key, &mut entry.value))
    }

    fn insert_new(&mut self, start: u32, end: u32) {
        // SAFETY: The caller supplies an exclusive map and backing allocation.
        let status = unsafe {
            sorted_map_insert(
                self.0,
                Pair {
                    key: start,
                    value: end,
                },
            )
        };
        require_success(status);
    }

    fn remove(&mut self, key: u32) {
        // SAFETY: The caller supplies an exclusive map and backing allocation.
        let status = unsafe { sorted_map_remove(self.0, key) };
        require_success(status);
    }
}

struct BoundedKeys<'a> {
    raw: RawVec<u32>,
    storage: PhantomData<&'a mut [MaybeUninit<u32>]>,
}

impl<'a> BoundedKeys<'a> {
    fn new(storage: &'a mut [MaybeUninit<u32>]) -> Self {
        Self {
            raw: RawVec {
                data: storage.as_mut_ptr().cast(),
                length: 0,
                // The caller supplied a u32 capacity in the ABI.
                capacity: storage.len() as u32,
            },
            storage: PhantomData,
        }
    }
}

impl DeletionKeys<u32> for BoundedKeys<'_> {
    fn push(&mut self, key: u32) {
        let index = self.raw.length;
        // SAFETY: The caller supplies exclusive scratch storage, and the
        // vector initializes the prefix before increasing its length.
        let status = unsafe { raw_vec_u32_insert(&mut self.raw, index, key) };
        require_success(status);
    }

    fn is_empty(&self) -> bool {
        self.raw.length == 0
    }
}

impl<'a> IntoIterator for BoundedKeys<'a> {
    type Item = u32;
    type IntoIter = Copied<slice::Iter<'a, u32>>;

    fn into_iter(self) -> Self::IntoIter {
        // SAFETY: Push initialized the live prefix. Consuming this adapter
        // transfers its exclusive storage borrow to the shared iterator.
        unsafe { slice::from_raw_parts(self.raw.data, self.raw.length as usize) }
            .iter()
            .copied()
    }
}

fn require_success(status: u32) {
    if status != OK {
        range_insert_algorithm::insertion_failed();
    }
}
