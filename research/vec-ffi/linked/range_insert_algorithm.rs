//! Backend-independent extraction of RangeSetBlaze's baseline insertion.
//! Extracted from Carl M. Kadie's RangeSetBlaze, src/set.rs at
//! 6ae67451fc57f7b0c91692ff17c4d53b284dbec7, under MIT OR Apache-2.0.
//! See docs/range-insert.md for the correspondence.

use core::{
    cmp::max,
    ops::{AddAssign, RangeInclusive, SubAssign},
};

pub trait Endpoint: Copy + Ord + 'static {
    type Length: AddAssign + SubAssign;

    fn checked_add_one(self) -> Option<Self>;
    fn add_one(self) -> Self;
    fn sub_one(self) -> Self;
    fn safe_len(range: &RangeInclusive<Self>) -> Self::Length;
}

impl Endpoint for u32 {
    type Length = u64;

    fn checked_add_one(self) -> Option<Self> {
        self.checked_add(1)
    }

    fn add_one(self) -> Self {
        self + 1
    }

    fn sub_one(self) -> Self {
        self - 1
    }

    fn safe_len(range: &RangeInclusive<Self>) -> Self::Length {
        debug_assert!(range.start() <= range.end());
        u64::from(range.end().overflowing_sub(*range.start()).0) + 1
    }
}

pub trait Map<T: Endpoint> {
    fn predecessor(&mut self, key: T) -> Option<(&T, &mut T)>;
    fn suffix(&mut self, key: T) -> impl Iterator<Item = (&T, &mut T)>;
    fn insert_new(&mut self, start: T, end: T);
    fn remove(&mut self, key: T);
}

pub trait DeletionKeys<T>: IntoIterator<Item = T> {
    fn push(&mut self, key: T);
}

/// `deletion_keys` must initially be empty.
pub fn internal_add_baseline<T: Endpoint>(
    map: &mut impl Map<T>,
    length: &mut T::Length,
    range: RangeInclusive<T>,
    deletion_keys: impl DeletionKeys<T>,
) {
    let (start, end) = range.into_inner();
    if end < start {
        return;
    }
    if let Some((start_before, end_before)) = map.predecessor(start) {
        if end_before
            .checked_add_one()
            .is_some_and(|end_before_succ| end_before_succ < start)
        {
            internal_add2(map, length, start, end, deletion_keys);
        } else if *end_before < end {
            *length += T::safe_len(&(*end_before..=end.sub_one()));
            *end_before = end;
            let start_before = *start_before;
            delete_extra(map, length, start_before, end, deletion_keys);
        }
    } else {
        internal_add2(map, length, start, end, deletion_keys);
    }
}

#[inline]
fn internal_add2<T: Endpoint>(
    map: &mut impl Map<T>,
    length: &mut T::Length,
    start: T,
    end: T,
    deletion_keys: impl DeletionKeys<T>,
) {
    map.insert_new(start, end);
    delete_extra(map, length, start, end, deletion_keys);
    *length += T::safe_len(&(start..=end));
}

fn delete_extra<T: Endpoint>(
    map: &mut impl Map<T>,
    length: &mut T::Length,
    start: T,
    end: T,
    mut deletion_keys: impl DeletionKeys<T>,
) {
    let mut after = map.suffix(start);
    let Some((start_after, end_after)) = after.next() else {
        insertion_failed();
    };
    debug_assert!(start == *start_after && end == *end_after);

    let mut end_new = end;
    // The production map_while/collect stops at the first gap and pushes
    // each accepted key after accounting for its range.
    for (start_delete, end_delete) in after {
        // Short circuit before incrementing a maximum endpoint.
        if *start_delete <= end || *start_delete <= end.add_one() {
            end_new = max(end_new, *end_delete);
            *length -= T::safe_len(&(*start_delete..=*end_delete));
            deletion_keys.push(*start_delete);
        } else {
            break;
        }
    }
    if end_new > end {
        *length += T::safe_len(&(end..=end_new.sub_one()));
        *end_after = end_new;
    }
    for start in deletion_keys {
        map.remove(start);
    }
}

#[cold]
#[inline(always)]
pub(crate) fn insertion_failed() -> ! {
    #[cfg(target_arch = "riscv32")]
    // SAFETY: The illegal instruction terminates the insertion by trapping.
    // Both harnesses must treat this as a fatal error.
    unsafe {
        core::arch::asm!("unimp", options(noreturn, nomem, nostack));
    }
    #[cfg(not(target_arch = "riscv32"))]
    panic!("range insertion failed");
}
