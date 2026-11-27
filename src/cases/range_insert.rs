//! Cases shared by the two executable harnesses.

use crate::header::{Pair, RawVec};
use core::mem::MaybeUninit;

type Insert = unsafe extern "C" fn(*mut RawVec<Pair>, *mut u64, u32, u32, *mut u32, u32);

/// # Safety
///
/// `insert` must implement the linked range insertion routine's ABI and
/// accept the supplied initialized map and scratch storage.
pub unsafe fn run(insert: Insert) {
    let cases: &[Case] = &[
        Case::new(&[], (9, 8), &[], 0, 0),
        Case::new(&[], (5, 5), &[(5, 5)], 1, 0),
        Case::new(&[(4, 9)], (5, 7), &[(4, 9)], 1, 0),
        Case::new(&[(4, 9)], (4, 4), &[(4, 9)], 1, 0),
        Case::new(&[(4, 9)], (10, 11), &[(4, 11)], 1, 0),
        Case::new(&[(4, 9)], (2, 3), &[(2, 9)], 2, 1),
        Case::new(&[(4, 9)], (0, 1), &[(0, 1), (4, 9)], 2, 0),
        Case::new(&[(4, 9)], (11, 12), &[(4, 9), (11, 12)], 2, 0),
        Case::new(
            &[(0, 1), (4, 6), (9, 12)],
            (8, 8),
            &[(0, 1), (4, 6), (8, 12)],
            4,
            1,
        ),
        Case::new(
            &[(0, 1), (4, 6), (9, 12), (16, 17)],
            (2, 9),
            &[(0, 12), (16, 17)],
            4,
            2,
        ),
        Case::new(&[], (0, u32::MAX), &[(0, u32::MAX)], 1, 0),
        Case::new(
            &[(0, 0), (u32::MAX, u32::MAX)],
            (1, u32::MAX),
            &[(0, u32::MAX)],
            2,
            1,
        ),
        Case::new(
            &[(u32::MAX, u32::MAX)],
            (u32::MAX, u32::MAX),
            &[(u32::MAX, u32::MAX)],
            1,
            0,
        ),
    ];
    for (case_index, &case) in cases.iter().enumerate() {
        // SAFETY: The case provides the initial map and scratch allocation.
        unsafe { check(insert, case_index, case) };
    }
}

#[derive(Clone, Copy)]
struct Case {
    initial: &'static [(u32, u32)],
    input: (u32, u32),
    expected: &'static [(u32, u32)],
    map_capacity: u32,
    scratch_capacity: u32,
}

impl Case {
    const fn new(
        initial: &'static [(u32, u32)],
        input: (u32, u32),
        expected: &'static [(u32, u32)],
        map_capacity: u32,
        scratch_capacity: u32,
    ) -> Self {
        Self {
            initial,
            input,
            expected,
            map_capacity,
            scratch_capacity,
        }
    }
}

fn cardinality(entries: &[(u32, u32)]) -> u64 {
    entries
        .iter()
        .map(|&(start, end)| u64::from(end) - u64::from(start) + 1)
        .sum()
}

unsafe fn check(insert: Insert, case_index: usize, case: Case) {
    let mut entries = [MaybeUninit::uninit(); 4];
    let mut scratch = [MaybeUninit::<u32>::uninit(); 2];
    assert!(case.map_capacity as usize <= entries.len());
    assert!(case.scratch_capacity as usize <= scratch.len());
    assert!(case.initial.len() <= case.map_capacity as usize);
    for (slot, &(key, value)) in entries.iter_mut().zip(case.initial) {
        slot.write(Pair { key, value });
    }
    let mut map = RawVec {
        data: entries.as_mut_ptr().cast(),
        length: case.initial.len() as u32,
        capacity: case.map_capacity,
    };
    let mut length = cardinality(case.initial);
    let (start, end) = case.input;
    // SAFETY: The map and scratch regions are disjoint and sized for their
    // capacities. The map live prefix and cached cardinality are initialized.
    unsafe {
        insert(
            &mut map,
            &mut length,
            start,
            end,
            scratch.as_mut_ptr().cast(),
            case.scratch_capacity,
        );
    }
    assert_eq!(
        map.length as usize,
        case.expected.len(),
        "case {case_index}"
    );
    assert_eq!(length, cardinality(case.expected), "case {case_index}");
    for (slot, &(key, value)) in entries.iter().zip(case.expected) {
        // SAFETY: The routine initializes the live prefix before it returns.
        assert_eq!(
            unsafe { slot.assume_init() },
            Pair { key, value },
            "case {case_index}"
        );
    }
}
