//! The production collection adapter for the extracted algorithm.

mod range_insert_algorithm;

use std::{collections::BTreeMap, ops::RangeInclusive};

use range_insert_algorithm::{DeletionKeys, Endpoint, Map, internal_add_baseline};

pub fn insert<T: Endpoint>(
    map: &mut BTreeMap<T, T>,
    length: &mut T::Length,
    range: RangeInclusive<T>,
) {
    internal_add_baseline(map, length, range, Vec::new());
}

impl<T: Endpoint> Map<T> for BTreeMap<T, T> {
    fn predecessor(&mut self, key: T) -> Option<(&T, &mut T)> {
        self.range_mut(..=key).next_back()
    }

    fn suffix(&mut self, key: T) -> impl Iterator<Item = (&T, &mut T)> {
        self.range_mut(key..)
    }

    fn insert_new(&mut self, start: T, end: T) {
        let previous = self.insert(start, end);
        debug_assert!(previous.is_none());
    }

    fn remove(&mut self, key: T) {
        self.remove(&key);
    }
}

impl<T> DeletionKeys<T> for Vec<T> {
    fn push(&mut self, key: T) {
        self.push(key);
    }

    fn is_empty(&self) -> bool {
        Vec::is_empty(self)
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, iter::Peekable};

    use super::insert;

    #[test]
    fn all_subsets_and_insertions_in_a_small_domain() {
        const WIDTH: u32 = 8;
        for original in 0u32..1 << WIDTH {
            for start in 0..WIDTH {
                for end in 0..WIDTH {
                    let mut map = ranges((0..WIDTH).filter(|point| original & (1 << point) != 0));
                    let mut length = u64::from(original.count_ones());
                    insert(&mut map, &mut length, start..=end);
                    let expected_points = (0..WIDTH).filter(|point| {
                        original & (1 << point) != 0 || (start..=end).contains(point)
                    });
                    assert_eq!(length, expected_points.clone().count() as u64);
                    assert_eq!(map, ranges(expected_points));
                }
            }
        }
    }

    #[test]
    fn full_domain_and_endpoint_extremes() {
        let mut map = BTreeMap::from([(0, 0), (u32::MAX, u32::MAX)]);
        let mut length = 2;
        insert(&mut map, &mut length, 1..=u32::MAX);
        insert(&mut map, &mut length, u32::MAX..=u32::MAX);
        assert_eq!(map, BTreeMap::from([(0, u32::MAX)]));
        assert_eq!(length, 1u64 << 32);
    }

    fn ranges(points: impl Iterator<Item = u32>) -> BTreeMap<u32, u32> {
        let mut points: Peekable<_> = points.peekable();
        let mut map = BTreeMap::new();
        while let Some(start) = points.next() {
            let mut end = start;
            while let Some(&next) = points.peek() {
                if end.checked_add(1) != Some(next) {
                    break;
                }
                end = next;
                points.next();
            }
            map.insert(start, end);
        }
        map
    }
}
