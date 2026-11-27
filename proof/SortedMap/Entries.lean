import SortedMap.Search

/-!
# Buffer contents as ordered-map entries

The machine-code theorems describe a buffer pointwise: the element at each
index. This module turns those descriptions into lists (`entriesOf`) and shows
that, for a sorted map, the contents that `raw_vec_pair_remove` and
`raw_vec_pair_insert` leave at the lower-bound position are exactly the
mathematical `erase` and `insert` of `SortedMap/Spec.lean`.
-/

namespace Riscfree.SortedMap

open Riscfree.RawVec

-- The entries from `start`, `count` of them.
def entriesFrom (old : Nat → Pair) (start count : Nat) : List Pair :=
  (List.range count).map fun offset => old (start + offset)

theorem entriesOf_split (old : Nat → Pair) {position length : Nat} (le : position ≤ length) :
    entriesOf old length = entriesOf old position ++ entriesFrom old position (length - position) := by
  unfold entriesOf entriesFrom
  conv => lhs; rw [show length = position + (length - position) by omega]
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem entriesFrom_succ (old : Nat → Pair) (start count : Nat) :
    entriesFrom old start (count + 1) = old start :: entriesFrom old (start + 1) count := by
  unfold entriesFrom
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, Function.comp_def, Nat.succ_eq_add_one]
  congr 1
  apply List.map_congr_left
  intro offset _
  rw [Nat.add_assoc, Nat.add_comm 1 offset]

theorem entriesOf_congr {old other : Nat → Pair} {length : Nat}
    (same : ∀ index < length, other index = old index) :
    entriesOf other length = entriesOf old length := by
  unfold entriesOf
  apply List.map_congr_left
  intro index inside
  exact same index (List.mem_range.mp inside)

theorem entriesFrom_congr {old other : Nat → Pair} {start count : Nat}
    (same : ∀ offset < count, other (start + offset) = old (start + offset)) :
    entriesFrom other start count = entriesFrom old start count := by
  unfold entriesFrom
  apply List.map_congr_left
  intro offset inside
  exact same offset (List.mem_range.mp inside)

theorem mem_entriesFrom {old : Nat → Pair} {start count : Nat} {entry : Pair}
    (member : entry ∈ entriesFrom old start count) : ∃ offset < count, entry = old (start + offset) := by
  unfold entriesFrom at member
  obtain ⟨offset, inside, same⟩ := List.mem_map.mp member
  exact ⟨offset, List.mem_range.mp inside, same.symm⟩

-- The lower-bound scan splits a sorted map at the search key.
theorem lowerSplit {old : Nat → Pair} {length : Nat} (key : Word)
    (sorted : Sorted (entriesOf old length)) :
    let position := scan .lower key old 0 length
    Split (entriesOf old position) (entriesFrom old position (length - position)) key := by
  intro position
  have bounds := scan_bounds (bound := .lower) (key := key) (old := old) 0 length
  refine ⟨fun entry member => ?_, fun entry member => ?_⟩
  · unfold entriesOf at member
    obtain ⟨index, inside, same⟩ := List.mem_map.mp member
    have passes := scan_passes (bound := .lower) (key := key) (old := old) 0 length index (by omega)
      (List.mem_range.mp inside)
    simp only [Bound.passes, decide_eq_true_eq] at passes
    rw [← same]
    exact passes
  · obtain ⟨offset, inside, same⟩ := mem_entriesFrom member
    rw [same]
    have stops := scan_stops (bound := .lower) (key := key) (old := old) 0 length (by
      change position < 0 + length; omega)
    simp only [Bound.passes, decide_eq_false_iff_not, Nat.not_lt] at stops
    change key.toNat ≤ (old position).key.toNat at stops
    by_cases first : offset = 0
    · rw [first, Nat.add_zero]; exact stops
    · have larger := sorted_entriesOf sorted (show position < position + offset by omega) (by omega)
      omega

-- The entries after the position of a sorted map are sorted.
theorem sorted_entriesFrom {old : Nat → Pair} {length position : Nat} (le : position ≤ length)
    (sorted : Sorted (entriesOf old length)) :
    Sorted (entriesFrom old position (length - position)) := by
  rw [entriesOf_split old le] at sorted
  exact (List.pairwise_append.mp sorted).2.1

end Riscfree.SortedMap
