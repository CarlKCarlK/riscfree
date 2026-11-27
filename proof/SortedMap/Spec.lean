import RawVec.Insert

/-!
# An ordered map, mathematically

The specification the sorted-map routines are proved against. It is
independent of the machine code and of linear search: a map is a list of
`Pair` entries whose keys strictly increase (`Sorted`), and the operations are
defined by recursion on that list or by counting, never by scanning a buffer.

* `rank .lower entries key` is the number of entries whose key is below
  `key`, and `rank .upper entries key` the number whose key is at most `key`.
  For a sorted map these are the positions of `BTreeMap::range(key..)` and
  just after `BTreeMap::range(..=key)`.
* `lookup` finds the value stored for a key.
* `insert` adds an entry, replacing the value of an entry with the same key.
* `erase` removes the entry with a key, if any.

The map laws (`lookup_insert`, `lookup_erase`) and invariant preservation
(`sorted_insert`, `sorted_erase`) are proved here. `Split` and the lemmas
after it describe where an entry sits, which is what the machine-code
theorems connect to.
-/

namespace Riscfree.SortedMap

open Riscfree.RawVec

abbrev Word := BitVec 32

-- Keys strictly increase, so each key occurs at most once.
def Sorted (entries : List Pair) : Prop :=
  entries.Pairwise fun first second => first.key.toNat < second.key.toNat

-- Which entries a search passes over: those with a key below the search key
-- (`lower`), or at most the search key (`upper`).
inductive Bound
  | lower
  | upper
  deriving DecidableEq

def Bound.passes : Bound → Word → Word → Bool
  | .lower, entry, key => decide (entry.toNat < key.toNat)
  | .upper, entry, key => decide (entry.toNat ≤ key.toNat)

-- The number of entries a search passes over. Counting does not depend on
-- the order of the entries.
def rank (bound : Bound) (entries : List Pair) (key : Word) : Nat :=
  entries.countP fun entry => bound.passes entry.key key

def lookup (entries : List Pair) (key : Word) : Option Word :=
  (entries.find? fun entry => entry.key = key).map Pair.value

def insert : List Pair → Pair → List Pair
  | [], entry => [entry]
  | first :: rest, entry =>
    if entry.key.toNat < first.key.toNat then entry :: first :: rest
    else if entry.key = first.key then entry :: rest
    else first :: insert rest entry

def erase (entries : List Pair) (key : Word) : List Pair :=
  entries.filter fun entry => entry.key ≠ key

section Laws

theorem sorted_cons {first : Pair} {rest : List Pair} :
    Sorted (first :: rest) ↔ (∀ entry ∈ rest, first.key.toNat < entry.key.toNat) ∧ Sorted rest :=
  List.pairwise_cons

-- Every key that `insert` produces is the new key or an old one.
theorem mem_insert {entries : List Pair} {entry other : Pair} (member : other ∈ insert entries entry) :
    other = entry ∨ other ∈ entries := by
  induction entries with
  | nil => simpa [insert] using member
  | cons first rest previous =>
    simp only [insert] at member
    split at member
    · simpa using member
    · split at member
      · simp only [List.mem_cons] at member
        rcases member with same | inside
        · exact Or.inl same
        · exact Or.inr (List.mem_cons_of_mem _ inside)
      · simp only [List.mem_cons] at member
        rcases member with same | inside
        · exact Or.inr (same ▸ List.mem_cons_self)
        · rcases previous inside with same | old
          · exact Or.inl same
          · exact Or.inr (List.mem_cons_of_mem _ old)

theorem sorted_insert {entries : List Pair} (sorted : Sorted entries) (entry : Pair) :
    Sorted (insert entries entry) := by
  induction entries with
  | nil => exact List.pairwise_singleton _ _
  | cons first rest previous =>
    obtain ⟨below, restSorted⟩ := sorted_cons.mp sorted
    simp only [insert]
    split
    · exact sorted_cons.mpr ⟨fun other member => by
        simp only [List.mem_cons] at member
        rcases member with same | inside
        · rw [same]; assumption
        · exact Nat.lt_trans (by assumption) (below other inside), sorted⟩
    · split
      · rename_i same
        exact sorted_cons.mpr ⟨fun other inside => same ▸ below other inside, restSorted⟩
      · rename_i notBelow different
        have above : first.key.toNat < entry.key.toNat := by
          have : first.key.toNat ≠ entry.key.toNat := fun equal =>
            different (BitVec.eq_of_toNat_eq equal.symm)
          omega
        refine sorted_cons.mpr ⟨fun other member => ?_, previous restSorted⟩
        rcases mem_insert member with same | old
        · rw [same]; exact above
        · exact below other old

theorem sorted_erase {entries : List Pair} (sorted : Sorted entries) (key : Word) :
    Sorted (erase entries key) :=
  List.Pairwise.filter _ sorted

theorem lookup_insert {entries : List Pair} (sorted : Sorted entries) (entry : Pair) (key : Word) :
    lookup (insert entries entry) key = if key = entry.key then some entry.value else lookup entries key := by
  induction entries with
  | nil =>
    by_cases same : key = entry.key
    · simp [insert, lookup, same]
    · simp [insert, lookup, same, Ne.symm same]
  | cons first rest previous =>
    obtain ⟨below, restSorted⟩ := sorted_cons.mp sorted
    simp only [insert]
    split
    · rename_i smaller
      by_cases same : key = entry.key
      · simp [lookup, same]
      · simp [lookup, List.find?_cons, same, Ne.symm same]
    · split
      · rename_i equal
        by_cases same : key = entry.key
        · simp [lookup, same]
        · -- The replaced entry had the key `entry.key`, which is not `key`.
          have different : first.key ≠ key := fun eq => same (eq ▸ equal ▸ rfl)
          simp [lookup, same, Ne.symm same, different]
      · rename_i notBelow different
        have rest := previous restSorted
        by_cases same : key = entry.key
        · have firstOther : first.key ≠ key := by rw [same]; exact Ne.symm different
          simp only [lookup, List.find?_cons, firstOther, decide_false] at rest ⊢
          simpa [same] using rest
        · by_cases atFirst : first.key = key
          · simp [lookup, atFirst, same]
          · simp only [lookup, List.find?_cons, atFirst, decide_false] at rest ⊢
            simpa [same] using rest

theorem lookup_erase (entries : List Pair) (key other : Word) :
    lookup (erase entries key) other = if other = key then none else lookup entries other := by
  induction entries with
  | nil => simp [erase, lookup]
  | cons first rest previous =>
    simp only [erase, lookup] at previous ⊢
    by_cases kept : first.key = key
    · rw [List.filter_cons_of_neg (by simpa using kept), previous]
      by_cases same : other = key
      · simp [same]
      · have firstOther : first.key ≠ other := by rw [kept]; exact Ne.symm same
        simp [same, firstOther]
    · rw [List.filter_cons_of_pos (by simpa using kept)]
      by_cases same : other = key
      · subst same
        simp [kept, List.find?_filter]
      · simp only [same, if_false] at previous ⊢
        by_cases atFirst : first.key = other
        · simp [atFirst]
        · simp only [List.find?_cons, atFirst, decide_false]
          exact previous

end Laws

/-! ## Where an entry sits

`Split front back key` says the entries before `back` all have keys below
`key` and the entries in `back` have keys at least `key`. For a sorted map,
`rank .lower` gives that split.
-/

section Split

-- `back` without its head, if the head has `key`.
def dropHead (back : List Pair) (key : Word) : List Pair :=
  match back with
  | [] => []
  | first :: rest => if first.key = key then rest else first :: rest

structure Split (front back : List Pair) (key : Word) : Prop where
  below : ∀ entry ∈ front, entry.key.toNat < key.toNat
  atLeast : ∀ entry ∈ back, key.toNat ≤ entry.key.toNat

theorem insert_append {front back : List Pair} {entry : Pair}
    (below : ∀ other ∈ front, other.key.toNat < entry.key.toNat) :
    insert (front ++ back) entry = front ++ insert back entry := by
  induction front with
  | nil => rfl
  | cons first rest previous =>
    have firstBelow := below first List.mem_cons_self
    have notBelow : ¬ entry.key.toNat < first.key.toNat := by omega
    have different : entry.key ≠ first.key := fun same => by rw [same] at firstBelow; omega
    simp only [List.cons_append, insert, notBelow, different, if_false]
    rw [previous fun other inside => below other (List.mem_cons_of_mem _ inside)]

-- Inserting at the split: a new key goes before `back`, and an equal key
-- replaces the head of `back`.
theorem insert_split {front back : List Pair} {entry : Pair} (split : Split front back entry.key) :
    insert (front ++ back) entry = front ++ entry :: dropHead back entry.key := by
  rw [insert_append split.below]
  cases back with
  | nil => rfl
  | cons first rest =>
    have atLeast := split.atLeast first List.mem_cons_self
    simp only [insert]
    by_cases same : entry.key = first.key
    · have notBelow : ¬ entry.key.toNat < first.key.toNat := by rw [same]; omega
      simp [same, dropHead]
    · have below : entry.key.toNat < first.key.toNat := by
        have : entry.key.toNat ≠ first.key.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
        omega
      simp [below, dropHead, Ne.symm same]

-- Erasing at the split of a sorted map removes at most the head of `back`.
theorem erase_split {front back : List Pair} {key : Word} (split : Split front back key)
    (sorted : Sorted back) :
    erase (front ++ back) key = front ++ dropHead back key := by
  have keepFront : erase front key = front := by
    apply List.filter_eq_self.mpr
    intro entry inside
    have := split.below entry inside
    simp only [ne_eq, decide_eq_true_eq]
    intro same
    rw [same] at this
    omega
  unfold erase at keepFront ⊢
  rw [List.filter_append, keepFront]
  congr 1
  cases back with
  | nil => rfl
  | cons first rest =>
    obtain ⟨above, _⟩ := sorted_cons.mp sorted
    have firstAtLeast := split.atLeast first List.mem_cons_self
    -- Every later key exceeds the head's, so none equals `key`.
    have keepRest : rest.filter (fun entry => entry.key ≠ key) = rest := by
      apply List.filter_eq_self.mpr
      intro entry inside
      have := above entry inside
      simp only [ne_eq, decide_eq_true_eq]
      intro same
      rw [same] at this
      omega
    by_cases same : first.key = key
    · rw [List.filter_cons_of_neg (by simpa using same), keepRest, dropHead, if_pos same]
    · rw [List.filter_cons_of_pos (by simpa using same), keepRest, dropHead, if_neg same]

end Split

end Riscfree.SortedMap
