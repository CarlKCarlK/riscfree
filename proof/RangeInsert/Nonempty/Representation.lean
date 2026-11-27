import RangeInsert.Nonempty.Correspondence
import RangeInsert.Nonempty.Fresh.ToHelper
import RangeInsert.Nonempty.Extension.Layout

/-! Index correspondence between a canonical RangeSetBlaze range list and
the initialized entries of the concrete map. -/

namespace Riscfree.RangeInsert.Nonempty

open RangeSetBlazeValidation RangeSetBlazeValidation.IntRange RangeSetBlazeValidation.RangeSetBlaze
open Riscfree.RawVec (Word Pair)
open Riscfree.SortedMap

theorem Represents.length {set : RangeSetBlaze} {call : Call} (represents : Represents set call) :
    set.ranges.length = call.length.toNat := by
  have length := congrArg List.length represents
  simpa only [List.length_map, entriesOf_length] using length

theorem Represents.wordsAt {set : RangeSetBlaze} {call : Call} (represents : Represents set call)
    (index : Nat) (inside : index < set.ranges.length) :
    set.ranges[index].val.lo = ((call.old index).key.toNat : Int) ∧
    set.ranges[index].val.hi = ((call.old index).value.toNat : Int) := by
  have bound : index < (entriesOf call.old call.length.toNat).length := by
    rw [entriesOf_length, ← represents.length]
    exact inside
  have same := congrArg (fun list : List (Int × Int) => list[index]?) represents
  simp only [List.getElem?_map, List.getElem?_eq_getElem inside, List.getElem?_eq_getElem bound,
    Option.map_some, Option.some.injEq, entriesOf_getElem, NR.endpoints, Pair.endpoints, Prod.mk.injEq] at same
  exact same

theorem Represents.ordered {set : RangeSetBlaze} {call : Call} (represents : Represents set call) :
    ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat := by
  intro index inside
  have located : index < set.ranges.length := by rw [represents.length]; exact inside
  obtain ⟨start, stop⟩ := represents.wordsAt index located
  have order : set.ranges[index].val.lo ≤ set.ranges[index].val.hi := set.ranges[index].property
  rw [start, stop] at order
  exact_mod_cast order

theorem Represents.takeUpper {set : RangeSetBlaze} {call : Call} (represents : Represents set call) :
    set.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo)) = set.ranges.take call.rank := by
  let entries := entriesOf call.old call.length.toNat
  let atMost (pair : Int × Int) : Bool := decide (pair.1 ≤ call.input.lo)
  have fromList : (set.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).map NR.endpoints =
      (set.ranges.map NR.endpoints).takeWhile atMost := by
    rw [List.takeWhile_map]
    rfl
  have fromMap : (entries.map Pair.endpoints).takeWhile atMost = (entries.take call.rank).map Pair.endpoints := by
    have rank : call.rank = SortedMap.rank .upper entries call.start := scan_eq_rank represents.sorted
    rw [List.takeWhile_map, rank, ← takeWhile_upper entries represents.sorted call.start]
    congr 2
    funext entry
    simp only [Function.comp_apply, atMost, Pair.endpoints, Call.input, Bound.passes, Nat.cast_le]
  have lengths : (set.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).length = call.rank := by
    have equality := congrArg List.length (fromList.trans ((congrArg (List.takeWhile atMost) represents).trans fromMap))
    simp only [List.length_map, List.length_take] at equality
    have bound := call.rank_le
    have size : entries.length = call.length.toNat := entriesOf_length _ _
    exact equality.trans (min_eq_left (by omega))
  rw [← lengths]
  exact List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)

private theorem takeWhileAgrees {α : Type} {first second : α → Bool} (list : List α)
    (agrees : ∀ item ∈ list, first item = second item) :
    list.takeWhile first = list.takeWhile second := by
  induction list with
  | nil => rfl
  | cons head rest ih =>
    have same := agrees head (by simp)
    have tail := ih fun item member => agrees item (by simp [member])
    simp only [List.takeWhile, same, tail]

theorem Represents.takeFresh {set : RangeSetBlaze} {call : Call} (represents : Represents set call)
    (absent : ∀ index < call.length.toNat, (call.old index).key ≠ call.start) :
    set.ranges.takeWhile (fun nr => decide (nr.val.lo < call.input.lo)) = set.ranges.take call.rank := by
  rw [← represents.takeUpper]
  apply takeWhileAgrees
  intro item member
  obtain ⟨index, inside, atIndex⟩ := List.mem_iff_getElem.mp member
  obtain ⟨lo, _⟩ := represents.wordsAt index inside
  rw [atIndex] at lo
  have miss := absent index (by rw [← represents.length]; exact inside)
  have unequal : (call.old index).key.toNat ≠ call.start.toNat :=
    fun same => miss (BitVec.eq_of_toNat_eq same)
  rw [lo]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Call.input, Nat.cast_lt, Nat.cast_le]
  omega

theorem Call.freshRank {call : Call} {capacity : RawVec.Word}
    (sorted : Sorted (entriesOf call.old call.length.toNat))
    (absent : ∀ index < call.length.toNat, (call.old index).key ≠ call.start) :
    (call.freshInsert capacity).position = call.rank := by
  let entries := entriesOf call.old call.length.toNat
  change scan .lower call.start call.old 0 call.length.toNat =
    scan .upper call.start call.old 0 call.length.toNat
  rw [scan_eq_rank sorted, scan_eq_rank sorted]
  unfold SortedMap.rank
  apply List.countP_congr
  intro entry member
  obtain ⟨index, inside, same⟩ := List.mem_iff_getElem.mp member
  rw [entriesOf_getElem] at same
  have indexBound : index < call.length.toNat := by rw [entriesOf_length] at inside; exact inside
  subst entry
  have unequal : (call.old index).key.toNat ≠ call.start.toNat :=
    fun same => absent index indexBound (BitVec.eq_of_toNat_eq same)
  simp only [Bound.passes, decide_eq_true_eq]
  omega

theorem Represents.freshInput {set : RangeSetBlaze} {call : Call} {capacity low high : RawVec.Word}
    {initial : Empty.Snapshot} (represents : Represents set call)
    (nonempty : call.start.toNat ≤ call.stop.toNat)
    (absent : ∀ index < call.length.toNat, (call.old index).key ≠ call.start)
    (spare : call.length.toNat < capacity.toNat) :
    let helper := call.freshHelper capacity initial low high
    let input : NR := ⟨call.input, by
      change (call.start.toNat : Int) ≤ call.stop.toNat
      exact_mod_cast nonempty⟩
    (set.ranges.take call.rank ++ input :: set.ranges.drop call.rank).map NR.endpoints =
      (entriesOf helper.old helper.length.toNat).map Pair.endpoints := by
  let insertion := call.freshInsert capacity
  let front := entriesOf call.old call.rank
  let back := entriesFrom call.old call.rank (call.length.toNat - call.rank)
  let input : NR := ⟨call.input, by
      change (call.start.toNat : Int) ≤ call.stop.toNat
      exact_mod_cast nonempty⟩
  have full : entriesOf call.old call.length.toNat = front ++ back :=
    entriesOf_split call.old call.rank_le
  have frontSize : (front.map Pair.endpoints).length = call.rank := by
    simp only [front, List.length_map, entriesOf_length]
  have frontMap : (set.ranges.take call.rank).map NR.endpoints = front.map Pair.endpoints := by
    rw [List.map_take, represents, full, List.map_append, ← frontSize, List.take_left]
  have backMap : (set.ranges.drop call.rank).map NR.endpoints = back.map Pair.endpoints := by
    rw [List.map_drop, represents, full, List.map_append, ← frontSize, List.drop_left]
  have keyAbsent (entry : Pair) (member : entry ∈ back) : entry.key ≠ call.start := by
    have present := List.mem_append_right front member
    change entry ∈ front ++ back at present
    change entriesOf call.old call.length.toNat = front ++ back at full
    rw [← full, entriesOf, List.mem_map] at present
    obtain ⟨index, inside, same⟩ := present
    rw [← same]
    exact absent index (List.mem_range.mp inside)
  have noDrop : dropHead back call.start = back := by
    cases parts : back with
    | nil => rfl
    | cons first rest =>
      have miss := keyAbsent first (by rw [parts]; exact List.mem_cons_self ..)
      simp only [dropHead, if_neg miss]
  have split : Split front back call.start := by
    have actual := lowerSplit call.start represents.sorted
    rw [show scan .lower call.start call.old 0 call.length.toNat = call.rank from Call.freshRank (capacity := capacity) represents.sorted absent] at actual
    exact actual
  have inserted : insert (entriesOf call.old call.length.toNat) insertion.value =
      front ++ insertion.value :: back := by
    have insertionKeys : insertion.value.key = call.start := rfl
    rw [full]
    have outcome := insert_split (entry := insertion.value) (insertionKeys.symm ▸ split)
    rw [insertionKeys, noDrop] at outcome
    exact outcome
  have update := (SortedMap.Insert.sortedMapInsertUpdates insertion represents.sorted).2
    (Call.freshDoesNotReplace capacity absent) (Call.freshVectorValid capacity spare)
  change (set.ranges.take call.rank ++ input :: set.ranges.drop call.rank).map NR.endpoints =
    (entriesOf insertion.vector.result (call.freshHelper capacity initial low high).length.toNat).map Pair.endpoints
  rw [call.freshHelperLength capacity initial low high spare]
  change _ = (entriesOf insertion.vector.result (insertion.length.toNat + 1)).map Pair.endpoints
  rw [update]
  change _ = (insert (entriesOf call.old call.length.toNat) insertion.value).map Pair.endpoints
  rw [inserted, List.map_append, List.map_append, List.map_cons, List.map_cons, frontMap, backMap]
  rfl

theorem Represents.extensionInput {set : RangeSetBlaze} {call : Call} {low high : RawVec.Word}
    {initial : Empty.Snapshot} (represents : Represents set call)
    (before pending : List NR) (old selected : NR)
    (split : set.ranges = before ++ old :: pending)
    (position : before.length = call.rank - 1)
    (sameStart : selected.val.lo = old.val.lo)
    (newEnd : selected.val.hi = call.stop.toNat) :
    let helper := call.extensionHelper initial low high
    (before ++ selected :: pending).map NR.endpoints =
      (entriesOf helper.old helper.length.toNat).map Pair.endpoints := by
  let list := set.ranges
  have index : before.length < set.ranges.length := by rw [split, List.length_append, List.length_cons]; omega
  have replaced : before ++ selected :: pending = list.set (call.rank - 1) selected := by
    change _ = set.ranges.set (call.rank - 1) selected
    rw [← position, split, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  have oldWord := (represents.wordsAt before.length index).1
  have atOld : set.ranges[before.length] = old := by
    have located : (before ++ old :: pending)[before.length] = old := by
      simp only [List.getElem_append_right (Nat.le_refl before.length), Nat.sub_self, List.getElem_cons_zero]
    have equality := congrArg (fun ranges : List NR => ranges[before.length]?) split
    change set.ranges[before.length]? = (before ++ old :: pending)[before.length]? at equality
    have bound : before.length < (before ++ old :: pending).length := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [List.getElem?_eq_getElem index, List.getElem?_eq_getElem bound, located] at equality
    exact Option.some.inj equality
  rw [atOld, position] at oldWord
  have endpoint : NR.endpoints selected =
      Pair.endpoints ⟨(call.old (call.rank - 1)).key, call.stop⟩ := Prod.ext (sameStart.trans oldWord) newEnd
  rw [replaced, List.map_set]
  change (set.ranges.map NR.endpoints).set (call.rank - 1) (NR.endpoints selected) =
    (entriesOf call.extendedEntries call.length.toNat).map Pair.endpoints
  rw [represents, endpoint]
  apply List.ext_getElem
  · simp only [List.length_set, List.length_map, entriesOf_length]
  · intro index _ _
    simp only [List.getElem_set, List.getElem_map, entriesOf_getElem, Call.extendedEntries]
    split
    · rename_i equal
      subst index
      simp
    · rename_i different
      have other : index ≠ call.rank - 1 := Ne.symm different
      simp [other]

end Riscfree.RangeInsert.Nonempty
