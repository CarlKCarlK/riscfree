import RangeSetBlaze.AlgoC
import RangeInsert.Nonempty.Predecessor

/-! The bounded map's live entries represent a canonical `RangeSetBlaze`
when, read in order, each entry's key and value are a range's start and
inclusive end. Under that representation the upper-bound rank selects the
same predecessor as the production model's `takeWhile`/`getLast?` split,
so the machine's covered-path test agrees with the model's branch. -/

namespace Riscfree.RangeInsert.Nonempty

open Riscfree.RawVec Riscfree.SortedMap
open RangeSetBlazeValidation RangeSetBlazeValidation.RangeSetBlaze RangeSetBlazeValidation.IntRange RangeSetBlazeValidation.IntRange.NR

def NR.endpoints (nr : NR) : Int × Int := (nr.val.lo, nr.val.hi)

def Pair.endpoints (pair : Pair) : Int × Int := (pair.key.toNat, pair.value.toNat)

/-- The machine's live entries, in order, are the set's ranges. -/
def Represents (s : RangeSetBlaze) (call : Call) : Prop :=
  s.ranges.map NR.endpoints = (entriesOf call.old call.length.toNat).map Pair.endpoints

/-- The input `start..=stop` as an integer range. -/
def Call.input (call : Call) : RangeSetBlazeValidation.IntRange := ⟨call.start.toNat, call.stop.toNat⟩

-- Canonical ranges start in strictly increasing order, so the entries are
-- sorted by key.
theorem Represents.sorted {s : RangeSetBlaze} {call : Call} (represents : Represents s call) :
    Sorted (entriesOf call.old call.length.toNat) := by
  have starts : (s.ranges.map NR.endpoints).Pairwise (fun first second => first.1 < second.1) :=
    List.pairwise_map.mpr (s.canonical.imp fun before => before_lo_lt before)
  rw [represents] at starts
  have keys := List.pairwise_map.mp starts
  exact keys.imp fun less => by
    simp only [Pair.endpoints] at less
    exact_mod_cast less

-- In a list sorted by key, the entries with key at most `key` are a prefix
-- whose length is the upper-bound rank.
theorem takeWhile_upper (entries : List Pair) (sorted : Sorted entries) (key : RawVec.Word) :
    entries.takeWhile (fun entry => Bound.passes .upper entry.key key) =
      entries.take (rank .upper entries key) := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨later, restSorted⟩ := List.pairwise_cons.mp sorted
    unfold rank
    by_cases passes : Bound.passes .upper first.key key = true
    · let atMost := fun entry : Pair => Bound.passes .upper entry.key key
      rw [List.takeWhile_cons_of_pos (p := atMost) passes,
        List.countP_cons_of_pos (p := atMost) passes, List.take_succ_cons]
      rw [ih restSorted]
      rfl
    · have none : rest.countP (fun entry => Bound.passes .upper entry.key key) = 0 := by
        rw [List.countP_eq_zero]
        intro entry member passesLater
        simp only [Bound.passes, decide_eq_true_eq] at passes passesLater
        have := later entry member
        omega
      let atMost := fun entry : Pair => Bound.passes .upper entry.key key
      rw [List.takeWhile_cons_of_neg (p := atMost) passes, List.countP_cons_of_neg (p := atMost) passes,
        none, List.take_zero]

/-- With a positive rank, the production model's predecessor is the range
stored in the entry before the rank. -/
theorem modelPredecessor {s : RangeSetBlaze} {call : Call} (represents : Represents s call)
    (found : 0 < call.rank) :
    ∃ predecessor : NR,
      (s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).getLast? =
        some predecessor ∧ predecessor.val.hi = call.predecessor.value.toNat := by
  let entries := entriesOf call.old call.length.toNat
  have sorted := represents.sorted
  have rankEq : call.rank = rank .upper entries call.start := scan_eq_rank sorted
  have rankBound := call.rank_le
  have length : entries.length = call.length.toNat := entriesOf_length _ _
  -- Both splits are the image of one split of the endpoint pairs.
  let atMost (pair : Int × Int) : Bool := decide (pair.1 ≤ (call.start.toNat : Int))
  have rangesSplit : (s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).map
      NR.endpoints = (s.ranges.map NR.endpoints).takeWhile atMost := by
    rw [List.takeWhile_map]
    rfl
  have entriesSplit : (entries.map Pair.endpoints).takeWhile atMost =
      (entries.take call.rank).map Pair.endpoints := by
    rw [List.takeWhile_map, rankEq, ← takeWhile_upper entries sorted call.start]
    congr 2
    funext entry
    simp only [Function.comp_apply, atMost, Pair.endpoints, Bound.passes, Nat.cast_le]
  have last : ((s.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).getLast?).map
      NR.endpoints = some (Pair.endpoints call.predecessor) := by
    rw [← List.getLast?_map, rangesSplit, represents, entriesSplit, List.getLast?_map,
      List.getLast?_take, if_neg (by omega), List.getElem?_eq_getElem (by omega)]
    simp only [Option.some_or, Option.map_some]
    rw [entriesOf_getElem]
    rfl
  obtain ⟨predecessor, found, endpoints⟩ := Option.map_eq_some_iff.mp last
  refine ⟨predecessor, found, ?_⟩
  have := congrArg Prod.snd endpoints
  exact this

/-- On the covered path the production model returns the set and the
cached count unchanged, which is what the machine does. -/
theorem containedModel {s : RangeSetBlaze} {call : Call} (cachedLength : Nat)
    (represents : Represents s call) (nonempty : call.start.toNat ≤ call.stop.toNat)
    (found : 0 < call.rank) (covered : call.stop.toNat ≤ call.predecessor.value.toNat) :
    internalAddProduction s cachedLength call.input = ⟨s, cachedLength⟩ := by
  obtain ⟨predecessor, last, ends⟩ := modelPredecessor represents found
  refine internalAddProduction_covered s cachedLength call.input ?_ predecessor last ?_
  · change (call.start.toNat : Int) ≤ call.stop.toNat
    exact_mod_cast nonempty
  · rw [ends]
    change (call.stop.toNat : Int) ≤ call.predecessor.value.toNat
    exact_mod_cast covered

/-- Leaving an accurate set and count unchanged is correct on the covered
path: the input adds nothing to the set, and the count stays its
cardinality. -/
theorem containedCorrect {s : RangeSetBlaze} {call : Call} {cachedLength : Nat}
    (represents : Represents s call) (accurate : cachedLength = s.cardinality)
    (nonempty : call.start.toNat ≤ call.stop.toNat)
    (found : 0 < call.rank) (covered : call.stop.toNat ≤ call.predecessor.value.toNat) :
    s.toSet = s.toSet ∪ call.input.toSet ∧ cachedLength = s.cardinality := by
  have correct := internalAddProduction_correct s cachedLength call.input accurate
  rw [containedModel cachedLength represents nonempty found covered] at correct
  exact correct

end Riscfree.RangeInsert.Nonempty
