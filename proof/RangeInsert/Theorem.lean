import RangeInsert.Correct
import RangeInsert.DeleteExtra.Model
import RangeInsert.Nonempty.Representation

/-! The linked range insertion against the production model. Every
successful path leaves a map that represents the model's result and a cache
that holds its cached count, so the returned map is the canonical union and
the cache is its cardinality. -/

namespace Riscfree.RangeInsert.Nonempty

open RangeSetBlazeValidation RangeSetBlazeValidation.IntRange RangeSetBlazeValidation.RangeSetBlaze
open Riscfree.RawVec (Word Pair)
open Riscfree.SortedMap (entriesOf Sorted)
open LeanRV32D RV32IM
open Riscfree.RV32
open Empty (Snapshot)

/-- A machine result represents a model result: the live entries are its
ranges in order, and the two cache words hold its cached count. -/
def Result.Represents (result : Result) (model : CLenResult) : Prop :=
  (entriesOf result.entries result.length.toNat).map Pair.endpoints =
      model.setResult.ranges.map NR.endpoints ∧
    (BitVec.append result.high result.low).toNat = model.cachedLength

-- The model leaves an empty input's set and count unchanged.
theorem emptyModel (set : RangeSetBlaze) (cached : Nat) (input : RangeSetBlazeValidation.IntRange)
    (empty : input.hi < input.lo) :
    (internalAddProduction set cached input).setResult.ranges = set.ranges ∧
      (internalAddProduction set cached input).cachedLength = cached := by
  unfold internalAddProduction internalAddProductionRaw
  simp [dif_pos empty]

theorem unchangedRepresents {set : RangeSetBlaze} {call : Call} (represents : Represents set call)
    (count : Nat) (low high : Word) (model : CLenResult)
    (ranges : model.setResult.ranges = set.ranges)
    (cached : model.cachedLength = (BitVec.append high low).toNat) :
    (Result.unchanged call count low high).Represents model :=
  ⟨by rw [ranges]; exact represents.symm, cached.symm⟩

-- A suffix of a range list costs no more than the whole list.
theorem rangesCardinality_suffix (before : List NR) (middle : NR) (pending : List NR) :
    rangesCardinality pending ≤ rangesCardinality (before ++ middle :: pending) := by
  simp only [rangesCardinality_append, rangesCardinality_cons]
  omega

-- Every represented range lies in the u32 domain.
theorem Represents.bounds {set : RangeSetBlaze} {call : Call} (represents : Represents set call) :
    ∀ range ∈ set.ranges, 0 ≤ range.val.lo ∧ range.val.hi ≤ 4294967295 := by
  intro range member
  have mapped : NR.endpoints range ∈ (entriesOf call.old call.length.toNat).map Pair.endpoints := by
    rw [← represents]; exact List.mem_map_of_mem member
  obtain ⟨pair, _, same⟩ := List.mem_map.mp mapped
  have lo := congrArg Prod.fst same
  have hi := congrArg Prod.snd same
  simp only [Pair.endpoints, NR.endpoints] at lo hi
  have bound := pair.value.isLt
  constructor
  · rw [← lo]; exact Int.natCast_nonneg _
  · rw [← hi]; change ((pair.value.toNat : Nat) : Int) ≤ ((4294967295 : Nat) : Int)
    exact_mod_cast (by omega : pair.value.toNat ≤ 4294967295)

theorem Represents.cardinalityFits {set : RangeSetBlaze} {call : Call} (represents : Represents set call) :
    set.cardinality ≤ 2 ^ 32 :=
  cardinalityFitsU32Domain set represents.bounds

set_option maxHeartbeats 2000000 in
/-- On the extension path, the helper's result represents the model's
extension of the predecessor. -/
theorem extensionRepresents {set : RangeSetBlaze} {call : Call} {initial : Empty.Snapshot}
    {low high : Word} (count : Nat) (represents : Represents set call)
    (sorted : Sorted (entriesOf call.old call.length.toNat))
    (accurate : (BitVec.append high low).toNat = set.cardinality)
    (nonempty : call.start.toNat ≤ call.stop.toNat) (found : 0 < call.rank)
    (touches : ¬ call.predecessor.value.toNat + 1 < call.start.toNat)
    (grows : call.predecessor.value.toNat < call.stop.toNat) :
    let helper := call.extensionHelper initial low high
    (Result.afterHelper helper count (helper.finalLow helper.acceptCount)
        (helper.finalHigh helper.acceptCount)).Represents
      (internalAddProduction set (BitVec.append high low).toNat call.input) := by
  intro helper
  obtain ⟨predecessor, last, ends⟩ := modelPredecessor represents found
  have nonemptyModel : call.input.lo ≤ call.input.hi := by
    change (call.start.toNat : Int) ≤ call.stop.toNat; exact_mod_cast nonempty
  have touchesModel : ¬ predecessor.val.hi + 1 < call.input.lo := by
    rw [ends]; change ¬ ((call.predecessor.value.toNat : Int) + 1 < call.start.toNat)
    exact_mod_cast touches
  have growsModel : predecessor.val.hi < call.input.hi := by
    rw [ends]; change (call.predecessor.value.toNat : Int) < call.stop.toNat; exact_mod_cast grows
  obtain ⟨rangesEq, cachedEq⟩ :=
    internalAddProduction_extension set (BitVec.append high low).toNat call.input nonemptyModel
      predecessor last touchesModel growsModel
  let atMost := fun nr : NR => decide (nr.val.lo ≤ call.input.lo)
  let prefixRanges := set.ranges.takeWhile atMost
  let after := set.ranges.dropWhile atMost
  -- The ranges split around the predecessor.
  have lastSplit : prefixRanges = prefixRanges.dropLast ++ [predecessor] := by
    have := List.dropLast_append_getLast? (l := prefixRanges) predecessor last
    exact this.symm
  have split : set.ranges = prefixRanges.dropLast ++ predecessor :: after := by
    have whole := List.takeWhile_append_dropWhile (p := atMost) (l := set.ranges)
    change prefixRanges ++ after = set.ranges at whole
    rw [lastSplit, List.append_assoc] at whole
    exact whole.symm
  have rankBound := call.rank_le
  have prefixLength : prefixRanges.length = call.rank := by
    change (set.ranges.takeWhile atMost).length = _
    rw [represents.takeUpper, List.length_take, represents.length]
    omega
  have position : prefixRanges.dropLast.length = call.rank - 1 := by
    rw [List.length_dropLast, prefixLength]
  let selected : NR := ⟨⟨predecessor.val.lo, call.input.hi⟩, predecessor.property.trans growsModel.le⟩
  have represented := represents.extensionInput (initial := initial) (low := low) (high := high)
    prefixRanges.dropLast after predecessor selected split position rfl rfl
  have helperPosition : helper.position = call.rank - 1 := call.extensionPosition sorted found initial low high
  have helperFound : helper.position < helper.length.toNat := by
    rw [helperPosition]; change call.rank - 1 < call.length.toNat; omega
  -- The helper starts from the count after the right extension.
  have cardinalityFits := represents.cardinalityFits
  have extension : rightExtensionCardinality predecessor.val.hi call.input.hi =
      call.stop.toNat - call.predecessor.value.toNat := by
    rw [ends]
    unfold rightExtensionCardinality
    change cardinality ⟨(call.predecessor.value.toNat : Int), (call.stop.toNat : Int) - 1⟩ = _
    rw [cardinality_of_nonempty (by change (call.predecessor.value.toNat : Int) ≤ (call.stop.toNat : Int) - 1; omega)]
    simp only
    omega
  have helperCache : (BitVec.append helper.high helper.low).toNat =
      (BitVec.append high low).toNat + rightExtensionCardinality predecessor.val.hi call.input.hi := by
    rw [extension]
    exact DeleteExtra.addExtension high low call.predecessor.value call.stop grows (by omega)
  have budget : rangesCardinality after ≤ (BitVec.append helper.high helper.low).toNat := by
    have suffix := rangesCardinality_suffix prefixRanges.dropLast predecessor after
    rw [← split] at suffix
    change rangesCardinality after ≤ set.cardinality at suffix
    rw [helperCache]; omega
  have enough := helper.enoughForSuffix helperFound prefixRanges.dropLast after selected
    (by rw [position, helperPosition]) represented budget
  have endNewBound := (helper.progress helper.acceptCount).endNew.isLt
  have fits : (BitVec.append helper.high helper.low).toNat +
      ((helper.progress helper.acceptCount).endNew.toNat - helper.stop.toNat) < 2 ^ 64 := by
    rw [helperCache, extension]; omega
  have matched := helper.entriesMatch helperFound prefixRanges.dropLast after selected
    (by rw [position, helperPosition]) rfl represented enough fits
  dsimp only at matched
  -- The model's result is the helper's.
  have modelEq : extendPredecessorProduction prefixRanges after predecessor ⟨call.input, nonemptyModel⟩
      (BitVec.append high low).toNat growsModel =
      ⟨prefixRanges.dropLast ++
        (finishDeleteExtraProduction selected after (BitVec.append helper.high helper.low).toNat).current ::
          (finishDeleteExtraProduction selected after (BitVec.append helper.high helper.low).toNat).pending,
        (finishDeleteExtraProduction selected after (BitVec.append helper.high helper.low).toNat).cachedLength⟩ := by
    rw [helperCache]
    rfl
  rw [modelEq] at rangesEq cachedEq
  refine ⟨?_, ?_⟩
  · rw [rangesEq, Result.afterHelperLength]
    exact matched.1.symm
  · rw [cachedEq]
    exact matched.2.symm

-- Adding the fresh input's width to a count that leaves room.
theorem freshCacheValue (low high distance : Word)
    (fits : (BitVec.append high low).toNat + distance.toNat + 1 < 2 ^ 64) :
    (BitVec.append (freshHigh low high distance) (freshLow low distance)).toNat =
      (BitVec.append high low).toNat + distance.toNat + 1 := by
  have added := congrArg BitVec.toNat (freshCacheAddition low high distance)
  change (BitVec.append (freshHigh low high distance) (freshLow low distance)).toNat =
    ((BitVec.append high low) + (BitVec.append 0#32 distance) + 1#64).toNat at added
  rw [added, BitVec.toNat_add, BitVec.toNat_add]
  have zeroHigh : (BitVec.append 0#32 distance).toNat = distance.toNat := by
    change (0#32 ++ distance).toNat = _
    rw [BitVec.toNat_append]; simp
  rw [zeroHigh]
  have one : (1#64).toNat = 1 := rfl
  rw [one]
  omega

set_option maxHeartbeats 2000000 in
/-- On the fresh path, the helper's result plus the input width represents
the model's fresh insertion. -/
theorem freshRepresents {set : RangeSetBlaze} {call : Call} {initial : Empty.Snapshot}
    {capacity low high : Word} (count : Nat) (represents : Represents set call)
    (sorted : Sorted (entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (accurate : (BitVec.append high low).toNat = set.cardinality)
    (nonempty : call.start.toNat ≤ call.stop.toNat)
    (absent : ∀ index < call.length.toNat, (call.old index).key ≠ call.start)
    (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces)
    (freshModel : (set.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).getLast? = none ∨
      ∃ predecessor : NR,
        (set.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).getLast? = some predecessor ∧
          predecessor.val.hi + 1 < call.input.lo) :
    let helper := call.freshHelper capacity initial low high
    (Result.afterHelper helper count
        (freshLow (helper.finalLow helper.acceptCount) (call.stop - call.start))
        (freshHigh (helper.finalLow helper.acceptCount) (helper.finalHigh helper.acceptCount)
          (call.stop - call.start))).Represents
      (internalAddProduction set (BitVec.append high low).toNat call.input) := by
  intro helper
  have nonemptyModel : call.input.lo ≤ call.input.hi := by
    change (call.start.toNat : Int) ≤ call.stop.toNat; exact_mod_cast nonempty
  obtain ⟨rangesEq, cachedEq⟩ :=
    internalAddProduction_fresh set (BitVec.append high low).toNat call.input nonemptyModel freshModel
  let input : NR := ⟨call.input, nonemptyModel⟩
  let before := set.ranges.take call.rank
  let pending := set.ranges.drop call.rank
  have takeEq := represents.takeFresh absent
  have dropEq : set.ranges.dropWhile (fun nr => decide (nr.val.lo < call.input.lo)) = pending := by
    have whole := List.takeWhile_append_dropWhile (p := fun nr : NR => decide (nr.val.lo < call.input.lo))
      (l := set.ranges)
    rw [takeEq] at whole
    have parts := List.take_append_drop call.rank set.ranges
    exact List.append_cancel_left (whole.trans parts.symm)
  have represented := represents.freshInput (capacity := capacity) (initial := initial) (low := low)
    (high := high) nonempty absent spare
  dsimp only at represented
  have helperPosition : helper.position = call.rank :=
    (call.freshHelperSelected sorted spare newKey).trans (call.freshRank sorted absent)
  have helperLength := call.freshHelperLength capacity initial low high spare
  have rankBound := call.rank_le
  have helperFound : helper.position < helper.length.toNat := by
    rw [helperPosition, helperLength]; omega
  have beforeLength : before.length = helper.position := by
    rw [helperPosition, List.length_take, represents.length]; omega
  have cardinalityFits := represents.cardinalityFits
  have helperCache : (BitVec.append helper.high helper.low).toNat = (BitVec.append high low).toNat := rfl
  have budget : rangesCardinality pending ≤ (BitVec.append helper.high helper.low).toNat := by
    rw [helperCache, accurate]
    change rangesCardinality (set.ranges.drop call.rank) ≤ rangesCardinality set.ranges
    conv_rhs => rw [← List.take_append_drop call.rank set.ranges]
    rw [rangesCardinality_append]; omega
  have enough := helper.enoughForSuffix helperFound before pending input beforeLength represented budget
  have endNewBound := (helper.progress helper.acceptCount).endNew.isLt
  have fits : (BitVec.append helper.high helper.low).toNat +
      ((helper.progress helper.acceptCount).endNew.toNat - helper.stop.toNat) < 2 ^ 64 := by
    rw [helperCache]; omega
  have matched := helper.entriesMatch helperFound before pending input beforeLength rfl represented
    enough fits
  dsimp only at matched
  -- Each successor the helper scans is an original entry.
  have successorOrdered : ∀ index < helper.acceptCount,
      (helper.successor index).key ≤ (helper.successor index).value := by
    intro index below
    have accepted := (helper.accepted index below).1
    rw [helperPosition, helperLength] at accepted
    change ((call.freshInsert capacity).vector.result (helper.position + 1 + index)).key ≤
      ((call.freshInsert capacity).vector.result (helper.position + 1 + index)).value
    rw [helperPosition, RawVec.Insert.Call.result, (call.freshInsert capacity).vectorIndex,
      call.freshRank sorted absent, if_neg (by omega), if_neg (by omega)]
    exact BitVec.le_def.mpr (ordered _ (by omega))
  have finalValue := helper.finalCached helper.acceptCount successorOrdered enough fits
  have distance : (call.stop - call.start).toNat = call.stop.toNat - call.start.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr nonempty)]
  -- The model's result is the helper's plus the input.
  have modelEq : freshInsertProduction set.ranges input (BitVec.append high low).toNat =
      ⟨before ++ (finishDeleteExtraProduction input pending (BitVec.append high low).toNat).current ::
          (finishDeleteExtraProduction input pending (BitVec.append high low).toNat).pending,
        (finishDeleteExtraProduction input pending (BitVec.append high low).toNat).cachedLength +
          input.val.cardinality⟩ := by
    unfold freshInsertProduction
    rw [List.span_eq_takeWhile_dropWhile, takeEq, dropEq]
  rw [modelEq] at rangesEq cachedEq
  rw [helperCache] at matched
  refine ⟨?_, ?_⟩
  · rw [rangesEq, Result.afterHelperLength]
    exact matched.1.symm
  · change (BitVec.append (freshHigh (helper.finalLow helper.acceptCount) (helper.finalHigh helper.acceptCount)
        (call.stop - call.start)) (freshLow (helper.finalLow helper.acceptCount) (call.stop - call.start))).toNat = _
    rw [cachedEq]
    dsimp only
    rw [matched.2]
    have width : input.val.cardinality = call.stop.toNat - call.start.toNat + 1 := by
      change cardinality ⟨(call.start.toNat : Int), (call.stop.toNat : Int)⟩ = _
      rw [cardinality_of_nonempty (by change (call.start.toNat : Int) ≤ call.stop.toNat; exact_mod_cast nonempty)]
      have cast : (call.stop.toNat : Int) - call.start.toNat + 1 =
          ((call.stop.toNat - call.start.toNat + 1 : Nat) : Int) := by omega
      change Int.toNat ((call.stop.toNat : Int) - call.start.toNat + 1) = _
      rw [cast, Int.toNat_natCast]
    rw [width, freshCacheValue _ _ _ (by rw [distance, finalValue, helperCache]; omega), distance]
    omega

/-- Entries before the upper-bound rank start at or before `start`. -/
theorem Call.belowRank (call : Call) : ∀ index < call.rank,
    (call.old index).key.toNat ≤ call.start.toNat := by
  intro index below
  have passes := SortedMap.scan_passes (bound := .upper) (key := call.start) (old := call.old) 0
    call.length.toNat index (Nat.zero_le _) below
  simpa [SortedMap.Bound.passes] using passes

/-- In a sorted map, entries from the upper-bound rank on start after `start`. -/
theorem Call.fromRank {call : Call} (sorted : Sorted (entriesOf call.old call.length.toNat)) :
    ∀ index, call.rank ≤ index → index < call.length.toNat →
      call.start.toNat < (call.old index).key.toNat := by
  intro index low high
  have bounds := SortedMap.scan_bounds (bound := .upper) (key := call.start) (old := call.old) 0
    call.length.toNat
  have rankIs : call.rank = SortedMap.scan .upper call.start call.old 0 call.length.toNat := rfl
  have early : SortedMap.scan .upper call.start call.old 0 call.length.toNat < 0 + call.length.toNat := by
    rw [← rankIs]; omega
  have stops := SortedMap.scan_stops (bound := .upper) (key := call.start) (old := call.old) 0
    call.length.toNat early
  simp only [SortedMap.Bound.passes, decide_eq_false_iff_not, Nat.not_le] at stops
  rcases Nat.eq_or_lt_of_le low with same | later
  · rw [← same]; exact stops
  · exact Nat.lt_trans stops (SortedMap.sorted_entriesOf sorted later high)

/-- On the fresh path no entry starts at `start`. -/
theorem Call.freshAbsent {call : Call} (sorted : Sorted (entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (fresh : call.rank = 0 ∨ call.predecessor.value.toNat + 1 < call.start.toNat) :
    ∀ index < call.length.toNat, (call.old index).key ≠ call.start := by
  intro index inside same
  have bound := call.rank_le
  by_cases before : index < call.rank
  · rcases fresh with zero | gap
    · omega
    · -- The predecessor is the last entry before the rank, and it ends before `start`.
      have last : index ≤ call.rank - 1 := by omega
      have keyOrder : (call.old index).key.toNat ≤ (call.predecessor).key.toNat := by
        rcases Nat.eq_or_lt_of_le last with equal | earlier
        · unfold Call.predecessor; rw [equal]
        · exact Nat.le_of_lt (SortedMap.sorted_entriesOf sorted earlier (by omega))
      have predecessorOrder := ordered (call.rank - 1) (by omega)
      unfold Call.predecessor at gap keyOrder
      rw [same] at keyOrder
      omega
  · have after := call.fromRank sorted index (by omega) inside
    rw [same] at after
    exact Nat.lt_irrefl _ after

/-- The linked range insertion's premises: the machine at entry, its
initial memory layout, a map that represents a canonical set, and an
accurate cached count. Fresh insertion needs a spare map slot, and the
deletion buffer has room for one key per map entry. That scratch bound is
sufficient but not necessary: the run uses one word per accepted successor,
and `Premises` states that exact path-specific count. -/
structure InsertionPremises (base returnAddress : Word) (original : Machine)
    (initial : Snapshot) (call : Call) (capacity low high : Word) (set : RangeSetBlaze) :
    Prop where
  entry : original = sync base original { initial with pc := 0 }
  mode : MachineMode original returnAddress
  arguments : Arguments initial call
  layout : InitialLayout base original initial call capacity low high
  represents : Represents set call
  accurate : (BitVec.append high low).toNat = set.cardinality
  spare : call.path = .fresh → call.length.toNat < capacity.toNat
  scratchRoom : call.length.toNat ≤ initial.a5.toNat

theorem InsertionPremises.toPremises {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word} {set : RangeSetBlaze}
    (premises : InsertionPremises base returnAddress original initial call capacity low high set) :
    Premises base returnAddress original initial call capacity low high := by
  refine ⟨premises.entry, premises.mode, premises.arguments, premises.layout,
    premises.represents.sorted, premises.represents.ordered, premises.spare, fun fresh => ?_, fun _ => ?_⟩
  · have bound := (call.freshHelper capacity initial low high).acceptCount_le
    rw [call.freshHelperLength capacity initial low high (premises.spare fresh)] at bound
    have := premises.scratchRoom
    omega
  · have bound := (call.extensionHelper initial low high).acceptCount_le
    change _ ≤ call.length.toNat - _ at bound
    have := premises.scratchRoom
    omega

set_option maxHeartbeats 2000000 in
/-- On every path, the machine's result represents the production model's
result for the stored set, its cached count, and the input range. -/
theorem Call.resultRepresents {set : RangeSetBlaze} {call : Call} (initial : Snapshot)
    {capacity low high : Word} (represents : Represents set call)
    (accurate : (BitVec.append high low).toNat = set.cardinality)
    (spare : call.path = .fresh → call.length.toNat < capacity.toNat) :
    (call.result initial capacity low high).Represents
      (internalAddProduction set (BitVec.append high low).toNat call.input) := by
  have sorted := represents.sorted
  have ordered := represents.ordered
  by_cases empty : call.stop.toNat < call.start.toNat
  · rw [Call.result, show call.path = .empty from if_pos empty]
    have backwards : call.input.hi < call.input.lo := by
      change (call.stop.toNat : Int) < call.start.toNat; exact_mod_cast empty
    obtain ⟨ranges, cached⟩ := emptyModel set (BitVec.append high low).toNat call.input backwards
    exact unchangedRepresents represents 19 low high _ ranges cached
  have nonempty := Nat.le_of_not_gt empty
  have fresh (select : call.path = .fresh)
      (branch : call.rank = 0 ∨ (0 < call.rank ∧ call.predecessor.value.toNat + 1 < call.start.toNat)) :
      (call.result initial capacity low high).Represents
        (internalAddProduction set (BitVec.append high low).toNat call.input) := by
    have absent := call.freshAbsent sorted ordered (branch.imp id And.right)
    have freshModel : (set.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).getLast? = none ∨
        ∃ predecessor : NR,
          (set.ranges.takeWhile (fun nr => decide (nr.val.lo ≤ call.input.lo))).getLast? = some predecessor ∧
            predecessor.val.hi + 1 < call.input.lo := by
      rcases branch with zero | ⟨found, gap⟩
      · left
        rw [represents.takeUpper, zero, List.take_zero]
        rfl
      · right
        obtain ⟨predecessor, last, ends⟩ := modelPredecessor represents found
        refine ⟨predecessor, last, ?_⟩
        rw [ends]
        change (call.predecessor.value.toNat : Int) + 1 < call.start.toNat
        exact_mod_cast gap
    rw [Call.result, select]
    exact freshRepresents _ represents sorted ordered accurate nonempty absent (spare select)
      (call.freshDoesNotReplace capacity absent) freshModel
  by_cases none : call.rank = 0
  · exact fresh (by simp only [Call.path, if_neg empty, if_pos none]) (Or.inl none)
  have found := Nat.pos_of_ne_zero none
  by_cases gap : call.predecessor.value.toNat + 1 < call.start.toNat
  · exact fresh (by simp only [Call.path, if_neg empty, if_neg none, if_pos gap]) (Or.inr ⟨found, gap⟩)
  by_cases grows : call.predecessor.value.toNat < call.stop.toNat
  · have path : call.path = .extension := by
      simp only [Call.path, if_neg empty, if_neg none, if_neg gap, if_pos grows]
    rw [Call.result, path]
    exact extensionRepresents _ represents sorted accurate nonempty found gap grows
  · have path : call.path = .contained := by
      simp only [Call.path, if_neg empty, if_neg none, if_neg gap, if_neg grows]
    rw [Call.result, path]
    have model := containedModel (BitVec.append high low).toNat represents nonempty found
      (Nat.le_of_not_gt grows)
    exact unchangedRepresents represents _ low high _ (by rw [model]) (by rw [model])

/-- Preserving the immutable header bytes preserves the allocation pointer
and capacity even when the initialized prefix has changed. -/
theorem MapStorage.metadataKept {original : Machine} {call : Call} {capacity : Word}
    (map : MapStorage original call capacity) {after : ByteMemory}
    (agrees : ∀ byte, (mapHeader call).Contains byte → ¬ (mapLengthWord call).Contains byte →
      after[byte]? = original.mem[byte]?) :
    WordAt after call.header.toNat call.data ∧
      WordAt after (call.header.toNat + 8) capacity := by
  have keptHeader {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 →
        (mapHeader call).Contains byte ∧ ¬ (mapLengthWord call).Contains byte) :
      WordAt after address value :=
    word.congr fun byte low high =>
      agrees byte (inside byte low high).1 (inside byte low high).2
  have dataKept := keptHeader map.dataWord fun byte low high => by
    refine ⟨⟨low, by change byte < call.header.toNat + 12; omega⟩, fun length => ?_⟩
    change call.header.toNat + 4 ≤ byte ∧ byte < call.header.toNat + 4 + 4 at length
    omega
  have capacityKept := keptHeader map.capacityWord fun byte low high => by
    refine ⟨⟨by change call.header.toNat ≤ byte; omega, by change byte < call.header.toNat + 12; omega⟩,
      fun length => ?_⟩
    change call.header.toNat + 4 ≤ byte ∧ byte < call.header.toNat + 4 + 4 at length
    omega
  exact ⟨dataKept, capacityKept⟩

/-- The machine write footprint permits only the length word of the map
header to change. Separation keeps the other regions away from it. -/
theorem InitialLayout.metadataKept {base : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high) {after : ByteMemory}
    (keep : ∀ byte, ¬ WritableByte initial call capacity byte → after[byte]? = original.mem[byte]?) :
    WordAt after call.header.toNat call.data ∧
      WordAt after (call.header.toNat + 8) capacity := by
  apply layout.map.metadataKept
  intro byte inHeader notLength
  apply keep byte
  intro writable
  rcases writable with stack | cache | scratch | length | map
  · exact layout.apart.headerStack byte inHeader stack
  · exact layout.apart.headerCache byte inHeader cache
  · exact layout.apart.headerScratch byte inHeader scratch
  · exact notLength length
  · exact layout.apart.headerMap byte inHeader map

/-- The linked range insertion returns to its caller after an exact number
of instructions, preserves every register outside the caller-saved list and
every byte it may not write, and stores the production model's result: the
canonical union of the set and the input, with its cardinality cached. The
map header keeps its data pointer and capacity; only its length changes. -/
theorem InsertionPremises.run {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word} {set : RangeSetBlaze}
    (premises : InsertionPremises base returnAddress original initial call capacity low high set) :
    let result := call.result initial capacity low high
    let model := internalAddProduction set (BitVec.append high low).toNat call.input
    ∃ final, Riscfree.RV32.run result.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      result.inMemory initial call final.mem ∧
      WordAt final.mem call.header.toNat call.data ∧
      WordAt final.mem (call.header.toNat + 8) capacity ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      (∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]?) ∧
      result.Represents model ∧
      model.setResult.toSet = set.toSet ∪ call.input.toSet ∧
      model.cachedLength = model.setResult.cardinality := by
  intro result model
  obtain ⟨final, ran, returned, stored, regs, keep⟩ := premises.toPremises.run
  have correct := internalAddProduction_correct set (BitVec.append high low).toNat call.input
    premises.accurate
  obtain ⟨dataKept, capacityKept⟩ := premises.layout.metadataKept keep
  exact ⟨final, ran, returned, stored, dataKept, capacityKept, regs, keep,
    call.resultRepresents initial premises.represents premises.accurate premises.spare, correct⟩

end Riscfree.RangeInsert.Nonempty
