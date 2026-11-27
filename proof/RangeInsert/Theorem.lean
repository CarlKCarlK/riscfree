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

end Riscfree.RangeInsert.Nonempty
