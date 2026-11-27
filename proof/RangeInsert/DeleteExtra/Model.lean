import RangeInsert.ModelArithmetic
import RangeInsert.Nonempty.Correspondence

/-! Relate the helper's measured scan to the production fixed-end loop.
The loop and its correctness stay in the imported RangeSetBlaze model. -/

namespace Riscfree.RangeInsert.DeleteExtra

open RangeSetBlazeValidation RangeSetBlazeValidation.IntRange
open RangeSetBlazeValidation.RangeSetBlaze
open Riscfree.RawVec (Word Pair)
open Riscfree.SortedMap (entriesOf entriesOf_length entriesOf_getElem)


theorem Call.widthOfModelSuccessor (call : Call) (index : Nat) (range : NR)
    (start : range.val.lo = ((call.successor index).key.toNat : Int))
    (stop : range.val.hi = ((call.successor index).value.toNat : Int)) :
    range.val.cardinality = call.successorWidth index := by
  rw [cardinality_of_nonempty range.property]
  rw [start, stop]
  change Int.toNat (((call.successor index).value.toNat : Int) - (call.successor index).key.toNat + 1) =
    (call.successor index).value.toNat + 1 - (call.successor index).key.toNat
  omega

theorem Call.loopMatches (call : Call) (found : call.position < call.length.toNat)
    (pending : List NR) (size : pending.length = call.length.toNat - (call.position + 1))
    (suffixWords : ∀ index (inside : index < pending.length),
      pending[index].val.lo = ((call.successor index).key.toNat : Int) ∧
      pending[index].val.hi = ((call.successor index).value.toNat : Int))
    (selected : NR) (endWord : selected.val.hi = (call.stop.toNat : Int))
    (cached : Nat) :
    let result := deleteExtraProductionLoop call.stop.toNat selected pending cached
    (ForwardCLenResult.current result).val.lo = selected.val.lo ∧
      (ForwardCLenResult.current result).val.hi = ((call.progress call.acceptCount).endNew.toNat : Int) ∧
      ForwardCLenResult.pending result = pending.drop call.acceptCount ∧
      ForwardCLenResult.cachedLength result = cached - call.removedWidth call.acceptCount := by
  have iterate : ∀ remaining index (current : NR),
      index + remaining = call.acceptCount →
      current.val.lo = selected.val.lo →
      current.val.hi = ((call.progress index).endNew.toNat : Int) →
      let result := deleteExtraProductionLoop call.stop.toNat current (pending.drop index)
        (cached - call.removedWidth index)
      (ForwardCLenResult.current result).val.lo = selected.val.lo ∧
        (ForwardCLenResult.current result).val.hi = ((call.progress call.acceptCount).endNew.toNat : Int) ∧
        ForwardCLenResult.pending result = pending.drop call.acceptCount ∧
        ForwardCLenResult.cachedLength result = cached - call.removedWidth call.acceptCount := by
    intro remaining
    induction remaining with
    | zero =>
      intro index current totals starts ends
      have finalIndex : index = call.acceptCount := by omega
      subst index
      dsimp only
      rcases call.stops found with endOfMap | ⟨gapInside, gap⟩
      · have finished : pending.drop call.acceptCount = [] := by
          apply List.drop_eq_nil_of_le
          omega
        rw [finished, deleteExtraProductionLoop_nil]
        exact ⟨starts, ends, rfl, rfl⟩
      · have inside : call.acceptCount < pending.length := by omega
        have facts := suffixWords call.acceptCount inside
        have strict : (call.stop.toNat : Int) + 1 < pending[call.acceptCount].val.lo := by
          rw [facts.1]
          have failure : ¬ (call.successor call.acceptCount).key.toNat ≤ call.limit.toNat :=
            Nat.not_le.mpr gap
          have beyond : call.stop.toNat + 1 < (call.successor call.acceptCount).key.toNat :=
            Nat.lt_of_not_ge fun fits => failure ((call.acceptsModel _).mpr fits)
          exact_mod_cast beyond
        rw [List.drop_eq_getElem_cons inside, deleteExtraProductionLoop_cons,
          if_neg (not_le.mpr strict)]
        exact ⟨starts, ends, rfl, rfl⟩
    | succ remaining ih =>
      intro index current totals starts ends
      have active : index < call.acceptCount := by omega
      have accepted := call.accepted index active
      have inside : index < pending.length := by omega
      have facts := suffixWords index inside
      let next := pending[index]
      have allowed : next.val.lo ≤ (call.stop.toNat : Int) + 1 := by
        change pending[index].val.lo ≤ _
        rw [facts.1]
        exact_mod_cast (call.acceptsModel _).mp accepted.2
      let merged : NR := ⟨⟨current.val.lo, max current.val.hi next.val.hi⟩,
        current.property.trans (le_max_left _ _)⟩
      have nextEnd : merged.val.hi = ((call.progress (index + 1)).endNew.toNat : Int) := by
        change max current.val.hi pending[index].val.hi = _
        rw [ends, facts.2, call.progressEndStep]
        push_cast
        rfl
      have width := call.widthOfModelSuccessor index next facts.1 facts.2
      have cont := ih (index + 1) merged (by omega) starts nextEnd
      dsimp only
      rw [List.drop_eq_getElem_cons inside, deleteExtraProductionLoop_cons]
      rw [if_pos allowed, width, Nat.sub_sub,
        ← call.removedWidth_succ]
      exact cont
  have zero : call.removedWidth 0 = 0 := rfl
  have result := iterate call.acceptCount 0 selected (by omega) rfl endWord
  simpa only [List.drop_zero, zero, Nat.sub_zero] using result

theorem Call.finishMatches (call : Call) (found : call.position < call.length.toNat)
    (pending : List NR) (size : pending.length = call.length.toNat - (call.position + 1))
    (suffixWords : ∀ index (inside : index < pending.length),
      pending[index].val.lo = ((call.successor index).key.toNat : Int) ∧
      pending[index].val.hi = ((call.successor index).value.toNat : Int))
    (selected : NR) (endWord : selected.val.hi = (call.stop.toNat : Int))
    (enough : call.removedWidth call.acceptCount ≤ (BitVec.append call.high call.low).toNat)
    (fits : (BitVec.append call.high call.low).toNat +
      ((call.progress call.acceptCount).endNew.toNat - call.stop.toNat) < 2 ^ 64) :
    let result := finishDeleteExtraProduction selected pending (BitVec.append call.high call.low).toNat
    (ForwardCLenResult.current result).val.lo = selected.val.lo ∧
      (ForwardCLenResult.current result).val.hi = ((call.progress call.acceptCount).endNew.toNat : Int) ∧
      ForwardCLenResult.pending result = pending.drop call.acceptCount ∧
      ForwardCLenResult.cachedLength result =
        (BitVec.append (call.finalHigh call.acceptCount) (call.finalLow call.acceptCount)).toNat := by
  let cached := (BitVec.append call.high call.low).toNat
  let scanned := deleteExtraProductionLoop (call.stop.toNat : Int) selected pending cached
  have ⟨starts, ends, leftover, length⟩ := call.loopMatches found pending size suffixWords selected endWord cached
  have ordered (index : Nat) (before : index < call.acceptCount) :
      (call.successor index).key ≤ (call.successor index).value := by
    have located := (call.accepted index before).1
    have inside : index < pending.length := by omega
    obtain ⟨start, stop⟩ := suffixWords index inside
    have valid := pending[index].property
    change pending[index].val.lo ≤ pending[index].val.hi at valid
    rw [start, stop] at valid
    exact BitVec.le_def.mpr (by exact_mod_cast valid)
  have final := call.finalCached call.acceptCount ordered enough fits
  have ⟨starts, ends, leftover, length⟩ :
      (ForwardCLenResult.current scanned).val.lo = selected.val.lo ∧
      (ForwardCLenResult.current scanned).val.hi = ((call.progress call.acceptCount).endNew.toNat : Int) ∧
      ForwardCLenResult.pending scanned = pending.drop call.acceptCount ∧
      ForwardCLenResult.cachedLength scanned = cached - call.removedWidth call.acceptCount :=
    ⟨starts, ends, leftover, length⟩
  dsimp only
  unfold finishDeleteExtraProduction
  rw [endWord]
  change (ForwardCLenResult.current (if (call.stop.toNat : Int) < (ForwardCLenResult.current scanned).val.hi then
      _ else scanned)).val.lo = _ ∧ _
  by_cases grows : call.extended call.acceptCount
  · have growth : (call.stop.toNat : Int) < (ForwardCLenResult.current scanned).val.hi := by
      rw [ends]
      exact_mod_cast grows
    have more : rightExtensionCardinality (call.stop.toNat : Int) (ForwardCLenResult.current scanned).val.hi =
        (call.progress call.acceptCount).endNew.toNat - call.stop.toNat := by
      rw [ends]
      unfold rightExtensionCardinality
      rw [cardinality_of_nonempty]
      · change Int.toNat (((call.progress call.acceptCount).endNew.toNat : Int) - 1 - call.stop.toNat + 1) = _
        omega
      · change (call.stop.toNat : Int) ≤ (call.progress call.acceptCount).endNew.toNat - 1
        unfold Call.extended at grows
        omega
    rw [if_pos growth]
    refine ⟨starts, ends, leftover, ?_⟩
    change ForwardCLenResult.cachedLength scanned +
      rightExtensionCardinality (call.stop.toNat : Int) (ForwardCLenResult.current scanned).val.hi = _
    rw [length, more, final]
  · have noGrowth : ¬ (call.stop.toNat : Int) < (ForwardCLenResult.current scanned).val.hi := by
      rw [ends]
      exact_mod_cast grows
    rw [if_neg noGrowth]
    refine ⟨starts, ends, leftover, ?_⟩
    rw [length, final]
    unfold Call.extended at grows
    omega

theorem endpointsAt {ranges : List NR} {old : Nat → Pair} {length index : Nat}
    (represented : ranges.map Nonempty.NR.endpoints = (entriesOf old length).map Nonempty.Pair.endpoints)
    (inside : index < ranges.length) :
    Nonempty.NR.endpoints ranges[index] = Nonempty.Pair.endpoints (old index) := by
  have values := congrArg List.length represented
  simp only [List.length_map] at values
  have bound : index < (entriesOf old length).length := by rw [← values]; exact inside
  have atIndex := congrArg (fun values : List (Int × Int) => values[index]?) represented
  simp only [List.getElem?_map, List.getElem?_eq_getElem inside, List.getElem?_eq_getElem bound,
    Option.map_some, Option.some.injEq, entriesOf_getElem] at atIndex
  exact atIndex

theorem Call.progressEndLower (call : Call) (index : Nat) :
    call.stop.toNat ≤ (call.progress index).endNew.toNat := by
  induction index with
  | zero => exact Nat.le_refl _
  | succ index ih =>
    rw [call.progressEndStep]
    exact ih.trans (le_max_left _ _)

theorem Call.finalEnd (call : Call) (count : Nat)
    (selectedStop : (call.old call.position).value = call.stop) :
    (call.after count call.position).value.toNat = (call.progress count).endNew.toNat := by
  by_cases grew : call.extended count
  · simp only [Call.after, true_and, if_pos grew]
  · simp only [Call.after, true_and, if_neg grew, selectedStop]
    have lower := call.progressEndLower count
    unfold Call.extended at grew
    omega

theorem Call.suffixWords (call : Call) (before pending : List NR) (selected : NR)
    (position : before.length = call.position)
    (represented : (before ++ selected :: pending).map Nonempty.NR.endpoints =
      (entriesOf call.old call.length.toNat).map Nonempty.Pair.endpoints) :
    pending.length = call.length.toNat - (call.position + 1) ∧
      ∀ index (inside : index < pending.length),
        pending[index].val.lo = ((call.successor index).key.toNat : Int) ∧
        pending[index].val.hi = ((call.successor index).value.toNat : Int) := by
  let original := before ++ selected :: pending
  have domain : original.length = call.length.toNat := by
    have eq := congrArg List.length represented
    simpa only [List.length_map, entriesOf_length] using eq
  have size : pending.length = call.length.toNat - (call.position + 1) := by
    change (before ++ selected :: pending).length = _ at domain
    simp only [List.length_append, List.length_cons, position] at domain
    omega
  have suffix (index : Nat) (inside : index < pending.length) :
      pending[index].val.lo = ((call.successor index).key.toNat : Int) ∧
      pending[index].val.hi = ((call.successor index).value.toNat : Int) := by
    have located : before.length + 1 + index < original.length := by
      simp only [original, List.length_append, List.length_cons]
      omega
    have related := endpointsAt represented located
    simp only [List.getElem_append_right (by omega : before.length ≤ before.length + 1 + index),
      show before.length + 1 + index - before.length = index + 1 by omega, List.getElem_cons_succ] at related
    change (pending[index].val.lo, pending[index].val.hi) =
      (BitVec.toNat (call.old (before.length + 1 + index)).key,
        BitVec.toNat (call.old (before.length + 1 + index)).value) at related
    rw [position] at related
    exact ⟨congrArg Prod.fst related, congrArg Prod.snd related⟩
  exact ⟨size, suffix⟩

/-- The helper leaves the original prefix, the selected range with its new
end, and the part of the suffix that the production scan did not absorb. -/
theorem Call.entriesMatch (call : Call) (found : call.position < call.length.toNat)
    (before pending : List NR) (selected : NR) (position : before.length = call.position)
    (endWord : selected.val.hi = (call.stop.toNat : Int))
    (represented : (before ++ selected :: pending).map Nonempty.NR.endpoints =
      (entriesOf call.old call.length.toNat).map Nonempty.Pair.endpoints)
    (enough : call.removedWidth call.acceptCount ≤ (BitVec.append call.high call.low).toNat)
    (fits : (BitVec.append call.high call.low).toNat +
      ((call.progress call.acceptCount).endNew.toNat - call.stop.toNat) < 2 ^ 64) :
    let result := finishDeleteExtraProduction selected pending (BitVec.append call.high call.low).toNat
    (before ++ ForwardCLenResult.current result :: ForwardCLenResult.pending result).map Nonempty.NR.endpoints =
      (entriesOf (drained (call.after call.acceptCount) call.position call.acceptCount)
        (call.length.toNat - call.acceptCount)).map Nonempty.Pair.endpoints ∧
    ForwardCLenResult.cachedLength result =
      (BitVec.append (call.finalHigh call.acceptCount) (call.finalLow call.acceptCount)).toNat := by
  let original := before ++ selected :: pending
  have domain : original.length = call.length.toNat := by
    have eq := congrArg List.length represented
    simpa only [List.length_map, entriesOf_length] using eq
  obtain ⟨size, suffix⟩ := call.suffixWords before pending selected position represented
  have acceptedFits : call.position + 1 + call.acceptCount ≤ call.length.toNat := by
    rcases call.stops found with endOfMap | ⟨inside, _⟩ <;> omega
  have pendingFits : call.acceptCount ≤ pending.length := by omega
  let result := finishDeleteExtraProduction selected pending (BitVec.append call.high call.low).toNat
  have ⟨startWord, stopWord, tail, width⟩ := call.finishMatches found pending size suffix selected endWord enough fits
  refine ⟨?_, width⟩
  change (before ++ ForwardCLenResult.current result :: ForwardCLenResult.pending result).map Nonempty.NR.endpoints = _
  have rest : ForwardCLenResult.pending result = pending.drop call.acceptCount := tail
  rw [rest]
  have beforeSelected : before.length < original.length := by rw [domain, position]; exact found
  have selectedEntry := endpointsAt represented beforeSelected
  simp only [List.getElem_append_right (Nat.le_refl before.length), Nat.sub_self, List.getElem_cons_zero] at selectedEntry
  rw [position] at selectedEntry
  have startBits : selected.val.lo = ((call.old call.position).key.toNat : Int) := congrArg Prod.fst selectedEntry
  have sameStop : (call.old call.position).value = call.stop := by
    apply BitVec.eq_of_toNat_eq
    have endBits : selected.val.hi = ((call.old call.position).value.toNat : Int) := congrArg Prod.snd selectedEntry
    rw [endWord] at endBits
    exact_mod_cast endBits.symm
  apply List.ext_getElem
  · simp only [List.length_map, List.length_append, List.length_cons, List.length_drop, entriesOf_length,
      position]
    omega
  · intro index left right
    simp only [List.getElem_map, entriesOf_getElem]
    by_cases inFront : index < before.length
    · have actual : index < original.length := by rw [domain]; omega
      have originalEntry := endpointsAt represented actual
      rw [List.getElem_append_left inFront] at originalEntry
      rw [List.getElem_append_left inFront]
      have earlier : index < call.position := by omega
      simpa [drained, earlier.le, Call.after, Nat.ne_of_lt earlier] using originalEntry
    · rw [List.getElem_append_right (Nat.le_of_not_gt inFront)]
      by_cases here : index = before.length
      · subst index
        simp only [Nat.sub_self, List.getElem_cons_zero]
        have atSelected : before.length = call.position := position
        rw [show drained (call.after call.acceptCount) call.position call.acceptCount before.length =
            call.after call.acceptCount call.position by simp only [drained, atSelected, le_refl, if_true]]
        unfold Nonempty.NR.endpoints Nonempty.Pair.endpoints
        rw [call.after_key, call.finalEnd call.acceptCount sameStop]
        exact Prod.ext (startWord.trans startBits) stopWord
      · have beyond : before.length < index := by omega
        have tailIndex : index - before.length = (index - (before.length + 1)) + 1 := by omega
        simp only [tailIndex, List.getElem_cons_succ, List.getElem_drop]
        have indexInside : index - (before.length + 1) + call.acceptCount < pending.length := by
          simp only [List.length_map, List.length_append, List.length_cons, List.length_drop] at left
          omega
        have matched := suffix (index - (before.length + 1) + call.acceptCount) indexInside
        have actual : call.position + 1 + (index - (before.length + 1) + call.acceptCount) =
            index + call.acceptCount := by omega
        have afterSelected : ¬ index ≤ call.position := by omega
        have other : index + call.acceptCount ≠ call.position := by omega
        simp only [drained, if_neg afterSelected, Call.after, other, false_and, if_false]
        unfold Call.successor at matched
        rw [actual] at matched
        simpa only [Nat.add_comm call.acceptCount (index - (before.length + 1))] using
          (Prod.ext matched.1 matched.2 : Nonempty.NR.endpoints pending[index - (before.length + 1) + call.acceptCount] =
            Nonempty.Pair.endpoints (call.old (index + call.acceptCount)))

theorem Call.removedWidthMatches (call : Call) (pending : List NR)
    (suffixWords : ∀ index (inside : index < pending.length),
      pending[index].val.lo = ((call.successor index).key.toNat : Int) ∧
      pending[index].val.hi = ((call.successor index).value.toNat : Int))
    (count : Nat) (bound : count ≤ pending.length) :
    call.removedWidth count = rangesCardinality (pending.take count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have inside : count < pending.length := by omega
    obtain ⟨start, stop⟩ := suffixWords count inside
    rw [call.removedWidth_succ, List.take_succ_eq_append_getElem inside, rangesCardinality_append,
      ih (by omega), rangesCardinality_cons, rangesCardinality_nil, Nat.add_zero,
      call.widthOfModelSuccessor count pending[count] start stop]

theorem Call.enoughForSuffix (call : Call) (found : call.position < call.length.toNat)
    (before pending : List NR) (selected : NR) (position : before.length = call.position)
    (represented : (before ++ selected :: pending).map Nonempty.NR.endpoints =
      (entriesOf call.old call.length.toNat).map Nonempty.Pair.endpoints)
    (budget : rangesCardinality pending ≤ (BitVec.append call.high call.low).toNat) :
    call.removedWidth call.acceptCount ≤ (BitVec.append call.high call.low).toNat := by
  obtain ⟨length, words⟩ := call.suffixWords before pending selected position represented
  have valid : call.acceptCount ≤ pending.length := by
    rcases call.stops found with endOfMap | ⟨within, _⟩ <;> omega
  have cardinality := rangesCardinality_append (pending.take call.acceptCount) (pending.drop call.acceptCount)
  rw [List.take_append_drop] at cardinality
  rw [call.removedWidthMatches pending words call.acceptCount valid]
  omega

end Riscfree.RangeInsert.DeleteExtra
