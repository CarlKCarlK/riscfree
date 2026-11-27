import RangeInsert.Nonempty.Fresh.Return
import RangeInsert.DeleteExtra.Count

/-! Relate the two machine words to the mathematical successor width
and right extension used by the production model. -/

namespace Riscfree.RangeInsert

open Riscfree.RV32
open Riscfree.RawVec (Word)

private theorem lessWord (left right : Word) :
    Step.lessWord left right = (if left < right then 1#32 else 0#32) := by
  by_cases less : left < right
  · simp only [Step.lessWord, if_pos (BitVec.lt_def.mp less), if_pos less]
    rfl
  · have natural : ¬ left.toNat < right.toNat := fun bound => less (BitVec.lt_def.mpr bound)
    simp only [Step.lessWord, if_neg natural, if_neg less]
    rfl

theorem joinedWords (high low : Word) :
    (BitVec.append high low).toNat = high.toNat * 2 ^ 32 + low.toNat := by
  change (high ++ low).toNat = _
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

theorem DeleteExtra.subtractWidth (high low start stop : Word) (ordered : start ≤ stop)
    (enough : stop.toNat + 1 - start.toNat ≤ (BitVec.append high low).toNat) :
    (BitVec.append (DeleteExtra.highAfter low high start stop) (DeleteExtra.lowAfter low start stop)).toNat =
      (BitVec.append high low).toNat - (stop.toNat + 1 - start.toNat) := by
  have allOnes : (0xffffffff#32) = BitVec.allOnes 32 := rfl
  have minusOne : (0xffffffff#32) = -(1#32) := rfl
  let difference : Word := stop - start
  let prior : BitVec 64 := BitVec.append high low
  let distance : BitVec 64 := BitVec.append 0#32 difference
  let widthWord : BitVec 64 := BitVec.add distance 1#64
  have words : (BitVec.append (DeleteExtra.highAfter low high start stop) (DeleteExtra.lowAfter low start stop)) =
      BitVec.sub prior widthWord := by
    unfold DeleteExtra.highAfter DeleteExtra.lowAfter
    rw [allOnes, BitVec.xor_allOnes, lessWord]
    rw [← allOnes, minusOne, ← BitVec.sub_eq_add_neg]
    exact subtractInclusiveWords high low (stop - start)
  have width : widthWord.toNat = stop.toNat + 1 - start.toNat := by
    rw [show widthWord.toNat = (distance.toNat + (1#64).toNat) % 2 ^ 64 from BitVec.toNat_add distance 1#64]
    change (distance.toNat + 1) % 2 ^ 64 = _
    have widen : distance.toNat = difference.toNat := by
      change (BitVec.append 0#32 difference).toNat = _
      simp only [joinedWords, show (0#32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add]
    rw [widen]
    have actual := inclusiveWidth start stop ordered
    change ((stop - start).toNat + 1) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt (by have := actual.2; omega)]
    exact actual.1
  have valid : widthWord ≤ prior := BitVec.le_def.mpr (by rw [width]; exact enough)
  rw [words, show (BitVec.sub prior widthWord).toNat = prior.toNat - widthWord.toNat from BitVec.toNat_sub_of_le valid,
    width]

theorem DeleteExtra.extensionDistance {start stop : Word} (grows : start.toNat < stop.toNat) :
    (DeleteExtra.distance start stop).toNat + 1 = stop.toNat - start.toNat := by
  have allOnes : (0xffffffff#32) = BitVec.allOnes 32 := rfl
  have bitDistance : DeleteExtra.distance start stop = stop - (start + 1#32) := by
    unfold DeleteExtra.distance
    rw [allOnes, BitVec.xor_allOnes, BitVec.sub_eq_add_neg]
    congr 1
    rw [BitVec.neg_add, BitVec.neg_eq_not_add start]
    exact (BitVec.add_sub_cancel _ _).symm
  have increment : (start + 1#32).toNat = start.toNat + 1 := by
    rw [BitVec.toNat_add]
    change (start.toNat + 1) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by have := stop.isLt; omega)
  have order : start + 1#32 ≤ stop := BitVec.le_def.mpr (by rw [increment]; omega)
  rw [bitDistance, BitVec.toNat_sub_of_le order, increment]
  omega

theorem DeleteExtra.addExtension (high low start stop : Word) (grows : start.toNat < stop.toNat)
    (fits : (BitVec.append high low).toNat + (stop.toNat - start.toNat) < 2 ^ 64) :
    (BitVec.append (DeleteExtra.extendedHigh low high start stop) (DeleteExtra.extendedLow low start stop)).toNat =
      (BitVec.append high low).toNat + (stop.toNat - start.toNat) := by
  let distance := DeleteExtra.distance start stop
  let prior : BitVec 64 := BitVec.append high low
  let delta : BitVec 64 := BitVec.append 0#32 distance
  let result : BitVec 64 := BitVec.add (BitVec.add prior delta) 1#64
  have words : (BitVec.append (DeleteExtra.extendedHigh low high start stop) (DeleteExtra.extendedLow low start stop)) =
      result :=
    Nonempty.freshCacheAddition low high distance
  have rightSize : distance.toNat + 1 = stop.toNat - start.toNat := DeleteExtra.extensionDistance grows
  rw [words]
  have inner : (BitVec.add prior delta).toNat = (prior.toNat + delta.toNat) % 2 ^ 64 :=
    BitVec.toNat_add prior delta
  have outer : result.toNat = ((BitVec.add prior delta).toNat + 1) % 2 ^ 64 :=
    BitVec.toNat_add (BitVec.add prior delta) 1#64
  rw [outer, inner]
  have widened : delta.toNat = distance.toNat := by
    change (BitVec.append 0#32 distance).toNat = _
    simp only [joinedWords, show (0#32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add]
  rw [widened]
  change (((BitVec.append high low).toNat + distance.toNat) % 2 ^ 64 + 1) % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt (by omega : (BitVec.append high low).toNat + distance.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (BitVec.append high low).toNat + distance.toNat + 1 < 2 ^ 64)]
  omega

theorem DeleteExtra.Call.acceptsModel (call : DeleteExtra.Call) (start : Word) :
    start.toNat ≤ call.limit.toNat ↔ start.toNat ≤ call.stop.toNat + 1 := by
  have input := start.isLt
  have stop := call.stop.isLt
  have increment : (call.stop + 1#32).toNat = (call.stop.toNat + 1) % 2 ^ 32 := by
    rw [BitVec.toNat_add]
    rfl
  unfold DeleteExtra.Call.limit
  by_cases maxed : call.stop.toNat + 1 = 2 ^ 32
  · have wraps : (call.stop + 1#32).toNat < call.stop.toNat := by rw [increment, maxed, Nat.mod_self]; omega
    rw [if_pos wraps]
    omega
  · have next : (call.stop + 1#32).toNat = call.stop.toNat + 1 := by
      rw [increment, Nat.mod_eq_of_lt (by omega)]
    have noWrap : ¬ (call.stop + 1#32).toNat < call.stop.toNat := by rw [next]; omega
    rw [if_neg noWrap, next]

namespace DeleteExtra

def Call.successorWidth (call : Call) (index : Nat) : Nat :=
  let successor := call.successor index
  successor.value.toNat + 1 - successor.key.toNat

def Call.removedWidth (call : Call) (count : Nat) : Nat :=
  ((List.range count).map call.successorWidth).sum

theorem Call.removedWidth_succ (call : Call) (count : Nat) :
    call.removedWidth (count + 1) = call.removedWidth count + call.successorWidth count := by
  simp only [Call.removedWidth, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem Call.removedWidth_mono (call : Call) {first last : Nat} (order : first ≤ last) :
    call.removedWidth first ≤ call.removedWidth last := by
  induction last with
  | zero =>
    have same : first = 0 := by omega
    rw [same]
  | succ last ih =>
    by_cases same : first = last + 1
    · rw [same]
    · have old := ih (by omega)
      rw [call.removedWidth_succ]
      omega

/-- The count after each accepted successor is the initial cached width
less the combined widths of those successors. -/
theorem Call.progressCached (call : Call) (accepted : Nat)
    (ordered : ∀ index < accepted, (call.successor index).key ≤ (call.successor index).value)
    (enough : call.removedWidth accepted ≤ (BitVec.append call.high call.low).toNat) :
    ∀ count ≤ accepted,
      (BitVec.append (call.progress count).high (call.progress count).low).toNat =
        (BitVec.append call.high call.low).toNat - call.removedWidth count := by
  intro count all
  induction count with
  | zero => simp only [Call.progress, Call.removedWidth, List.range_zero, List.map_nil, List.sum_nil, Nat.sub_zero]
  | succ count ih =>
    have previous := ih (by omega)
    have bound := call.removedWidth_mono all
    rw [call.removedWidth_succ] at bound
    have enoughHere : call.successorWidth count ≤
        (BitVec.append (call.progress count).high (call.progress count).low).toNat := by
      rw [previous]
      omega
    have subtract := DeleteExtra.subtractWidth (call.progress count).high (call.progress count).low
      (call.successor count).key (call.successor count).value (ordered count (by omega)) enoughHere
    change (BitVec.append (call.progress (count + 1)).high (call.progress (count + 1)).low).toNat = _
    rw [show (BitVec.append (call.progress (count + 1)).high (call.progress (count + 1)).low).toNat =
        (BitVec.append (highAfter (call.progress count).low (call.progress count).high
          (call.successor count).key (call.successor count).value)
          (lowAfter (call.progress count).low (call.successor count).key (call.successor count).value)).toNat from rfl,
      subtract, previous, call.removedWidth_succ]
    exact Nat.sub_sub _ _ _

theorem Call.progressEndStep (call : Call) (count : Nat) :
    (call.progress (count + 1)).endNew.toNat =
      max (call.progress count).endNew.toNat (call.successor count).value.toNat := by
  simp only [Call.progress]
  split
  · exact (max_eq_left (by omega)).symm
  · exact (max_eq_right (by omega)).symm

theorem Call.finalCached (call : Call) (accepted : Nat)
    (ordered : ∀ index < accepted, (call.successor index).key ≤ (call.successor index).value)
    (enough : call.removedWidth accepted ≤ (BitVec.append call.high call.low).toNat)
    (fits : (BitVec.append call.high call.low).toNat +
      ((call.progress accepted).endNew.toNat - call.stop.toNat) < 2 ^ 64) :
    (BitVec.append (call.finalHigh accepted) (call.finalLow accepted)).toNat =
      (BitVec.append call.high call.low).toNat - call.removedWidth accepted +
        ((call.progress accepted).endNew.toNat - call.stop.toNat) := by
  have before := call.progressCached accepted ordered enough accepted (Nat.le_refl _)
  by_cases grows : call.extended accepted
  · simp only [Call.finalHigh, Call.finalLow, if_pos grows]
    have added := DeleteExtra.addExtension (call.progress accepted).high (call.progress accepted).low
      call.stop (call.progress accepted).endNew grows (by rw [before]; omega)
    rw [added, before]
  · simp only [Call.finalHigh, Call.finalLow, if_neg grows, before]
    unfold Call.extended at grows
    omega

end DeleteExtra

end Riscfree.RangeInsert
