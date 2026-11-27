import Mathlib.Data.List.Pairwise

/-! Arithmetic used by the u32/u64 instance, independently of its instruction
selection. -/

namespace Riscfree.RangeInsert

/-- The mathematical form of the short-circuit test in `delete_extra`.
If the second operand is needed, the successor is strictly within the u32
domain. -/
theorem successorTest (start stop : BitVec 32) :
    (start.toNat ≤ stop.toNat ∨ start.toNat ≤ (stop + 1).toNat) ↔
      start.toNat ≤ stop.toNat + 1 := by
  by_cases short : start.toNat ≤ stop.toNat
  · simp [short, Nat.le_trans short (Nat.le_succ _)]
  · have startBound := start.isLt
    have increment : (stop + 1).toNat = stop.toNat + 1 := by
      rw [BitVec.toNat_add]
      change (stop.toNat + 1) % 2 ^ 32 = _
      exact Nat.mod_eq_of_lt (by omega)
    rw [increment]
    simp only [short, false_or]

/-- The predecessor has a strict gap precisely when the checked increment
succeeds and its result lies strictly before the new start. -/
theorem predecessorGap (start stop : BitVec 32) :
    (stop.toNat < 2 ^ 32 - 1 ∧ (stop + 1).toNat < start.toNat) ↔
      stop.toNat + 1 < start.toNat := by
  have startBound := start.isLt
  by_cases canIncrement : stop.toNat < 2 ^ 32 - 1
  · have increment : (stop + 1).toNat = stop.toNat + 1 := by
      rw [BitVec.toNat_add]
      change (stop.toNat + 1) % 2 ^ 32 = _
      exact Nat.mod_eq_of_lt (by omega)
    rw [increment]
    simp only [canIncrement, true_and]
  · have noGap : ¬ stop.toNat + 1 < start.toNat := by omega
    simp [canIncrement, noGap]

/-- The widened inclusive width is exact, including the full 32-bit domain. -/
theorem inclusiveWidth (start stop : BitVec 32) (ordered : start ≤ stop) :
    (stop - start).toNat + 1 = stop.toNat + 1 - start.toNat ∧
      (stop - start).toNat + 1 ≤ 2 ^ 32 := by
  have stopBound := stop.isLt
  have naturalOrder := BitVec.le_def.mp ordered
  rw [BitVec.toNat_sub_of_le ordered]
  omega

/-- Three additions of at most a full domain, from an accurate count, fit
even if the effects of intervening subtractions are ignored. -/
theorem cachedAdditionsFit (length first second third : Nat)
    (initial : length ≤ 2 ^ 32) (firstFit : first ≤ 2 ^ 32)
    (secondFit : second ≤ 2 ^ 32) (thirdFit : third ≤ 2 ^ 32) :
    length + first + second + third < 2 ^ 64 := by omega

private theorem joinedNat (high low : BitVec 32) :
    (high ++ low).toNat = high.toNat * 2 ^ 32 + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

private theorem addWords (high low addHigh addLow : BitVec 32) :
    let sum := low + addLow
    let carry : BitVec 32 := if sum < low then 1#32 else 0#32
    ((high + addHigh + carry) ++ sum) = (high ++ low) + (addHigh ++ addLow) := by
  dsimp only
  apply BitVec.eq_of_toNat_eq
  simp only [joinedNat, BitVec.lt_def, BitVec.toNat_add]
  have highBound := high.isLt
  have lowBound := low.isLt
  have addHighBound := addHigh.isLt
  have addLowBound := addLow.isLt
  split <;> simp only [show (1#32).toNat = 1 from rfl, show (0#32).toNat = 0 from rfl] <;> omega

/-- The RV32I carry instructions implement the widened inclusive addition.
The first comparison can use either low-word addend. -/
theorem addInclusiveWords (high low distance : BitVec 32) :
    let sum := low + distance
    let carry : BitVec 32 := if sum < distance then 1#32 else 0#32
    let incremented := sum + 1#32
    let extra : BitVec 32 := if incremented < 1#32 then 1#32 else 0#32
    ((high + carry + extra) ++ incremented) =
      (high ++ low) + (0#32 ++ distance) + 1#64 := by
  have first := addWords high distance 0#32 low
  dsimp only at first
  rw [BitVec.add_zero, BitVec.add_comm distance low] at first
  have joined : (high ++ distance) + (0#32 ++ low) =
      (high ++ low) + (0#32 ++ distance) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, joinedNat]
    omega
  rw [joined] at first
  have nextCarry (sum : BitVec 32) : sum + 1#32 < sum ↔ sum + 1#32 < 1#32 := by
    have bound := sum.isLt
    simp only [BitVec.lt_def, BitVec.toNat_add]
    change (sum.toNat + 1) % 2^32 < sum.toNat ↔ (sum.toNat + 1) % 2^32 < 1
    omega
  have second := addWords
    (high + (if low + distance < distance then 1#32 else 0#32)) (low + distance) 0#32 1#32
  dsimp only at second
  simp only [BitVec.add_zero, nextCarry, show (0#32 ++ 1#32) = 1#64 by decide] at second
  dsimp only
  rw [second, first]

/-- The successor subtraction uses the complement of its distance and a
decrement in the high word to subtract an inclusive length. -/
theorem subtractInclusiveWords (high low distance : BitVec 32) :
    let sum := low + ~~~distance
    let carry : BitVec 32 := if sum < low then 1#32 else 0#32
    ((high + carry - 1) ++ sum) =
      (high ++ low) - ((0#32 ++ distance) + 1#64) := by
  have added := addWords high low (~~~(0#32)) (~~~distance)
  have inverse : (~~~(0#32)) = -1#32 := by decide
  have complement (word : BitVec 64) : ~~~word = -(word + 1#64) := by
    rw [BitVec.neg_add, BitVec.neg_eq_not_add word,
      BitVec.add_sub_cancel]
  dsimp only at added ⊢
  rw [← BitVec.not_append, complement, inverse, BitVec.add_assoc,
    BitVec.add_comm (-1#32), ← BitVec.add_assoc,
    ← BitVec.sub_eq_add_neg, ← BitVec.sub_eq_add_neg] at added
  exact added

end Riscfree.RangeInsert
