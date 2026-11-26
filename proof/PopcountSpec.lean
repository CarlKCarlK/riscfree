/-!
# Popcount specification

The mathematical specification counts the bits of four little-endian words.
Both linked implementations, `popcount128` and `popcount128_swar`, are proved
against `inputBits`.
-/

namespace Riscfree

/-! ## Mathematical specification -/

section Specification

abbrev Word := BitVec 32
abbrev Memory := Word → Word

def scan : Nat → Word → Word → Word
  | 0, _, total => total
  | remaining + 1, word, total =>
    scan remaining (word >>> (1 : Nat)) (total + (word &&& 1#32))

def scanInput (memory : Memory) (input : Word) : Word :=
  let next := input + 4
  let third := next + 4
  let fourth := third + 4
  scan 32 (memory fourth) (scan 32 (memory third)
    (scan 32 (memory next) (scan 32 (memory input) 0#32)))

theorem cpopShift (word : Word) (remaining : Nat) :
    (word >>> (1 : Nat)).cpopNatRec remaining 0 + (word.getLsbD 0).toNat =
      word.cpopNatRec (remaining + 1) 0 := by
  induction remaining with
  | zero => simp
  | succ remaining previous =>
    rw [BitVec.cpopNatRec_succ (x := word >>> (1 : Nat)),
      BitVec.cpopNatRec_eq (acc := 0 + ((word >>> (1 : Nat)).getLsbD remaining).toNat),
      BitVec.cpopNatRec_succ (x := word) (n := remaining + 1),
      BitVec.cpopNatRec_eq (acc := 0 + (word.getLsbD (remaining + 1)).toNat),
      ← previous]
    simp only [BitVec.getLsbD_ushiftRight, Nat.zero_add, Nat.add_comm 1 remaining]
    ac_rfl

theorem scanCorrect (remaining : Nat) (word total : Word)
    (bound : total.toNat + remaining < 2 ^ 32) :
    (scan remaining word total).toNat = total.toNat + word.cpopNatRec remaining 0 := by
  induction remaining generalizing word total with
  | zero => simp [scan]
  | succ remaining previous =>
    have lowBit : (word &&& 1#32).toNat = (word.getLsbD 0).toNat := by
      rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
      cases word.getLsbD 0 <;> decide
    have lowBound : (word.getLsbD 0).toNat ≤ 1 := by cases word.getLsbD 0 <;> decide
    have addExact : (total + (word &&& 1#32)).toNat = total.toNat + (word.getLsbD 0).toNat := by
      rw [BitVec.toNat_add_of_lt, lowBit]
      omega
    have nextBound : (total + (word &&& 1#32)).toNat + remaining < 2 ^ 32 := by omega
    rw [scan, previous _ _ nextBound, addExact, Nat.add_assoc, ← cpopShift]
    ac_rfl

def inputBits (memory : Memory) (input : Word) : BitVec 128 :=
  let next := input + 4
  let third := next + 4
  let fourth := third + 4
  memory fourth ++ memory third ++ memory next ++ memory input

theorem scanInputCorrect (memory : Memory) (input : Word) :
    (scanInput memory input).toNat = (inputBits memory input).cpop.toNat := by
  have scanWord (word total : Word) (bound : total.toNat ≤ 96) :
      (scan 32 word total).toNat = total.toNat + word.cpop.toNat := by
    rw [BitVec.toNat_cpop, scanCorrect]
    omega
  have first := scanWord (memory input) 0#32 (by decide)
  have second := scanWord (memory (input + 4)) (scan 32 (memory input) 0#32) (by
    rw [first, BitVec.toNat_zero, Nat.zero_add]
    have := BitVec.toNat_cpop_le (memory input)
    omega)
  have third := scanWord (memory (input + 4 + 4))
    (scan 32 (memory (input + 4)) (scan 32 (memory input) 0#32)) (by
      rw [second, first, BitVec.toNat_zero, Nat.zero_add]
      have := BitVec.toNat_cpop_le (memory input)
      have := BitVec.toNat_cpop_le (memory (input + 4))
      omega)
  have fourth := scanWord (memory (input + 4 + 4 + 4))
    (scan 32 (memory (input + 4 + 4)) (scan 32 (memory (input + 4)) (scan 32 (memory input) 0#32))) (by
      rw [third, second, first, BitVec.toNat_zero, Nat.zero_add]
      have := BitVec.toNat_cpop_le (memory input)
      have := BitVec.toNat_cpop_le (memory (input + 4))
      have := BitVec.toNat_cpop_le (memory (input + 4 + 4))
      omega)
  simp only [scanInput, fourth, third, second, first, BitVec.toNat_zero,
    Nat.zero_add, inputBits, BitVec.toNat_cpop_append]
  ac_rfl

-- The four input words that both routines read.
def inputAddresses (input : Word) : List Word :=
  [input, input + 4, input + 4 + 4, input + 4 + 4 + 4]

end Specification

end Riscfree
