import RangeInsert.OomReturn
import RawVec.Model

namespace Riscfree.RangeInsert.OomReturn.Nonvacuity

open LeanRV32D RV32IM
open Riscfree.RV32 Riscfree.RawVec
open Empty (Snapshot)
open RawVec.Model (codeBase returnTo)

private def initial : Snapshot :=
  { ra := returnTo, sp := 0x5000, s0 := 1, s1 := 2, s2 := 3, s3 := 4, s4 := 5, s5 := 6,
    a0 := 0x3000, a1 := 0x6000, a2 := 2, a3 := 3, a4 := 0x7000, a5 := 0 }

private def exit : Snapshot :=
  { initial with
    sp := 0x4fd0, ra := 0x1800, s0 := 21, s1 := 22, s2 := 23, s3 := 24,
    s4 := 25, s5 := 26, a0 := 7 }

private def image : Model.Image where
  word index :=
    if 0x13f9 ≤ index then ([6, 5, 4, 3, 2, 1, returnTo] : List Word)[index - 0x13f9]?
    else Model.tableWord 0x400 instructions index
  keys := List.range' 0x1000 (4 * instructions.length) ++ List.range' 0x4fe4 28

private def contents : Model.Contents Word := ⟨0, 0, fun _ => 0⟩

private def machine : Machine :=
  sync codeBase (Model.frame image contents) exit

private theorem stackWord (address value : Word)
    (fits : 0x4fe4 ≤ address.toNat ∧ address.toNat + 4 ≤ 0x5000)
    (aligned : address.toNat % 4 = 0) (valueAt : Model.contents image contents (address.toNat / 4) = value) :
    WordAt (Model.frame image contents).mem address.toNat value := by
  rw [← valueAt]
  apply wordMemoryWord _ _ _ aligned
  intro byte inside
  simp only [Model.keys, image, List.mem_append, List.mem_range'_1]
  omega

theorem witness : Premises codeBase machine initial exit := by
  have modeled : Model.Modeled image contents machine := Model.syncModeled _ _ _
  have code : CodeImage instructions codeBase machine := by
    refine Model.tableImage modeled instructions codeBase 0x1000 rfl (by decide) (by decide) ?_ ?_
    · intro index bound byte inside
      simp only [image, List.mem_append, List.mem_range'_1]
      omega
    · intro index bound
      have length : instructions.length = 10 := rfl
      rw [length] at bound
      simpa only [image, if_neg (show ¬ 0x13f9 ≤ 0x1000 / 4 + index by omega)] using
        (Model.tableWordAt 0x400 instructions (index := index) (by change index < 10; omega))
  refine ⟨(Model.frameState contents).atSync codeBase exit, code, (syncSync _ _).symm,
    rfl, rfl, by decide, by decide, ?_, ?_⟩
  · intro address member
    simp only [savedRegisters, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Model.readable modeled (by decide) (by decide)
  · intro entry member
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stackWord _ _ (by decide) (by decide) (by decide)

theorem witnessReturns :
    Riscfree.RV32.run 10 machine =
      some (sync codeBase machine (Empty.restore initial { exit with a0 := 1 } (returnTo - codeBase))) :=
  witness.run

end Riscfree.RangeInsert.OomReturn.Nonvacuity
