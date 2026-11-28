import RangeInsert.Bounded.EntryEmpty
import RawVec.Model

namespace Riscfree.RangeInsert.Bounded.EntryEmptyNonvacuity

open LeanRV32D RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Empty (Snapshot pushed)
open EntryEmpty (Premises runEmpty)

private def image : Model.Image where
  word := Model.tableWord 0x400 instructions
  keys := List.range' 0x1000 (4 * instructions.length)

private def dataContents : Model.Contents Word :=
  ⟨0, 0, fun _ => 0⟩

private def initial : Snapshot where
  ra := Model.returnTo
  sp := 0x5000
  s0 := 1
  s1 := 2
  s2 := 3
  s3 := 4
  s4 := 5
  s5 := 6
  a0 := 0x3000
  a1 := 0
  a4 := 0
  a5 := 0
  a2 := 9
  a3 := 8

private def machine : Machine :=
  sync Model.codeBase (Model.frame image dataContents) initial

theorem witness : Premises Model.codeBase Model.returnTo machine initial := by
  have modeled : Model.Modeled image dataContents machine := Model.syncModeled _ _ _
  have mode : MachineMode machine Model.returnTo :=
    { (Model.frameState dataContents).atSync Model.codeBase initial with
      returnLow := by decide
      returnNext := by decide
      ra := syncRead (base := Model.codeBase) (frame := Model.frame image dataContents)
        initial (index := 1) (by decide) }
  have code : CodeImage instructions Model.codeBase machine := by
    refine Model.tableImage modeled instructions Model.codeBase 0x1000 rfl (by decide)
      (by decide) ?_ ?_
    · intro index bound byte small
      simp only [image, List.mem_range'_1]
      omega
    · intro index bound
      exact Model.tableWordAt 0x400 instructions bound
  refine ⟨⟨(syncSync _ _).symm, rfl, mode, code, by decide, ?_, ?_, ?_⟩, by decide⟩
  · intro byte _ below
    left
    change byte < 0x5000 - 48
    have size : Model.codeBase.toNat + 4 * instructions.length ≤ 0x5000 - 48 := by decide
    omega
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Model.readable modeled (by decide) (by decide)
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Model.writable modeled (by decide) (by decide)

theorem witnessReturns :
    Riscfree.RV32.run 21 machine =
      some (sync Model.codeBase { machine with mem := pushed machine.mem initial }
        { initial with pc := Model.returnTo - Model.codeBase, a0 := 0 }) :=
  runEmpty witness

end Riscfree.RangeInsert.Bounded.EntryEmptyNonvacuity
