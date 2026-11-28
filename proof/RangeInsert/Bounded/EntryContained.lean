import RangeInsert.Bounded.EntryPredecessor
import RangeInsert.Nonempty.Contained

/-! The bounded routine's run for a nonempty input whose end is covered by its
predecessor. After the shared prefix and the verified upper-bound search,
the entry point finds no strict gap, finds that the end is already covered,
sets the OK status, and returns through the common epilogue without writing
the map or the cached length. -/

namespace Riscfree.RangeInsert.Bounded.EntryContained

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open Empty (Snapshot frameBase OutsideFrame pushed pushedOutside restore restoreRegisters returnPc)
open EntryEmpty (Frame)
open EntryPredecessor (Map Inspected inspectPredecessor)
open Entry
open Nonempty (Call Arguments noStrictGap)

set_option maxHeartbeats 2000000

/-- The exact instruction count of the covered path: 33 through the
predecessor inspection, including the verified search, then the gap and
coverage branches, the OK status, the jump, and the 9-instruction epilogue. -/
def containedCount (call : Call) : Nat := 46 + call.search.count .upper

/-- Premises of the covered path. `found` and `covered` select the path. -/
structure Premises (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) : Prop extends Frame base returnAddress original initial where
  arguments : Arguments initial call
  map : Map base original initial.sp call
  nonempty : call.start.toNat ≤ call.stop.toNat
  found : 0 < call.rank
  covered : call.stop.toNat ≤ call.predecessor.value.toNat

theorem runContained {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (premises : Premises base returnAddress original initial call) :
    ∃ state : Snapshot,
      run (containedCount call) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := pushed original.mem initial }
          (restore initial { state with a0 := 0 } (returnAddress - base))) ∧
      (state.t0 = initial.t0 ∧ state.t1 = initial.t1 ∧ state.a6 = initial.a6 ∧
        state.a7 = initial.a7 ∧ state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧
        state.s8 = initial.s8 ∧ state.s9 = initial.s9 ∧ state.s10 = initial.s10) := by
  obtain ⟨state, inspected, regs⟩ := inspectPredecessor premises.toFrame premises.arguments
    premises.map premises.nonempty premises.found
  have machine := premises.mode.toMachineState
  have image := premises.toFrame.pushedImage
  have touches : state.a4 = 0#32 := by
    rw [regs.gap]
    exact noStrictGap (Nat.le_trans premises.nonempty premises.covered)
  have covered : state.s1.toNat ≤ state.a2.toNat := by
    rw [regs.stop, regs.predecessorEnd]
    exact premises.covered
  have tail : run 13 (sync base { original with mem := pushed original.mem initial } state) =
      some (sync base { original with mem := pushed original.mem initial }
        (restore initial { state with pc := 0x1a4, a0 := 0 } (returnAddress - base))) := by
    have gapStep := step8c machine image state regs.pc
    rw [if_pos touches] at gapStep
    refine runStep gapStep ?_
    have coveredStep := step130 machine image { state with pc := 0x130 } rfl
    simp only [if_pos covered] at coveredStep
    refine runStep coveredStep ?_
    refine runStep (step28 machine image _ rfl) ?_
    refine runStep (step2c machine image _ rfl) ?_
    exact premises.toFrame.epilogue _ rfl regs.sp
  refine ⟨{ state with pc := 0x1a4 }, ?_, regs.untouched⟩
  rw [show containedCount call = (33 + call.search.count .upper) + 13 by
    unfold containedCount; omega, runAdd, inspected, Option.bind_some]
  exact tail

/-- A nonempty input covered by its predecessor returns OK after exactly
`46 + upper-bound count` instructions. Every register except PC, nextPC,
and a0–a5 is preserved. Only the entry's 48-byte stack frame can be
modified, so the map and the cached length are unchanged. -/
theorem Premises.run {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call}
    (premises : Premises base returnAddress original initial call) :
    ∃ final, Riscfree.RV32.run (containedCount call) original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some (0#32) ∧
      (∀ key ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]? := by
  obtain ⟨state, ran, kept⟩ := runContained premises
  let final := restore initial { state with a0 := 0 } (returnAddress - base)
  have pc := returnPc (base := base) { original with mem := pushed original.mem initial } final rfl
  have registers := restoreRegisters premises.entry (pushed original.mem initial)
    { state with a0 := 0 } (returnAddress - base) kept
  refine ⟨_, (congrArg (Riscfree.RV32.run (containedCount call)) premises.entry).trans ran,
    pc, ?_, registers, fun byte outside => ?_⟩
  · exact readReg_succ.mp (syncRead (base := base)
      (frame := { original with mem := pushed original.mem initial }) final (index := 10) (by decide))
  · rw [syncMem]
    exact pushedOutside original.mem initial premises.frameFits byte outside

end Riscfree.RangeInsert.Bounded.EntryContained
