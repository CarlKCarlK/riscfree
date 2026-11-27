import RangeInsert.Nonempty.Predecessor
import RangeInsert.Empty

/-! The linked run for a nonempty input whose end is covered by its
predecessor. After the shared prefix and the verified upper-bound search,
the entry point loads the predecessor's end, finds no strict gap, finds
that the end is already covered, and returns through the common epilogue
without writing the map or the cached length. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Empty (Snapshot Frame frameBase OutsideFrame pushed pushedOutside restore restoreRegisters
  returnPc)

set_option maxHeartbeats 2000000

/-- The exact instruction count of the covered path: 19 to the call, the
verified search, 16 to the epilogue, and the 9-instruction epilogue. -/
def Call.containedCount (call : Call) : Nat := 44 + call.search.count .upper

/-- Premises of the covered path. `found` and `covered` select the path:
some key is at most `start`, and the last such entry ends at or after
`stop`. The path writes neither the map nor the cached length, so it needs
no write permission outside the frame. -/
structure ContainedPremises (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) : Prop extends Frame base returnAddress original initial where
  arguments : Arguments initial call
  map : Map base original initial.sp call
  nonempty : call.start.toNat ≤ call.stop.toNat
  found : 0 < call.rank
  covered : call.stop.toNat ≤ call.predecessor.value.toNat

-- No strict gap follows a predecessor that ends at or after `start`,
-- including a predecessor that ends at `u32::MAX`.
theorem noStrictGap {predecessorEnd start : Word} (reaches : start.toNat ≤ predecessorEnd.toNat) :
    Step.lessWord predecessorEnd 0xffffffff#32 &&& Step.lessWord (predecessorEnd + 1#32) start =
      0#32 := by
  unfold Step.lessWord
  by_cases below : predecessorEnd.toNat < (0xffffffff#32).toNat
  · have noGap : ¬ (predecessorEnd + 1#32).toNat < start.toNat := by
      rw [BitVec.toNat_add]
      change ¬ (predecessorEnd.toNat + 1) % 2 ^ 32 < start.toNat
      change predecessorEnd.toNat < 4294967295 at below
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg noGap]
    split <;> rfl
  · rw [if_neg below]
    split <;> rfl

theorem runContained {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (premises : ContainedPremises base returnAddress original initial call) :
    ∃ state : Snapshot,
      run call.containedCount (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := pushed original.mem initial }
          (restore initial state (returnAddress - base))) ∧
      (state.t0 = initial.t0 ∧ state.t1 = initial.t1 ∧ state.a6 = initial.a6 ∧
        state.a7 = initial.a7 ∧ state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧
        state.s8 = initial.s8 ∧ state.s9 = initial.s9 ∧ state.s10 = initial.s10) := by
  obtain ⟨state, inspected, regs⟩ := inspectPredecessor premises.toFrame premises.arguments
    premises.map premises.nonempty premises.found
  have machine := premises.mode.toMachineState
  have image := premises.toFrame.pushedImage
  obtain ⟨exit, returned, kept⟩ : ∃ exit : Snapshot,
      run 11 (sync base { original with mem := pushed original.mem initial } state) =
        some (sync base { original with mem := pushed original.mem initial }
          (restore initial exit (returnAddress - base))) ∧
      (exit.t0 = initial.t0 ∧ exit.t1 = initial.t1 ∧ exit.a6 = initial.a6 ∧
        exit.a7 = initial.a7 ∧ exit.s6 = initial.s6 ∧ exit.s7 = initial.s7 ∧
        exit.s8 = initial.s8 ∧ exit.s9 = initial.s9 ∧ exit.s10 = initial.s10) := by
    have touches : state.a4 = 0#32 := by
      rw [regs.gap]
      exact noStrictGap (Nat.le_trans premises.nonempty premises.covered)
    refine ⟨{ state with pc := 0x124 }, runStep (branchTouches machine image _ regs.pc touches) ?_,
      regs.untouched⟩
    refine runStep (branchCovered machine image _ rfl (by
      change state.s1.toNat ≤ state.a2.toNat
      rw [regs.stop, regs.predecessorEnd]
      exact premises.covered)) ?_
    exact premises.toFrame.epilogue _ rfl regs.sp
  refine ⟨exit, ?_, kept⟩
  rw [show call.containedCount = (33 + call.search.count .upper) + 11 by
    unfold Call.containedCount; omega, runAdd, inspected, Option.bind_some]
  exact returned

/-- A nonempty input covered by its predecessor returns after exactly
`44 + upper-bound count` instructions. Every register except PC, nextPC,
and a0–a5 is preserved, including the stack pointer and the callee-saved
registers. Only the entry's 48-byte stack frame can be modified, so the
map and the cached length are unchanged. -/
theorem ContainedPremises.run {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call}
    (premises : ContainedPremises base returnAddress original initial call) :
    ∃ final, Riscfree.RV32.run call.containedCount original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (∀ key ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]? := by
  obtain ⟨state, ran, kept⟩ := runContained premises
  let final := restore initial state (returnAddress - base)
  have pc := returnPc (base := base) { original with mem := pushed original.mem initial } final rfl
  have registers := restoreRegisters premises.entry (pushed original.mem initial) state
    (returnAddress - base) kept
  refine ⟨_, (congrArg (Riscfree.RV32.run call.containedCount) premises.entry).trans ran,
    pc, registers, fun byte outside => ?_⟩
  rw [syncMem]
  exact pushedOutside original.mem initial premises.frameFits byte outside

end Riscfree.RangeInsert.Nonempty
