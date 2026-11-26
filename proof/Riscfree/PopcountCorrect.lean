import Riscfree.PopcountSimulation

namespace Riscfree.Popcount

open LeanRV32D RV32IM RV32

private theorem Trace.sailRun (trace : Trace base initial.a0 count first last)
    (platform : Platform base frame initial)
    (data : first.memory = initial.memory) (registers : first.other = initial.other) :
    RV32.run count (sync base frame first) = some (sync base frame last) := by
  induction trace with
  | done => rfl
  | next guard step _ ih =>
    obtain ⟨sailStep, dataAfter, regsAfter⟩ := stepRefines platform _ _ guard data registers step
    simp only [RV32.run, sailStep, Option.bind_some]
    exact ih dataAfter regsAfter

-- The input view describes the four words in Sail byte memory. A retired
-- instruction updates the architectural PC and Sail's internal nextPC.
-- Every other register outside the six documented scratch registers is framed.
theorem popcount128SailCorrect (base : Word) (machine : Machine) (initial : State)
    (entry : machine = sync base machine { initial with pc := 0 })
    (platform : Platform base machine initial) :
    ∃ final, RV32.run 664 machine = some final ∧
      final.regs.get? Register.PC = some (initial.other 1) ∧
      (final.regs.get? Register.x10).map BitVec.toNat =
        some (inputBits initial.memory initial.a0).cpop.toNat ∧
      final.mem = machine.mem ∧
      ∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x7, .x10, .x28, .x29],
        final.regs.get? register = machine.regs.get? register := by
  obtain ⟨last, trace⟩ := wholeTrace base initial
  have actual := trace.sailRun platform rfl rfl
  have correct := Riscfree.popcount128Correct base initial platform.returnLow
  rw [trace.run_eq] at correct
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at correct
  refine ⟨sync base machine last, ?_, ?_, ?_, syncMem _ _ _, syncFrame _ _ _⟩
  · exact (congrArg (RV32.run 664) entry).trans actual
  · exact readReg_succ.mp ((correct.1) ▸ syncReadPC base machine last)
  · have read : Sail.readReg Register.x10 (sync base machine last) =
        .ok last.a0 (sync base machine last) := syncReadX10 base machine last
    rw [readReg_succ.mp read, Option.map_some, correct.2.1]

#print axioms popcount128SailCorrect

end Riscfree.Popcount
