import RangeInsert.Empty.Execution

namespace Riscfree.RangeInsert.Empty

open LeanRV32D RV32IM
open Riscfree.RV32 Riscfree.RawVec

private theorem trackedRegs (indices : List (Fin 32)) (value : Fin 32 → Word)
    (original : Machine) (memory : ByteMemory) :
    (writeTracked indices value { original with mem := memory }).regs =
      (writeTracked indices value original).regs := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [writeTracked, writeX, write_reg_state, ih]

private theorem frameRegisters (base returnPC : Word) (original : Machine)
    (memory : ByteMemory) (initial : Snapshot) (key : Register)
    (notPc : key ≠ Register.PC) (notNext : key ≠ Register.nextPC) :
    (sync base { original with mem := memory } { initial with pc := returnPC }).regs.get? key =
      (sync base original { initial with pc := 0 }).regs.get? key := by
  unfold sync
  rw [readUnchanged _ _ (Ne.symm notPc), readUnchanged _ _ (Ne.symm notNext),
    readUnchanged _ _ (Ne.symm notPc), readUnchanged _ _ (Ne.symm notNext)]
  exact congrArg (fun regs => regs.get? key)
    (trackedRegs (tracked Snapshot) (RegisterView.value initial) original memory)

/-- An empty input returns in 19 instructions. Every register except PC and
nextPC is preserved, including the stack pointer. Only the 48-byte stack
frame can be modified. -/
theorem Premises.run {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (premises : Premises base returnAddress original initial) :
    ∃ final, Riscfree.RV32.run 19 original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (∀ key : Register, key ≠ Register.PC → key ≠ Register.nextPC →
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]? := by
  let final := sync base { original with mem := pushed original.mem initial }
    { initial with pc := returnAddress - base }
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (Riscfree.RV32.run 19) premises.entry).trans (runEmpty premises)
  · have read := syncReadPC (base := base)
      (frame := { original with mem := pushed original.mem initial })
      { initial with pc := returnAddress - base }
    apply readReg_succ.mp
    change Sail.readReg Register.PC final = .ok returnAddress final
    have target : base + (returnAddress - base) = returnAddress := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    exact target ▸ read
  · intro key notPc notNext
    exact (frameRegisters base _ original _ initial key notPc notNext).trans
      (congrArg (fun state => state.regs.get? key) premises.entry.symm)
  · intro byte outside
    exact pushedOutside original.mem initial premises.frameFits byte outside

end Riscfree.RangeInsert.Empty
