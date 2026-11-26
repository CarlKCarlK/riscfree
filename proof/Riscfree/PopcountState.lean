import Popcount
import Riscfree.RV32.RegisterFrame

namespace Riscfree.Popcount

open LeanRV32D RV32IM Riscfree.RV32

-- PC and nextPC are synchronized at retirement. The remaining registers
-- and all byte memory come from the original Sail state.
def scratch (frame : Machine) (state : State) : Machine :=
  let frame := write_reg_state frame Register.x5 state.t0
  let frame := write_reg_state frame Register.x6 state.t1
  let frame := write_reg_state frame Register.x7 state.t2
  let frame := write_reg_state frame Register.x10 state.a0
  let frame := write_reg_state frame Register.x28 state.t3
  write_reg_state frame Register.x29 state.t4

def sync (base : Word) (frame : Machine) (state : State) : Machine :=
  let pc := base + state.pc
  write_reg_state (write_reg_state (scratch frame state) Register.nextPC pc) Register.PC pc

@[simp] theorem syncMem (base : Word) (frame : Machine) (state : State) :
    (sync base frame state).mem = frame.mem := rfl

theorem syncFrame (base : Word) (frame : Machine) (state : State) (register : Register)
    (outside : register ∉ [Register.PC, .nextPC, .x5, .x6, .x7, .x10, .x28, .x29]) :
    (sync base frame state).regs.get? register = frame.regs.get? register := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨pc, next, x5, x6, x7, x10, x28, x29⟩ := outside
  simp [sync, scratch, readUnchanged, Ne.symm pc, Ne.symm next, Ne.symm x5,
    Ne.symm x6, Ne.symm x7, Ne.symm x10, Ne.symm x28, Ne.symm x29]

theorem syncReadFrame (base : Word) (frame : Machine) (state : State) (register : Register)
    (outside : register ∉ [Register.PC, .nextPC, .x5, .x6, .x7, .x10, .x28, .x29])
    {value : RegisterType register}
    (read : Sail.readReg register frame = .ok value frame) :
    Sail.readReg register (sync base frame state) = .ok value (sync base frame state) :=
  readReg_succ.mpr ((syncFrame base frame state register outside).trans (readReg_succ.mp read))

theorem syncReadPC (base : Word) (frame : Machine) (state : State) :
    Sail.readReg Register.PC (sync base frame state) = .ok (base + state.pc) (sync base frame state) :=
  readReg_succ.mpr (writeReg_get_same _)

theorem syncSetPC (base : Word) (frame : Machine) (state : State) (next : Word) :
    write_reg_state (write_reg_state (sync base frame state) Register.nextPC (base + next))
      Register.PC (base + next) = sync base frame { state with pc := next } := by
  unfold sync
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite, writeOverwrite]
  rfl

theorem syncSetX5 (base : Word) (frame : RV32.Machine) (state : State) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x5
      value) Register.PC (base + next) = sync base frame { state with pc := next, t0 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x5 _ _ (by decide), writeCommute _ .nextPC .x5 _ _ (by decide),
    writeCommute _ .x29 .x5 _ _ (by decide),
    writeCommute _ .x28 .x5 _ _ (by decide),
    writeCommute _ .x10 .x5 _ _ (by decide),
    writeCommute _ .x7 .x5 _ _ (by decide),
    writeCommute _ .x6 .x5 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX5 (base : Word) (frame : RV32.Machine) (state : State) :
    read_xreg (5 : Fin 32) (sync base frame state) = .ok state.t0 (sync base frame state) := by
  change Sail.readReg Register.x5 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX6 (base : Word) (frame : RV32.Machine) (state : State) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x6
      value) Register.PC (base + next) = sync base frame { state with pc := next, t1 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x6 _ _ (by decide), writeCommute _ .nextPC .x6 _ _ (by decide),
    writeCommute _ .x29 .x6 _ _ (by decide),
    writeCommute _ .x28 .x6 _ _ (by decide),
    writeCommute _ .x10 .x6 _ _ (by decide),
    writeCommute _ .x7 .x6 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX6 (base : Word) (frame : RV32.Machine) (state : State) :
    read_xreg (6 : Fin 32) (sync base frame state) = .ok state.t1 (sync base frame state) := by
  change Sail.readReg Register.x6 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX7 (base : Word) (frame : RV32.Machine) (state : State) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x7
      value) Register.PC (base + next) = sync base frame { state with pc := next, t2 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x7 _ _ (by decide), writeCommute _ .nextPC .x7 _ _ (by decide),
    writeCommute _ .x29 .x7 _ _ (by decide),
    writeCommute _ .x28 .x7 _ _ (by decide),
    writeCommute _ .x10 .x7 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX7 (base : Word) (frame : RV32.Machine) (state : State) :
    read_xreg (7 : Fin 32) (sync base frame state) = .ok state.t2 (sync base frame state) := by
  change Sail.readReg Register.x7 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX10 (base : Word) (frame : RV32.Machine) (state : State) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x10
      value) Register.PC (base + next) = sync base frame { state with pc := next, a0 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x10 _ _ (by decide), writeCommute _ .nextPC .x10 _ _ (by decide),
    writeCommute _ .x29 .x10 _ _ (by decide),
    writeCommute _ .x28 .x10 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX10 (base : Word) (frame : RV32.Machine) (state : State) :
    read_xreg (10 : Fin 32) (sync base frame state) = .ok state.a0 (sync base frame state) := by
  change Sail.readReg Register.x10 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX28 (base : Word) (frame : RV32.Machine) (state : State) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x28
      value) Register.PC (base + next) = sync base frame { state with pc := next, t3 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x28 _ _ (by decide), writeCommute _ .nextPC .x28 _ _ (by decide),
    writeCommute _ .x29 .x28 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX28 (base : Word) (frame : RV32.Machine) (state : State) :
    read_xreg (28 : Fin 32) (sync base frame state) = .ok state.t3 (sync base frame state) := by
  change Sail.readReg Register.x28 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX29 (base : Word) (frame : RV32.Machine) (state : State) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x29
      value) Register.PC (base + next) = sync base frame { state with pc := next, t4 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x29 _ _ (by decide), writeCommute _ .nextPC .x29 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX29 (base : Word) (frame : RV32.Machine) (state : State) :
    read_xreg (29 : Fin 32) (sync base frame state) = .ok state.t4 (sync base frame state) := by
  change Sail.readReg Register.x29 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

end Riscfree.Popcount
