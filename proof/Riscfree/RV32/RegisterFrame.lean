import Riscfree.RV32.Execution

namespace Riscfree.RV32

open LeanRV32D RV32IM

@[simp] theorem writeMem (state : Machine) (key : Register) (value : RegisterType key) :
    (write_reg_state state key value).mem = state.mem := rfl

theorem writeOverwrite (state : Machine) (key : Register) (old new : RegisterType key) :
    write_reg_state (write_reg_state state key old) key new = write_reg_state state key new := by
  unfold write_reg_state
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro query
  by_cases same : key = query
  · subst query
    simp [Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, same]

theorem writeCommute (state : Machine) (first second : Register)
    (left : RegisterType first) (right : RegisterType second) (different : first ≠ second) :
    write_reg_state (write_reg_state state first left) second right =
      write_reg_state (write_reg_state state second right) first left := by
  unfold write_reg_state
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro query
  by_cases firstMatch : first = query
  · subst query
    simp [Std.ExtDHashMap.get?_insert, Ne.symm different]
  · by_cases secondMatch : second = query
    · subst query
      simp [Std.ExtDHashMap.get?_insert, different]
    · simp [Std.ExtDHashMap.get?_insert, firstMatch, secondMatch]

theorem readUnchanged (state : Machine) {readKey writeKey : Register}
    (value : RegisterType writeKey) (different : writeKey ≠ readKey) :
    (write_reg_state state writeKey value).regs.get? readKey = state.regs.get? readKey := by
  simp [write_reg_state, Std.ExtDHashMap.get?_insert, different]

theorem stepWrite (state : Machine) (word : BitVec 32)
    (operation : instruction) (dest : Fin 32) (next value : BitVec 32)
    (fetched : LeanRV32D.Functions.fetch () state = .ok (.F_Base word) state)
    (decoded : LeanRV32D.Functions.ext_decode word state = .ok operation state)
    (effect : execute_instruction operation state = .ok (.Retire_Success ())
      (write_reg_state (write_reg_state state Register.nextPC next) (reg_of_fin dest)
        ((register_type_reg_of_fin_equiv dest) ▸ value))) :
    step state = some
      (write_reg_state (write_reg_state (write_reg_state state Register.nextPC next) (reg_of_fin dest)
          ((register_type_reg_of_fin_equiv dest) ▸ value)) Register.PC next) := by
  apply stepOfEffects state _ word operation next fetched decoded effect
  apply readReg_of_write_other_reg_state _ reg_of_fin_neq_nextPC.symm
  exact readReg_succ.mpr (writeReg_get_same state)

theorem stepSetPC (state : Machine) (word : BitVec 32)
    (operation : instruction) (next : BitVec 32)
    (fetched : LeanRV32D.Functions.fetch () state = .ok (.F_Base word) state)
    (decoded : LeanRV32D.Functions.ext_decode word state = .ok operation state)
    (effect : execute_instruction operation state = .ok (.Retire_Success ())
      (write_reg_state state Register.nextPC next)) :
    step state = some (write_reg_state (write_reg_state state Register.nextPC next) Register.PC next) := by
  apply stepOfEffects state _ word operation next fetched decoded effect
  exact readReg_succ.mpr (writeReg_get_same state)

end Riscfree.RV32
