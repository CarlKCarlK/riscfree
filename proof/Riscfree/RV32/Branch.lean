import Riscfree.RV32.RegisterFrame
import PicoFV.RV32IM.RVSail.Opcodes.beq
import PicoFV.RV32IM.RVSail.Opcodes.bne
import PicoFV.RV32IM.RVSail.Opcodes.bgeu
import PicoFV.RV32IM.RVSail.Opcodes.bltu
import PicoFV.RV32IM.RVSail.Opcodes.jal

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

private theorem lowBitClear (address : BitVec 32) (aligned : address % 4 = 0)
    (bit : Nat) (small : bit < 2) : address[bit]'(by omega) = false := by
  have divisible := congrArg BitVec.toNat aligned
  change address.toNat % 2 ^ 2 = 0 at divisible
  have masked := Nat.testBit_mod_two_pow address.toNat 2 bit
  rw [divisible] at masked
  simpa [small, BitVec.getElem_eq_testBit_toNat] using masked.symm

-- Use Pico's pure branch equivalence and prove the alignment fact in the
-- kernel. Pico's higher-level branch wrapper uses compiled evaluation for it.
theorem branchEffect (state : Machine) (left right : regidx) (offset : BitVec 13)
    (pc leftValue rightValue : BitVec 32)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (leftRead : read_xreg (regidx_to_fin left) state = .ok leftValue state)
    (rightRead : read_xreg (regidx_to_fin right) state = .ok rightValue state)
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (aligned : leftValue ≠ rightValue → (pc + offset.signExtend 32) % 4 = 0) :
    execute_instruction (.BTYPE (offset, right, left, .BNE)) state =
      .ok (.Retire_Success ()) (write_reg_state state Register.nextPC
        (if leftValue = rightValue then pc + 4#32 else pc + offset.signExtend 32)) := by
  rw [PureSpec.RV32.execute_BNE_pure_equiv
    ⟨offset, leftValue, rightValue, pc⟩ left right leftRead rightRead pcRead misaRead]
  by_cases same : leftValue = rightValue
  · simp [PureSpec.RV32.execute_BNE_pure, same, writeReg_state_success]
  · have low := lowBitClear _ (aligned same) 0 (by decide)
    have next := lowBitClear _ (aligned same) 1 (by decide)
    simp [PureSpec.RV32.execute_BNE_pure, same, low, next, writeReg_state_success]

theorem beqEffect (state : Machine) (left right : regidx) (offset : BitVec 13)
    (pc leftValue rightValue : BitVec 32)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (leftRead : read_xreg (regidx_to_fin left) state = .ok leftValue state)
    (rightRead : read_xreg (regidx_to_fin right) state = .ok rightValue state)
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (aligned : leftValue = rightValue → (pc + offset.signExtend 32) % 4 = 0) :
    execute_instruction (.BTYPE (offset, right, left, .BEQ)) state =
      .ok (.Retire_Success ()) (write_reg_state state Register.nextPC
        (if leftValue = rightValue then pc + offset.signExtend 32 else pc + 4#32)) := by
  rw [PureSpec.RV32.execute_BEQ_pure_equiv
    ⟨offset, leftValue, rightValue, pc⟩ left right leftRead rightRead pcRead misaRead]
  by_cases same : leftValue = rightValue
  · have low := lowBitClear _ (aligned same) 0 (by decide)
    have next := lowBitClear _ (aligned same) 1 (by decide)
    simp [PureSpec.RV32.execute_BEQ_pure, same, low, next, writeReg_state_success]
  · simp [PureSpec.RV32.execute_BEQ_pure, same, writeReg_state_success]

theorem bgeuEffect (state : Machine) (left right : regidx) (offset : BitVec 13)
    (pc leftValue rightValue : BitVec 32)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (leftRead : read_xreg (regidx_to_fin left) state = .ok leftValue state)
    (rightRead : read_xreg (regidx_to_fin right) state = .ok rightValue state)
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (aligned : (pc + offset.signExtend 32) % 4 = 0) :
    execute_instruction (.BTYPE (offset, right, left, .BGEU)) state =
      .ok (.Retire_Success ()) (write_reg_state state Register.nextPC
        (if rightValue.toNat ≤ leftValue.toNat then pc + offset.signExtend 32 else pc + 4#32)) := by
  rw [PureSpec.RV32.execute_BGEU_pure_equiv
    ⟨offset, leftValue, rightValue, pc⟩ left right leftRead rightRead pcRead misaRead]
  have low := lowBitClear _ aligned 0 (by decide)
  have next := lowBitClear _ aligned 1 (by decide)
  by_cases taken : rightValue.toNat ≤ leftValue.toNat <;>
    simp [PureSpec.RV32.execute_BGEU_pure, taken, low, next, writeReg_state_success]

theorem bltuEffect (state : Machine) (left right : regidx) (offset : BitVec 13)
    (pc leftValue rightValue : BitVec 32)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (leftRead : read_xreg (regidx_to_fin left) state = .ok leftValue state)
    (rightRead : read_xreg (regidx_to_fin right) state = .ok rightValue state)
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (aligned : (pc + offset.signExtend 32) % 4 = 0) :
    execute_instruction (.BTYPE (offset, right, left, .BLTU)) state =
      .ok (.Retire_Success ()) (write_reg_state state Register.nextPC
        (if leftValue.toNat < rightValue.toNat then pc + offset.signExtend 32 else pc + 4#32)) := by
  rw [PureSpec.RV32.execute_BLTU_pure_equiv
    ⟨offset, leftValue, rightValue, pc⟩ left right leftRead rightRead pcRead misaRead]
  have low := lowBitClear _ aligned 0 (by decide)
  have next := lowBitClear _ aligned 1 (by decide)
  by_cases taken : leftValue.toNat < rightValue.toNat <;>
    simp [PureSpec.RV32.execute_BLTU_pure, taken, low, next, writeReg_state_success]

-- `j` (`jal x0`) through Pico's pure equivalence, with the alignment fact
-- proved in the kernel. Pico's `execute_JAL_equiv` uses compiled evaluation
-- for it (`BitVec.mod_4_zero_equiv_32`).
theorem jalEffect (state : Machine) (imm : BitVec 21) (pc : BitVec 32)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (aligned : (pc + imm.signExtend 32) % 4 = 0) :
    execute_instruction (.JAL (imm, .Regidx 0)) state =
      .ok (.Retire_Success ()) (write_reg_state state Register.nextPC (pc + imm.signExtend 32)) := by
  rw [PureSpec.RV32.execute_JAL_pure_equiv ⟨imm, 0, pc⟩ (.Regidx 0) pcRead misaRead]
  have low := lowBitClear _ aligned 0 (by decide)
  have next := lowBitClear _ aligned 1 (by decide)
  simp [PureSpec.RV32.execute_JAL_pure, low, next, writeReg_state_success, write_xreg, regidx_to_fin]

end Riscfree.RV32
