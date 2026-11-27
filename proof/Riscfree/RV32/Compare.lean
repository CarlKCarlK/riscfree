import Riscfree.RV32.Steps
import PicoFV.RV32IM.RVSail.Opcodes.sltiu
import PicoFV.RV32IM.RVSail.Opcodes.sltu

namespace Riscfree.RV32.Step

open LeanRV32D LeanRV32D.Functions RV32IM

variable {S : Type} [RegisterView S] {base : BitVec 32} {frame : Machine} {state next : S}
  {word : BitVec 32}

def lessWord (left right : BitVec 32) : BitVec 32 :=
  (if left.toNat < right.toNat then 1#1 else 0#1).setWidth 32

theorem sltu {left right dest : regidx} {leftValue rightValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.RTYPE (right, left, dest, .SLTU)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (lessWord leftValue rightValue)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_SLTU_equiv
    ((OpcodeSpec.RV32.spec_SLTU_hypotheses (r1 := left) (r2 := right) (rd := dest)).mpr
      ⟨syncReadPC state, leftRead, rightRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_SLTU, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member, lessWord] using effect

theorem sltiu {source dest : regidx} {imm : BitVec 12} {sourceValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.ITYPE (imm, source, dest, .SLTIU)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (lessWord sourceValue (imm.signExtend 32))) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_SLTIU_equiv
    ((OpcodeSpec.RV32.spec_SLTIU_hypotheses (r1 := source) (rd := dest) (imm := imm)).mpr
      ⟨syncReadPC state, sourceRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_SLTIU, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member, lessWord] using effect

end Riscfree.RV32.Step
