import Riscfree.RV32.Steps
import PicoFV.RV32IM.RVSail.Opcodes.xor
import PicoFV.RV32IM.RVSail.Opcodes.xori

/-! Generic snapshot steps for XOR and XORI, from Pico FV's equivalences. -/

namespace Riscfree.RV32.Step

open LeanRV32D LeanRV32D.Functions RV32IM

variable {S : Type} [RegisterView S] {base : BitVec 32} {frame : Machine} {state next : S}
  {word : BitVec 32}

theorem xor {left right dest : regidx} {leftValue rightValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.RTYPE (right, left, dest, .XOR)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (leftValue ^^^ rightValue)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_XOR_equiv
    ((OpcodeSpec.RV32.spec_XOR_hypotheses (r1 := left) (r2 := right) (rd := dest)).mpr
      ⟨syncReadPC state, leftRead, rightRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_XOR, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem xori {source dest : regidx} {imm : BitVec 12} {sourceValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.ITYPE (imm, source, dest, .XORI)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (sourceValue ^^^ imm.signExtend 32)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_XORI_equiv
    ((OpcodeSpec.RV32.spec_XORI_hypotheses (r1 := source) (rd := dest) (imm := imm)).mpr
      ⟨syncReadPC state, sourceRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_XORI, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

end Riscfree.RV32.Step
