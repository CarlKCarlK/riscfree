import Riscfree.RV32.Branch
import Riscfree.RV32.Memory
import Riscfree.RV32.Snapshot
import PicoFV.RV32IM.RVSail.Opcodes.add
import PicoFV.RV32IM.RVSail.Opcodes.and
import PicoFV.RV32IM.RVSail.Opcodes.andi
import PicoFV.RV32IM.RVSail.Opcodes.auipc
import PicoFV.RV32IM.RVSail.Opcodes.jalr
import PicoFV.RV32IM.RVSail.Opcodes.lui
import PicoFV.RV32IM.RVSail.Opcodes.mul
import PicoFV.RV32IM.RVSail.Opcodes.srli
import PicoFV.RV32IM.RVSail.Opcodes.slli
import PicoFV.RV32IM.RVSail.Opcodes.sub

/-!
# One Sail step on a snapshot

Each lemma takes the fetched word and its Sail decoding, applies Pico FV's
equivalence theorem for that instruction, and returns the next snapshot.
The application supplies the source register reads and checks that the
next snapshot holds the written value and the next PC.
-/

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

variable {S : Type} [RegisterView S] {base : BitVec 32} {frame : Machine} {state next : S}
  {word : BitVec 32}

-- The next snapshot falls through and differs from `state` only in `dest`.
def Writes (state next : S) (dest : Fin 32) (written : BitVec 32) : Prop :=
  RegisterView.pc next = RegisterView.pc state + 4#32 ∧
    ∀ other ∈ tracked S, RegisterView.value next other =
      if other = dest then written else RegisterView.value state other

-- The next snapshot has the given PC and the same tracked registers.
def Jumps (state next : S) (target : BitVec 32) : Prop :=
  RegisterView.pc next = target ∧
    ∀ other ∈ tracked S, RegisterView.value next other = RegisterView.value state other

theorem nonzeroIndex {index : Fin 32} (member : index ∈ tracked S) : index.val ≠ 0 := by
  intro zero
  rw [show index = 0 from Fin.ext zero] at member
  exact RegisterView.nonzero (Snapshot := S) member

-- Pico's low-word multiply is the 32-bit product.
theorem mulLow (left right : BitVec 32) : execute_MUL_pure left right .MUL = left * right := by
  apply BitVec.eq_of_toNat_eq
  simp [execute_MUL_pure, Sail.BitVec.extractLsb, BitVec.extend, BitVec.toNat_mul]

theorem retire {operation : instruction} {dest : Fin 32} {written : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) = .ok operation (sync base frame state))
    (effect : execute_instruction operation (sync base frame state) = .ok (.Retire_Success ())
      (writeX (write_reg_state (sync base frame state) Register.nextPC
        (base + RegisterView.pc state + 4#32)) dest written))
    (member : dest ∈ tracked S) (writes : Writes state next dest written) :
    step (sync base frame state) = some (sync base frame next) := by
  obtain ⟨pcNext, agree⟩ := writes
  rw [BitVec.add_assoc, ← pcNext] at effect
  exact (stepWrite _ _ _ dest _ _ fetched decoded effect).trans
    (congrArg some (syncWrite state next written member agree))

theorem jump {operation : instruction} {target : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) = .ok operation (sync base frame state))
    (effect : execute_instruction operation (sync base frame state) = .ok (.Retire_Success ())
      (write_reg_state (sync base frame state) Register.nextPC (base + target)))
    (jumps : Jumps state next target) :
    step (sync base frame state) = some (sync base frame next) := by
  obtain ⟨pcNext, agree⟩ := jumps
  rw [← pcNext] at effect
  exact (stepSetPC _ _ _ _ fetched decoded effect).trans
    (congrArg some (syncSetPC state next agree))

-- An instruction that writes `dest` and sets the next PC to any target, as a
-- linking jump does.
theorem retireTo {operation : instruction} {dest : Fin 32} {written target : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) = .ok operation (sync base frame state))
    (effect : execute_instruction operation (sync base frame state) = .ok (.Retire_Success ())
      (writeX (write_reg_state (sync base frame state) Register.nextPC (base + target)) dest written))
    (member : dest ∈ tracked S) (pcNext : RegisterView.pc next = target)
    (agree : ∀ other ∈ tracked S, RegisterView.value next other =
      if other = dest then written else RegisterView.value state other) :
    step (sync base frame state) = some (sync base frame next) := by
  rw [← pcNext] at effect
  exact (stepWrite _ _ _ dest _ _ fetched decoded effect).trans
    (congrArg some (syncWrite state next written member agree))

-- Prepend one step to a run.
theorem runStep {first second : Machine} {count : Nat} {result : Option Machine}
    (stepped : step first = some second) (rest : run count second = result) :
    run (count + 1) first = result := by
  simp only [run, stepped, Option.bind_some, rest]

namespace Step

theorem slli {source dest : regidx} {shift : BitVec 6} {sourceValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.SHIFTIOP (shift, source, dest, .SLLI)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (sourceValue <<< (shift % 32))) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_SLLI_equiv
    ((OpcodeSpec.RV32.spec_SLLI_hypotheses (rd := dest) (imm := shift)).mpr
      ⟨syncReadPC state, sourceRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_SLLI, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem bgeu {left right : regidx} {offset : BitVec 13} {leftValue rightValue : BitVec 32}
    {misa : RegisterType Register.misa}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.BTYPE (offset, right, left, .BGEU)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (misaRead : Sail.readReg Register.misa (sync base frame state) = .ok misa (sync base frame state))
    (aligned : (base + RegisterView.pc state + offset.signExtend 32) % 4 = 0)
    (jumps : Jumps state next (if rightValue.toNat ≤ leftValue.toNat then
      RegisterView.pc state + offset.signExtend 32 else RegisterView.pc state + 4#32)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := bgeuEffect _ left right offset _ leftValue rightValue (syncReadPC state)
    leftRead rightRead misaRead aligned
  refine jump fetched decoded ?_ jumps
  rw [effect]
  split <;> simp only [BitVec.add_assoc]

theorem bltu {left right : regidx} {offset : BitVec 13} {leftValue rightValue : BitVec 32}
    {misa : RegisterType Register.misa}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.BTYPE (offset, right, left, .BLTU)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (misaRead : Sail.readReg Register.misa (sync base frame state) = .ok misa (sync base frame state))
    (aligned : (base + RegisterView.pc state + offset.signExtend 32) % 4 = 0)
    (jumps : Jumps state next (if leftValue.toNat < rightValue.toNat then
      RegisterView.pc state + offset.signExtend 32 else RegisterView.pc state + 4#32)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := bltuEffect _ left right offset _ leftValue rightValue (syncReadPC state)
    leftRead rightRead misaRead aligned
  refine jump fetched decoded ?_ jumps
  rw [effect]
  split <;> simp only [BitVec.add_assoc]


theorem addi {source dest : regidx} {imm : BitVec 12} {sourceValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.ITYPE (imm, source, dest, .ADDI)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (sourceValue + imm.signExtend 32)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_ADDI_equiv
    ((OpcodeSpec.RV32.spec_ADDI_hypotheses (imm := imm) (rd := dest)).mpr
      ⟨syncReadPC state, sourceRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_ADDI, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

-- `mv rd, rs` is `addi rd, rs, 0`.
theorem mv {source dest : regidx} {sourceValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.ITYPE (0#12, source, dest, .ADDI)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) sourceValue) :
    step (sync base frame state) = some (sync base frame next) :=
  addi fetched decoded sourceRead member (by
    rwa [show (0#12).signExtend 32 = 0#32 from rfl, BitVec.add_zero])

theorem andi {source dest : regidx} {imm : BitVec 12} {sourceValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.ITYPE (imm, source, dest, .ANDI)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (sourceValue &&& imm.signExtend 32)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_ANDI_equiv
    ((OpcodeSpec.RV32.spec_ANDI_hypotheses (r1 := source) (rd := dest) (imm := imm)).mpr
      ⟨syncReadPC state, sourceRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_ANDI, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem srli {source dest : regidx} {shift : BitVec 6} {sourceValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.SHIFTIOP (shift, source, dest, .SRLI)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (sourceValue >>> (shift % 32))) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_SRLI_equiv
    ((OpcodeSpec.RV32.spec_SRLI_hypotheses (r1 := source) (rd := dest) (imm := shift)).mpr
      ⟨syncReadPC state, sourceRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_SRLI, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem lui {dest : regidx} {imm : BitVec 20}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.UTYPE (imm, dest, .LUI)) (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (imm ++ 0#12)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_LUI_equiv
    ((OpcodeSpec.RV32.spec_LUI_hypotheses (rd := dest) (imm := imm) (state := sync base frame state)
      (pc_val := base + RegisterView.pc state)).mpr (syncReadPC state))
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_LUI, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem add {left right dest : regidx} {leftValue rightValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.RTYPE (right, left, dest, .ADD)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (leftValue + rightValue)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_ADD_equiv
    ((OpcodeSpec.RV32.spec_ADD_hypotheses (r1 := left) (r2 := right) (rd := dest)).mpr
      ⟨syncReadPC state, leftRead, rightRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_ADD, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem sub {left right dest : regidx} {leftValue rightValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.RTYPE (right, left, dest, .SUB)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (leftValue - rightValue)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_SUB_equiv
    ((OpcodeSpec.RV32.spec_SUB_hypotheses (r1 := left) (r2 := right) (rd := dest)).mpr
      ⟨syncReadPC state, leftRead, rightRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_SUB, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem and {left right dest : regidx} {leftValue rightValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.RTYPE (right, left, dest, .AND)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (leftValue &&& rightValue)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_AND_equiv
    ((OpcodeSpec.RV32.spec_AND_hypotheses (r1 := left) (r2 := right) (rd := dest)).mpr
      ⟨syncReadPC state, leftRead, rightRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_AND, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

theorem mul {left right dest : regidx} {leftValue rightValue : BitVec 32} {srs1 srs2 : Signedness}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.MUL (right, left, dest, { result_part := .Low, signed_rs1 := srs1, signed_rs2 := srs2 }))
        (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (leftValue * rightValue)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_MUL_equiv (srs1 := srs1) (srs2 := srs2)
    ((OpcodeSpec.RV32.spec_MUL_hypotheses (r1 := left) (r2 := right) (rd := dest)).mpr
      ⟨syncReadPC state, leftRead, rightRead⟩)
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_MUL, operation_list_effect, operation_effect, mulLow,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

-- The address-local RAM read is a premise; `Platform` supplies it for the input words.
theorem lw {source dest : regidx} {imm : BitVec 12} {pointer loaded : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.LOAD (imm, source, dest, false, 4)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok pointer (sync base frame state))
    (read : vmem_read_addr (.Virtaddr (pointer + imm.signExtend 32)) (imm.signExtend 32) 4
      (.Load .Data) false false false
        (write_reg_state (sync base frame state) Register.nextPC (base + RegisterView.pc state + 4#32)) =
      .ok (.Ok loaded)
        (write_reg_state (sync base frame state) Register.nextPC (base + RegisterView.pc state + 4#32)))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) loaded) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := executeWordLoad _ source dest imm _ pointer loaded (syncReadPC state) sourceRead read
  refine retire fetched decoded ?_ member writes
  simpa [writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

-- A taken branch must land on a four-byte boundary.
theorem bne {left right : regidx} {offset : BitVec 13} {leftValue rightValue : BitVec 32}
    {misa : RegisterType Register.misa}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.BTYPE (offset, right, left, .BNE)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (misaRead : Sail.readReg Register.misa (sync base frame state) = .ok misa (sync base frame state))
    (aligned : leftValue ≠ rightValue →
      (base + RegisterView.pc state + offset.signExtend 32) % 4 = 0)
    (jumps : Jumps state next (if leftValue = rightValue then RegisterView.pc state + 4#32
      else RegisterView.pc state + offset.signExtend 32)) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := branchEffect _ left right offset _ leftValue rightValue (syncReadPC state)
    leftRead rightRead misaRead aligned
  refine jump fetched decoded ?_ jumps
  rw [effect]
  split <;> simp only [BitVec.add_assoc]

-- Return through `source`, discarding the link value (`rd` is x0).
theorem jalr {source : regidx} {imm : BitVec 12} {sourceValue target : BitVec 32}
    {misa : RegisterType Register.misa} {mseccfg : RegisterType Register.mseccfg}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.JALR (imm, source, .Regidx 0)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (misaRead : Sail.readReg Register.misa (sync base frame state) = .ok misa (sync base frame state))
    (privilege : Sail.readReg Register.cur_privilege (sync base frame state) =
      .ok .Machine (sync base frame state))
    (mseccfgRead : Sail.readReg Register.mseccfg (sync base frame state) =
      .ok mseccfg (sync base frame state))
    (halfword : BitVec.ofBool (sourceValue + imm.signExtend 32)[1] = 0#1)
    (destination : base + target = 0xfffffffe#32 &&& (sourceValue + imm.signExtend 32))
    (jumps : Jumps state next target) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_JALR_equiv
    ((OpcodeSpec.RV32.spec_JALR_hypotheses (rs1 := source) (rd := .Regidx 0) (imm := imm)).mpr
      ⟨syncReadPC state, sourceRead⟩) misaRead privilege mseccfgRead halfword
  refine jump fetched decoded ?_ jumps
  rw [destination]
  simpa [OpcodeSpec.RV32.spec_JALR, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, regidx_to_fin] using effect

theorem auipc {dest : regidx} {imm : BitVec 20}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.UTYPE (imm, dest, .AUIPC)) (sync base frame state))
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest)
      (base + RegisterView.pc state + (imm ++ 0#12))) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_AUIPC_equiv
    ((OpcodeSpec.RV32.spec_AUIPC_hypotheses (rd := dest) (imm := imm)
      (state := sync base frame state) (pc_val := base + RegisterView.pc state)).mpr
        (syncReadPC state))
  refine retire fetched decoded ?_ member writes
  simpa [OpcodeSpec.RV32.spec_AUIPC, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

-- A call through `source` that links the next PC into a tracked `dest`.
-- Sail reads `source` before writing `dest`, so the two may be the same register.
theorem jalrLink {source dest : regidx} {imm : BitVec 12} {sourceValue target : BitVec 32}
    {misa : RegisterType Register.misa} {mseccfg : RegisterType Register.mseccfg}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.JALR (imm, source, dest)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok sourceValue (sync base frame state))
    (misaRead : Sail.readReg Register.misa (sync base frame state) = .ok misa (sync base frame state))
    (privilege : Sail.readReg Register.cur_privilege (sync base frame state) =
      .ok .Machine (sync base frame state))
    (mseccfgRead : Sail.readReg Register.mseccfg (sync base frame state) =
      .ok mseccfg (sync base frame state))
    (halfword : BitVec.ofBool (sourceValue + imm.signExtend 32)[1] = 0#1)
    (destination : base + target = 0xfffffffe#32 &&& (sourceValue + imm.signExtend 32))
    (member : regidx_to_fin dest ∈ tracked S) (pcNext : RegisterView.pc next = target)
    (agree : ∀ other ∈ tracked S, RegisterView.value next other =
      if other = regidx_to_fin dest then base + RegisterView.pc state + 4#32
      else RegisterView.value state other) :
    step (sync base frame state) = some (sync base frame next) := by
  have effect := OpcodeSpec.RV32.execute_JALR_equiv
    ((OpcodeSpec.RV32.spec_JALR_hypotheses (rs1 := source) (rd := dest) (imm := imm)).mpr
      ⟨syncReadPC state, sourceRead⟩) misaRead privilege mseccfgRead halfword
  refine retireTo fetched decoded ?_ member pcNext agree
  rw [destination]
  simpa [OpcodeSpec.RV32.spec_JALR, operation_list_effect, operation_effect,
    writeReg_state_success, write_xreg, writeX, nonzeroIndex member] using effect

end Step

end Riscfree.RV32

/-- Discharge `Writes` or `Jumps` for an explicit snapshot update. The facts
rewrite the PC goal; every register index is then checked by evaluation. -/
syntax "advance" "[" term,* "]" : tactic

macro_rules
  | `(tactic| advance [$facts,*]) => do
  let lemmas ← facts.getElems.mapM fun fact => `(Lean.Parser.Tactic.simpLemma| $fact:term)
  let facts : Array (Lean.TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma]) := lemmas.map fun fact => ⟨fact.raw⟩
  `(tactic| exact ⟨by simp only [$facts,*] <;> rfl, fun other _ => by fin_cases other <;> rfl⟩)
