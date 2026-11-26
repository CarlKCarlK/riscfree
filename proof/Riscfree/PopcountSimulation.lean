import Riscfree.PopcountPlatform
import PicoFV.RV32IM.RVSail.Opcodes.add
import PicoFV.RV32IM.RVSail.Opcodes.andi
import Riscfree.RV32.Branch
import PicoFV.RV32IM.RVSail.Opcodes.jalr
import PicoFV.RV32IM.RVSail.Opcodes.srli

namespace Riscfree.Popcount

open LeanRV32D LeanRV32D.Functions RV32IM RV32

private abbrev reg (register : BitVec 5) : regidx := .Regidx register

private theorem alignedOffset (base offset : Word)
    (aligned : base % 4 = 0) (offsetAligned : offset.toNat % 4 = 0) :
    (base + offset) % 4 = 0 := by
  have h := congrArg BitVec.toNat aligned
  change base.toNat % 4 = 0 at h
  apply BitVec.eq_of_toNat_eq
  change (base + offset).toNat % 4 = 0
  rw [BitVec.toNat_add]
  omega

private theorem locate (base : Word) (initial final : State)
    (stepped : Riscfree.step base initial = some final) :
    ∃ index : Fin instructions.length, initial.pc = BitVec.ofNat 32 (index.val * 4) := by
  by_cases aligned : initial.pc.toNat % 4 = 0
  · let index := initial.pc.toNat / 4
    by_cases bound : index < 14
    · refine ⟨⟨index, bound⟩, BitVec.eq_of_toNat_eq ?_⟩
      simp only [BitVec.toNat_ofNat]
      have same : index * 4 = initial.pc.toNat := by dsimp [index]; omega
      rw [same, Nat.mod_eq_of_lt initial.pc.isLt]
    · have absent : Riscfree.program[index]? = none := by
        apply Array.getElem?_eq_none
        simpa only [programDecoded] using Nat.le_of_not_gt bound
      simp [Riscfree.step, aligned, ← show index = initial.pc.toNat / 4 from rfl, absent] at stepped
  · simp [Riscfree.step, aligned] at stepped

-- Select the actual Sail decoding before considering the effect of the instruction.
private theorem decodeAt (platform : Platform base frame initial) (state : State)
    (index : Fin instructions.length) :
    ext_decode instructions[index.val].1 (sync base frame state) =
      .ok instructions[index.val].2 (sync base frame state) :=
  linkedWordsDecode _ (platform.privilegeAt state) (platform.landingPadAt state)
    _ (List.getElem_mem index.isLt)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem stepRefines (platform : Platform base frame initial)
    (state final : State)
    (guard : Safe initial.a0 state)
    (data : state.memory = initial.memory)
    (registers : state.other = initial.other)
    (stepped : Riscfree.step base state = some final) :
    RV32.step (sync base frame state) = some (sync base frame final) ∧
      final.memory = initial.memory ∧ final.other = initial.other := by
  obtain ⟨index, atPC⟩ := locate base state final stepped
  have fetched := platform.fetchAt state index atPC
  have decoded := decodeAt platform state index
  have pcRead := syncReadPC base frame state
  let machine := sync base frame state
  change RV32.step machine = _ ∧ _
  fin_cases index
  · change state.pc = 0#32 at atPC
    change fetch () machine = .ok (.F_Base 0x00400293) machine at fetched
    change ext_decode 0x00400293 machine = .ok (.ITYPE (4, reg 0, reg 5, .ADDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 4#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have retired := RV32.stepADDI machine 0x00400293 (reg 0) (reg 5) 4
      (base + state.pc) 0 fetched decoded pcRead (by rfl) (by decide)
    rw [next] at retired
    exact retired.trans (congrArg some (syncSetX5 base frame state 4 _))
  · change state.pc = 4#32 at atPC
    change fetch () machine = .ok (.F_Base 0x00000313) machine at fetched
    change ext_decode 0x00000313 machine = .ok (.ITYPE (0, reg 0, reg 6, .ADDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 8#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have retired := RV32.stepADDI machine 0x00000313 (reg 0) (reg 6) 0
      (base + state.pc) 0 fetched decoded pcRead (by rfl) (by decide)
    rw [next] at retired
    exact retired.trans (congrArg some (syncSetX6 base frame state 8 _))
  · change state.pc = 8#32 at atPC
    change fetch () machine = .ok (.F_Base 0x00052383) machine at fetched
    change ext_decode 0x00052383 machine = .ok (.LOAD (0, reg 10, reg 7, false, 4)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 12#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have wordRead := platform.readWord state (base + 12#32) state.a0 (guard atPC)
    have effect := executeWordLoad machine (reg 10) (reg 7) 0
      (base + state.pc) state.a0 (state.memory state.a0) pcRead (syncReadX10 base frame state) (by
        simpa [data, next] using wordRead)
    have retired := RV32.stepWrite machine 0x00052383 _ 7 (base + 12#32) (state.memory state.a0)
      fetched decoded (by
        simpa [writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
    exact retired.trans (congrArg some (syncSetX7 base frame state 12 _))
  · change state.pc = 12#32 at atPC
    change fetch () machine = .ok (.F_Base 0x02000e13) machine at fetched
    change ext_decode 0x02000e13 machine = .ok (.ITYPE (32, reg 0, reg 28, .ADDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 16#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have retired := RV32.stepADDI machine 0x02000e13 (reg 0) (reg 28) 32
      (base + state.pc) 0 fetched decoded pcRead (by rfl) (by decide)
    rw [next] at retired
    exact retired.trans (congrArg some (syncSetX28 base frame state 16 _))
  · change state.pc = 16#32 at atPC
    change fetch () machine = .ok (.F_Base 0x0013fe93) machine at fetched
    change ext_decode 0x0013fe93 machine = .ok (.ITYPE (1, reg 7, reg 29, .ANDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 20#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have effect := OpcodeSpec.RV32.execute_ANDI_equiv
      ((OpcodeSpec.RV32.spec_ANDI_hypotheses (r1 := reg 7) (rd := reg 29) (imm := 1#12)).mpr ⟨pcRead, (syncReadX7 base frame state)⟩)
    have retired := RV32.stepWrite machine 0x0013fe93 _ 29 (base + 20#32) (state.t2 &&& 1#32)
      fetched decoded (by
        simpa [OpcodeSpec.RV32.spec_ANDI, operation_list_effect, operation_effect,
          writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
    exact retired.trans (congrArg some (syncSetX29 base frame state 20 _))
  · change state.pc = 20#32 at atPC
    change fetch () machine = .ok (.F_Base 0x01d30333) machine at fetched
    change ext_decode 0x01d30333 machine = .ok (.RTYPE (reg 29, reg 6, reg 6, .ADD)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 24#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have effect := OpcodeSpec.RV32.execute_ADD_equiv
      ((OpcodeSpec.RV32.spec_ADD_hypotheses (r1 := reg 6) (r2 := reg 29) (rd := reg 6)).mpr ⟨pcRead, (syncReadX6 base frame state), (syncReadX29 base frame state)⟩)
    have retired := RV32.stepWrite machine 0x01d30333 _ 6 (base + 24#32) (state.t1 + state.t4)
      fetched decoded (by
        simpa [OpcodeSpec.RV32.spec_ADD, operation_list_effect, operation_effect,
          writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
    exact retired.trans (congrArg some (syncSetX6 base frame state 24 _))
  · change state.pc = 24#32 at atPC
    change fetch () machine = .ok (.F_Base 0x0013d393) machine at fetched
    change ext_decode 0x0013d393 machine = .ok (.SHIFTIOP (1, reg 7, reg 7, .SRLI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 28#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have effect := OpcodeSpec.RV32.execute_SRLI_equiv
      ((OpcodeSpec.RV32.spec_SRLI_hypotheses (r1 := reg 7) (rd := reg 7) (imm := 1#6)).mpr ⟨pcRead, (syncReadX7 base frame state)⟩)
    have retired := RV32.stepWrite machine 0x0013d393 _ 7 (base + 28#32) (state.t2 >>> (1 : Nat))
      fetched decoded (by
        simpa [OpcodeSpec.RV32.spec_SRLI, operation_list_effect, operation_effect,
          writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
    exact retired.trans (congrArg some (syncSetX7 base frame state 28 _))
  · change state.pc = 28#32 at atPC
    change fetch () machine = .ok (.F_Base 0xfffe0e13) machine at fetched
    change ext_decode 0xfffe0e13 machine = .ok (.ITYPE (0xfff, reg 28, reg 28, .ADDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 32#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have retired := RV32.stepADDI machine 0xfffe0e13 (reg 28) (reg 28) 4095
      (base + state.pc) state.t3 fetched decoded pcRead (syncReadX28 base frame state) (by decide)
    rw [next] at retired
    exact retired.trans (congrArg some (syncSetX28 base frame state 32 _))
  · change state.pc = 32#32 at atPC
    change fetch () machine = .ok (.F_Base 0xfe0e18e3) machine at fetched
    change ext_decode 0xfe0e18e3 machine = .ok (.BTYPE (0x1ff0, reg 0, reg 28, .BNE)) machine at decoded
    obtain ⟨misa, misaRead⟩ := platform.misa
    have misaAt := syncReadFrame base frame state Register.misa (by decide) misaRead
    have branch : (base + state.pc + (0x1ff0#13).signExtend 32) = base + 16#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have next : base + state.pc + 4#32 = base + 36#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have effect := branchEffect machine (reg 28) (reg 0) 0x1ff0#13
      (base + state.pc) state.t3 0#32 pcRead
      (syncReadX28 base frame state) (by rfl) misaAt (by
        intro
        rw [branch]
        exact alignedOffset base 16 platform.alignedCode (by decide))
    by_cases zero : state.t3 = 0#32
    · simp [Riscfree.step, atPC, programDecoded, State.read, zero] at stepped
      subst final
      refine ⟨?_, data, registers⟩
      have retired := RV32.stepSetPC machine 0xfe0e18e3 _ (base + 36#32)
        fetched decoded (by
          simpa only [if_pos zero, next] using effect)
      rw [syncSetPC] at retired
      simpa [zero] using retired
    · simp [Riscfree.step, atPC, programDecoded, State.read, zero] at stepped
      subst final
      refine ⟨?_, data, registers⟩
      have retired := RV32.stepSetPC machine 0xfe0e18e3 _ (base + 16#32)
        fetched decoded (by
          simpa only [if_neg zero, branch] using effect)
      rw [syncSetPC] at retired
      simpa [zero] using retired
  · change state.pc = 36#32 at atPC
    change fetch () machine = .ok (.F_Base 0x00450513) machine at fetched
    change ext_decode 0x00450513 machine = .ok (.ITYPE (4, reg 10, reg 10, .ADDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 40#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have retired := RV32.stepADDI machine 0x00450513 (reg 10) (reg 10) 4
      (base + state.pc) state.a0 fetched decoded pcRead (syncReadX10 base frame state) (by decide)
    rw [next] at retired
    exact retired.trans (congrArg some (syncSetX10 base frame state 40 _))
  · change state.pc = 40#32 at atPC
    change fetch () machine = .ok (.F_Base 0xfff28293) machine at fetched
    change ext_decode 0xfff28293 machine = .ok (.ITYPE (0xfff, reg 5, reg 5, .ADDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 44#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have retired := RV32.stepADDI machine 0xfff28293 (reg 5) (reg 5) 4095
      (base + state.pc) state.t0 fetched decoded pcRead (syncReadX5 base frame state) (by decide)
    rw [next] at retired
    exact retired.trans (congrArg some (syncSetX5 base frame state 44 _))
  · change state.pc = 44#32 at atPC
    change fetch () machine = .ok (.F_Base 0xfc029ee3) machine at fetched
    change ext_decode 0xfc029ee3 machine = .ok (.BTYPE (0x1fdc, reg 0, reg 5, .BNE)) machine at decoded
    obtain ⟨misa, misaRead⟩ := platform.misa
    have misaAt := syncReadFrame base frame state Register.misa (by decide) misaRead
    have branch : (base + state.pc + (0x1fdc#13).signExtend 32) = base + 8#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have next : base + state.pc + 4#32 = base + 48#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have effect := branchEffect machine (reg 5) (reg 0) 0x1fdc#13
      (base + state.pc) state.t0 0#32 pcRead
      (syncReadX5 base frame state) (by rfl) misaAt (by
        intro
        rw [branch]
        exact alignedOffset base 8 platform.alignedCode (by decide))
    by_cases zero : state.t0 = 0#32
    · simp [Riscfree.step, atPC, programDecoded, State.read, zero] at stepped
      subst final
      refine ⟨?_, data, registers⟩
      have retired := RV32.stepSetPC machine 0xfc029ee3 _ (base + 48#32)
        fetched decoded (by
          simpa only [if_pos zero, next] using effect)
      rw [syncSetPC] at retired
      simpa [zero] using retired
    · simp [Riscfree.step, atPC, programDecoded, State.read, zero] at stepped
      subst final
      refine ⟨?_, data, registers⟩
      have retired := RV32.stepSetPC machine 0xfc029ee3 _ (base + 8#32)
        fetched decoded (by
          simpa only [if_neg zero, branch] using effect)
      rw [syncSetPC] at retired
      simpa [zero] using retired
  · change state.pc = 48#32 at atPC
    change fetch () machine = .ok (.F_Base 0x00030513) machine at fetched
    change ext_decode 0x00030513 machine = .ok (.ITYPE (0, reg 6, reg 10, .ADDI)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    have next : base + state.pc + 4#32 = base + 52#32 := by
      rw [atPC, BitVec.add_assoc]
      rfl
    have retired := RV32.stepADDI machine 0x00030513 (reg 6) (reg 10) 0
      (base + state.pc) state.t1 fetched decoded pcRead (syncReadX6 base frame state) (by decide)
    rw [next] at retired
    simp only [show (0 : BitVec 12).signExtend 32 = 0#32 from rfl, BitVec.add_zero] at retired
    exact retired.trans (congrArg some (syncSetX10 base frame state 52 _))
  · change state.pc = 52#32 at atPC
    change fetch () machine = .ok (.F_Base 0x00008067) machine at fetched
    change ext_decode 0x00008067 machine = .ok (.JALR (0, reg 1, reg 0)) machine at decoded
    simp [Riscfree.step, atPC, programDecoded, State.read, State.write] at stepped
    subst final
    refine ⟨?_, data, registers⟩
    obtain ⟨misa, misaRead⟩ := platform.misa
    obtain ⟨config, configRead⟩ := platform.mseccfg
    have raRead : read_xreg 1 machine = .ok (initial.other 1) machine := by
      exact syncReadFrame base frame state Register.x1 (by decide) platform.ra
    have mask : initial.other 1 &&& 0xfffffffe#32 = initial.other 1 := platform.returnLow
    have returned : 0xfffffffe#32 &&& initial.other 1 = initial.other 1 := by
      rw [BitVec.and_comm, mask]
    have effect := OpcodeSpec.RV32.execute_JALR_equiv
      ((OpcodeSpec.RV32.spec_JALR_hypotheses (rs1 := reg 1) (rd := reg 0) (imm := 0#12)).mpr
        ⟨pcRead, raRead⟩)
      (syncReadFrame base frame state Register.misa (by decide) misaRead)
      (platform.privilegeAt state)
      (syncReadFrame base frame state Register.mseccfg (by decide) configRead)
      (by simp [platform.returnNext, BitVec.ofBool])
    have next : base + (initial.other 1 - base) = initial.other 1 := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    have retired := RV32.stepSetPC machine 0x00008067 _ (base + (initial.other 1 - base))
      fetched decoded (by
        simpa [OpcodeSpec.RV32.spec_JALR, operation_list_effect, operation_effect,
          writeReg_state_success, write_xreg, regidx_to_fin, returned, next] using effect)
    rw [syncSetPC] at retired
    simpa [registers, mask] using retired

end Riscfree.Popcount
