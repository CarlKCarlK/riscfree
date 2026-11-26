import Riscfree.RV32.Effects

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

-- Naturally aligned data reads need only the PMA of the matching region.
-- Other regions can be read-only or absent. The pinned Sail configuration
-- disables its CLINT and the premise below disables its host interface.
set_option maxHeartbeats 1500000 in
theorem readPhysicalWord (state : Machine)
    (address : BitVec 32) (region : PMA_Region) (regions : List PMA_Region)
    (status : RegisterType Register.mstatus)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (machine : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (mstatusRead : Sail.readReg Register.mstatus state = .ok status state)
    (mprv : status.extractLsb 17 17 = 0#1)
    (loadedRegions : Sail.readReg Register.pma_regions state = .ok regions state)
    (pmaMatch : matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region)
    (readable : region.attributes.readable = true)
    (htifOff : Sail.readReg Register.htif_tohost_base state = .ok none state)
    (aligned : (4 : Int) ∣ address.toNat)
    (bytes0 : state.mem[address.toNat]? = some byte0)
    (bytes1 : state.mem[address.toNat + 1]? = some byte1)
    (bytes2 : state.mem[address.toNat + 2]? = some byte2)
    (bytes3 : state.mem[address.toNat + 3]? = some byte3) :
    mem_read (.Load .Data) (.Physaddr (address.setWidth 34)) 4 false false false state =
      .ok (.Ok (byte3 ++ byte2 ++ byte1 ++ byte0)) state := by
  have bound : address.toNat < 17179869184 := by
    have := address.isLt
    omega
  have nonMmio : ¬ (address.toNat : Int) + 4 ≤ 0 := by omega
  cases fault : region.attributes.misaligned_fault <;>
    simp [machine, mstatusRead, mprv, loadedRegions, -matching_pma, pmaMatch, readable,
      fault, aligned, htifOff, nonMmio, Nat.mod_eq_of_lt bound, Nat.add_assoc, bytes0, bytes1, bytes2, bytes3]

theorem machineDataTranslation (state : Machine) (address : BitVec 32) (status : RegisterType Register.mstatus)
    (machine : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (mstatusRead : Sail.readReg Register.mstatus state = .ok status state)
    (mprv : status.extractLsb 17 17 = 0#1) :
    translateAddr (.Virtaddr address) (.Load .Data) state =
      .ok (.Ok (.Physaddr (address.setWidth 34), ())) state := by
  have machineEq : (Privilege.Machine == Privilege.Machine) = true := rfl
  simp [machineEq, machine, mstatusRead, mprv, translationMode, init_ext_ptw]

theorem readAlignedRamWord (state : Machine)
    (address offset : BitVec 32) (region : PMA_Region) (regions : List PMA_Region)
    (status : RegisterType Register.mstatus) (byte0 byte1 byte2 byte3 : BitVec 8)
    (machine : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (mstatusRead : Sail.readReg Register.mstatus state = .ok status state)
    (mprv : status.extractLsb 17 17 = 0#1)
    (loadedRegions : Sail.readReg Register.pma_regions state = .ok regions state)
    (pmaMatch : matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region)
    (readable : region.attributes.readable = true)
    (htifOff : Sail.readReg Register.htif_tohost_base state = .ok none state)
    (aligned : address.toNat % 4 = 0)
    (bytes0 : state.mem[address.toNat]? = some byte0)
    (bytes1 : state.mem[address.toNat + 1]? = some byte1)
    (bytes2 : state.mem[address.toNat + 2]? = some byte2)
    (bytes3 : state.mem[address.toNat + 3]? = some byte3) :
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false state =
      .ok (.Ok (byte3 ++ byte2 ++ byte1 ++ byte0)) state := by
  exact alignedWordRead state address offset _ _ aligned
    (machineDataTranslation state address status machine mstatusRead mprv)
    (readPhysicalWord state address region regions status byte0 byte1 byte2 byte3
      machine mstatusRead mprv loadedRegions pmaMatch readable htifOff
      (by omega) bytes0 bytes1 bytes2 bytes3)


-- Execute the signed RV32 LW encoding. This has the same effects as Pico's
-- LW spec once the address-local RAM read supplies the little-endian word.
theorem executeWordLoad (state : Machine) (base dest : regidx) (imm : BitVec 12)
    (pc pointer word : BitVec 32)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (baseRead : read_xreg (regidx_to_fin base) state = .ok pointer state)
    (read : let entered := write_reg_state state Register.nextPC (pc + 4#32)
      vmem_read_addr (.Virtaddr (pointer + imm.signExtend 32)) (imm.signExtend 32) 4
        (.Load .Data) false false false entered = .ok (.Ok word) entered) :
    execute_instruction (.LOAD (imm, base, dest, false, 4)) state =
      (do
        Sail.writeReg Register.nextPC (pc + 4#32)
        write_xreg (regidx_to_fin dest) word
        pure (ExecutionResult.Retire_Success ())) state := by
  have index (register : regidx) :
      register = .Regidx (BitVec.ofNat 5 (regidx_to_fin register).val) := by
    cases register
    simp [regidx_to_fin]
  have sourceNext := read_xreg_write_other_reg_state (write_val := pc + 4#32)
    (regidx_to_fin base) baseRead reg_of_fin_neq_nextPC
  dsimp only at read
  simp [execute_instruction, pcRead, writeReg_state_success, execute, execute_LOAD, vmem_read,
    rX_read_xreg_equiv _ base _ (index base), wX_write_xreg_equiv _ _ dest _ (index dest)]
  simp [sourceNext, read]

-- The same Pico load effect applies when the addressed RAM provides the word.
-- There is no global PMA assumption in this statement.
theorem ramLoadUsesPicoEffects (state : Machine) (base dest : regidx) (imm : BitVec 12)
    (pc pointer : BitVec 32) (byte0 byte1 byte2 byte3 : BitVec 8)
    (nonzero : (dest == regidx.Regidx 0#5) = false)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (baseRead : read_xreg (regidx_to_fin base) state = .ok pointer state)
    (read : let entered := write_reg_state state Register.nextPC (pc + 4#32)
      vmem_read_addr (.Virtaddr (pointer + imm.signExtend 32)) (imm.signExtend 32) 4
        (.Load .Data) false false false entered = .ok (.Ok (byte3 ++ byte2 ++ byte1 ++ byte0)) entered) :
    execute_instruction (.LOAD (imm, base, dest, false, 4)) state =
      (operation_list_effect
        (OpcodeSpec.RV32.spec_LW base dest imm pc pointer byte0 byte1 byte2 byte3) state).state := by
  rw [executeWordLoad state base dest imm pc pointer _ pcRead baseRead read]
  simp [OpcodeSpec.RV32.spec_LW, nonzero, operation_list_effect, operation_effect,
    writeReg_state_success]
  cases write_xreg (regidx_to_fin dest) (byte3 ++ byte2 ++ byte1 ++ byte0)
    (write_reg_state state Register.nextPC (pc + 4#32)) <;> rfl

end Riscfree.RV32
