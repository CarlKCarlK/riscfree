import Riscfree.LinkedPopcount
import Riscfree.PopcountState
import Riscfree.PopcountTrace
import Riscfree.RV32.Memory

namespace Riscfree.Popcount

open LeanRV32D LeanRV32D.Functions RV32IM RV32

def inputAddresses (input : Word) : List Word :=
  [input, input + 4, input + 4 + 4, input + 4 + 4 + 4]

-- The instruction-side platform premise describes just the loaded code image.
-- It applies after any change to the six scratch registers and the PC.
-- RAM permissions are checked per word. No writable flash or global PMA is assumed.
structure Platform (base : Word) (frame : Machine) (initial : State) : Prop where
  alignedCode : base % 4 = 0
  returnLow : initial.other 1 &&& 0xfffffffe = initial.other 1
  returnNext : (initial.other 1)[1] = false
  ra : Sail.readReg Register.x1 frame = .ok (initial.other 1) frame
  privilege : Sail.readReg Register.cur_privilege frame = .ok .Machine frame
  misa : ∃ value, Sail.readReg Register.misa frame = .ok value frame
  mseccfg : ∃ value, Sail.readReg Register.mseccfg frame = .ok value frame
  landingPad : get_xLPE .Machine frame = .ok false frame
  status : ∃ value, Sail.readReg Register.mstatus frame = .ok value frame ∧
    value.extractLsb 17 17 = 0#1
  htif : Sail.readReg Register.htif_tohost_base frame = .ok none frame
  ram : ∀ address ∈ inputAddresses initial.a0,
    ∃ regions region byte0 byte1 byte2 byte3,
      Sail.readReg Register.pma_regions frame = .ok regions frame ∧
      matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region ∧
      region.attributes.readable = true ∧ address.toNat % 4 = 0 ∧
      frame.mem[address.toNat]? = some byte0 ∧ frame.mem[address.toNat + 1]? = some byte1 ∧
      frame.mem[address.toNat + 2]? = some byte2 ∧ frame.mem[address.toNat + 3]? = some byte3 ∧
      initial.memory address = byte3 ++ byte2 ++ byte1 ++ byte0
  code : ∀ (state : State) (index : Fin instructions.length),
    state.pc = BitVec.ofNat 32 (index.val * 4) →
    InstructionWord (sync base frame state) (base + state.pc) instructions[index.val].1

theorem Platform.fetchAt (platform : Platform base frame initial) (state : State)
    (index : Fin instructions.length) (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base frame state) = .ok (.F_Base instructions[index.val].1) (sync base frame state) := by
  obtain ⟨misa, read⟩ := platform.misa
  apply (platform.code state index pc).fetch (syncReadPC base frame state)
    (syncReadFrame base frame state Register.misa (by decide) read)
  fin_cases index <;> rfl

theorem Platform.privilegeAt (platform : Platform base frame initial) (state : State) :
    Sail.readReg Register.cur_privilege (sync base frame state) =
      .ok .Machine (sync base frame state) :=
  syncReadFrame _ _ _ _ (by decide) platform.privilege

theorem Platform.landingPadAt (platform : Platform base frame initial) (state : State) :
    get_xLPE .Machine (sync base frame state) = .ok false (sync base frame state) := by
  obtain ⟨config, read⟩ := platform.mseccfg
  have same := syncReadFrame base frame state Register.mseccfg (by decide) read
  have disabled := platform.landingPad
  simp [get_xLPE, read] at disabled
  simp [get_xLPE, same, disabled]

theorem Platform.readWord (platform : Platform base frame initial) (state : State)
    (next address : Word) (inRam : address ∈ inputAddresses initial.a0) :
    let entered := write_reg_state (sync base frame state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) 0 4 (.Load .Data) false false false entered =
      .ok (.Ok (initial.memory address)) entered := by
  dsimp only
  obtain ⟨regions, region, byte0, byte1, byte2, byte3, pma, matched, readable, aligned,
    bytes0, bytes1, bytes2, bytes3, word⟩ := platform.ram address inRam
  obtain ⟨status, statusRead, mprv⟩ := platform.status
  rw [word]
  refine readAlignedRamWord _ address 0 region regions status byte0 byte1 byte2 byte3 ?_ ?_
    mprv ?_ matched readable ?_ aligned ?_ ?_ ?_ ?_
  · exact readReg_of_write_other_reg_state (platform.privilegeAt state) (by decide)
  · exact readReg_of_write_other_reg_state (syncReadFrame _ _ _ _ (by decide) statusRead) (by decide)
  · exact readReg_of_write_other_reg_state (syncReadFrame _ _ _ _ (by decide) pma) (by decide)
  · exact readReg_of_write_other_reg_state (syncReadFrame _ _ _ _ (by decide) platform.htif) (by decide)
  all_goals simp only [writeMem, syncMem]; assumption

end Riscfree.Popcount
