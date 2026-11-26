import Riscfree.RV32.Steps

/-!
# Code mapping, RAM, and processor assumptions

`Platform` states what a routine needs from the hart and the memory system.
The instruction-side premise describes only the loaded code image, after any
change to the tracked registers and the PC. RAM permissions are checked per
data word. No writable flash or global PMA is assumed.
-/

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

structure Platform (S : Type) [RegisterView S] (instructions : List (BitVec 32 × instruction))
    (base : BitVec 32) (frame : Machine) (addresses : List (BitVec 32)) (returnAddress : BitVec 32)
    (memory : BitVec 32 → BitVec 32) : Prop where
  alignedCode : base % 4 = 0
  returnLow : returnAddress &&& 0xfffffffe = returnAddress
  returnNext : (returnAddress)[1] = false
  ra : Sail.readReg Register.x1 frame = .ok returnAddress frame
  privilege : Sail.readReg Register.cur_privilege frame = .ok .Machine frame
  misa : ∃ value, Sail.readReg Register.misa frame = .ok value frame
  mseccfg : ∃ value, Sail.readReg Register.mseccfg frame = .ok value frame
  landingPad : get_xLPE .Machine frame = .ok false frame
  status : ∃ value, Sail.readReg Register.mstatus frame = .ok value frame ∧
    value.extractLsb 17 17 = 0#1
  htif : Sail.readReg Register.htif_tohost_base frame = .ok none frame
  ram : ∀ address ∈ addresses,
    ∃ regions region byte0 byte1 byte2 byte3,
      Sail.readReg Register.pma_regions frame = .ok regions frame ∧
      matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region ∧
      region.attributes.readable = true ∧ address.toNat % 4 = 0 ∧
      frame.mem[address.toNat]? = some byte0 ∧ frame.mem[address.toNat + 1]? = some byte1 ∧
      frame.mem[address.toNat + 2]? = some byte2 ∧ frame.mem[address.toNat + 3]? = some byte3 ∧
      memory address = byte3 ++ byte2 ++ byte1 ++ byte0
  code : ∀ (state : S) (index : Fin instructions.length),
    RegisterView.pc state = BitVec.ofNat 32 (index.val * 4) →
    InstructionWord (sync base frame state) (base + RegisterView.pc state) instructions[index.val].1

namespace Platform

variable {S : Type} [RegisterView S] {instructions : List (BitVec 32 × instruction)}
  {base : BitVec 32} {frame : Machine} {addresses : List (BitVec 32)} {returnAddress : BitVec 32}
  {memory : BitVec 32 → BitVec 32}

-- A register that no general-purpose index names keeps its frame value.
theorem systemRead (state : S) {key : Register} (notX : ∀ index : Fin 32, reg_of_fin index ≠ key)
    (notPC : key ≠ Register.PC) (notNext : key ≠ Register.nextPC)
    {value : RegisterType key} (read : Sail.readReg key frame = .ok value frame) :
    Sail.readReg key (sync base frame state) = .ok value (sync base frame state) :=
  syncReadFrame state key notPC notNext (fun index _ => notX index) read

variable (platform : Platform S instructions base frame addresses returnAddress memory)
include platform

theorem privilegeAt (state : S) :
    Sail.readReg Register.cur_privilege (sync base frame state) =
      .ok .Machine (sync base frame state) :=
  systemRead state (fun _ => reg_of_fin_neq_cur_privilege) (by decide) (by decide) platform.privilege

theorem misaAt (state : S) :
    ∃ value, Sail.readReg Register.misa (sync base frame state) = .ok value (sync base frame state) := by
  obtain ⟨value, read⟩ := platform.misa
  exact ⟨value, systemRead state (by decide) (by decide) (by decide) read⟩

theorem mseccfgAt (state : S) :
    ∃ value, Sail.readReg Register.mseccfg (sync base frame state) =
      .ok value (sync base frame state) := by
  obtain ⟨value, read⟩ := platform.mseccfg
  exact ⟨value, systemRead state (by decide) (by decide) (by decide) read⟩

theorem landingPadAt (state : S) :
    get_xLPE .Machine (sync base frame state) = .ok false (sync base frame state) := by
  obtain ⟨config, read⟩ := platform.mseccfg
  have same := systemRead (base := base) state (by decide) (by decide) (by decide) read
  have disabled := platform.landingPad
  simp [get_xLPE, read] at disabled
  simp [get_xLPE, same, disabled]

theorem readWord (state : S) (next offset address : BitVec 32) (inRam : address ∈ addresses) :
    let entered := write_reg_state (sync base frame state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false entered =
      .ok (.Ok (memory address)) entered := by
  dsimp only
  obtain ⟨regions, region, byte0, byte1, byte2, byte3, pma, matched, readable, aligned,
    bytes0, bytes1, bytes2, bytes3, word⟩ := platform.ram address inRam
  obtain ⟨status, statusRead, mprv⟩ := platform.status
  rw [word]
  refine readAlignedRamWord _ address offset region regions status byte0 byte1 byte2 byte3 ?_ ?_
    mprv ?_ matched readable ?_ aligned ?_ ?_ ?_ ?_
  · exact readReg_of_write_other_reg_state (platform.privilegeAt state) (by decide)
  · exact readReg_of_write_other_reg_state
      (systemRead state (fun _ => reg_of_fin_neq_mstatus) (by decide) (by decide) statusRead) (by decide)
  · exact readReg_of_write_other_reg_state
      (systemRead state (fun _ => reg_of_fin_neq_pma_regions) (by decide) (by decide) pma) (by decide)
  · exact readReg_of_write_other_reg_state
      (systemRead state (fun _ => reg_of_fin_neq_htif_tohost_base) (by decide) (by decide)
        platform.htif) (by decide)
  all_goals simp only [writeMem, syncMem]; assumption

-- Select the linked word and its Sail decoding before considering its effect.
theorem fetchAndDecode
    (decodes : ∀ state : S, ∀ entry ∈ instructions,
      ext_decode entry.1 (sync base frame state) = .ok entry.2 (sync base frame state))
    (uncompressed : ∀ entry ∈ instructions, isRVC (entry.1.extractLsb' 0 16) = false)
    (state : S) (index : Fin instructions.length)
    (pc : RegisterView.pc state = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base frame state) =
        .ok (.F_Base instructions[index.val].1) (sync base frame state) ∧
      ext_decode instructions[index.val].1 (sync base frame state) =
        .ok instructions[index.val].2 (sync base frame state) := by
  obtain ⟨misa, read⟩ := platform.misaAt state
  have member := List.getElem_mem index.isLt
  exact ⟨(platform.code state index pc).fetch (syncReadPC state) read (uncompressed _ member),
    decodes state _ member⟩

theorem alignedOffset (offset : BitVec 32) (offsetAligned : offset.toNat % 4 = 0) :
    (base + offset) % 4 = 0 := by
  have aligned := congrArg BitVec.toNat platform.alignedCode
  change base.toNat % 4 = 0 at aligned
  apply BitVec.eq_of_toNat_eq
  change (base + offset).toNat % 4 = 0
  rw [BitVec.toNat_add]
  omega

-- A word load from one of the platform's RAM words.
theorem lw {state next : S} {word : BitVec 32} {source dest : regidx} {imm : BitVec 12}
    {pointer address : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.LOAD (imm, source, dest, false, 4)) (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok pointer (sync base frame state))
    (inRam : address ∈ addresses) (effective : pointer + imm.signExtend 32 = address)
    (member : regidx_to_fin dest ∈ tracked S)
    (writes : Writes state next (regidx_to_fin dest) (memory address)) :
    step (sync base frame state) = some (sync base frame next) := by
  subst effective
  exact Step.lw fetched decoded sourceRead (platform.readWord state _ _ _ inRam) member writes

-- A branch whose taken target is four-byte aligned relative to the code base.
theorem bne {state next : S} {word : BitVec 32} {left right : regidx} {offset : BitVec 13}
    {leftValue rightValue : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.BTYPE (offset, right, left, .BNE)) (sync base frame state))
    (leftRead : read_xreg (regidx_to_fin left) (sync base frame state) =
      .ok leftValue (sync base frame state))
    (rightRead : read_xreg (regidx_to_fin right) (sync base frame state) =
      .ok rightValue (sync base frame state))
    (targetAligned : (RegisterView.pc state + offset.signExtend 32).toNat % 4 = 0)
    (jumps : Jumps state next (if leftValue = rightValue then RegisterView.pc state + 4#32
      else RegisterView.pc state + offset.signExtend 32)) :
    step (sync base frame state) = some (sync base frame next) := by
  obtain ⟨misa, misaRead⟩ := platform.misaAt state
  refine Step.bne fetched decoded leftRead rightRead misaRead ?_ jumps
  intro
  rw [BitVec.add_assoc]
  exact platform.alignedOffset _ targetAligned

-- `ret` (`jalr x0, 0(ra)`) jumps to the platform's return address.
theorem ret {state next : S} {word : BitVec 32}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.JALR (0#12, .Regidx 1, .Regidx 0)) (sync base frame state))
    (untracked : (1 : Fin 32) ∉ tracked S)
    (jumps : Jumps state next (returnAddress - base)) :
    step (sync base frame state) = some (sync base frame next) := by
  obtain ⟨misa, misaRead⟩ := platform.misaAt state
  obtain ⟨config, configRead⟩ := platform.mseccfgAt state
  have raRead : read_xreg 1 (sync base frame state) = .ok returnAddress (sync base frame state) :=
    syncReadFrame state Register.x1 (by decide) (by decide)
      (fun index member same => untracked (by
        rw [show index = 1 from by
          fin_cases index <;> first | rfl | simp [reg_of_fin] at same] at member
        exact member)) platform.ra
  refine Step.jalr (imm := 0#12) (sourceValue := returnAddress) fetched decoded raRead misaRead
    (platform.privilegeAt state) configRead ?_ ?_ jumps
  · simp [platform.returnNext, BitVec.ofBool]
  · rw [BitVec.add_comm base, BitVec.sub_add_cancel]
    have mask : returnAddress &&& 0xfffffffe#32 = returnAddress := platform.returnLow
    rw [show (0#12).signExtend 32 = 0#32 from rfl, BitVec.add_zero, BitVec.and_comm, mask]

end Platform

end Riscfree.RV32
