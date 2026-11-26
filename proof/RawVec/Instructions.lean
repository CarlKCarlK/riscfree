import Riscfree.RV32.Decode
import Riscfree.RV32.Store
import Riscfree.RV32.Fetch

namespace Riscfree.RawVec

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

abbrev Word := BitVec 32

def instructions : List (Word × instruction) :=
  [ (0x00452683, .LOAD (4, reg 10, reg 13, false, 4))
  , (0x00852703, .LOAD (8, reg 10, reg 14, false, 4))
  , (0x00d77663, .BTYPE (12, reg 13, reg 14, .BGEU))
  , (0x00300513, .ITYPE (3, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x00b6f663, .BTYPE (12, reg 11, reg 13, .BGEU))
  , (0x00200513, .ITYPE (2, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x00e69663, .BTYPE (12, reg 14, reg 13, .BNE))
  , (0x00100513, .ITYPE (1, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x02d5f663, .BTYPE (44, reg 13, reg 11, .BGEU))
  , (0x00052703, .LOAD (0, reg 10, reg 14, false, 4))
  , (0x00269793, .SHIFTIOP (2, reg 13, reg 15, .SLLI))
  , (0x00f70733, .RTYPE (reg 15, reg 14, reg 14, .ADD))
  , (0x00068793, .ITYPE (0, reg 13, reg 15, .ADDI))
  , (0xffc72803, .LOAD (0xffc, reg 14, reg 16, false, 4))
  , (0xfff78793, .ITYPE (0xfff, reg 15, reg 15, .ADDI))
  , (0xffc70893, .ITYPE (0xffc, reg 14, reg 17, .ADDI))
  , (0x01072023, .STORE (0, reg 16, reg 14, 4))
  , (0x00088713, .ITYPE (0, reg 17, reg 14, .ADDI))
  , (0xfef5e6e3, .BTYPE (0x1fec, reg 15, reg 11, .BLTU))
  , (0x00052783, .LOAD (0, reg 10, reg 15, false, 4))
  , (0x00259593, .SHIFTIOP (2, reg 11, reg 11, .SLLI))
  , (0x00b785b3, .RTYPE (reg 11, reg 15, reg 11, .ADD))
  , (0x00168693, .ITYPE (1, reg 13, reg 13, .ADDI))
  , (0x00c5a023, .STORE (0, reg 12, reg 11, 4))
  , (0x00d52223, .STORE (4, reg 13, reg 10, 4))
  , (0x00000513, .ITYPE (0, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions, ext_decode entry.1 state = .ok entry.2 state := by
  decode_table_normal_form instructions [privilege, landingPad]

structure Snapshot where
  pc : Word := 0
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word := 0
  a4 : Word := 0
  a5 : Word := 0
  a6 : Word := 0
  a7 : Word := 0

instance : RegisterView Snapshot where
  tracked := [10, 11, 12, 13, 14, 15, 16, 17]
  pc state := state.pc
  value state index := match index.val with
    | 10 => state.a0
    | 11 => state.a1
    | 12 => state.a2
    | 13 => state.a3
    | 14 => state.a4
    | 15 => state.a5
    | 16 => state.a6
    | 17 => state.a7
    | _ => 0
  distinct := by decide
  nonzero := by decide

@[simp] theorem viewPc (state : Snapshot) : RegisterView.pc state = state.pc := rfl

-- The memory system maps these executable bytes independently of data writes.
def CodeAgrees (base : Word) (original memory : ByteMemory) : Prop :=
  ∀ byte, base.toNat ≤ byte → byte < base.toNat + 120 →
    memory[byte]? = original[byte]?

def Mapped (frame : Machine) (address : Word) (permission : PMA_Region → Prop) : Prop :=
  address.toNat % 4 = 0 ∧ ∃ regions region,
    Sail.readReg Register.pma_regions frame = .ok regions frame ∧
    matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region ∧ permission region

abbrev Readable (frame : Machine) (address : Word) :=
  Mapped frame address (fun region => region.attributes.readable = true)

abbrev Writable (frame : Machine) (address : Word) :=
  Mapped frame address (fun region => region.attributes.writable = true)

structure Environment (base returnAddress : Word) (original : Machine) : Prop where
  codeFits : base.toNat + 120 ≤ 2 ^ 32
  platform : ∀ memory, CodeAgrees base original.mem memory →
    Platform Snapshot instructions base { original with mem := memory } [] returnAddress (fun _ => 0)

-- In machine mode, Sail's fetch reads the code bytes from executable memory,
-- so the code mapping for every memory that keeps those bytes follows from the
-- original machine. No RAM words are needed: the routine's data accesses
-- carry their own `Readable` and `Writable` premises.
theorem Environment.ofMachine {base returnAddress : Word} {original : Machine}
    (mode : MachineMode original returnAddress) (image : CodeImage instructions base original) :
    Environment base returnAddress original where
  codeFits := image.fits
  platform memory agrees :=
    Platform.ofCodeImage (mode.withMemory memory)
      (image.withMemory memory fun byte low high => agrees byte low high)
      (fun _ inside => nomatch inside)

section Instructions

variable {base returnAddress : Word} {original : Machine} {memory : ByteMemory}

private theorem fetchDecode
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (index : Fin instructions.length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base {original with mem := memory} state) =
        .ok (.F_Base instructions[index.val].1) (sync base {original with mem := memory} state) ∧
      ext_decode instructions[index.val].1 (sync base {original with mem := memory} state) =
        .ok instructions[index.val].2 (sync base {original with mem := memory} state) :=
  platform.fetchAndDecode
    (fun state => linkedWordsDecode _ (platform.privilegeAt state) (platform.landingPadAt state))
    (by decide) state index pc

set_option maxHeartbeats 1500000 in
private theorem Platform.loadWord
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (next offset address value : Word)
    (permission : Readable original address) (word : WordAt memory address.toNat value) :
    let entered := write_reg_state (sync base {original with mem := memory} state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false entered =
      .ok (.Ok value) entered := by
  dsimp only
  obtain ⟨aligned, regions, region, readRegions, matched, readable⟩ := permission
  obtain ⟨status, statusRead, mprv⟩ := platform.status
  have combined : BitVec.append (BitVec.append (BitVec.append (value.extractLsb' 24 8)
      (value.extractLsb' 16 8)) (value.extractLsb' 8 8)) (value.extractLsb' 0 8) = value := by
    have high := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := value) (start₁ := 16)
      (start₂ := 24) (len₁ := 8) (len₂ := 8) rfl
    have middle := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := value) (start₁ := 8)
      (start₂ := 16) (len₁ := 8) (len₂ := 16) rfl
    exact (congrArg (fun first => BitVec.append (BitVec.append first (value.extractLsb' 8 8))
      (value.extractLsb' 0 8)) high).trans
        ((congrArg (fun first => BitVec.append first (value.extractLsb' 0 8)) middle).trans
          (BitVec.extractLsb'_append_extractLsb' (w := 24) (len := 8) (x := value)))
  have regionsReg : original.regs.get? Register.pma_regions = some regions :=
    readReg_succ.mp readRegions
  refine (readAlignedRamWord _ address offset region regions status
    (value.extractLsb' 0 8) (value.extractLsb' 8 8) (value.extractLsb' 16 8)
    (value.extractLsb' 24 8) ?_ ?_ mprv ?_
    matched readable ?_ aligned ?_ ?_ ?_ ?_).trans ?_
  · exact readReg_of_write_other_reg_state (platform.privilegeAt state) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) statusRead)
      (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide)
        (readReg_succ.mpr regionsReg)) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) platform.htif)
      (by decide)
  · exact word 0
  · exact word 1
  · exact word 2
  · exact word 3
  · exact congrArg (fun word => EStateM.Result.ok (Sail.Ok word)
      (write_reg_state (sync base {original with mem := memory} state) Register.nextPC next)) combined

private theorem Platform.storeWord
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (next address value : Word)
    (permission : Writable original address) :
    let entered := write_reg_state (sync base {original with mem := memory} state) Register.nextPC next
    vmem_write_addr (.Virtaddr address) 4 value (.Store .Data) false false false entered =
      .ok (.Ok true) (setWord entered address.toNat value) := by
  dsimp only
  obtain ⟨aligned, regions, region, readRegions, matched, writable⟩ := permission
  obtain ⟨status, statusRead, mprv⟩ := platform.status
  have regionsReg : original.regs.get? Register.pma_regions = some regions :=
    readReg_succ.mp readRegions
  refine writeAlignedRamWord _ address value region regions status ?_ ?_ mprv ?_
    matched writable ?_ aligned
  · exact readReg_of_write_other_reg_state (platform.privilegeAt state) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) statusRead)
      (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide)
        (readReg_succ.mpr regionsReg)) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) platform.htif)
      (by decide)

private theorem addLiteralZero (value : Word) : value + (0 : Word) = value :=
  BitVec.add_zero _

theorem step00
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 0#32) (value : Word)
    (permission : Readable original (state.a0 + 4#32)) (contents : WordAt memory ((state.a0 + 4#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 4#32, a3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨0, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step04
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 4#32) (value : Word)
    (permission : Readable original (state.a0 + 8#32)) (contents : WordAt memory ((state.a0 + 8#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 8#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨1, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step08
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 8#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a3.toNat ≤ state.a4.toNat then 20#32 else 12#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨2, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 13) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step0c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 12#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 16#32, a0 := 3#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨3, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step10
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 16#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨4, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

theorem step14
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 20#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a1.toNat ≤ state.a3.toNat then 32#32 else 24#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨5, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 11) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step18
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 24#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 28#32, a0 := 2#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨6, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step1c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 28#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨7, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

theorem step20
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 32#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a3 = state.a4 then 36#32 else 44#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨8, by decide⟩ atPC
  refine platform.bne fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 14) (by decide)) ?_ ?_
  · rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step24
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 36#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 40#32, a0 := 1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨9, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step28
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 40#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨10, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

theorem step2c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 44#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a3.toNat ≤ state.a1.toNat then 88#32 else 48#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨11, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 13) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step30
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 48#32) (value : Word)
    (permission : Readable original state.a0) (contents : WordAt memory (state.a0).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 52#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨12, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  have loaded := Platform.loadWord platform state (base + state.pc + 4#32) 0 state.a0 value
    permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

theorem step34
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 52#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 56#32, a5 := state.a3 <<< (2 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨13, by decide⟩ atPC
  exact Step.slli fetched decoded (syncRead state (index := 13) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step38
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 56#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 60#32, a4 := state.a4 + state.a5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨14, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 15) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step3c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 60#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 64#32, a5 := state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨15, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 13) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step40
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 64#32) (value : Word)
    (permission : Readable original (state.a4 + 0xfffffffc#32)) (contents : WordAt memory ((state.a4 + 0xfffffffc#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 68#32, a6 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨16, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 14) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step44
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 68#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 72#32, a5 := state.a5 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨17, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 15) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step48
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 72#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 76#32, a7 := state.a4 + 0xfffffffc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨18, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 14) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step4c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 76#32) (permission : Writable original state.a4) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory (state.a4).toNat state.a6)} { state with pc := 80#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨19, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 80#32 }) (pointer := state.a4) (value := state.a6)
    fetched decoded (syncRead state (index := 14) (by decide))
    (syncRead state (index := 16) (by decide))
    (by
      have stored := Platform.storeWord platform state (base + state.pc + 4#32) state.a4
        state.a6 permission
      simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stored)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stepped

theorem step50
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 80#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 84#32, a4 := state.a7 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨20, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 17) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step54
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 84#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a1.toNat < state.a5.toNat then 64#32 else 88#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨21, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bltu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 15) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step58
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 88#32) (value : Word)
    (permission : Readable original state.a0) (contents : WordAt memory (state.a0).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 92#32, a5 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨22, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  have loaded := Platform.loadWord platform state (base + state.pc + 4#32) 0 state.a0 value
    permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

theorem step5c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 92#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 96#32, a1 := state.a1 <<< (2 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨23, by decide⟩ atPC
  exact Step.slli fetched decoded (syncRead state (index := 11) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step60
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 96#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 100#32, a1 := state.a5 + state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨24, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (index := 15) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step64
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 100#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 104#32, a3 := state.a3 + 1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨25, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 13) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step68
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 104#32) (permission : Writable original state.a1) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory (state.a1).toNat state.a2)} { state with pc := 108#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨26, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 108#32 }) (pointer := state.a1) (value := state.a2)
    fetched decoded (syncRead state (index := 11) (by decide))
    (syncRead state (index := 12) (by decide))
    (by
      have stored := Platform.storeWord platform state (base + state.pc + 4#32) state.a1
        state.a2 permission
      simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stored)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stepped

theorem step6c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 108#32) (permission : Writable original (state.a0 + 4#32)) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory ((state.a0 + 4#32)).toNat state.a3)} { state with pc := 112#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨27, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 112#32 }) (pointer := state.a0) (value := state.a3)
    fetched decoded (syncRead state (index := 10) (by decide))
    (syncRead state (index := 13) (by decide))
    (by exact Platform.storeWord platform state _ _ _ permission)
    (by advance [viewPc, atPC])
  exact stepped

theorem step70
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 112#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 116#32, a0 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨28, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step74
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 116#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨29, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

end Instructions

end Riscfree.RawVec
