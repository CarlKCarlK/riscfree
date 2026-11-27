import RawVec.Access

/-!
# The linked instructions of `sorted_map_remove`

The routine saves `ra`, `s0`, `s1`, and `s2` in a 16-byte frame, rejects an
invalid length, and calls `sorted_map_lower_bound`, which lies `0x34` bytes
before it. If the entry at the returned position has the key, it restores the
frame and tail-calls `raw_vec_pair_remove`, `0x1dc` bytes before it, with
`t1`. Otherwise it restores the frame and returns `ABSENT` (5).

The `auipc`/`jalr` pairs come from the linker, so the table records the words
of the linked demo, and `verifyElf` checks both call offsets.

The routine writes `ra`, so its proof tracks `ra` and handles each `ret` and
call itself rather than through `Platform`.
-/

namespace Riscfree.SortedMap.Remove

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

def instructions : List (Word × instruction) :=
  [ (0xff010113, .ITYPE (0xff0, reg 2, reg 2, .ADDI))
  , (0x00112623, .STORE (12, reg 1, reg 2, 4))
  , (0x00812423, .STORE (8, reg 8, reg 2, 4))
  , (0x00912223, .STORE (4, reg 9, reg 2, 4))
  , (0x01212023, .STORE (0, reg 18, reg 2, 4))
  , (0x00452483, .LOAD (4, reg 10, reg 9, false, 4))
  , (0x00852603, .LOAD (8, reg 10, reg 12, false, 4))
  , (0x00967663, .BTYPE (12, reg 9, reg 12, .BGEU))
  , (0x00300513, .ITYPE (3, reg 0, reg 10, .ADDI))
  , (0x0540006f, .JAL (0x54, reg 0))
  , (0x00058413, .ITYPE (0, reg 11, reg 8, .ADDI))
  , (0x00050913, .ITYPE (0, reg 10, reg 18, .ADDI))
  , (0x00000097, .UTYPE (0, reg 1, .AUIPC))
  , (0xf9c080e7, .JALR (0xf9c, reg 1, reg 1))
  , (0x00050593, .ITYPE (0, reg 10, reg 11, .ADDI))
  , (0x00500513, .ITYPE (5, reg 0, reg 10, .ADDI))
  , (0x0295fc63, .BTYPE (0x38, reg 9, reg 11, .BGEU))
  , (0x00092683, .LOAD (0, reg 18, reg 13, false, 4))
  , (0x00359713, .SHIFTIOP (3, reg 11, reg 14, .SLLI))
  , (0x00e686b3, .RTYPE (reg 14, reg 13, reg 13, .ADD))
  , (0x0006a683, .LOAD (0, reg 13, reg 13, false, 4))
  , (0x02869263, .BTYPE (0x24, reg 8, reg 13, .BNE))
  , (0x00090513, .ITYPE (0, reg 18, reg 10, .ADDI))
  , (0x00c12083, .LOAD (12, reg 2, reg 1, false, 4))
  , (0x00812403, .LOAD (8, reg 2, reg 8, false, 4))
  , (0x00412483, .LOAD (4, reg 2, reg 9, false, 4))
  , (0x00012903, .LOAD (0, reg 2, reg 18, false, 4))
  , (0x01010113, .ITYPE (16, reg 2, reg 2, .ADDI))
  , (0x00000317, .UTYPE (0, reg 6, .AUIPC))
  , (0xdb430067, .JALR (0xdb4, reg 6, reg 0))
  , (0x00c12083, .LOAD (12, reg 2, reg 1, false, 4))
  , (0x00812403, .LOAD (8, reg 2, reg 8, false, 4))
  , (0x00412483, .LOAD (4, reg 2, reg 9, false, 4))
  , (0x00012903, .LOAD (0, reg 2, reg 18, false, 4))
  , (0x01010113, .ITYPE (16, reg 2, reg 2, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

-- The callees, relative to the routine: `sorted_map_lower_bound` 0x34 bytes
-- before it and `raw_vec_pair_remove` 0x1dc bytes before it.
def searchOffset : Word := 0xffffffcc
def vectorOffset : Word := 0xfffffe24

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions, ext_decode entry.1 state = .ok entry.2 state := by
  decode_table_normal_form instructions [privilege, landingPad]

structure Snapshot where
  pc : Word := 0
  ra : Word
  sp : Word
  t1 : Word
  s0 : Word
  s1 : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word
  a5 : Word
  s2 : Word

instance : RegisterView Snapshot where
  tracked := [1, 2, 6, 8, 9, 10, 11, 12, 13, 14, 15, 18]
  pc state := state.pc
  value state index := match index.val with
    | 1 => state.ra
    | 2 => state.sp
    | 6 => state.t1
    | 8 => state.s0
    | 9 => state.s1
    | 10 => state.a0
    | 11 => state.a1
    | 12 => state.a2
    | 13 => state.a3
    | 14 => state.a4
    | 15 => state.a5
    | 18 => state.s2
    | _ => 0
  distinct := by decide
  nonzero := by decide

@[simp] theorem viewPc (state : Snapshot) : RegisterView.pc state = state.pc := rfl

-- A branch or jump target `offset` bytes into the routine is word-aligned.
theorem alignedTargetNat {base : Word} (aligned : base.toNat % 4 = 0) (offset : Word)
    (offsetAligned : offset.toNat % 4 = 0) : (base + offset).toNat % 4 = 0 := by
  rw [BitVec.toNat_add]
  omega

theorem alignedTarget {base : Word} (aligned : base.toNat % 4 = 0) (offset : Word)
    (offsetAligned : offset.toNat % 4 = 0) : (base + offset) % 4 = 0 := by
  apply BitVec.eq_of_toNat_eq
  change (base + offset).toNat % 4 = 0
  exact alignedTargetNat aligned offset offsetAligned

theorem offsetAdd (base first second sum : Word) (adds : first + second = sum) :
    base + first + second = base + sum := by
  rw [BitVec.add_assoc, adds]

section Steps

variable {base : Word} {original : Machine} {memory : ByteMemory}

private theorem fetchDecode (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (index : Fin instructions.length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base { original with mem := memory } state) = .ok (.F_Base instructions[index.val].1) (sync base { original with mem := memory } state) ∧
      ext_decode instructions[index.val].1 (sync base { original with mem := memory } state) =
        .ok instructions[index.val].2 (sync base { original with mem := memory } state) := by
  have here := machine.withMemory memory
  have synced := here.atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  have member := List.getElem_mem index.isLt
  exact ⟨(image.code here.privilege (here.status.imp fun _ read => read.1) here.htif state index pc).fetch
      (syncReadPC state) misaRead ((by decide : ∀ entry ∈ instructions,
        isRVC (entry.1.extractLsb' 0 16) = false) _ member),
    linkedWordsDecode _ synced.privilege synced.landingPad _ member⟩

private theorem load (machine : MachineState original) {state : Snapshot} {address value : Word}
    (permission : Readable original address) (contents : WordAt memory address.toNat value)
    (next offset : Word) :
    let entered := write_reg_state (sync base { original with mem := memory } state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false entered =
      .ok (.Ok value) entered := by
  obtain ⟨aligned, regions, region, regionsRead, matched, readable⟩ := permission
  have stored : original.regs.get? Register.pma_regions = some regions := readReg_succ.mp regionsRead
  exact (machine.withMemory memory).loadWord (base := base) state next offset address value regions
    region (readReg_succ.mpr stored) matched readable aligned contents

private theorem store (machine : MachineState original) {state : Snapshot} {address : Word}
    (permission : Writable original address) (next value : Word) :
    let entered := write_reg_state (sync base { original with mem := memory } state) Register.nextPC next
    vmem_write_addr (.Virtaddr address) 4 value (.Store .Data) false false false entered =
      .ok (.Ok true) (setWord entered address.toNat value) := by
  obtain ⟨aligned, regions, region, regionsRead, matched, writable⟩ := permission
  have stored : original.regs.get? Register.pma_regions = some regions := readReg_succ.mp regionsRead
  exact (machine.withMemory memory).storeWord (base := base) state next address value regions region
    (readReg_succ.mpr stored) matched writable aligned

variable (machine : MachineState original)
  (image : CodeImage instructions base { original with mem := memory })
include machine image

/-! ## The prologue -/

theorem step00 (state : Snapshot) (atPC : state.pc = 0x00#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x04#32, sp := state.sp + 0xfffffff0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨0, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step04 (state : Snapshot) (atPC : state.pc = 0x04#32)
    (permission : Writable original (state.sp + 12#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 12#32).toNat state.ra } { state with pc := 0x08#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨1, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 0x08#32 }) (pointer := state.sp)
    (value := state.ra) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 1) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.ra)
    (by advance [viewPc, atPC])
  exact stepped

theorem step08 (state : Snapshot) (atPC : state.pc = 0x08#32)
    (permission : Writable original (state.sp + 8#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 8#32).toNat state.s0 } { state with pc := 0x0c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨2, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 0x0c#32 }) (pointer := state.sp)
    (value := state.s0) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 8) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s0)
    (by advance [viewPc, atPC])
  exact stepped

theorem step0c (state : Snapshot) (atPC : state.pc = 0x0c#32)
    (permission : Writable original (state.sp + 4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 4#32).toNat state.s1 } { state with pc := 0x10#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨3, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 0x10#32 }) (pointer := state.sp)
    (value := state.s1) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 9) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s1)
    (by advance [viewPc, atPC])
  exact stepped

theorem step10 (state : Snapshot) (atPC : state.pc = 0x10#32)
    (permission : Writable original (state.sp + 0#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0#32).toNat state.s2 } { state with pc := 0x14#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨4, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 0x14#32 }) (pointer := state.sp)
    (value := state.s2) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 18) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s2)
    (by advance [viewPc, atPC])
  exact stepped

/-! ## The length check -/

theorem step14 (state : Snapshot) (atPC : state.pc = 0x14#32) (value : Word)
    (permission : Readable original (state.a0 + 4#32))
    (contents : WordAt memory (state.a0 + 4#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x18#32, s1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨5, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 10) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step18 (state : Snapshot) (atPC : state.pc = 0x18#32) (value : Word)
    (permission : Readable original (state.a0 + 8#32))
    (contents : WordAt memory (state.a0 + 8#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x1c#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨6, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 10) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1c (state : Snapshot) (atPC : state.pc = 0x1c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s1.toNat ≤ state.a2.toNat then 0x28#32 else 0x20#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨7, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.bgeu fetched decoded (syncRead state (index := 12) (by decide))
    (syncRead state (index := 9) (by decide)) misaRead ?_ ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩
  rw [BitVec.add_assoc, viewPc, atPC]
  exact alignedTarget image.aligned _ (by decide)

theorem step20 (state : Snapshot) (atPC : state.pc = 0x20#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x24#32, a0 := 3#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨8, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step24 (state : Snapshot) (atPC : state.pc = 0x24#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x78#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨9, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.jal fetched decoded misaRead ?_ ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩
  rw [BitVec.add_assoc, viewPc, atPC]
  exact alignedTarget image.aligned _ (by decide)

/-! ## The call to `sorted_map_lower_bound` -/

theorem step28 (state : Snapshot) (atPC : state.pc = 0x28#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x2c#32, s0 := state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨10, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step2c (state : Snapshot) (atPC : state.pc = 0x2c#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x30#32, s2 := state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨11, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step30 (state : Snapshot) (atPC : state.pc = 0x30#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x34#32, ra := base + 0x30#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨12, by decide⟩ atPC
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, offsetAdd base _ _ 0x30#32 (by decide)]
  advance [viewPc, atPC]

-- `jalr ra, -0x64(ra)` enters `sorted_map_lower_bound` and links the next word.
theorem step34 (state : Snapshot) (atPC : state.pc = 0x34#32) (link : state.ra = base + 0x30#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := searchOffset, ra := base + 0x38#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨13, by decide⟩ atPC
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xf9c#12).signExtend 32 = base + searchOffset := by
    rw [link, offsetAdd base _ _ searchOffset (by decide)]
  have targetAligned : (base + searchOffset).toNat % 4 = 0 :=
    alignedTargetNat image.aligned searchOffset (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xf9c#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + searchOffset = 0xfffffffe#32 &&& (state.ra + (0xf9c#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (offsetAdd base 0x34#32 4#32 0x38#32 rfl).symm)

/-! ## The key comparison -/

theorem step38 (state : Snapshot) (atPC : state.pc = 0x38#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x3c#32, a1 := state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨14, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step3c (state : Snapshot) (atPC : state.pc = 0x3c#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x40#32, a0 := 5#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨15, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step40 (state : Snapshot) (atPC : state.pc = 0x40#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s1.toNat ≤ state.a1.toNat then 0x78#32 else 0x44#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨16, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.bgeu fetched decoded (syncRead state (index := 11) (by decide))
    (syncRead state (index := 9) (by decide)) misaRead ?_ ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩
  rw [BitVec.add_assoc, viewPc, atPC]
  exact alignedTarget image.aligned _ (by decide)

theorem step44 (state : Snapshot) (atPC : state.pc = 0x44#32) (value : Word)
    (permission : Readable original state.s2) (contents : WordAt memory state.s2.toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x48#32, a3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨17, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 18) (by decide)) ?_ (by decide)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step48 (state : Snapshot) (atPC : state.pc = 0x48#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x4c#32, a4 := state.a1 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨18, by decide⟩ atPC
  exact Step.slli fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step4c (state : Snapshot) (atPC : state.pc = 0x4c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x50#32, a3 := state.a3 + state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨19, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (index := 13) (by decide))
    (syncRead state (index := 14) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step50 (state : Snapshot) (atPC : state.pc = 0x50#32) (value : Word)
    (permission : Readable original state.a3) (contents : WordAt memory state.a3.toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x54#32, a3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨20, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 13) (by decide)) ?_ (by decide)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step54 (state : Snapshot) (atPC : state.pc = 0x54#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a3 = state.s0 then 0x58#32 else 0x78#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨21, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.bne fetched decoded (syncRead state (index := 13) (by decide))
    (syncRead state (index := 8) (by decide)) misaRead (fun _ => ?_)
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩
  rw [BitVec.add_assoc, viewPc, atPC]
  exact alignedTarget image.aligned _ (by decide)

/-! ## The tail call to `raw_vec_pair_remove` -/

theorem step58 (state : Snapshot) (atPC : state.pc = 0x58#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x5c#32, a0 := state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨22, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step5c (state : Snapshot) (atPC : state.pc = 0x5c#32) (value : Word)
    (permission : Readable original (state.sp + 12#32))
    (contents : WordAt memory (state.sp + 12#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x60#32, ra := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨23, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step60 (state : Snapshot) (atPC : state.pc = 0x60#32) (value : Word)
    (permission : Readable original (state.sp + 8#32))
    (contents : WordAt memory (state.sp + 8#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x64#32, s0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨24, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step64 (state : Snapshot) (atPC : state.pc = 0x64#32) (value : Word)
    (permission : Readable original (state.sp + 4#32))
    (contents : WordAt memory (state.sp + 4#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x68#32, s1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨25, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step68 (state : Snapshot) (atPC : state.pc = 0x68#32) (value : Word)
    (permission : Readable original (state.sp + 0#32))
    (contents : WordAt memory (state.sp + 0#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x6c#32, s2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨26, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step6c (state : Snapshot) (atPC : state.pc = 0x6c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x70#32, sp := state.sp + 16#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨27, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step70 (state : Snapshot) (atPC : state.pc = 0x70#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x74#32, t1 := base + 0x70#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨28, by decide⟩ atPC
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, offsetAdd base _ _ 0x70#32 (by decide)]
  advance [viewPc, atPC]

-- `jr -0x24c(t1)` enters `raw_vec_pair_remove`, whose `ret` returns to our caller.
theorem step74 (state : Snapshot) (atPC : state.pc = 0x74#32) (link : state.t1 = base + 0x70#32) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := vectorOffset }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨29, by decide⟩ atPC
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.t1 + (0xdb4#12).signExtend 32 = base + vectorOffset := by
    rw [link, offsetAdd base _ _ vectorOffset (by decide)]
  have targetAligned : (base + vectorOffset).toNat % 4 = 0 :=
    alignedTargetNat image.aligned vectorOffset (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalr fetched decoded (syncRead state (index := 6) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ ⟨rfl, fun _ _ => rfl⟩
  · change BitVec.ofBool (state.t1 + (0xdb4#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + vectorOffset = 0xfffffffe#32 &&& (state.t1 + (0xdb4#12).signExtend 32)
    rw [target, maskEven _ bit0]

/-! ## The epilogue of a call that returns itself -/

theorem step78 (state : Snapshot) (atPC : state.pc = 0x78#32) (value : Word)
    (permission : Readable original (state.sp + 12#32))
    (contents : WordAt memory (state.sp + 12#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x7c#32, ra := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨30, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step7c (state : Snapshot) (atPC : state.pc = 0x7c#32) (value : Word)
    (permission : Readable original (state.sp + 8#32))
    (contents : WordAt memory (state.sp + 8#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x80#32, s0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨31, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step80 (state : Snapshot) (atPC : state.pc = 0x80#32) (value : Word)
    (permission : Readable original (state.sp + 4#32))
    (contents : WordAt memory (state.sp + 4#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x84#32, s1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨32, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step84 (state : Snapshot) (atPC : state.pc = 0x84#32) (value : Word)
    (permission : Readable original (state.sp + 0#32))
    (contents : WordAt memory (state.sp + 0#32).toNat value) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := 0x88#32, s2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨33, by decide⟩ atPC
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step88 (state : Snapshot) (atPC : state.pc = 0x88#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x8c#32, sp := state.sp + 16#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨34, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

-- `ret` reaches a caller whose return address is word-aligned.
theorem step8c (state : Snapshot) (atPC : state.pc = 0x8c#32) (returnAddress : Word)
    (link : state.ra = returnAddress) (returnLow : returnAddress &&& 0xfffffffe = returnAddress)
    (returnNext : returnAddress[1] = false) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨35, by decide⟩ atPC
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  refine Step.jalr (imm := 0#12) (sourceValue := returnAddress) fetched decoded
    (link ▸ syncRead state (index := 1) (by decide)) misaRead synced.privilege configRead ?_ ?_
    (by advance [viewPc])
  · simp [returnNext, BitVec.ofBool]
  · have mask : returnAddress &&& 0xfffffffe#32 = returnAddress := returnLow
    rw [BitVec.add_comm base, BitVec.sub_add_cancel,
      show (0#12).signExtend 32 = 0#32 from rfl, BitVec.add_zero, BitVec.and_comm, mask]

end Steps

end Riscfree.SortedMap.Remove
