import RawVec.Access

/-!
# The linked instructions of `raw_vec_pair_insert`

The same generic `RawVec<T>::insert` as `raw_vec_u32_insert`, with eight-byte
`Pair` elements. Its registers differ: the length and capacity live in `a4`
and `a5`, the loop counter in `a6`, and the moved pair passes through `a7` and
`t0`, with `t1` holding the next pointer.
-/

namespace Riscfree.RawVec.PairInsert

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

def instructions : List (Word × instruction) :=
  [ (0x00452703, .LOAD (4, reg 10, reg 14, false, 4))
  , (0x00852783, .LOAD (8, reg 10, reg 15, false, 4))
  , (0x00e7f663, .BTYPE (12, reg 14, reg 15, .BGEU))
  , (0x00300513, .ITYPE (3, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x00b77663, .BTYPE (12, reg 11, reg 14, .BGEU))
  , (0x00200513, .ITYPE (2, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x00f71663, .BTYPE (12, reg 15, reg 14, .BNE))
  , (0x00100513, .ITYPE (1, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x02e5fa63, .BTYPE (52, reg 14, reg 11, .BGEU))
  , (0x00052783, .LOAD (0, reg 10, reg 15, false, 4))
  , (0x00371813, .SHIFTIOP (3, reg 14, reg 16, .SLLI))
  , (0x010787b3, .RTYPE (reg 16, reg 15, reg 15, .ADD))
  , (0x00070813, .ITYPE (0, reg 14, reg 16, .ADDI))
  , (0xff87a883, .LOAD (0xff8, reg 15, reg 17, false, 4))
  , (0xffc7a283, .LOAD (0xffc, reg 15, reg 5, false, 4))
  , (0xfff80813, .ITYPE (0xfff, reg 16, reg 16, .ADDI))
  , (0xff878313, .ITYPE (0xff8, reg 15, reg 6, .ADDI))
  , (0x0117a023, .STORE (0, reg 17, reg 15, 4))
  , (0x0057a223, .STORE (4, reg 5, reg 15, 4))
  , (0x00030793, .ITYPE (0, reg 6, reg 15, .ADDI))
  , (0xff05e2e3, .BTYPE (0x1fe4, reg 16, reg 11, .BLTU))
  , (0x00052803, .LOAD (0, reg 10, reg 16, false, 4))
  , (0x00359593, .SHIFTIOP (3, reg 11, reg 11, .SLLI))
  , (0x00b805b3, .RTYPE (reg 11, reg 16, reg 11, .ADD))
  , (0x00170713, .ITYPE (1, reg 14, reg 14, .ADDI))
  , (0x00c5a023, .STORE (0, reg 12, reg 11, 4))
  , (0x00d5a223, .STORE (4, reg 13, reg 11, 4))
  , (0x00e52223, .STORE (4, reg 14, reg 10, 4))
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
  t0 : Word := 0
  t1 : Word := 0
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word := 0
  a5 : Word := 0
  a6 : Word := 0
  a7 : Word := 0

instance : RegisterView Snapshot where
  tracked := [5, 6, 10, 11, 12, 13, 14, 15, 16, 17]
  pc state := state.pc
  value state index := match index.val with
    | 5 => state.t0
    | 6 => state.t1
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

abbrev CodeAgrees : Word → ByteMemory → ByteMemory → Prop := CodeAgreesFor 132

abbrev Environment (base returnAddress : Word) (original : Machine) : Prop :=
  EnvironmentFor Snapshot instructions 132 base returnAddress original

theorem Environment.ofMachine {base returnAddress : Word} {original : Machine}
    (mode : MachineMode original returnAddress) (image : CodeImage instructions base original) :
    Environment base returnAddress original :=
  EnvironmentFor.ofMachine mode image rfl

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

theorem step00
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 0#32) (value : Word)
    (permission : Readable original (state.a0 + 4#32)) (contents : WordAt memory ((state.a0 + 4#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 4#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨0, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step04
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 4#32) (value : Word)
    (permission : Readable original (state.a0 + 8#32)) (contents : WordAt memory ((state.a0 + 8#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 8#32, a5 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨1, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step08
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 8#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a4.toNat ≤ state.a5.toNat then 20#32 else 12#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨2, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 15) (by decide)) (syncRead state (index := 14) (by decide)) misaRead ?_ ?_
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
      some (sync base {original with mem := memory} { state with pc := if state.a1.toNat ≤ state.a4.toNat then 32#32 else 24#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨5, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 11) (by decide)) misaRead ?_ ?_
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
      some (sync base {original with mem := memory} { state with pc := if state.a4 = state.a5 then 36#32 else 44#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨8, by decide⟩ atPC
  refine platform.bne fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 15) (by decide)) ?_ ?_
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
      some (sync base {original with mem := memory} { state with pc := if state.a4.toNat ≤ state.a1.toNat then 96#32 else 48#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨11, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 14) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step30
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 48#32) (value : Word)
    (permission : Readable original state.a0) (contents : WordAt memory (state.a0).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 52#32, a5 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨12, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  have loaded := Platform.loadWord platform state (base + state.pc + 4#32) 0 state.a0 value
    permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

theorem step34
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 52#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 56#32, a6 := state.a4 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨13, by decide⟩ atPC
  exact Step.slli fetched decoded (syncRead state (index := 14) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step38
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 56#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 60#32, a5 := state.a5 + state.a6 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨14, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (index := 15) (by decide)) (syncRead state (index := 16) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step3c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 60#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 64#32, a6 := state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨15, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 14) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step40
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 64#32) (value : Word)
    (permission : Readable original (state.a5 + 0xfffffff8#32)) (contents : WordAt memory ((state.a5 + 0xfffffff8#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 68#32, a7 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨16, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 15) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step44
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 68#32) (value : Word)
    (permission : Readable original (state.a5 + 0xfffffffc#32)) (contents : WordAt memory ((state.a5 + 0xfffffffc#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 72#32, t0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨17, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 15) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step48
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 72#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 76#32, a6 := state.a6 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨18, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 16) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step4c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 76#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 80#32, t1 := state.a5 + 0xfffffff8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨19, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 15) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step50
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 80#32) (permission : Writable original state.a5) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory (state.a5).toNat state.a7)} { state with pc := 84#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨20, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 84#32 }) (pointer := state.a5) (value := state.a7)
    fetched decoded (syncRead state (index := 15) (by decide))
    (syncRead state (index := 17) (by decide))
    (by
      have stored := Platform.storeWord platform state (base + state.pc + 4#32) state.a5
        state.a7 permission
      simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stored)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stepped

theorem step54
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 84#32) (permission : Writable original (state.a5 + 4#32)) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory ((state.a5 + 4#32)).toNat state.t0)} { state with pc := 88#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨21, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 88#32 }) (pointer := state.a5) (value := state.t0)
    fetched decoded (syncRead state (index := 15) (by decide))
    (syncRead state (index := 5) (by decide))
    (by exact Platform.storeWord platform state _ _ _ permission)
    (by advance [viewPc, atPC])
  exact stepped

theorem step58
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 88#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 92#32, a5 := state.t1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨22, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 6) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step5c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 92#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a1.toNat < state.a6.toNat then 64#32 else 96#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨23, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bltu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 16) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step60
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 96#32) (value : Word)
    (permission : Readable original state.a0) (contents : WordAt memory (state.a0).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 100#32, a6 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨24, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  have loaded := Platform.loadWord platform state (base + state.pc + 4#32) 0 state.a0 value
    permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

theorem step64
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 100#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 104#32, a1 := state.a1 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨25, by decide⟩ atPC
  exact Step.slli fetched decoded (syncRead state (index := 11) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step68
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 104#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 108#32, a1 := state.a6 + state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨26, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (index := 16) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step6c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 108#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 112#32, a4 := state.a4 + 1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨27, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 14) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step70
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 112#32) (permission : Writable original state.a1) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory (state.a1).toNat state.a2)} { state with pc := 116#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨28, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 116#32 }) (pointer := state.a1) (value := state.a2)
    fetched decoded (syncRead state (index := 11) (by decide))
    (syncRead state (index := 12) (by decide))
    (by
      have stored := Platform.storeWord platform state (base + state.pc + 4#32) state.a1
        state.a2 permission
      simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stored)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using stepped

theorem step74
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 116#32) (permission : Writable original (state.a1 + 4#32)) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory ((state.a1 + 4#32)).toNat state.a3)} { state with pc := 120#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨29, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 120#32 }) (pointer := state.a1) (value := state.a3)
    fetched decoded (syncRead state (index := 11) (by decide))
    (syncRead state (index := 13) (by decide))
    (by exact Platform.storeWord platform state _ _ _ permission)
    (by advance [viewPc, atPC])
  exact stepped

theorem step78
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 120#32) (permission : Writable original (state.a0 + 4#32)) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory ((state.a0 + 4#32)).toNat state.a4)} { state with pc := 124#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨30, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 124#32 }) (pointer := state.a0) (value := state.a4)
    fetched decoded (syncRead state (index := 10) (by decide))
    (syncRead state (index := 14) (by decide))
    (by exact Platform.storeWord platform state _ _ _ permission)
    (by advance [viewPc, atPC])
  exact stepped

theorem step7c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 124#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 128#32, a0 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨31, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step80
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 128#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨32, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

end Instructions

end Riscfree.RawVec.PairInsert
