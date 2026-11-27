import RawVec.Access

/-!
# The linked instructions of `raw_vec_pair_remove`

The same generic `RawVec<T>::remove` as `raw_vec_u32_remove`, with eight-byte
`Pair` elements, and the same register assignment: the length in `a3`, the
capacity and then the new length in `a2`, and the loop pointer in `a1`. It
shifts by 3 instead of 2, steps the pointer by 8, and moves each pair through
`a4` and `a5`.
-/

namespace Riscfree.RawVec.PairRemove

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

def instructions : List (Word × instruction) :=
  [ (0x00452683, .LOAD (4, reg 10, reg 13, false, 4))
  , (0x00852603, .LOAD (8, reg 10, reg 12, false, 4))
  , (0x00d67663, .BTYPE (12, reg 13, reg 12, .BGEU))
  , (0x00300513, .ITYPE (3, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x04d5f463, .BTYPE (72, reg 13, reg 11, .BGEU))
  , (0xfff68613, .ITYPE (0xfff, reg 13, reg 12, .ADDI))
  , (0x02c5fa63, .BTYPE (52, reg 12, reg 11, .BGEU))
  , (0x00052703, .LOAD (0, reg 10, reg 14, false, 4))
  , (0x00359593, .SHIFTIOP (3, reg 11, reg 11, .SLLI))
  , (0x00e585b3, .RTYPE (reg 14, reg 11, reg 11, .ADD))
  , (0x00369693, .SHIFTIOP (3, reg 13, reg 13, .SLLI))
  , (0x00858593, .ITYPE (8, reg 11, reg 11, .ADDI))
  , (0x00d706b3, .RTYPE (reg 13, reg 14, reg 13, .ADD))
  , (0x0005a703, .LOAD (0, reg 11, reg 14, false, 4))
  , (0x0045a783, .LOAD (4, reg 11, reg 15, false, 4))
  , (0xfee5ac23, .STORE (0xff8, reg 14, reg 11, 4))
  , (0xfef5ae23, .STORE (0xffc, reg 15, reg 11, 4))
  , (0x00858593, .ITYPE (8, reg 11, reg 11, .ADDI))
  , (0xfed596e3, .BTYPE (0x1fec, reg 13, reg 11, .BNE))
  , (0x00c52223, .STORE (4, reg 12, reg 10, 4))
  , (0x00000513, .ITYPE (0, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x00200513, .ITYPE (2, reg 0, reg 10, .ADDI))
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
  a2 : Word := 0
  a3 : Word := 0
  a4 : Word := 0
  a5 : Word := 0

instance : RegisterView Snapshot where
  tracked := [10, 11, 12, 13, 14, 15]
  pc state := state.pc
  value state index := match index.val with
    | 10 => state.a0
    | 11 => state.a1
    | 12 => state.a2
    | 13 => state.a3
    | 14 => state.a4
    | 15 => state.a5
    | _ => 0
  distinct := by decide
  nonzero := by decide

@[simp] theorem viewPc (state : Snapshot) : RegisterView.pc state = state.pc := rfl

abbrev Environment (base returnAddress : Word) (original : Machine) : Prop :=
  EnvironmentFor Snapshot instructions 100 base returnAddress original

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
      some (sync base {original with mem := memory} { state with pc := 4#32, a3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨0, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step04
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 4#32) (value : Word)
    (permission : Readable original (state.a0 + 8#32)) (contents : WordAt memory ((state.a0 + 8#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 8#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨1, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step08
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 8#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a3.toNat ≤ state.a2.toNat then 20#32 else 12#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨2, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 13) (by decide)) misaRead ?_ ?_
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
      some (sync base {original with mem := memory} { state with pc := if state.a3.toNat ≤ state.a1.toNat then 92#32 else 24#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨5, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 13) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step18
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 24#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 28#32, a2 := state.a3 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨6, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 13) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step1c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 28#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a2.toNat ≤ state.a1.toNat then 80#32 else 32#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨7, by decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.bgeu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 12) (by decide)) misaRead ?_ ?_
  · rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step20
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 32#32) (value : Word)
    (permission : Readable original state.a0) (contents : WordAt memory (state.a0).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 36#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨8, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  have loaded := Platform.loadWord platform state (base + state.pc + 4#32) 0 state.a0 value
    permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

theorem step24
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 36#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 40#32, a1 := state.a1 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨9, by decide⟩ atPC
  exact Step.slli fetched decoded (syncRead state (index := 11) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step28
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 40#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 44#32, a1 := state.a1 + state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨10, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step2c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 44#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 48#32, a3 := state.a3 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨11, by decide⟩ atPC
  exact Step.slli fetched decoded (syncRead state (index := 13) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step30
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 48#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 52#32, a1 := state.a1 + 8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨12, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 11) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step34
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 52#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 56#32, a3 := state.a4 + state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨13, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step38
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 56#32) (value : Word)
    (permission : Readable original state.a1) (contents : WordAt memory (state.a1).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 60#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨14, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 11) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  have loaded := Platform.loadWord platform state (base + state.pc + 4#32) 0 state.a1 value
    permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

theorem step3c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 60#32) (value : Word)
    (permission : Readable original (state.a1 + 4#32)) (contents : WordAt memory ((state.a1 + 4#32)).toNat value) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 64#32, a5 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨15, by decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 11) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  exact Platform.loadWord platform state _ _ _ _ permission contents

theorem step40
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 64#32)
    (permission : Writable original (state.a1 + 0xfffffff8#32)) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory ((state.a1 + 0xfffffff8#32)).toNat state.a4)} { state with pc := 68#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨16, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 68#32 }) (pointer := state.a1) (value := state.a4)
    fetched decoded (syncRead state (index := 11) (by decide))
    (syncRead state (index := 14) (by decide))
    (by exact Platform.storeWord platform state _ _ _ permission)
    (by advance [viewPc, atPC])
  exact stepped

theorem step44
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 68#32)
    (permission : Writable original (state.a1 + 0xfffffffc#32)) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory ((state.a1 + 0xfffffffc#32)).toNat state.a5)} { state with pc := 72#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨17, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 72#32 }) (pointer := state.a1) (value := state.a5)
    fetched decoded (syncRead state (index := 11) (by decide))
    (syncRead state (index := 15) (by decide))
    (by exact Platform.storeWord platform state _ _ _ permission)
    (by advance [viewPc, atPC])
  exact stepped

theorem step48
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 72#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 76#32, a1 := state.a1 + 8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨18, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 11) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step4c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 76#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := if state.a1 = state.a3 then 80#32 else 56#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨19, by decide⟩ atPC
  refine platform.bne fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 13) (by decide)) ?_ ?_
  · rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step50
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 80#32) (permission : Writable original (state.a0 + 4#32)) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := (storeWord memory ((state.a0 + 4#32)).toNat state.a2)} { state with pc := 84#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨20, by decide⟩ atPC
  have stepped := Step.sw (next := { state with pc := 84#32 }) (pointer := state.a0) (value := state.a2)
    fetched decoded (syncRead state (index := 10) (by decide))
    (syncRead state (index := 12) (by decide))
    (by exact Platform.storeWord platform state _ _ _ permission)
    (by advance [viewPc, atPC])
  exact stepped

theorem step54
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 84#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 88#32, a0 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨21, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step58
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 88#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨22, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

theorem step5c
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 92#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := 96#32, a0 := 2#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨23, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step60
    (platform : Platform Snapshot instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : Snapshot) (atPC : state.pc = 96#32) :
    step (sync base {original with mem := memory} state) =
      some (sync base {original with mem := memory} { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨24, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

end Instructions

end Riscfree.RawVec.PairRemove
