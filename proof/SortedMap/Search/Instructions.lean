import SortedMap.Search

/-!
# The linked instructions of the two sorted-map searches

`sorted_map_lower_bound` and `sorted_map_upper_bound` compile to the same 13
instructions except the branch at offset `0x14`, which leaves the loop when
the search does not pass the entry: `bgeu a4, a1` (the key is at least the
search key) for the lower bound, and `bltu a1, a4` (the key exceeds the search
key) for the upper bound. One table, parameterized by `Bound`, describes both,
so every step lemma below is proved once for both routines.

The length is in `a2`, the loop pointer in `a3`, the loaded key in `a4`, and
the counter, then the result, in `a0`.
-/

namespace Riscfree.SortedMap.Search

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

-- The branch that leaves the loop at an entry the search does not pass.
def exitBranch : Bound → Word × instruction
  | .lower => (0x00b77e63, .BTYPE (0x1c, reg 11, reg 14, .BGEU))
  | .upper => (0x00e5ee63, .BTYPE (0x1c, reg 14, reg 11, .BLTU))

def instructions (bound : Bound) : List (Word × instruction) :=
  [ (0x00452603, .LOAD (4, reg 10, reg 12, false, 4))
  , (0x02060463, .BTYPE (0x28, reg 0, reg 12, .BEQ))
  , (0x00052683, .LOAD (0, reg 10, reg 13, false, 4))
  , (0x00000513, .ITYPE (0, reg 0, reg 10, .ADDI))
  , (0x0006a703, .LOAD (0, reg 13, reg 14, false, 4))
  , exitBranch bound
  , (0x00150513, .ITYPE (1, reg 10, reg 10, .ADDI))
  , (0x00868693, .ITYPE (8, reg 13, reg 13, .ADDI))
  , (0xfea618e3, .BTYPE (0x1ff0, reg 10, reg 12, .BNE))
  , (0x00060513, .ITYPE (0, reg 12, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x00000513, .ITYPE (0, reg 0, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

def lowerInstructions : List (Word × instruction) := instructions .lower

def upperInstructions : List (Word × instruction) := instructions .upper

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem lowerWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ lowerInstructions, ext_decode entry.1 state = .ok entry.2 state := by
  unfold lowerInstructions
  decode_table_normal_form instructions [privilege, landingPad]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem upperWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ upperInstructions, ext_decode entry.1 state = .ok entry.2 state := by
  unfold upperInstructions
  decode_table_normal_form instructions [privilege, landingPad]

theorem linkedWordsDecode (bound : Bound) (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions bound, ext_decode entry.1 state = .ok entry.2 state := by
  cases bound
  · exact lowerWordsDecode state privilege landingPad
  · exact upperWordsDecode state privilege landingPad

theorem uncompressed (bound : Bound) :
    ∀ entry ∈ instructions bound, isRVC (entry.1.extractLsb' 0 16) = false := by
  cases bound <;> decide

theorem instructionsLength (bound : Bound) : (instructions bound).length = 13 := rfl

structure Snapshot where
  pc : Word := 0
  a0 : Word
  a1 : Word
  a2 : Word := 0
  a3 : Word := 0
  a4 : Word := 0

instance : RegisterView Snapshot where
  tracked := [10, 11, 12, 13, 14]
  pc state := state.pc
  value state index := match index.val with
    | 10 => state.a0
    | 11 => state.a1
    | 12 => state.a2
    | 13 => state.a3
    | 14 => state.a4
    | _ => 0
  distinct := by decide
  nonzero := by decide

@[simp] theorem viewPc (state : Snapshot) : RegisterView.pc state = state.pc := rfl

abbrev Environment (bound : Bound) (base returnAddress : Word) (original : Machine) : Prop :=
  EnvironmentFor Snapshot (instructions bound) 52 base returnAddress original

theorem Environment.ofMachine {bound : Bound} {base returnAddress : Word} {original : Machine}
    (mode : MachineMode original returnAddress) (image : CodeImage (instructions bound) base original) :
    Environment bound base returnAddress original :=
  EnvironmentFor.ofMachine mode image rfl

section Instructions

variable {bound : Bound} {base returnAddress : Word} {original : Machine}

local notation "Linked" => Platform Snapshot (instructions bound) base original [] returnAddress (fun _ => 0)

private theorem fetchDecode (platform : Linked) (state : Snapshot)
    (index : Fin (instructions bound).length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base original state) =
        .ok (.F_Base (instructions bound)[index.val].1) (sync base original state) ∧
      ext_decode (instructions bound)[index.val].1 (sync base original state) =
        .ok (instructions bound)[index.val].2 (sync base original state) :=
  platform.fetchAndDecode
    (fun state => linkedWordsDecode bound _ (platform.privilegeAt state) (platform.landingPadAt state))
    (uncompressed bound) state index pc

-- `lw a2, 4(a0)`: the length.
theorem step00 (platform : Linked) (state : Snapshot) (atPC : state.pc = 0#32) (value : Word)
    (permission : Readable original (state.a0 + 4#32))
    (contents : WordAt original.mem (state.a0 + 4#32).toNat value) :
    step (sync base original state) =
      some (sync base original { state with pc := 4#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨0, by rw [instructionsLength]; decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide)
    (by advance [viewPc, atPC])
  exact Platform.loadWord (memory := original.mem) platform state _ _ _ _ permission contents

-- `beqz a2, 0x2c`: an empty map returns 0.
theorem step04 (platform : Linked) (state : Snapshot) (atPC : state.pc = 4#32) :
    step (sync base original state) =
      some (sync base original { state with pc := if state.a2 = 0#32 then 44#32 else 8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨1, by rw [instructionsLength]; decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  refine Step.beq fetched decoded (syncRead state (index := 12) (by decide)) rfl misaRead ?_ ?_
  · intro
    rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  · exact ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

-- `lw a3, 0(a0)`: the data pointer.
theorem step08 (platform : Linked) (state : Snapshot) (atPC : state.pc = 8#32) (value : Word)
    (permission : Readable original state.a0) (contents : WordAt original.mem state.a0.toNat value) :
    step (sync base original state) =
      some (sync base original { state with pc := 12#32, a3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨2, by rw [instructionsLength]; decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide)
    (by advance [viewPc, atPC])
  have loaded := Platform.loadWord (memory := original.mem) platform state
    (base + state.pc + 4#32) 0 state.a0 value permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

-- `li a0, 0`: the counter.
theorem step0c (platform : Linked) (state : Snapshot) (atPC : state.pc = 12#32) :
    step (sync base original state) =
      some (sync base original { state with pc := 16#32, a0 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨3, by rw [instructionsLength]; decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

-- `lw a4, 0(a3)`: the entry's key.
theorem step10 (platform : Linked) (state : Snapshot) (atPC : state.pc = 16#32) (value : Word)
    (permission : Readable original state.a3) (contents : WordAt original.mem state.a3.toNat value) :
    step (sync base original state) =
      some (sync base original { state with pc := 20#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨4, by rw [instructionsLength]; decide⟩ atPC
  refine Step.lw fetched decoded (syncRead state (index := 13) (by decide)) ?_ (by decide)
    (by advance [viewPc, atPC])
  have loaded := Platform.loadWord (memory := original.mem) platform state
    (base + state.pc + 4#32) 0 state.a3 value permission contents
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using loaded

-- The exit branch: continue at `0x18` past an entry the search passes, and
-- return from `0x30` otherwise.
theorem step14 (platform : Linked) (state : Snapshot) (atPC : state.pc = 20#32) :
    step (sync base original state) =
      some (sync base original
        { state with pc := if bound.passes state.a4 state.a1 then 24#32 else 48#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨5, by rw [instructionsLength]; decide⟩ atPC
  obtain ⟨_, misaRead⟩ := platform.misaAt state
  have aligned : (base + RegisterView.pc state + (0x1c#13).signExtend 32) % 4 = 0 := by
    rw [BitVec.add_assoc]
    apply platform.alignedOffset
    rw [viewPc, atPC]; decide
  cases bound
  · refine Step.bgeu fetched decoded (syncRead state (index := 14) (by decide))
      (syncRead state (index := 11) (by decide)) misaRead aligned ⟨?_, fun _ _ => rfl⟩
    simp only [viewPc, atPC]
    show (if Bound.passes .lower state.a4 state.a1 then 24#32 else 48#32) =
      if state.a1.toNat ≤ state.a4.toNat then 20#32 + (0x1c#13).signExtend 32 else 20#32 + 4#32
    by_cases atLeast : state.a1.toNat ≤ state.a4.toNat
    · rw [if_pos atLeast, show Bound.passes .lower state.a4 state.a1 = false by
        simp only [Bound.passes, decide_eq_false_iff_not]; omega]
      rfl
    · rw [if_neg atLeast, show Bound.passes .lower state.a4 state.a1 = true by
        simp only [Bound.passes, decide_eq_true_eq]; omega]
      rfl
  · refine Step.bltu fetched decoded (syncRead state (index := 11) (by decide))
      (syncRead state (index := 14) (by decide)) misaRead aligned ⟨?_, fun _ _ => rfl⟩
    simp only [viewPc, atPC]
    show (if Bound.passes .upper state.a4 state.a1 then 24#32 else 48#32) =
      if state.a1.toNat < state.a4.toNat then 20#32 + (0x1c#13).signExtend 32 else 20#32 + 4#32
    by_cases above : state.a1.toNat < state.a4.toNat
    · rw [if_pos above, show Bound.passes .upper state.a4 state.a1 = false by
        simp only [Bound.passes, decide_eq_false_iff_not]; omega]
      rfl
    · rw [if_neg above, show Bound.passes .upper state.a4 state.a1 = true by
        simp only [Bound.passes, decide_eq_true_eq]; omega]
      rfl

-- `addi a0, a0, 1`: count the passed entry.
theorem step18 (platform : Linked) (state : Snapshot) (atPC : state.pc = 24#32) :
    step (sync base original state) =
      some (sync base original { state with pc := 28#32, a0 := state.a0 + 1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨6, by rw [instructionsLength]; decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

-- `addi a3, a3, 8`: the next entry.
theorem step1c (platform : Linked) (state : Snapshot) (atPC : state.pc = 28#32) :
    step (sync base original state) =
      some (sync base original { state with pc := 32#32, a3 := state.a3 + 8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨7, by rw [instructionsLength]; decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

-- `bne a2, a0, 0x10`: loop until the counter reaches the length.
theorem step20 (platform : Linked) (state : Snapshot) (atPC : state.pc = 32#32) :
    step (sync base original state) =
      some (sync base original { state with pc := if state.a2 = state.a0 then 36#32 else 16#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨8, by rw [instructionsLength]; decide⟩ atPC
  exact platform.bne fetched decoded (syncRead state (index := 12) (by decide))
    (syncRead state (index := 10) (by decide)) (by rw [viewPc, atPC]; decide)
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

-- `mv a0, a2`: every entry passed, so the result is the length.
theorem step24 (platform : Linked) (state : Snapshot) (atPC : state.pc = 36#32) :
    step (sync base original state) =
      some (sync base original { state with pc := 40#32, a0 := state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨9, by rw [instructionsLength]; decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step28 (platform : Linked) (state : Snapshot) (atPC : state.pc = 40#32) :
    step (sync base original state) =
      some (sync base original { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨10, by rw [instructionsLength]; decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

-- `li a0, 0`: the result for an empty map.
theorem step2c (platform : Linked) (state : Snapshot) (atPC : state.pc = 44#32) :
    step (sync base original state) =
      some (sync base original { state with pc := 48#32, a0 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨11, by rw [instructionsLength]; decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

theorem step30 (platform : Linked) (state : Snapshot) (atPC : state.pc = 48#32) :
    step (sync base original state) =
      some (sync base original { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode platform state ⟨12, by rw [instructionsLength]; decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

end Instructions

end Riscfree.SortedMap.Search
