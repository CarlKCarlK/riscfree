import RangeInsert.Empty.Execution
import Riscfree.RV32.Compare

/-! Single Sail steps of the range insertion entry point on its nonempty
paths: argument moves, the predecessor call, the predecessor end test, and
the covered-range branch. Each lemma reuses the entry's checked decode
table and snapshot from `RangeInsert.Empty.Execution`. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Empty (Snapshot fetchDecode load viewPc)

set_option maxHeartbeats 2000000

-- `sorted_map_upper_bound` lies 0x208 bytes before the entry point.
def upperBoundOffset : Word := 0xfffffdf8

section Steps

variable {base : Word} {original : Machine} {memory : ByteMemory}
variable (machine : MachineState original)
  (image : CodeImage instructions base { original with mem := memory })
include machine image

theorem branchNonempty (state : Snapshot) (atPC : state.pc = 0x24#32)
    (nonempty : state.a2.toNat ≤ state.a3.toNat) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x28#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨9, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.bltu fetched decoded (syncRead state (index := 13) (by decide))
    (syncRead state (index := 12) (by decide)) misaRead ?_ ⟨?_, fun _ _ => rfl⟩
  · rw [BitVec.add_assoc, viewPc, atPC]
    exact SortedMap.Remove.alignedTarget image.aligned _ (by decide)
  · change 0x28#32 = if state.a3.toNat < state.a2.toNat then
        state.pc + (0x100#13).signExtend 32 else state.pc + 4#32
    rw [if_neg (by omega), atPC]
    rfl

theorem step28 (state : Snapshot) (atPC : state.pc = 0x28#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x2c#32, s3 := state.a5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨10, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 15) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step2c (state : Snapshot) (atPC : state.pc = 0x2c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x30#32, s4 := state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨11, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step30 (state : Snapshot) (atPC : state.pc = 0x30#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x34#32, s1 := state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨12, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step34 (state : Snapshot) (atPC : state.pc = 0x34#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x38#32, s2 := state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨13, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step38 (state : Snapshot) (atPC : state.pc = 0x38#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x3c#32, s0 := state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨14, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step3c (state : Snapshot) (atPC : state.pc = 0x3c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x40#32, s5 := state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨15, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step40 (state : Snapshot) (atPC : state.pc = 0x40#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x44#32, a1 := state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨16, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step44 (state : Snapshot) (atPC : state.pc = 0x44#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x48#32, ra := base + 0x44#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨17, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0x44#32 (by decide)]
  advance [viewPc, atPC]

-- `jalr ra, -0x24c(ra)` calls `sorted_map_upper_bound` and links `+0x4c`.
theorem step48 (state : Snapshot) (atPC : state.pc = 0x48#32) (link : state.ra = base + 0x44#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        { state with pc := upperBoundOffset, ra := base + 0x4c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨18, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xdb4#12).signExtend 32 = base + upperBoundOffset := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ upperBoundOffset (by decide)]
  have targetAligned : (base + upperBoundOffset).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned upperBoundOffset (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xdb4#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + upperBoundOffset = 0xfffffffe#32 &&& (state.ra + (0xdb4#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0x48#32 4#32 0x4c#32 rfl).symm)

-- A nonzero upper-bound rank means a predecessor exists.
theorem branchFound (state : Snapshot) (atPC : state.pc = 0x4c#32) (found : state.a0 ≠ 0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x50#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨19, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.beq fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun same => (found same).elim) ⟨?_, fun _ _ => rfl⟩
  change 0x50#32 = if state.a0 = 0#32 then state.pc + (0x64#13).signExtend 32 else state.pc + 4#32
  rw [if_neg found, atPC]
  rfl

theorem step50 (state : Snapshot) (atPC : state.pc = 0x50#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x54#32, a1 := state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨20, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step54 (state : Snapshot) (atPC : state.pc = 0x54#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x58#32, a0 := state.s5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨21, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 21) (by decide)) (by decide)
    (by advance [viewPc, atPC])

-- Load the map's data pointer from its header.
theorem step58 (state : Snapshot) (atPC : state.pc = 0x58#32) (value : Word)
    (permission : Readable original state.s5) (contents : WordAt memory state.s5.toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x5c#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨22, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 21) (by decide)) ?_ (by decide)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step5c (state : Snapshot) (atPC : state.pc = 0x5c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x60#32, a1 := state.a1 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨23, by decide⟩ atPC (by decide)
  exact Step.slli fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step60 (state : Snapshot) (atPC : state.pc = 0x60#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x64#32, a2 := state.a2 + state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨24, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide))
    (syncRead state (index := 11) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step64 (state : Snapshot) (atPC : state.pc = 0x64#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x68#32, a1 := state.a2 + 0xfffffff8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨25, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step68 (state : Snapshot) (atPC : state.pc = 0x68#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x6c#32, a3 := state.a2 + 0xfffffffc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨26, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

-- The compiler's null test on the predecessor's key pointer.
theorem branchKeyPointer (state : Snapshot) (atPC : state.pc = 0x6c#32) (nonnull : state.a1 ≠ 0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x70#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨27, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.beq fetched decoded (syncRead state (index := 11) (by decide)) rfl misaRead
    (fun same => (nonnull same).elim) ⟨?_, fun _ _ => rfl⟩
  change 0x70#32 = if state.a1 = 0#32 then state.pc + (0x50#13).signExtend 32 else state.pc + 4#32
  rw [if_neg nonnull, atPC]
  rfl

-- Load the predecessor's end.
theorem step70 (state : Snapshot) (atPC : state.pc = 0x70#32) (value : Word)
    (permission : Readable original state.a3) (contents : WordAt memory state.a3.toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x74#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨28, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 13) (by decide)) ?_ (by decide)
    (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step74 (state : Snapshot) (atPC : state.pc = 0x74#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x78#32, a4 := state.a2 + 1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨29, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

-- `a5 := predecessor_end < u32::MAX`.
theorem step78 (state : Snapshot) (atPC : state.pc = 0x78#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        { state with pc := 0x7c#32, a5 := Step.lessWord state.a2 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨30, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

-- `a4 := predecessor_end + 1 < start`.
theorem step7c (state : Snapshot) (atPC : state.pc = 0x7c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        { state with pc := 0x80#32, a4 := Step.lessWord state.a4 state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨31, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 14) (by decide))
    (syncRead state (index := 18) (by decide)) (by decide) (by advance [viewPc, atPC])

theorem step80 (state : Snapshot) (atPC : state.pc = 0x80#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x84#32, a4 := state.a5 &&& state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨32, by decide⟩ atPC (by decide)
  exact Step.and fetched decoded (syncRead state (index := 15) (by decide))
    (syncRead state (index := 14) (by decide)) (by decide) (by advance [viewPc, atPC])

-- No strict gap after the predecessor: continue at the covered-range test.
theorem branchTouches (state : Snapshot) (atPC : state.pc = 0x84#32) (touches : state.a4 = 0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x148#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨33, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.beq fetched decoded (syncRead state (index := 14) (by decide)) rfl misaRead
    (fun _ => ?_) ⟨?_, fun _ _ => rfl⟩
  · rw [BitVec.add_assoc, viewPc, atPC]
    exact SortedMap.Remove.alignedTarget image.aligned _ (by decide)
  · change 0x148#32 = if state.a4 = 0#32 then state.pc + (0xc4#13).signExtend 32 else state.pc + 4#32
    rw [if_pos touches, atPC]
    rfl

-- The predecessor already covers the end: go to the common epilogue.
theorem branchCovered (state : Snapshot) (atPC : state.pc = 0x148#32)
    (covered : state.s1.toNat ≤ state.a2.toNat) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x124#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨82, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.bgeu fetched decoded (syncRead state (index := 12) (by decide))
    (syncRead state (index := 9) (by decide)) misaRead ?_ ⟨?_, fun _ _ => rfl⟩
  · rw [BitVec.add_assoc, viewPc, atPC]
    exact SortedMap.Remove.alignedTarget image.aligned _ (by decide)
  · change 0x124#32 = if state.s1.toNat ≤ state.a2.toNat then
        state.pc + (0x1fdc#13).signExtend 32 else state.pc + 4#32
    rw [if_pos covered, atPC]
    rfl

end Steps

end Riscfree.RangeInsert.Nonempty
