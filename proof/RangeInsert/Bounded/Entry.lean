import RangeInsert.Empty.Execution
import RangeInsert.Bounded.InsertTable
import Riscfree.RV32.Compare
import Riscfree.RV32.Logic

/-! Sail step lemmas for the entry point's modifying paths, generated from
the linked and decoded instruction table. -/

namespace Riscfree.RangeInsert.Bounded.Entry

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions linkedWordsDecode)
open Empty (Snapshot viewPc load store)

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

section Steps

variable {base : Word} {original : Machine} {memory : ByteMemory}
theorem fetchDecode (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (index : Fin instructions.length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4))
    (notTrap : instructions[index.val].1 ≠ 0xc0001073) :
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
    linkedWordsDecode _ synced.privilege synced.landingPad _ member notTrap⟩

variable (machine : MachineState original)
  (image : CodeImage instructions base { original with mem := memory })
include machine image

theorem step00 (state : Snapshot) (atPC : state.pc = 0x0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x4#32, sp := state.sp + 0xffffffd0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨0, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step04 (state : Snapshot) (atPC : state.pc = 0x4#32)
    (permission : Writable original (state.sp + 0x2c#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x2c#32).toNat state.ra }
        { state with pc := 0x8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨1, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x8#32 }) (pointer := state.sp)
    (value := state.ra) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 1) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.ra)
    (by advance [viewPc, atPC])
  exact stepped

theorem step08 (state : Snapshot) (atPC : state.pc = 0x8#32)
    (permission : Writable original (state.sp + 0x28#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x28#32).toNat state.s0 }
        { state with pc := 0xc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨2, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xc#32 }) (pointer := state.sp)
    (value := state.s0) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 8) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s0)
    (by advance [viewPc, atPC])
  exact stepped

theorem step0c (state : Snapshot) (atPC : state.pc = 0xc#32)
    (permission : Writable original (state.sp + 0x24#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x24#32).toNat state.s1 }
        { state with pc := 0x10#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨3, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x10#32 }) (pointer := state.sp)
    (value := state.s1) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 9) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s1)
    (by advance [viewPc, atPC])
  exact stepped

theorem step10 (state : Snapshot) (atPC : state.pc = 0x10#32)
    (permission : Writable original (state.sp + 0x20#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x20#32).toNat state.s2 }
        { state with pc := 0x14#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨4, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x14#32 }) (pointer := state.sp)
    (value := state.s2) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 18) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s2)
    (by advance [viewPc, atPC])
  exact stepped

theorem step14 (state : Snapshot) (atPC : state.pc = 0x14#32)
    (permission : Writable original (state.sp + 0x1c#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x1c#32).toNat state.s3 }
        { state with pc := 0x18#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨5, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x18#32 }) (pointer := state.sp)
    (value := state.s3) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 19) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s3)
    (by advance [viewPc, atPC])
  exact stepped

theorem step18 (state : Snapshot) (atPC : state.pc = 0x18#32)
    (permission : Writable original (state.sp + 0x18#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x18#32).toNat state.s4 }
        { state with pc := 0x1c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨6, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x1c#32 }) (pointer := state.sp)
    (value := state.s4) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 20) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s4)
    (by advance [viewPc, atPC])
  exact stepped

theorem step1c (state : Snapshot) (atPC : state.pc = 0x1c#32)
    (permission : Writable original (state.sp + 0x14#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x14#32).toNat state.s5 }
        { state with pc := 0x20#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨7, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x20#32 }) (pointer := state.sp)
    (value := state.s5) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 21) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s5)
    (by advance [viewPc, atPC])
  exact stepped

theorem step20 (state : Snapshot) (atPC : state.pc = 0x20#32)
    (permission : Writable original (state.sp + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x4#32).toNat state.a0 }
        { state with pc := 0x24#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨8, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x24#32 }) (pointer := state.sp)
    (value := state.a0) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 10) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a0)
    (by advance [viewPc, atPC])
  exact stepped

theorem step24 (state : Snapshot) (atPC : state.pc = 0x24#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a2.toNat ≤ state.a3.toNat then 0x30#32 else 0x28#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨9, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bgeu fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 12) (by decide)) misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step28 (state : Snapshot) (atPC : state.pc = 0x28#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x2c#32, a0 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨10, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded rfl (by decide)
    (by advance [viewPc, atPC])

theorem step2c (state : Snapshot) (atPC : state.pc = 0x2c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨11, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.jal fetched decoded misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step30 (state : Snapshot) (atPC : state.pc = 0x30#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x34#32, s3 := state.a5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨12, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 15) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step34 (state : Snapshot) (atPC : state.pc = 0x34#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x38#32, s4 := state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨13, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step38 (state : Snapshot) (atPC : state.pc = 0x38#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x3c#32, s1 := state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨14, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step3c (state : Snapshot) (atPC : state.pc = 0x3c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x40#32, s2 := state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨15, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step40 (state : Snapshot) (atPC : state.pc = 0x40#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x44#32, s0 := state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨16, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step44 (state : Snapshot) (atPC : state.pc = 0x44#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x48#32, s5 := state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨17, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step48 (state : Snapshot) (atPC : state.pc = 0x48#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x4c#32, a1 := state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨18, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step4c (state : Snapshot) (atPC : state.pc = 0x4c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x50#32, ra := base + 0x4c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨19, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0x4c#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffdec#32`.
theorem step50 (state : Snapshot) (atPC : state.pc = 0x50#32)
    (link : state.ra = base + 0x4c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffdec#32, ra := base + 0x54#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨20, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xda0#12).signExtend 32 = base + 0xfffffdec#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffdec#32 (by decide)]
  have targetAligned : (base + 0xfffffdec#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffdec#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xda0#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffdec#32 = 0xfffffffe#32 &&& (state.ra + (0xda0#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0x50#32 4#32 0x54#32 rfl).symm)

theorem step54 (state : Snapshot) (atPC : state.pc = 0x54#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0xb4#32 else 0x58#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨21, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step58 (state : Snapshot) (atPC : state.pc = 0x58#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x5c#32, a1 := state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨22, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step5c (state : Snapshot) (atPC : state.pc = 0x5c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x60#32, a0 := state.s5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨23, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 21) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step60 (state : Snapshot) (atPC : state.pc = 0x60#32) (value : Word)
    (permission : Readable original (state.s5))
    (contents : WordAt memory (state.s5).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x64#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨24, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 21) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step64 (state : Snapshot) (atPC : state.pc = 0x64#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x68#32, a1 := state.a1 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨25, by decide⟩ atPC (by decide)
  exact Step.slli fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step68 (state : Snapshot) (atPC : state.pc = 0x68#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x6c#32, a2 := state.a2 + state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨26, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step6c (state : Snapshot) (atPC : state.pc = 0x6c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x70#32, a1 := state.a2 + 0xfffffff8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨27, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step70 (state : Snapshot) (atPC : state.pc = 0x70#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x74#32, a3 := state.a2 + 0xfffffffc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨28, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step74 (state : Snapshot) (atPC : state.pc = 0x74#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a1 = 0#32 then 0xc0#32 else 0x78#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨29, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 11) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step78 (state : Snapshot) (atPC : state.pc = 0x78#32) (value : Word)
    (permission : Readable original (state.a3))
    (contents : WordAt memory (state.a3).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x7c#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨30, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 13) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step7c (state : Snapshot) (atPC : state.pc = 0x7c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x80#32, a4 := state.a2 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨31, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step80 (state : Snapshot) (atPC : state.pc = 0x80#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x84#32, a5 := Step.lessWord state.a2 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨32, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step84 (state : Snapshot) (atPC : state.pc = 0x84#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x88#32, a4 := Step.lessWord state.a4 state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨33, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step88 (state : Snapshot) (atPC : state.pc = 0x88#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x8c#32, a4 := state.a5 &&& state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨34, by decide⟩ atPC (by decide)
  exact Step.and fetched decoded (syncRead state (index := 15) (by decide)) (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step8c (state : Snapshot) (atPC : state.pc = 0x8c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a4 = 0#32 then 0x130#32 else 0x90#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨35, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 14) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step90 (state : Snapshot) (atPC : state.pc = 0x90#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x94#32, a1 := state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨36, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step94 (state : Snapshot) (atPC : state.pc = 0x94#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x98#32, a2 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨37, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step98 (state : Snapshot) (atPC : state.pc = 0x98#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x9c#32, ra := base + 0x98#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨38, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0x98#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffc78#32`.
theorem step9c (state : Snapshot) (atPC : state.pc = 0x9c#32)
    (link : state.ra = base + 0x98#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffc78#32, ra := base + 0xa0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨39, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xbe0#12).signExtend 32 = base + 0xfffffc78#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffc78#32 (by decide)]
  have targetAligned : (base + 0xfffffc78#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffc78#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xbe0#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffc78#32 = 0xfffffffe#32 &&& (state.ra + (0xbe0#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0x9c#32 4#32 0xa0#32 rfl).symm)

theorem stepa0 (state : Snapshot) (atPC : state.pc = 0xa0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0xd4#32 else 0xa4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨40, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepa4 (state : Snapshot) (atPC : state.pc = 0xa4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xa8#32, a1 := 0#32 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨41, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded rfl (by decide)
    (by advance [viewPc, atPC])

theorem stepa8 (state : Snapshot) (atPC : state.pc = 0xa8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = state.a1 then 0x1a0#32 else 0xac#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨42, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 11) (by decide)) misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepb4 (state : Snapshot) (atPC : state.pc = 0xb4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xb8#32, a1 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨45, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded rfl (by decide)
    (by advance [viewPc, atPC])

theorem stepb8 (state : Snapshot) (atPC : state.pc = 0xb8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xbc#32, a0 := state.s5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨46, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 21) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepbc (state : Snapshot) (atPC : state.pc = 0xbc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a1 = 0#32 then 0xc0#32 else 0x78#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨47, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 11) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepc0 (state : Snapshot) (atPC : state.pc = 0xc0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xc4#32, a1 := state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨48, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepc4 (state : Snapshot) (atPC : state.pc = 0xc4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xc8#32, a2 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨49, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepc8 (state : Snapshot) (atPC : state.pc = 0xc8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xcc#32, ra := base + 0xc8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨50, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0xc8#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffc78#32`.
theorem stepcc (state : Snapshot) (atPC : state.pc = 0xcc#32)
    (link : state.ra = base + 0xc8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffc78#32, ra := base + 0xd0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨51, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xbb0#12).signExtend 32 = base + 0xfffffc78#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffc78#32 (by decide)]
  have targetAligned : (base + 0xfffffc78#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffc78#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xbb0#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffc78#32 = 0xfffffffe#32 &&& (state.ra + (0xbb0#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0xcc#32 4#32 0xd0#32 rfl).symm)

theorem stepd0 (state : Snapshot) (atPC : state.pc = 0xd0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0xd4#32 else 0x198#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨52, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepd4 (state : Snapshot) (atPC : state.pc = 0xd4#32)
    (permission : Writable original (state.sp + 0x8#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x8#32).toNat state.s4 }
        { state with pc := 0xd8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨53, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xd8#32 }) (pointer := state.sp)
    (value := state.s4) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 20) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s4)
    (by advance [viewPc, atPC])
  exact stepped

theorem stepd8 (state : Snapshot) (atPC : state.pc = 0xd8#32)
    (permission : Writable original (state.sp + 0xc#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0xc#32).toNat 0#32 }
        { state with pc := 0xdc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨54, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xdc#32 }) (pointer := state.sp)
    (value := 0#32) fetched decoded (syncRead state (index := 2) (by decide)) rfl
    (store machine (state := state) permission (base + state.pc + 4#32) 0#32)
    (by advance [viewPc, atPC])
  exact stepped

theorem stepdc (state : Snapshot) (atPC : state.pc = 0xdc#32)
    (permission : Writable original (state.sp + 0x10#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x10#32).toNat state.s3 }
        { state with pc := 0xe0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨55, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xe0#32 }) (pointer := state.sp)
    (value := state.s3) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 19) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s3)
    (by advance [viewPc, atPC])
  exact stepped

theorem stepe0 (state : Snapshot) (atPC : state.pc = 0xe0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xe4#32, a0 := state.sp + 0x4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨56, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepe4 (state : Snapshot) (atPC : state.pc = 0xe4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xe8#32, a4 := state.sp + 0x8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨57, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepe8 (state : Snapshot) (atPC : state.pc = 0xe8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xec#32, a1 := state.s0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨58, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 8) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepec (state : Snapshot) (atPC : state.pc = 0xec#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xf0#32, a2 := state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨59, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepf0 (state : Snapshot) (atPC : state.pc = 0xf0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xf4#32, a3 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨60, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepf4 (state : Snapshot) (atPC : state.pc = 0xf4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xf8#32, ra := base + 0xf4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨61, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0xf4#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffe20#32`.
theorem stepf8 (state : Snapshot) (atPC : state.pc = 0xf8#32)
    (link : state.ra = base + 0xf4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffe20#32, ra := base + 0xfc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨62, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xd2c#12).signExtend 32 = base + 0xfffffe20#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffe20#32 (by decide)]
  have targetAligned : (base + 0xfffffe20#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffe20#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xd2c#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffe20#32 = 0xfffffffe#32 &&& (state.ra + (0xd2c#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0xf8#32 4#32 0xfc#32 rfl).symm)

theorem stepfc (state : Snapshot) (atPC : state.pc = 0xfc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0x100#32 else 0x1a0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨63, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step100 (state : Snapshot) (atPC : state.pc = 0x100#32) (value : Word)
    (permission : Readable original (state.s0))
    (contents : WordAt memory (state.s0).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x104#32, a1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨64, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 8) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step104 (state : Snapshot) (atPC : state.pc = 0x104#32) (value : Word)
    (permission : Readable original (state.s0 + 0x4#32))
    (contents : WordAt memory (state.s0 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x108#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨65, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 8) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step108 (state : Snapshot) (atPC : state.pc = 0x108#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x10c#32, a3 := state.s1 - state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨66, by decide⟩ atPC (by decide)
  exact Step.sub fetched decoded (syncRead state (index := 9) (by decide)) (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step10c (state : Snapshot) (atPC : state.pc = 0x10c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x110#32, a1 := state.a3 + state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨67, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step110 (state : Snapshot) (atPC : state.pc = 0x110#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x114#32, a3 := Step.lessWord state.a1 state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨68, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step114 (state : Snapshot) (atPC : state.pc = 0x114#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x118#32, a1 := state.a1 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨69, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step118 (state : Snapshot) (atPC : state.pc = 0x118#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x11c#32, a2 := state.a2 + state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨70, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step11c (state : Snapshot) (atPC : state.pc = 0x11c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x120#32, a3 := Step.lessWord state.a1 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨71, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step120 (state : Snapshot) (atPC : state.pc = 0x120#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x124#32, a2 := state.a2 + state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨72, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step124 (state : Snapshot) (atPC : state.pc = 0x124#32)
    (permission' : Writable original (state.s0)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0).toNat state.a1 }
        { state with pc := 0x128#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨73, by decide⟩ atPC (by decide)
  have permission : Writable original (state.s0 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x128#32 }) (pointer := state.s0)
    (value := state.a1) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 11) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a1)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step128 (state : Snapshot) (atPC : state.pc = 0x128#32)
    (permission : Writable original (state.s0 + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0 + 0x4#32).toNat state.a2 }
        { state with pc := 0x12c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨74, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x12c#32 }) (pointer := state.s0)
    (value := state.a2) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 12) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a2)
    (by advance [viewPc, atPC])
  exact stepped

theorem step12c (state : Snapshot) (atPC : state.pc = 0x12c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨75, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.jal fetched decoded misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step130 (state : Snapshot) (atPC : state.pc = 0x130#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s1.toNat ≤ state.a2.toNat then 0x28#32 else 0x134#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨76, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bgeu fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 9) (by decide)) misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step134 (state : Snapshot) (atPC : state.pc = 0x134#32) (value : Word)
    (permission : Readable original (state.s0))
    (contents : WordAt memory (state.s0).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x138#32, a0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨77, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 8) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step138 (state : Snapshot) (atPC : state.pc = 0x138#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x13c#32, a2 := state.a2 ^^^ 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨78, by decide⟩ atPC (by decide)
  exact Step.xori fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step13c (state : Snapshot) (atPC : state.pc = 0x13c#32) (value : Word)
    (permission : Readable original (state.s0 + 0x4#32))
    (contents : WordAt memory (state.s0 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x140#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨79, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 8) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step140 (state : Snapshot) (atPC : state.pc = 0x140#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x144#32, a2 := state.s1 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨80, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 9) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step144 (state : Snapshot) (atPC : state.pc = 0x144#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x148#32, a0 := state.a2 + state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨81, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step148 (state : Snapshot) (atPC : state.pc = 0x148#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x14c#32, a2 := Step.lessWord state.a0 state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨82, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step14c (state : Snapshot) (atPC : state.pc = 0x14c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x150#32, a0 := state.a0 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨83, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step150 (state : Snapshot) (atPC : state.pc = 0x150#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x154#32, a2 := state.a4 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨84, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step154 (state : Snapshot) (atPC : state.pc = 0x154#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x158#32, a4 := Step.lessWord state.a0 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨85, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step158 (state : Snapshot) (atPC : state.pc = 0x158#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x15c#32, a2 := state.a2 + state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨86, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step15c (state : Snapshot) (atPC : state.pc = 0x15c#32)
    (permission' : Writable original (state.s0)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0).toNat state.a0 }
        { state with pc := 0x160#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨87, by decide⟩ atPC (by decide)
  have permission : Writable original (state.s0 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x160#32 }) (pointer := state.s0)
    (value := state.a0) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 10) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a0)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step160 (state : Snapshot) (atPC : state.pc = 0x160#32)
    (permission : Writable original (state.s0 + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0 + 0x4#32).toNat state.a2 }
        { state with pc := 0x164#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨88, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x164#32 }) (pointer := state.s0)
    (value := state.a2) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 12) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a2)
    (by advance [viewPc, atPC])
  exact stepped

theorem step164 (state : Snapshot) (atPC : state.pc = 0x164#32) (value : Word)
    (permission : Readable original (state.a1))
    (contents : WordAt memory (state.a1).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x168#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨89, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 11) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step168 (state : Snapshot) (atPC : state.pc = 0x168#32)
    (permission' : Writable original (state.a3)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.a3).toNat state.s1 }
        { state with pc := 0x16c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨90, by decide⟩ atPC (by decide)
  have permission : Writable original (state.a3 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x16c#32 }) (pointer := state.a3)
    (value := state.s1) fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 9) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s1)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step16c (state : Snapshot) (atPC : state.pc = 0x16c#32)
    (permission : Writable original (state.sp + 0x8#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x8#32).toNat state.s4 }
        { state with pc := 0x170#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨91, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x170#32 }) (pointer := state.sp)
    (value := state.s4) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 20) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s4)
    (by advance [viewPc, atPC])
  exact stepped

theorem step170 (state : Snapshot) (atPC : state.pc = 0x170#32)
    (permission : Writable original (state.sp + 0xc#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0xc#32).toNat 0#32 }
        { state with pc := 0x174#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨92, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x174#32 }) (pointer := state.sp)
    (value := 0#32) fetched decoded (syncRead state (index := 2) (by decide)) rfl
    (store machine (state := state) permission (base + state.pc + 4#32) 0#32)
    (by advance [viewPc, atPC])
  exact stepped

theorem step174 (state : Snapshot) (atPC : state.pc = 0x174#32)
    (permission : Writable original (state.sp + 0x10#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x10#32).toNat state.s3 }
        { state with pc := 0x178#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨93, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x178#32 }) (pointer := state.sp)
    (value := state.s3) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 19) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s3)
    (by advance [viewPc, atPC])
  exact stepped

theorem step178 (state : Snapshot) (atPC : state.pc = 0x178#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x17c#32, a0 := state.sp + 0x4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨94, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step17c (state : Snapshot) (atPC : state.pc = 0x17c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x180#32, a4 := state.sp + 0x8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨95, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step180 (state : Snapshot) (atPC : state.pc = 0x180#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x184#32, a1 := state.s0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨96, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 8) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step184 (state : Snapshot) (atPC : state.pc = 0x184#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x188#32, a3 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨97, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step188 (state : Snapshot) (atPC : state.pc = 0x188#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x18c#32, ra := base + 0x188#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨98, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0x188#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffe20#32`.
theorem step18c (state : Snapshot) (atPC : state.pc = 0x18c#32)
    (link : state.ra = base + 0x188#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffe20#32, ra := base + 0x190#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨99, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xc98#12).signExtend 32 = base + 0xfffffe20#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffe20#32 (by decide)]
  have targetAligned : (base + 0xfffffe20#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffe20#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xc98#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffe20#32 = 0xfffffffe#32 &&& (state.ra + (0xc98#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0x18c#32 4#32 0x190#32 rfl).symm)

theorem step190 (state : Snapshot) (atPC : state.pc = 0x190#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0x194#32 else 0x1a0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨100, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step194 (state : Snapshot) (atPC : state.pc = 0x194#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨101, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.jal fetched decoded misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step198 (state : Snapshot) (atPC : state.pc = 0x198#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x19c#32, a1 := 0#32 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨102, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded rfl (by decide)
    (by advance [viewPc, atPC])

theorem step19c (state : Snapshot) (atPC : state.pc = 0x19c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = state.a1 then 0x1a0#32 else 0x1c8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨103, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 11) (by decide)) misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step1a0 (state : Snapshot) (atPC : state.pc = 0x1a0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a4#32, a0 := 0#32 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨104, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded rfl (by decide)
    (by advance [viewPc, atPC])

theorem step1a4 (state : Snapshot) (atPC : state.pc = 0x1a4#32) (value : Word)
    (permission : Readable original (state.sp + 0x2c#32))
    (contents : WordAt memory (state.sp + 0x2c#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a8#32, ra := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨105, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1a8 (state : Snapshot) (atPC : state.pc = 0x1a8#32) (value : Word)
    (permission : Readable original (state.sp + 0x28#32))
    (contents : WordAt memory (state.sp + 0x28#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1ac#32, s0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨106, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1ac (state : Snapshot) (atPC : state.pc = 0x1ac#32) (value : Word)
    (permission : Readable original (state.sp + 0x24#32))
    (contents : WordAt memory (state.sp + 0x24#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1b0#32, s1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨107, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1b0 (state : Snapshot) (atPC : state.pc = 0x1b0#32) (value : Word)
    (permission : Readable original (state.sp + 0x20#32))
    (contents : WordAt memory (state.sp + 0x20#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1b4#32, s2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨108, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1b4 (state : Snapshot) (atPC : state.pc = 0x1b4#32) (value : Word)
    (permission : Readable original (state.sp + 0x1c#32))
    (contents : WordAt memory (state.sp + 0x1c#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1b8#32, s3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨109, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1b8 (state : Snapshot) (atPC : state.pc = 0x1b8#32) (value : Word)
    (permission : Readable original (state.sp + 0x18#32))
    (contents : WordAt memory (state.sp + 0x18#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1bc#32, s4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨110, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1bc (state : Snapshot) (atPC : state.pc = 0x1bc#32) (value : Word)
    (permission : Readable original (state.sp + 0x14#32))
    (contents : WordAt memory (state.sp + 0x14#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1c0#32, s5 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨111, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1c0 (state : Snapshot) (atPC : state.pc = 0x1c0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1c4#32, sp := state.sp + 0x30#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨112, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step1c4 (state : Snapshot) (atPC : state.pc = 0x1c4#32) (returnAddress : Word)
    (link : state.ra = returnAddress) (returnLow : returnAddress &&& 0xfffffffe = returnAddress)
    (returnNext : returnAddress[1] = false) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨113, by decide⟩ atPC (by decide)
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

end Riscfree.RangeInsert.Bounded.Entry
