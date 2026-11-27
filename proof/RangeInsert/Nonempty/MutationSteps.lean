import RangeInsert.Empty.Execution
import Riscfree.RV32.Compare
import Riscfree.RV32.Logic

/-! Sail step lemmas for the entry point's modifying paths, generated from
the linked and decoded instruction table. -/

namespace Riscfree.RangeInsert.Nonempty.Mutation

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Empty (Snapshot fetchDecode viewPc load store)

set_option maxHeartbeats 2000000

section Steps

variable {base : Word} {original : Machine} {memory : ByteMemory}
variable (machine : MachineState original)
  (image : CodeImage instructions base { original with mem := memory })
include machine image

theorem step88 (state : Snapshot) (atPC : state.pc = 0x88#32)
    (permission : Writable original (state.sp + 0x8#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x8#32).toNat state.s4 }
        { state with pc := 0x8c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨34, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x8c#32 }) (pointer := state.sp)
    (value := state.s4) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 20) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s4)
    (by advance [viewPc, atPC])
  exact stepped

theorem step8c (state : Snapshot) (atPC : state.pc = 0x8c#32)
    (permission : Writable original (state.sp + 0xc#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0xc#32).toNat 0#32 }
        { state with pc := 0x90#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨35, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x90#32 }) (pointer := state.sp)
    (value := 0#32) fetched decoded (syncRead state (index := 2) (by decide)) rfl
    (store machine (state := state) permission (base + state.pc + 4#32) 0#32)
    (by advance [viewPc, atPC])
  exact stepped

theorem step90 (state : Snapshot) (atPC : state.pc = 0x90#32)
    (permission : Writable original (state.sp + 0x10#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x10#32).toNat state.s3 }
        { state with pc := 0x94#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨36, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x94#32 }) (pointer := state.sp)
    (value := state.s3) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 19) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s3)
    (by advance [viewPc, atPC])
  exact stepped

theorem step94 (state : Snapshot) (atPC : state.pc = 0x94#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x98#32, a1 := state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨37, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step98 (state : Snapshot) (atPC : state.pc = 0x98#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x9c#32, a2 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨38, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step9c (state : Snapshot) (atPC : state.pc = 0x9c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xa0#32, ra := base + 0x9c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨39, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0x9c#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffc84#32`.
theorem stepa0 (state : Snapshot) (atPC : state.pc = 0xa0#32)
    (link : state.ra = base + 0x9c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffc84#32, ra := base + 0xa4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨40, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xbe8#12).signExtend 32 = base + 0xfffffc84#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffc84#32 (by decide)]
  have targetAligned : (base + 0xfffffc84#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffc84#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xbe8#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffc84#32 = 0xfffffffe#32 &&& (state.ra + (0xbe8#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0xa0#32 4#32 0xa4#32 rfl).symm)

theorem stepa4 (state : Snapshot) (atPC : state.pc = 0xa4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0xdc#32 else 0xa8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨41, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepb0 (state : Snapshot) (atPC : state.pc = 0xb0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xb4#32, a1 := 0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨44, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded rfl (by decide)
    (by advance [viewPc, atPC])

theorem stepb4 (state : Snapshot) (atPC : state.pc = 0xb4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xb8#32, a0 := state.s5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨45, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 21) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepb8 (state : Snapshot) (atPC : state.pc = 0xb8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a1 = 0#32 then 0xbc#32 else 0x70#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨46, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 11) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepbc (state : Snapshot) (atPC : state.pc = 0xbc#32)
    (permission : Writable original (state.sp + 0x8#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x8#32).toNat state.s4 }
        { state with pc := 0xc0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨47, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xc0#32 }) (pointer := state.sp)
    (value := state.s4) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 20) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s4)
    (by advance [viewPc, atPC])
  exact stepped

theorem stepc0 (state : Snapshot) (atPC : state.pc = 0xc0#32)
    (permission : Writable original (state.sp + 0xc#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0xc#32).toNat 0#32 }
        { state with pc := 0xc4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨48, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xc4#32 }) (pointer := state.sp)
    (value := 0#32) fetched decoded (syncRead state (index := 2) (by decide)) rfl
    (store machine (state := state) permission (base + state.pc + 4#32) 0#32)
    (by advance [viewPc, atPC])
  exact stepped

theorem stepc4 (state : Snapshot) (atPC : state.pc = 0xc4#32)
    (permission : Writable original (state.sp + 0x10#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x10#32).toNat state.s3 }
        { state with pc := 0xc8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨49, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xc8#32 }) (pointer := state.sp)
    (value := state.s3) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 19) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s3)
    (by advance [viewPc, atPC])
  exact stepped

theorem stepc8 (state : Snapshot) (atPC : state.pc = 0xc8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xcc#32, a1 := state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨50, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepcc (state : Snapshot) (atPC : state.pc = 0xcc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xd0#32, a2 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨51, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepd0 (state : Snapshot) (atPC : state.pc = 0xd0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xd4#32, ra := base + 0xd0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨52, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0xd0#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffc84#32`.
theorem stepd4 (state : Snapshot) (atPC : state.pc = 0xd4#32)
    (link : state.ra = base + 0xd0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffc84#32, ra := base + 0xd8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨53, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xbb4#12).signExtend 32 = base + 0xfffffc84#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffc84#32 (by decide)]
  have targetAligned : (base + 0xfffffc84#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffc84#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xbb4#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffc84#32 = 0xfffffffe#32 &&& (state.ra + (0xbb4#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0xd4#32 4#32 0xd8#32 rfl).symm)

theorem stepd8 (state : Snapshot) (atPC : state.pc = 0xd8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0xdc#32 else 0x1ac#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨54, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepdc (state : Snapshot) (atPC : state.pc = 0xdc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xe0#32, a0 := state.sp + 0x4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨55, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepe0 (state : Snapshot) (atPC : state.pc = 0xe0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xe4#32, a4 := state.sp + 0x8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨56, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepe4 (state : Snapshot) (atPC : state.pc = 0xe4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xe8#32, a1 := state.s0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨57, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 8) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepe8 (state : Snapshot) (atPC : state.pc = 0xe8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xec#32, a2 := state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨58, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepec (state : Snapshot) (atPC : state.pc = 0xec#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xf0#32, a3 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨59, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepf0 (state : Snapshot) (atPC : state.pc = 0xf0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xf4#32, ra := base + 0xf0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨60, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0xf0#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffe2c#32`.
theorem stepf4 (state : Snapshot) (atPC : state.pc = 0xf4#32)
    (link : state.ra = base + 0xf0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffe2c#32, ra := base + 0xf8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨61, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xd3c#12).signExtend 32 = base + 0xfffffe2c#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffe2c#32 (by decide)]
  have targetAligned : (base + 0xfffffe2c#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffe2c#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xd3c#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffe2c#32 = 0xfffffffe#32 &&& (state.ra + (0xd3c#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0xf4#32 4#32 0xf8#32 rfl).symm)

theorem stepf8 (state : Snapshot) (atPC : state.pc = 0xf8#32) (value : Word)
    (permission : Readable original (state.s0))
    (contents : WordAt memory (state.s0).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfc#32, a0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨62, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 8) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem stepfc (state : Snapshot) (atPC : state.pc = 0xfc#32) (value : Word)
    (permission : Readable original (state.s0 + 0x4#32))
    (contents : WordAt memory (state.s0 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x100#32, a1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨63, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 8) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step100 (state : Snapshot) (atPC : state.pc = 0x100#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x104#32, a2 := state.s1 - state.s2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨64, by decide⟩ atPC (by decide)
  exact Step.sub fetched decoded (syncRead state (index := 9) (by decide)) (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step104 (state : Snapshot) (atPC : state.pc = 0x104#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x108#32, a0 := state.a2 + state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨65, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step108 (state : Snapshot) (atPC : state.pc = 0x108#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x10c#32, a2 := Step.lessWord state.a0 state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨66, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step10c (state : Snapshot) (atPC : state.pc = 0x10c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x110#32, a0 := state.a0 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨67, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step110 (state : Snapshot) (atPC : state.pc = 0x110#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x114#32, a1 := state.a1 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨68, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step114 (state : Snapshot) (atPC : state.pc = 0x114#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x118#32, a2 := Step.lessWord state.a0 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨69, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step118 (state : Snapshot) (atPC : state.pc = 0x118#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x11c#32, a1 := state.a1 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨70, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step11c (state : Snapshot) (atPC : state.pc = 0x11c#32)
    (permission' : Writable original (state.s0)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0).toNat state.a0 }
        { state with pc := 0x120#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨71, by decide⟩ atPC (by decide)
  have permission : Writable original (state.s0 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x120#32 }) (pointer := state.s0)
    (value := state.a0) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 10) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a0)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step120 (state : Snapshot) (atPC : state.pc = 0x120#32)
    (permission : Writable original (state.s0 + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0 + 0x4#32).toNat state.a1 }
        { state with pc := 0x124#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨72, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x124#32 }) (pointer := state.s0)
    (value := state.a1) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 11) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a1)
    (by advance [viewPc, atPC])
  exact stepped

theorem step148 (state : Snapshot) (atPC : state.pc = 0x148#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s1.toNat ≤ state.a2.toNat then 0x124#32 else 0x14c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨82, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bgeu fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 9) (by decide)) misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step14c (state : Snapshot) (atPC : state.pc = 0x14c#32) (value : Word)
    (permission : Readable original (state.s0))
    (contents : WordAt memory (state.s0).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x150#32, a0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨83, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 8) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step150 (state : Snapshot) (atPC : state.pc = 0x150#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x154#32, a2 := state.a2 ^^^ 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨84, by decide⟩ atPC (by decide)
  exact Step.xori fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step154 (state : Snapshot) (atPC : state.pc = 0x154#32) (value : Word)
    (permission : Readable original (state.s0 + 0x4#32))
    (contents : WordAt memory (state.s0 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x158#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨85, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 8) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step158 (state : Snapshot) (atPC : state.pc = 0x158#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x15c#32, a2 := state.s1 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨86, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 9) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step15c (state : Snapshot) (atPC : state.pc = 0x15c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x160#32, a0 := state.a2 + state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨87, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step160 (state : Snapshot) (atPC : state.pc = 0x160#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x164#32, a2 := Step.lessWord state.a0 state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨88, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step164 (state : Snapshot) (atPC : state.pc = 0x164#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x168#32, a0 := state.a0 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨89, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step168 (state : Snapshot) (atPC : state.pc = 0x168#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x16c#32, a2 := state.a4 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨90, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step16c (state : Snapshot) (atPC : state.pc = 0x16c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x170#32, a4 := Step.lessWord state.a0 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨91, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step170 (state : Snapshot) (atPC : state.pc = 0x170#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x174#32, a2 := state.a2 + state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨92, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step174 (state : Snapshot) (atPC : state.pc = 0x174#32)
    (permission' : Writable original (state.s0)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0).toNat state.a0 }
        { state with pc := 0x178#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨93, by decide⟩ atPC (by decide)
  have permission : Writable original (state.s0 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x178#32 }) (pointer := state.s0)
    (value := state.a0) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 10) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a0)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step178 (state : Snapshot) (atPC : state.pc = 0x178#32)
    (permission : Writable original (state.s0 + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s0 + 0x4#32).toNat state.a2 }
        { state with pc := 0x17c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨94, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x17c#32 }) (pointer := state.s0)
    (value := state.a2) fetched decoded (syncRead state (index := 8) (by decide)) (syncRead state (index := 12) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a2)
    (by advance [viewPc, atPC])
  exact stepped

theorem step17c (state : Snapshot) (atPC : state.pc = 0x17c#32) (value : Word)
    (permission : Readable original (state.a1))
    (contents : WordAt memory (state.a1).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x180#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨95, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 11) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step180 (state : Snapshot) (atPC : state.pc = 0x180#32)
    (permission' : Writable original (state.a3)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.a3).toNat state.s1 }
        { state with pc := 0x184#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨96, by decide⟩ atPC (by decide)
  have permission : Writable original (state.a3 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x184#32 }) (pointer := state.a3)
    (value := state.s1) fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 9) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s1)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step184 (state : Snapshot) (atPC : state.pc = 0x184#32)
    (permission : Writable original (state.sp + 0x8#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x8#32).toNat state.s4 }
        { state with pc := 0x188#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨97, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x188#32 }) (pointer := state.sp)
    (value := state.s4) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 20) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s4)
    (by advance [viewPc, atPC])
  exact stepped

theorem step188 (state : Snapshot) (atPC : state.pc = 0x188#32)
    (permission : Writable original (state.sp + 0xc#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0xc#32).toNat 0#32 }
        { state with pc := 0x18c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨98, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x18c#32 }) (pointer := state.sp)
    (value := 0#32) fetched decoded (syncRead state (index := 2) (by decide)) rfl
    (store machine (state := state) permission (base + state.pc + 4#32) 0#32)
    (by advance [viewPc, atPC])
  exact stepped

theorem step18c (state : Snapshot) (atPC : state.pc = 0x18c#32)
    (permission : Writable original (state.sp + 0x10#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x10#32).toNat state.s3 }
        { state with pc := 0x190#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨99, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x190#32 }) (pointer := state.sp)
    (value := state.s3) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 19) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s3)
    (by advance [viewPc, atPC])
  exact stepped

theorem step190 (state : Snapshot) (atPC : state.pc = 0x190#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x194#32, a0 := state.sp + 0x4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨100, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step194 (state : Snapshot) (atPC : state.pc = 0x194#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x198#32, a4 := state.sp + 0x8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨101, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step198 (state : Snapshot) (atPC : state.pc = 0x198#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x19c#32, a1 := state.s0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨102, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 8) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step19c (state : Snapshot) (atPC : state.pc = 0x19c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a0#32, a3 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨103, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step1a0 (state : Snapshot) (atPC : state.pc = 0x1a0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a4#32, ra := base + 0x1a0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨104, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0x1a0#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at routine offset `0xfffffe2c#32`.
theorem step1a4 (state : Snapshot) (atPC : state.pc = 0x1a4#32)
    (link : state.ra = base + 0x1a0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffe2c#32, ra := base + 0x1a8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨105, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xc8c#12).signExtend 32 = base + 0xfffffe2c#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffe2c#32 (by decide)]
  have targetAligned : (base + 0xfffffe2c#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffe2c#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xc8c#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffe2c#32 = 0xfffffffe#32 &&& (state.ra + (0xc8c#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0x1a4#32 4#32 0x1a8#32 rfl).symm)

theorem step1a8 (state : Snapshot) (atPC : state.pc = 0x1a8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x124#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨106, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.jal fetched decoded misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

end Steps

end Riscfree.RangeInsert.Nonempty.Mutation
