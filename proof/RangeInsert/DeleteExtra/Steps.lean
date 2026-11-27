import RangeInsert.DeleteTable
import Riscfree.RV32.Compare
import Riscfree.RV32.Logic
import SortedMap.Remove.Instructions

/-! Single Sail steps of the linked `delete_extra` helper. Generated from the
checked table by `generate_delete_extra_steps.py`; each lemma names its
successor snapshot, so an error in the generator cannot weaken a proof. -/

namespace Riscfree.RangeInsert.DeleteExtra

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open DeleteTable (instructions linkedWordsDecode)

set_option maxHeartbeats 2000000

-- The helper's own registers and every register its callees write.
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
  a6 : Word
  a7 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word
  s7 : Word
  s8 : Word
  s9 : Word
  s10 : Word

instance : RegisterView Snapshot where
  tracked := [1, 2, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
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
    | 16 => state.a6
    | 17 => state.a7
    | 18 => state.s2
    | 19 => state.s3
    | 20 => state.s4
    | 21 => state.s5
    | 22 => state.s6
    | 23 => state.s7
    | 24 => state.s8
    | 25 => state.s9
    | 26 => state.s10
    | _ => 0
  distinct := by decide
  nonzero := by decide

@[simp] theorem viewPc (state : Snapshot) : RegisterView.pc state = state.pc := rfl

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

theorem load (machine : MachineState original) {state : Snapshot} {address value : Word}
    (permission : Readable original address) (contents : WordAt memory address.toNat value)
    (next offset : Word) :
    let entered := write_reg_state (sync base { original with mem := memory } state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false entered =
      .ok (.Ok value) entered := by
  obtain ⟨aligned, regions, region, regionsRead, matched, readable⟩ := permission
  have stored : original.regs.get? Register.pma_regions = some regions := readReg_succ.mp regionsRead
  exact (machine.withMemory memory).loadWord (base := base) state next offset address value regions
    region (readReg_succ.mpr stored) matched readable aligned contents

theorem store (machine : MachineState original) {state : Snapshot} {address : Word}
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
    (permission : Writable original (state.sp + 0x10#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x10#32).toNat state.s6 }
        { state with pc := 0x24#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨8, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x24#32 }) (pointer := state.sp)
    (value := state.s6) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 22) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s6)
    (by advance [viewPc, atPC])
  exact stepped

theorem step24 (state : Snapshot) (atPC : state.pc = 0x24#32)
    (permission : Writable original (state.sp + 0xc#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0xc#32).toNat state.s7 }
        { state with pc := 0x28#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨9, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x28#32 }) (pointer := state.sp)
    (value := state.s7) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 23) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s7)
    (by advance [viewPc, atPC])
  exact stepped

theorem step28 (state : Snapshot) (atPC : state.pc = 0x28#32)
    (permission : Writable original (state.sp + 0x8#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x8#32).toNat state.s8 }
        { state with pc := 0x2c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨10, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x2c#32 }) (pointer := state.sp)
    (value := state.s8) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 24) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s8)
    (by advance [viewPc, atPC])
  exact stepped

theorem step2c (state : Snapshot) (atPC : state.pc = 0x2c#32)
    (permission : Writable original (state.sp + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x4#32).toNat state.s9 }
        { state with pc := 0x30#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨11, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x30#32 }) (pointer := state.sp)
    (value := state.s9) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 25) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s9)
    (by advance [viewPc, atPC])
  exact stepped

theorem step30 (state : Snapshot) (atPC : state.pc = 0x30#32)
    (permission' : Writable original (state.sp)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp).toNat state.s10 }
        { state with pc := 0x34#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨12, by decide⟩ atPC (by decide)
  have permission : Writable original (state.sp + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x34#32 }) (pointer := state.sp)
    (value := state.s10) fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 26) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s10)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step34 (state : Snapshot) (atPC : state.pc = 0x34#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x38#32, s1 := state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨13, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step38 (state : Snapshot) (atPC : state.pc = 0x38#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x3c#32, s3 := state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨14, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step3c (state : Snapshot) (atPC : state.pc = 0x3c#32) (value : Word)
    (permission : Readable original (state.a0))
    (contents : WordAt memory (state.a0).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x40#32, s0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨15, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 10) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step40 (state : Snapshot) (atPC : state.pc = 0x40#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x44#32, s2 := state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨16, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step44 (state : Snapshot) (atPC : state.pc = 0x44#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x48#32, a0 := state.s0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨17, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 8) (by decide)) (by decide)
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

-- A call to the callee at helper offset `0xffffff08#32`.
theorem step50 (state : Snapshot) (atPC : state.pc = 0x50#32)
    (link : state.ra = base + 0x4c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xffffff08#32, ra := base + 0x54#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨20, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xebc#12).signExtend 32 = base + 0xffffff08#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xffffff08#32 (by decide)]
  have targetAligned : (base + 0xffffff08#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xffffff08#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xebc#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xffffff08#32 = 0xfffffffe#32 &&& (state.ra + (0xebc#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0x50#32 4#32 0x54#32 rfl).symm)

theorem step54 (state : Snapshot) (atPC : state.pc = 0x54#32) (value : Word)
    (permission : Readable original (state.s0 + 0x4#32))
    (contents : WordAt memory (state.s0 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x58#32, a1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨21, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 8) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step58 (state : Snapshot) (atPC : state.pc = 0x58#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = state.a1 then 0x1cc#32 else 0x5c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨22, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 11) (by decide)) misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step5c (state : Snapshot) (atPC : state.pc = 0x5c#32) (value : Word)
    (permission : Readable original (state.s0))
    (contents : WordAt memory (state.s0).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x60#32, s7 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨23, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 8) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step60 (state : Snapshot) (atPC : state.pc = 0x60#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x64#32, a3 := state.a0 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨24, by decide⟩ atPC (by decide)
  exact Step.slli fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step64 (state : Snapshot) (atPC : state.pc = 0x64#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x68#32, a2 := state.a1 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨25, by decide⟩ atPC (by decide)
  exact Step.slli fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step68 (state : Snapshot) (atPC : state.pc = 0x68#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x6c#32, a0 := state.a0 ^^^ state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨26, by decide⟩ atPC (by decide)
  exact Step.xor fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step6c (state : Snapshot) (atPC : state.pc = 0x6c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x70#32, a1 := state.s3 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨27, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 19) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step70 (state : Snapshot) (atPC : state.pc = 0x70#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x74#32, a0 := Step.lessWord state.a0 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨28, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step74 (state : Snapshot) (atPC : state.pc = 0x74#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x78#32, a3 := state.s7 + state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨29, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 23) (by decide)) (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step78 (state : Snapshot) (atPC : state.pc = 0x78#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x7c#32, a0 := state.a0 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨30, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step7c (state : Snapshot) (atPC : state.pc = 0x7c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x80#32, s6 := state.s3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨31, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 19) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step80 (state : Snapshot) (atPC : state.pc = 0x80#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a1.toNat < state.s3.toNat then 0x88#32 else 0x84#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨32, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bltu fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 19) (by decide)) misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step84 (state : Snapshot) (atPC : state.pc = 0x84#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x88#32, s6 := state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨33, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step88 (state : Snapshot) (atPC : state.pc = 0x88#32) (value : Word)
    (permission : Readable original (state.s2))
    (contents : WordAt memory (state.s2).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x8c#32, a1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨34, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 18) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step8c (state : Snapshot) (atPC : state.pc = 0x8c#32) (value : Word)
    (permission : Readable original (state.s2 + 0x4#32))
    (contents : WordAt memory (state.s2 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x90#32, s8 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨35, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 18) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step90 (state : Snapshot) (atPC : state.pc = 0x90#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x94#32, s7 := state.s7 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨36, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 23) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step94 (state : Snapshot) (atPC : state.pc = 0x94#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x98#32, s4 := state.a0 &&& state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨37, by decide⟩ atPC (by decide)
  exact Step.and fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step98 (state : Snapshot) (atPC : state.pc = 0x98#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x9c#32, a3 := state.a3 + 0x8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨38, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step9c (state : Snapshot) (atPC : state.pc = 0x9c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xa0#32, s5 := state.s3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨39, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 19) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepa0 (state : Snapshot) (atPC : state.pc = 0xa0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xf0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨40, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.jal fetched decoded misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepa4 (state : Snapshot) (atPC : state.pc = 0xa4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xa8#32, a4 := state.a4 - state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨41, by decide⟩ atPC (by decide)
  exact Step.sub fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepa8 (state : Snapshot) (atPC : state.pc = 0xa8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xac#32, a0 := state.a4 ^^^ 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨42, by decide⟩ atPC (by decide)
  exact Step.xori fetched decoded (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepac (state : Snapshot) (atPC : state.pc = 0xac#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xb0#32, s9 := state.a1 + state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨43, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepb0 (state : Snapshot) (atPC : state.pc = 0xb0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xb4#32, a0 := Step.lessWord 0#32 state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨44, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded rfl (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepb4 (state : Snapshot) (atPC : state.pc = 0xb4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xb8#32, a4 := Step.lessWord state.s9 state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨45, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 25) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepb8 (state : Snapshot) (atPC : state.pc = 0xb8#32) (value : Word)
    (permission : Readable original (state.a3))
    (contents : WordAt memory (state.a3).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xbc#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨46, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 13) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem stepbc (state : Snapshot) (atPC : state.pc = 0xbc#32) (value : Word)
    (permission : Readable original (state.s1 + 0x4#32))
    (contents : WordAt memory (state.s1 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xc0#32, a1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨47, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 9) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem stepc0 (state : Snapshot) (atPC : state.pc = 0xc0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xc4#32, a4 := state.s8 + state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨48, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 24) (by decide)) (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepc4 (state : Snapshot) (atPC : state.pc = 0xc4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xc8#32, a0 := state.a0 <<< (3 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨49, by decide⟩ atPC (by decide)
  exact Step.slli fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepc8 (state : Snapshot) (atPC : state.pc = 0xc8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xcc#32, s10 := state.a3 + state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨50, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepcc (state : Snapshot) (atPC : state.pc = 0xcc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xd0#32, s8 := state.a4 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨51, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepd0 (state : Snapshot) (atPC : state.pc = 0xd0#32)
    (permission' : Writable original (state.s2)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s2).toNat state.s9 }
        { state with pc := 0xd4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨52, by decide⟩ atPC (by decide)
  have permission : Writable original (state.s2 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0xd4#32 }) (pointer := state.s2)
    (value := state.s9) fetched decoded (syncRead state (index := 18) (by decide)) (syncRead state (index := 25) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s9)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem stepd4 (state : Snapshot) (atPC : state.pc = 0xd4#32)
    (permission : Writable original (state.s2 + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s2 + 0x4#32).toNat state.s8 }
        { state with pc := 0xd8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨53, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xd8#32 }) (pointer := state.s2)
    (value := state.s8) fetched decoded (syncRead state (index := 18) (by decide)) (syncRead state (index := 24) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s8)
    (by advance [viewPc, atPC])
  exact stepped

theorem stepd8 (state : Snapshot) (atPC : state.pc = 0xd8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xdc#32, a0 := state.s1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨54, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepdc (state : Snapshot) (atPC : state.pc = 0xdc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xe0#32, ra := base + 0xdc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨55, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0xdc#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at helper offset `0xfffffd20#32`.
theorem stepe0 (state : Snapshot) (atPC : state.pc = 0xe0#32)
    (link : state.ra = base + 0xdc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xfffffd20#32, ra := base + 0xe4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨56, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xc44#12).signExtend 32 = base + 0xfffffd20#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xfffffd20#32 (by decide)]
  have targetAligned : (base + 0xfffffd20#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xfffffd20#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xc44#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xfffffd20#32 = 0xfffffffe#32 &&& (state.ra + (0xc44#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0xe0#32 4#32 0xe4#32 rfl).symm)

theorem stepe4 (state : Snapshot) (atPC : state.pc = 0xe4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xe8#32, a1 := state.s9 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨57, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 25) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepe8 (state : Snapshot) (atPC : state.pc = 0xe8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xec#32, a3 := state.s10 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨58, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 26) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem stepec (state : Snapshot) (atPC : state.pc = 0xec#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0xf0#32 else 0x1c4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨59, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepf0 (state : Snapshot) (atPC : state.pc = 0xf0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a3 = state.s7 then 0x11c#32 else 0xf4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨60, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 23) (by decide)) misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepf4 (state : Snapshot) (atPC : state.pc = 0xf4#32) (value : Word)
    (permission : Readable original (state.a3))
    (contents : WordAt memory (state.a3).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xf8#32, a0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨61, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 13) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem stepf8 (state : Snapshot) (atPC : state.pc = 0xf8#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s6.toNat < state.a0.toNat then 0x11c#32 else 0xfc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨62, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bltu fetched decoded (syncRead state (index := 22) (by decide)) (syncRead state (index := 10) (by decide)) misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem stepfc (state : Snapshot) (atPC : state.pc = 0xfc#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x100#32, a2 := state.a3 ^^^ state.s7 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨63, by decide⟩ atPC (by decide)
  exact Step.xor fetched decoded (syncRead state (index := 13) (by decide)) (syncRead state (index := 23) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step100 (state : Snapshot) (atPC : state.pc = 0x100#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x104#32, a4 := Step.lessWord state.a2 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨64, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step104 (state : Snapshot) (atPC : state.pc = 0x104#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x108#32, a4 := state.a4 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨65, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step108 (state : Snapshot) (atPC : state.pc = 0x108#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x10c#32, a4 := state.a4 &&& state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨66, by decide⟩ atPC (by decide)
  exact Step.and fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 13) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step10c (state : Snapshot) (atPC : state.pc = 0x10c#32) (value : Word)
    (permission : Readable original (state.a4 + 0x4#32))
    (contents : WordAt memory (state.a4 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x110#32, a4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨67, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 14) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step110 (state : Snapshot) (atPC : state.pc = 0x110#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a4.toNat < state.s5.toNat then 0xa4#32 else 0x114#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨68, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bltu fetched decoded (syncRead state (index := 14) (by decide)) (syncRead state (index := 21) (by decide)) misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step114 (state : Snapshot) (atPC : state.pc = 0x114#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x118#32, s5 := state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨69, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 14) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step118 (state : Snapshot) (atPC : state.pc = 0x118#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xa4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨70, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.jal fetched decoded misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step11c (state : Snapshot) (atPC : state.pc = 0x11c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s5.toNat ≤ state.s3.toNat then 0x154#32 else 0x120#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨71, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bgeu fetched decoded (syncRead state (index := 19) (by decide)) (syncRead state (index := 21) (by decide)) misaRead
    (by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step120 (state : Snapshot) (atPC : state.pc = 0x120#32) (value : Word)
    (permission : Readable original (state.s2))
    (contents : WordAt memory (state.s2).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x124#32, a0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨72, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 18) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step124 (state : Snapshot) (atPC : state.pc = 0x124#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x128#32, a1 := state.s3 ^^^ 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨73, by decide⟩ atPC (by decide)
  exact Step.xori fetched decoded (syncRead state (index := 19) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step128 (state : Snapshot) (atPC : state.pc = 0x128#32) (value : Word)
    (permission : Readable original (state.s2 + 0x4#32))
    (contents : WordAt memory (state.s2 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x12c#32, a2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨74, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 18) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step12c (state : Snapshot) (atPC : state.pc = 0x12c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x130#32, a1 := state.s5 + state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨75, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 21) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step130 (state : Snapshot) (atPC : state.pc = 0x130#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x134#32, a0 := state.a1 + state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨76, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step134 (state : Snapshot) (atPC : state.pc = 0x134#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x138#32, a1 := Step.lessWord state.a0 state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨77, by decide⟩ atPC (by decide)
  exact Step.sltu fetched decoded (syncRead state (index := 10) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step138 (state : Snapshot) (atPC : state.pc = 0x138#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x13c#32, a0 := state.a0 + 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨78, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step13c (state : Snapshot) (atPC : state.pc = 0x13c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x140#32, a1 := state.a2 + state.a1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨79, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 12) (by decide)) (syncRead state (index := 11) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step140 (state : Snapshot) (atPC : state.pc = 0x140#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x144#32, a2 := Step.lessWord state.a0 0x1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨80, by decide⟩ atPC (by decide)
  exact Step.sltiu fetched decoded (syncRead state (index := 10) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step144 (state : Snapshot) (atPC : state.pc = 0x144#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x148#32, a1 := state.a1 + state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨81, by decide⟩ atPC (by decide)
  exact Step.add fetched decoded (syncRead state (index := 11) (by decide)) (syncRead state (index := 12) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step148 (state : Snapshot) (atPC : state.pc = 0x148#32)
    (permission' : Writable original (state.s2)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s2).toNat state.a0 }
        { state with pc := 0x14c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨82, by decide⟩ atPC (by decide)
  have permission : Writable original (state.s2 + BitVec.signExtend 32 (0 : BitVec 12)) := by
    rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero]
    exact permission'
  have stepped := Step.sw (next := { state with pc := 0x14c#32 }) (pointer := state.s2)
    (value := state.a0) fetched decoded (syncRead state (index := 18) (by decide)) (syncRead state (index := 10) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a0)
    (by advance [viewPc, atPC])
  rw [show BitVec.signExtend 32 (0 : BitVec 12) = (0 : Word) from rfl, addLiteralZero] at stepped
  exact stepped

theorem step14c (state : Snapshot) (atPC : state.pc = 0x14c#32)
    (permission : Writable original (state.s2 + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s2 + 0x4#32).toNat state.a1 }
        { state with pc := 0x150#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨83, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x150#32 }) (pointer := state.s2)
    (value := state.a1) fetched decoded (syncRead state (index := 18) (by decide)) (syncRead state (index := 11) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a1)
    (by advance [viewPc, atPC])
  exact stepped

theorem step150 (state : Snapshot) (atPC : state.pc = 0x150#32)
    (permission : Writable original (state.s4 + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.s4 + 0x4#32).toNat state.s5 }
        { state with pc := 0x154#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨84, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x154#32 }) (pointer := state.s4)
    (value := state.s5) fetched decoded (syncRead state (index := 20) (by decide)) (syncRead state (index := 21) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s5)
    (by advance [viewPc, atPC])
  exact stepped

theorem step154 (state : Snapshot) (atPC : state.pc = 0x154#32) (value : Word)
    (permission : Readable original (state.s1 + 0x4#32))
    (contents : WordAt memory (state.s1 + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x158#32, s2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨85, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 9) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step158 (state : Snapshot) (atPC : state.pc = 0x158#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s2 = 0#32 then 0x184#32 else 0x15c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨86, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.beq fetched decoded (syncRead state (index := 18) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step15c (state : Snapshot) (atPC : state.pc = 0x15c#32) (value : Word)
    (permission : Readable original (state.s1))
    (contents : WordAt memory (state.s1).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x160#32, s1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨87, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 9) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step160 (state : Snapshot) (atPC : state.pc = 0x160#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x164#32, s2 := state.s2 <<< (2 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨88, by decide⟩ atPC (by decide)
  exact Step.slli fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step164 (state : Snapshot) (atPC : state.pc = 0x164#32) (value : Word)
    (permission : Readable original (state.s1))
    (contents : WordAt memory (state.s1).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x168#32, a1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨89, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 9) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step168 (state : Snapshot) (atPC : state.pc = 0x168#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x16c#32, a0 := state.s0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨90, by decide⟩ atPC (by decide)
  exact Step.mv fetched decoded (syncRead state (index := 8) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step16c (state : Snapshot) (atPC : state.pc = 0x16c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x170#32, ra := base + 0x16c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨91, by decide⟩ atPC (by decide)
  refine Step.auipc fetched decoded (by decide) ?_
  rw [viewPc, atPC, SortedMap.Remove.offsetAdd base _ _ 0x16c#32 (by decide)]
  advance [viewPc, atPC]

-- A call to the callee at helper offset `0xffffff3c#32`.
theorem step170 (state : Snapshot) (atPC : state.pc = 0x170#32)
    (link : state.ra = base + 0x16c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xffffff3c#32, ra := base + 0x174#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨92, by decide⟩ atPC (by decide)
  have synced := (machine.withMemory memory).atSync base state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xdd0#12).signExtend 32 = base + 0xffffff3c#32 := by
    rw [link, SortedMap.Remove.offsetAdd base _ _ 0xffffff3c#32 (by decide)]
  have targetAligned : (base + 0xffffff3c#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat image.aligned 0xffffff3c#32 (by decide)
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xdd0#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change base + 0xffffff3c#32 = 0xfffffffe#32 &&& (state.ra + (0xdd0#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [viewPc, atPC]; exact (SortedMap.Remove.offsetAdd base 0x170#32 4#32 0x174#32 rfl).symm)

theorem step174 (state : Snapshot) (atPC : state.pc = 0x174#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.a0 = 0#32 then 0x178#32 else 0x1bc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨93, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step178 (state : Snapshot) (atPC : state.pc = 0x178#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x17c#32, s2 := state.s2 + 0xfffffffc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨94, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 18) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step17c (state : Snapshot) (atPC : state.pc = 0x17c#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x180#32, s1 := state.s1 + 0x4#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨95, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 9) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step180 (state : Snapshot) (atPC : state.pc = 0x180#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := if state.s2 = 0#32 then 0x184#32 else 0x164#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨96, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  exact Step.bne fetched decoded (syncRead state (index := 18) (by decide)) rfl misaRead
    (fun _ => by rw [BitVec.add_assoc, viewPc, atPC]; exact SortedMap.Remove.alignedTarget image.aligned _ (by decide))
    ⟨by simp only [viewPc, atPC]; rfl, fun _ _ => rfl⟩

theorem step184 (state : Snapshot) (atPC : state.pc = 0x184#32) (value : Word)
    (permission : Readable original (state.sp + 0x2c#32))
    (contents : WordAt memory (state.sp + 0x2c#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x188#32, ra := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨97, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step188 (state : Snapshot) (atPC : state.pc = 0x188#32) (value : Word)
    (permission : Readable original (state.sp + 0x28#32))
    (contents : WordAt memory (state.sp + 0x28#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x18c#32, s0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨98, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step18c (state : Snapshot) (atPC : state.pc = 0x18c#32) (value : Word)
    (permission : Readable original (state.sp + 0x24#32))
    (contents : WordAt memory (state.sp + 0x24#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x190#32, s1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨99, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step190 (state : Snapshot) (atPC : state.pc = 0x190#32) (value : Word)
    (permission : Readable original (state.sp + 0x20#32))
    (contents : WordAt memory (state.sp + 0x20#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x194#32, s2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨100, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step194 (state : Snapshot) (atPC : state.pc = 0x194#32) (value : Word)
    (permission : Readable original (state.sp + 0x1c#32))
    (contents : WordAt memory (state.sp + 0x1c#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x198#32, s3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨101, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step198 (state : Snapshot) (atPC : state.pc = 0x198#32) (value : Word)
    (permission : Readable original (state.sp + 0x18#32))
    (contents : WordAt memory (state.sp + 0x18#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x19c#32, s4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨102, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step19c (state : Snapshot) (atPC : state.pc = 0x19c#32) (value : Word)
    (permission : Readable original (state.sp + 0x14#32))
    (contents : WordAt memory (state.sp + 0x14#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a0#32, s5 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨103, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1a0 (state : Snapshot) (atPC : state.pc = 0x1a0#32) (value : Word)
    (permission : Readable original (state.sp + 0x10#32))
    (contents : WordAt memory (state.sp + 0x10#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a4#32, s6 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨104, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1a4 (state : Snapshot) (atPC : state.pc = 0x1a4#32) (value : Word)
    (permission : Readable original (state.sp + 0xc#32))
    (contents : WordAt memory (state.sp + 0xc#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1a8#32, s7 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨105, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1a8 (state : Snapshot) (atPC : state.pc = 0x1a8#32) (value : Word)
    (permission : Readable original (state.sp + 0x8#32))
    (contents : WordAt memory (state.sp + 0x8#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1ac#32, s8 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨106, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1ac (state : Snapshot) (atPC : state.pc = 0x1ac#32) (value : Word)
    (permission : Readable original (state.sp + 0x4#32))
    (contents : WordAt memory (state.sp + 0x4#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1b0#32, s9 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨107, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

theorem step1b0 (state : Snapshot) (atPC : state.pc = 0x1b0#32) (value : Word)
    (permission : Readable original (state.sp))
    (contents : WordAt memory (state.sp).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1b4#32, s10 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨108, by decide⟩ atPC (by decide)
  refine Step.lw fetched decoded (syncRead state (index := 2) (by decide)) ?_ (by decide) (by advance [viewPc, atPC])
  simpa only [show (0 : BitVec 12).signExtend 32 = (0 : Word) from rfl, addLiteralZero] using
    load machine (state := state) permission contents (base + state.pc + 4#32) 0

theorem step1b4 (state : Snapshot) (atPC : state.pc = 0x1b4#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x1b8#32, sp := state.sp + 0x30#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨109, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

theorem step1b8 (state : Snapshot) (atPC : state.pc = 0x1b8#32) (returnAddress : Word)
    (link : state.ra = returnAddress) (returnLow : returnAddress &&& 0xfffffffe = returnAddress)
    (returnNext : returnAddress[1] = false) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨110, by decide⟩ atPC (by decide)
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

end Riscfree.RangeInsert.DeleteExtra
