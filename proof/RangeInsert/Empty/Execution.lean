import RangeInsert.InsertTable
import SortedMap.Remove.Instructions

/-! The range insertion entry point's stack frame and the run for an
empty inclusive range. The prologue and epilogue are shared by the
returning paths. -/

namespace Riscfree.RangeInsert.Empty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions linkedWordsDecode)

set_option maxHeartbeats 2000000

structure Snapshot where
  pc : Word := 0
  ra : Word
  sp : Word
  s0 : Word
  s1 : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word
  a5 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word

instance : RegisterView Snapshot where
  tracked := [1, 2, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21]
  pc state := state.pc
  value state index := match index.val with
    | 1 => state.ra
    | 2 => state.sp
    | 8 => state.s0
    | 9 => state.s1
    | 10 => state.a0
    | 11 => state.a1
    | 12 => state.a2
    | 13 => state.a3
    | 14 => state.a4
    | 15 => state.a5
    | 18 => state.s2
    | 19 => state.s3
    | 20 => state.s4
    | 21 => state.s5
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


private theorem step00 (state : Snapshot) (atPC : state.pc = 0x0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x4#32, sp := state.sp + 0xffffffd0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨0, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem step04 (state : Snapshot) (atPC : state.pc = 0x4#32)
    (permission : Writable original (state.sp + 0x2c#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x2c#32).toNat state.ra }
        { state with pc := 0x8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨1, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x8#32 }) (pointer := state.sp)
    (value := state.ra) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 1) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.ra)
    (by advance [viewPc, atPC])
  exact stepped

private theorem step08 (state : Snapshot) (atPC : state.pc = 0x8#32)
    (permission : Writable original (state.sp + 0x28#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x28#32).toNat state.s0 }
        { state with pc := 0xc#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨2, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0xc#32 }) (pointer := state.sp)
    (value := state.s0) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 8) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s0)
    (by advance [viewPc, atPC])
  exact stepped

private theorem step0c (state : Snapshot) (atPC : state.pc = 0xc#32)
    (permission : Writable original (state.sp + 0x24#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x24#32).toNat state.s1 }
        { state with pc := 0x10#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨3, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x10#32 }) (pointer := state.sp)
    (value := state.s1) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 9) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s1)
    (by advance [viewPc, atPC])
  exact stepped

private theorem step10 (state : Snapshot) (atPC : state.pc = 0x10#32)
    (permission : Writable original (state.sp + 0x20#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x20#32).toNat state.s2 }
        { state with pc := 0x14#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨4, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x14#32 }) (pointer := state.sp)
    (value := state.s2) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 18) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s2)
    (by advance [viewPc, atPC])
  exact stepped

private theorem step14 (state : Snapshot) (atPC : state.pc = 0x14#32)
    (permission : Writable original (state.sp + 0x1c#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x1c#32).toNat state.s3 }
        { state with pc := 0x18#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨5, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x18#32 }) (pointer := state.sp)
    (value := state.s3) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 19) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s3)
    (by advance [viewPc, atPC])
  exact stepped

private theorem step18 (state : Snapshot) (atPC : state.pc = 0x18#32)
    (permission : Writable original (state.sp + 0x18#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x18#32).toNat state.s4 }
        { state with pc := 0x1c#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨6, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x1c#32 }) (pointer := state.sp)
    (value := state.s4) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 20) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s4)
    (by advance [viewPc, atPC])
  exact stepped

private theorem step1c (state : Snapshot) (atPC : state.pc = 0x1c#32)
    (permission : Writable original (state.sp + 0x14#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x14#32).toNat state.s5 }
        { state with pc := 0x20#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨7, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x20#32 }) (pointer := state.sp)
    (value := state.s5) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 21) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.s5)
    (by advance [viewPc, atPC])
  exact stepped

private theorem step20 (state : Snapshot) (atPC : state.pc = 0x20#32)
    (permission : Writable original (state.sp + 0x4#32)) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := storeWord memory (state.sp + 0x4#32).toNat state.a0 }
        { state with pc := 0x24#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨8, by decide⟩ atPC (by decide)
  have stepped := Step.sw (next := { state with pc := 0x24#32 }) (pointer := state.sp)
    (value := state.a0) fetched decoded (syncRead state (index := 2) (by decide))
    (syncRead state (index := 10) (by decide))
    (store machine (state := state) permission (base + state.pc + 4#32) state.a0)
    (by advance [viewPc, atPC])
  exact stepped

private theorem branchEmpty (state : Snapshot) (atPC : state.pc = 0x24#32)
    (empty : state.a3.toNat < state.a2.toNat) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x124#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨9, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.bltu fetched decoded (syncRead state (index := 13) (by decide))
    (syncRead state (index := 12) (by decide)) misaRead ?_ ⟨?_, fun _ _ => rfl⟩
  · rw [BitVec.add_assoc, viewPc, atPC]
    exact SortedMap.Remove.alignedTarget image.aligned _ (by decide)
  · change 0x124#32 = if state.a3.toNat < state.a2.toNat then
        state.pc + (0x100#13).signExtend 32 else state.pc + 4#32
    rw [if_pos empty, atPC]
    rfl

private theorem step124 (state : Snapshot) (atPC : state.pc = 0x124#32) (value : Word)
    (permission : Readable original (state.sp + 0x2c#32))
    (contents : WordAt memory (state.sp + 0x2c#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x128#32, ra := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨73, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

private theorem step128 (state : Snapshot) (atPC : state.pc = 0x128#32) (value : Word)
    (permission : Readable original (state.sp + 0x28#32))
    (contents : WordAt memory (state.sp + 0x28#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x12c#32, s0 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨74, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

private theorem step12c (state : Snapshot) (atPC : state.pc = 0x12c#32) (value : Word)
    (permission : Readable original (state.sp + 0x24#32))
    (contents : WordAt memory (state.sp + 0x24#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x130#32, s1 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨75, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

private theorem step130 (state : Snapshot) (atPC : state.pc = 0x130#32) (value : Word)
    (permission : Readable original (state.sp + 0x20#32))
    (contents : WordAt memory (state.sp + 0x20#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x134#32, s2 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨76, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

private theorem step134 (state : Snapshot) (atPC : state.pc = 0x134#32) (value : Word)
    (permission : Readable original (state.sp + 0x1c#32))
    (contents : WordAt memory (state.sp + 0x1c#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x138#32, s3 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨77, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

private theorem step138 (state : Snapshot) (atPC : state.pc = 0x138#32) (value : Word)
    (permission : Readable original (state.sp + 0x18#32))
    (contents : WordAt memory (state.sp + 0x18#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x13c#32, s4 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨78, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

private theorem step13c (state : Snapshot) (atPC : state.pc = 0x13c#32) (value : Word)
    (permission : Readable original (state.sp + 0x14#32))
    (contents : WordAt memory (state.sp + 0x14#32).toNat value) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x140#32, s5 := value }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨79, by decide⟩ atPC (by decide)
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide))
    (load machine permission contents _ _) (by decide) (by advance [viewPc, atPC])

private theorem step140 (state : Snapshot) (atPC : state.pc = 0x140#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x144#32, sp := state.sp + 0x30#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨80, by decide⟩ atPC (by decide)
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem step144 (state : Snapshot) (atPC : state.pc = 0x144#32) (returnAddress : Word)
    (link : state.ra = returnAddress) (returnLow : returnAddress &&& 0xfffffffe = returnAddress)
    (returnNext : returnAddress[1] = false) :
    step (sync base { original with mem := memory } state) = some (sync base { original with mem := memory } { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨81, by decide⟩ atPC (by decide)
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

def frameBase (sp : Word) : Word := sp - 48

def OutsideFrame (sp : Word) (byte : Nat) : Prop :=
  byte < sp.toNat - 48 ∨ sp.toNat ≤ byte

structure Frame (base returnAddress : Word) (original : Machine) (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  link : initial.ra = returnAddress
  mode : MachineMode original returnAddress
  code : CodeImage instructions base original
  frameFits : 48 ≤ initial.sp.toNat
  codeOutside : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
    OutsideFrame initial.sp byte
  readable : ∀ offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word),
    Readable original (frameBase initial.sp + offset)
  writable : ∀ offset ∈ ([44, 40, 36, 32, 28, 24, 20, 4] : List Word),
    Writable original (frameBase initial.sp + offset)

structure Premises (base returnAddress : Word) (original : Machine) (initial : Snapshot) : Prop
    extends Frame base returnAddress original initial where
  empty : initial.a3.toNat < initial.a2.toNat

theorem frameAddress {sp : Word} (fits : 48 ≤ sp.toNat) (offset : Word)
    (small : offset.toNat ≤ 44) :
    (frameBase sp + offset).toNat = sp.toNat - 48 + offset.toNat := by
  have below := sp.isLt
  have noWrap : 48#32 ≤ sp := BitVec.le_def.mpr fits
  change ((sp - 48#32) + offset).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le noWrap]
  change (sp.toNat - 48 + offset.toNat) % 2 ^ 32 = _
  exact Nat.mod_eq_of_lt (by omega)

private def push (sp offset value : Word) (memory : ByteMemory) : ByteMemory :=
  storeWord memory (frameBase sp + offset).toNat value

def pushed (memory : ByteMemory) (state : Snapshot) : ByteMemory :=
  memory |> push state.sp 44 state.ra |> push state.sp 40 state.s0
    |> push state.sp 36 state.s1 |> push state.sp 32 state.s2 |> push state.sp 28 state.s3
    |> push state.sp 24 state.s4 |> push state.sp 20 state.s5 |> push state.sp 4 state.a0

private theorem pushOutside {sp : Word} (memory : ByteMemory) (offset value : Word)
    (fits : 48 ≤ sp.toNat) (small : offset.toNat ≤ 44) (byte : Nat)
    (outside : OutsideFrame sp byte) :
    (push sp offset value memory)[byte]? = memory[byte]? := by
  apply storeWordOutside
  rw [frameAddress fits offset small]
  unfold OutsideFrame at outside
  omega

private theorem pushOther {sp offset other value written : Word} {memory : ByteMemory}
    (fits : 48 ≤ sp.toNat) (small : offset.toNat ≤ 44) (otherSmall : other.toNat ≤ 44)
    (apart : other.toNat + 4 ≤ offset.toNat)
    (word : WordAt memory (frameBase sp + offset).toNat value) :
    WordAt (push sp other written memory) (frameBase sp + offset).toNat value := by
  apply word.storeOther
  rw [frameAddress fits offset small, frameAddress fits other otherSmall]
  omega

private theorem savedWords (memory : ByteMemory) (state : Snapshot) (fits : 48 ≤ state.sp.toNat) :
    WordAt (pushed memory state) (frameBase state.sp + 44).toNat state.ra ∧
    WordAt (pushed memory state) (frameBase state.sp + 40).toNat state.s0 ∧
    WordAt (pushed memory state) (frameBase state.sp + 36).toNat state.s1 ∧
    WordAt (pushed memory state) (frameBase state.sp + 32).toNat state.s2 ∧
    WordAt (pushed memory state) (frameBase state.sp + 28).toNat state.s3 ∧
    WordAt (pushed memory state) (frameBase state.sp + 24).toNat state.s4 ∧
    WordAt (pushed memory state) (frameBase state.sp + 20).toNat state.s5 := by
  unfold pushed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    repeat refine pushOther fits (by decide) (by decide) (by decide) ?_
    exact wordAtStore _ _ _

theorem pushedOutside (memory : ByteMemory) (initial : Snapshot)
    (fits : 48 ≤ initial.sp.toNat) (byte : Nat) (outside : OutsideFrame initial.sp byte) :
    (pushed memory initial)[byte]? = memory[byte]? := by
  unfold pushed
  iterate 8 rw [pushOutside _ _ _ fits (by decide) _ outside]

theorem Frame.imageAt {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (agrees : ∀ byte, OutsideFrame initial.sp byte → memory[byte]? = original.mem[byte]?) :
    CodeImage instructions base { original with mem := memory } :=
  frame.code.withMemory memory fun byte low high =>
    agrees byte (frame.codeOutside byte low high)

theorem Frame.pushedImage {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) :
    CodeImage instructions base { original with mem := pushed original.mem initial } :=
  frame.imageAt _ (pushedOutside _ _ frame.frameFits)

theorem Frame.prologue {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) :
    run 9 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := pushed original.mem initial }
        { initial with pc := 0x24, sp := frameBase initial.sp }) := by
  let machine := frame.mode.toMachineState
  have image := frame.imageAt
  have initialImage := image original.mem (fun _ _ => rfl)
  have lowered : initial.sp + 0xffffffd0#32 = frameBase initial.sp := by
    rw [frameBase, BitVec.sub_eq_add_neg]
    rfl
  refine runStep (step00 machine initialImage _ rfl) ?_
  simp only [lowered]
  refine runStep (step04 machine initialImage _ rfl (frame.writable _ (by decide))) ?_
  refine runStep (step08 machine (image _ ?_) _ rfl (frame.writable _ (by decide))) ?_
  · intro byte outside
    exact pushOutside _ _ _ frame.frameFits (by decide) _ outside
  refine runStep (step0c machine (image _ ?_) _ rfl (frame.writable _ (by decide))) ?_
  · intro byte outside
    change (push initial.sp 40 initial.s0 (push initial.sp 44 initial.ra original.mem))[byte]? = _
    iterate 2 rw [pushOutside _ _ _ frame.frameFits (by decide) _ outside]
  refine runStep (step10 machine (image _ ?_) _ rfl (frame.writable _ (by decide))) ?_
  · intro byte outside
    change (push initial.sp 36 initial.s1 (push initial.sp 40 initial.s0
      (push initial.sp 44 initial.ra original.mem)))[byte]? = _
    iterate 3 rw [pushOutside _ _ _ frame.frameFits (by decide) _ outside]
  refine runStep (step14 machine (image _ ?_) _ rfl (frame.writable _ (by decide))) ?_
  · intro byte outside
    change (push initial.sp 32 initial.s2 (push initial.sp 36 initial.s1
      (push initial.sp 40 initial.s0 (push initial.sp 44 initial.ra original.mem))))[byte]? = _
    iterate 4 rw [pushOutside _ _ _ frame.frameFits (by decide) _ outside]
  refine runStep (step18 machine (image _ ?_) _ rfl (frame.writable _ (by decide))) ?_
  · intro byte outside
    change (push initial.sp 28 initial.s3 (push initial.sp 32 initial.s2
      (push initial.sp 36 initial.s1 (push initial.sp 40 initial.s0
        (push initial.sp 44 initial.ra original.mem)))))[byte]? = _
    iterate 5 rw [pushOutside _ _ _ frame.frameFits (by decide) _ outside]
  refine runStep (step1c machine (image _ ?_) _ rfl (frame.writable _ (by decide))) ?_
  · intro byte outside
    change (push initial.sp 24 initial.s4 (push initial.sp 28 initial.s3
      (push initial.sp 32 initial.s2 (push initial.sp 36 initial.s1
        (push initial.sp 40 initial.s0 (push initial.sp 44 initial.ra original.mem))))))[byte]? = _
    iterate 6 rw [pushOutside _ _ _ frame.frameFits (by decide) _ outside]
  refine runStep (step20 machine (image _ ?_) _ rfl (frame.writable _ (by decide))) ?_
  · intro byte outside
    change (push initial.sp 20 initial.s5 (push initial.sp 24 initial.s4
      (push initial.sp 28 initial.s3 (push initial.sp 32 initial.s2
        (push initial.sp 36 initial.s1 (push initial.sp 40 initial.s0
          (push initial.sp 44 initial.ra original.mem)))))))[byte]? = _
    iterate 7 rw [pushOutside _ _ _ frame.frameFits (by decide) _ outside]
  rfl

def restore (initial state : Snapshot) (pc : Word) : Snapshot :=
  { state with
    pc := pc, sp := initial.sp, ra := initial.ra,
    s0 := initial.s0, s1 := initial.s1, s2 := initial.s2, s3 := initial.s3,
    s4 := initial.s4, s5 := initial.s5 }

theorem Frame.epilogueFrom {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) {background : Machine}
    (machine : MachineState background) (image : CodeImage instructions base background)
    (readable : ∀ offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word),
      Readable background (frameBase initial.sp + offset))
    (saved : ∀ (offset : Word) (value : Word),
      offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word) →
      WordAt (pushed original.mem initial) (frameBase initial.sp + offset).toNat value →
      WordAt background.mem (frameBase initial.sp + offset).toNat value)
    (state : Snapshot)
    (atExit : state.pc = 0x124#32) (lowered : state.sp = frameBase initial.sp) :
    run 9 (sync base background state) =
      some (sync base background
        (restore initial state (returnAddress - base))) := by
  obtain ⟨ra, s0, s1, s2, s3, s4, s5⟩ := savedWords original.mem initial frame.frameFits
  refine runStep (step124 machine image _ atExit _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 44 _ (by decide) ra)) ?_
  refine runStep (step128 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 40 _ (by decide) s0)) ?_
  refine runStep (step12c machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 36 _ (by decide) s1)) ?_
  refine runStep (step130 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 32 _ (by decide) s2)) ?_
  refine runStep (step134 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 28 _ (by decide) s3)) ?_
  refine runStep (step138 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 24 _ (by decide) s4)) ?_
  refine runStep (step13c machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 20 _ (by decide) s5)) ?_
  refine runStep (step140 machine image _ rfl) ?_
  refine runStep (step144 machine image _ rfl returnAddress frame.link
    frame.mode.returnLow frame.mode.returnNext) ?_
  have restored : frameBase initial.sp + 48#32 = initial.sp := BitVec.sub_add_cancel _ _
  simp only [lowered, restored]
  rfl

theorem Frame.epilogue {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (state : Snapshot)
    (atExit : state.pc = 0x124#32) (lowered : state.sp = frameBase initial.sp) :
    run 9 (sync base { original with mem := pushed original.mem initial } state) =
      some (sync base { original with mem := pushed original.mem initial }
        (restore initial state (returnAddress - base))) :=
  frame.epilogueFrom (frame.mode.toMachineState.withMemory (pushed original.mem initial))
    frame.pushedImage (fun offset member => by
      obtain ⟨aligned, regions, region, read, mapped, permission⟩ := frame.readable offset member
      have stored : original.regs.get? Register.pma_regions = some regions := readReg_succ.mp read
      exact ⟨aligned, regions, region, readReg_succ.mpr stored, mapped, permission⟩)
    (fun _ _ _ contents => contents) state atExit lowered

theorem runEmpty {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (premises : Premises base returnAddress original initial) :
    run 19 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := pushed original.mem initial }
        { initial with pc := returnAddress - base }) := by
  rw [show 19 = 9 + (1 + 9) by decide, runAdd, premises.toFrame.prologue, Option.bind_some]
  refine runStep (branchEmpty premises.mode.toMachineState premises.toFrame.pushedImage _ rfl
    premises.empty) ?_
  exact premises.toFrame.epilogue _ rfl rfl

end Riscfree.RangeInsert.Empty
