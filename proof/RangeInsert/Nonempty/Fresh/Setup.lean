import RangeInsert.Nonempty.Extension

/-! The two linked calls which insert a fresh range into the map. Both
initialize the same scratch header before the call. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Writable)
open Empty (Snapshot fetchDecode viewPc)
open InsertTable (instructions)
open Mutation

section
variable {base : Word} {original : Machine} {memory : ByteMemory}
variable (machine : MachineState original)
  (image : CodeImage instructions base { original with mem := memory })
include machine image

theorem branchNoPredecessor (state : Snapshot) (atPC : state.pc = 0x4c#32) (none : state.a0 = 0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xb0#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨19, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.beq fetched decoded (syncRead state (index := 10) (by decide)) rfl misaRead
    (fun _ => ?_) ⟨?_, fun _ _ => rfl⟩
  · rw [BitVec.add_assoc, viewPc, atPC]
    exact SortedMap.Remove.alignedTarget image.aligned _ (by decide)
  · change 0xb0#32 = if state.a0 = 0#32 then state.pc + (0x64#13).signExtend 32 else state.pc + 4#32
    rw [if_pos none, atPC]
    rfl

theorem branchGap (state : Snapshot) (atPC : state.pc = 0x84#32) (gap : state.a4 ≠ 0#32) :
    step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x88#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchDecode machine image state ⟨33, by decide⟩ atPC (by decide)
  obtain ⟨_, misaRead⟩ := ((machine.withMemory memory).atSync base state).misa
  refine Step.beq fetched decoded (syncRead state (index := 14) (by decide)) rfl misaRead
    (fun same => (gap same).elim) ⟨?_, fun _ _ => rfl⟩
  change 0x88#32 = if state.a4 = 0#32 then state.pc + (0xc4#13).signExtend 32 else state.pc + 4#32
  rw [if_neg gap, atPC]
  rfl

end

def insertOffset : Word := 0xfffffc84

def scratchWrites (state : Snapshot) : List (Word × Word) :=
  [(state.sp + 8#32, state.s4), (state.sp + 12#32, 0#32), (state.sp + 16#32, state.s3)]

structure FreshSetup (base : Word) (original : Machine) (state : Snapshot) : Prop where
  data : Writable original (state.sp + 8#32)
  length : Writable original (state.sp + 12#32)
  capacity : Writable original (state.sp + 16#32)
  codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
    ∀ write ∈ scratchWrites state, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte

def insertCalling (base returnOffset : Word) (state : Snapshot) (header : Word) : Snapshot :=
  { state with pc := insertOffset, ra := base + returnOffset, a0 := header, a1 := state.s2, a2 := state.s1 }

theorem freshSetupGap {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atStores : state.pc = 0x88#32) (setup : FreshSetup base original state) :
    run 7 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := writeWords memory (scratchWrites state) }
        (insertCalling base 0xa4#32 state state.a0)) := by
  let partialMemory (count : Nat) := writeWords memory ((scratchWrites state).take count)
  have atPartial (count : Nat) : CodeImage instructions base { original with mem := partialMemory count } :=
    image.withMemory _ fun byte low high =>
      writeWordsOutside _ _ _ fun write member => setup.codeApart byte low high write (List.mem_of_mem_take member)
  refine runStep (step88 machine image _ atStores setup.data) ?_
  refine runStep (step8c machine (atPartial 1) _ rfl setup.length) ?_
  refine runStep (step90 machine (atPartial 2) _ rfl setup.capacity) ?_
  refine runStep (step94 machine (atPartial 3) _ rfl) ?_
  refine runStep (step98 machine (atPartial 3) _ rfl) ?_
  refine runStep (step9c machine (atPartial 3) _ rfl) ?_
  exact runStep (stepa0 machine (atPartial 3) _ rfl rfl) rfl

set_option maxHeartbeats 1000000 in
theorem freshSetupFirst {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atBranch : state.pc = 0xb0#32) (setup : FreshSetup base original state) :
    run 10 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := writeWords memory (scratchWrites state) }
        (insertCalling base 0xd8#32 state state.s5)) := by
  let partialMemory (count : Nat) := writeWords memory ((scratchWrites state).take count)
  have atPartial (count : Nat) : CodeImage instructions base { original with mem := partialMemory count } :=
    image.withMemory _ fun byte low high =>
      writeWordsOutside _ _ _ fun write member => setup.codeApart byte low high write (List.mem_of_mem_take member)
  let ready : Snapshot := { state with pc := 0xb8#32, a0 := state.s5, a1 := 0#32 }
  let stores : Snapshot := { ready with pc := 0xbc#32 }
  have branch : step (sync base { original with mem := memory } ready) =
      some (sync base { original with mem := memory } stores) := by
    have stepped := stepb8 machine image ready rfl
    have target : (if ready.a1 = 0#32 then 0xbc#32 else 0x70#32) = stores.pc :=
      if_pos (rfl : ready.a1 = 0#32)
    rw [target] at stepped
    exact stepped
  have start : run 3 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } stores) := by
    exact runStep (stepb0 machine image state atBranch)
      (runStep (stepb4 machine image _ rfl) (runStep branch rfl))
  rw [show 10 = 3 + 7 by decide, runAdd, start, Option.bind_some]
  refine runStep (stepbc machine image _ rfl setup.data) ?_
  refine runStep (stepc0 machine (atPartial 1) _ rfl setup.length) ?_
  refine runStep (stepc4 machine (atPartial 2) _ rfl setup.capacity) ?_
  refine runStep (stepc8 machine (atPartial 3) _ rfl) ?_
  refine runStep (stepcc machine (atPartial 3) _ rfl) ?_
  refine runStep (stepd0 machine (atPartial 3) _ rfl) ?_
  exact runStep (stepd4 machine (atPartial 3) _ rfl rfl) rfl

def freshHelperCalling (base : Word) (state : Snapshot) : Snapshot :=
  { state with
    pc := extensionHelperOffset, ra := base + 0xf8#32
    a0 := state.sp + 4#32, a1 := state.s0, a2 := state.s2, a3 := state.s1, a4 := state.sp + 8#32 }

theorem freshHelperSetup {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atSetup : state.pc = 0xdc#32) :
    run 7 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } (freshHelperCalling base state)) := by
  refine runStep (stepdc machine image _ atSetup) ?_
  refine runStep (stepe0 machine image _ rfl) ?_
  refine runStep (stepe4 machine image _ rfl) ?_
  refine runStep (stepe8 machine image _ rfl) ?_
  refine runStep (stepec machine image _ rfl) ?_
  refine runStep (stepf0 machine image _ rfl) ?_
  exact runStep (stepf4 machine image _ rfl rfl) rfl

theorem freshAfterInsert {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atReturn : state.pc = 0xa4#32 ∨ state.pc = 0xd8#32)
    (success : state.a0 = 0#32) :
    run 8 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } (freshHelperCalling base state)) := by
  have entered : step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xdc#32 }) := by
    rcases atReturn with gap | first
    · simpa only [if_pos success] using stepa4 machine image state gap
    · simpa only [if_pos success] using stepd8 machine image state first
  exact runStep entered (freshHelperSetup machine image _ rfl)

end Riscfree.RangeInsert.Nonempty
