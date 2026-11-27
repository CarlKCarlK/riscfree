import RangeInsert.Nonempty.Predecessor
import RangeInsert.Nonempty.MutationSteps
import RangeInsert.DeleteExtra.Helper

/-! The outer path that extends an existing predecessor before calling
the linked deletion helper. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable CodeAgreesFor)
open Empty (Snapshot)
open InsertTable (instructions)
open Mutation

private def calculated (state : Snapshot) (low high : Word) : Snapshot :=
  let resultLow := DeleteExtra.extendedLow low state.a2 state.s1
  { state with
    pc := 0x174#32
    a0 := resultLow
    a2 := DeleteExtra.extendedHigh low high state.a2 state.s1
    a4 := Step.lessWord resultLow 0x1#32 }

/-- The branch to extension and the two-word cache arithmetic cost eleven
instructions. The stores follow this run. -/
theorem extensionArithmetic {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atTest : state.pc = 0x148#32) (grows : state.a2.toNat < state.s1.toNat)
    (low high : Word) (lowReadable : Readable original state.s0)
    (highReadable : Readable original (state.s0 + 4#32))
    (lowWord : WordAt memory state.s0.toNat low)
    (highWord : WordAt memory (state.s0 + 4#32).toNat high) :
    run 11 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } (calculated state low high)) := by
  refine runStep (step148 machine image _ atTest) ?_
  rw [if_neg (Nat.not_le.mpr grows)]
  refine runStep (step14c machine image _ rfl low lowReadable lowWord) ?_
  refine runStep (step150 machine image _ rfl) ?_
  refine runStep (step154 machine image _ rfl high highReadable highWord) ?_
  refine runStep (step158 machine image _ rfl) ?_
  refine runStep (step15c machine image _ rfl) ?_
  refine runStep (step160 machine image _ rfl) ?_
  refine runStep (step164 machine image _ rfl) ?_
  refine runStep (step168 machine image _ rfl) ?_
  refine runStep (step16c machine image _ rfl) ?_
  exact runStep (step170 machine image _ rfl) rfl

/-- The stores from the completed arithmetic to the helper call, in the
order of the instructions. The temporary header lives in the outer frame. -/
def extensionWrites (state : Snapshot) : List (Word × Word) :=
  [(state.s0, state.a0), (state.s0 + 4#32, state.a2), (state.a3, state.s1),
    (state.sp + 8#32, state.s4), (state.sp + 12#32, 0#32), (state.sp + 16#32, state.s3)]

def writeWords (memory : ByteMemory) : List (Word × Word) → ByteMemory
  | [] => memory
  | (address, value) :: remaining => writeWords (storeWord memory address.toNat value) remaining

theorem writeWordsOutside (memory : ByteMemory) (writes : List (Word × Word)) (byte : Nat)
    (outside : ∀ write ∈ writes, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte) :
    (writeWords memory writes)[byte]? = memory[byte]? := by
  induction writes generalizing memory with
  | nil => rfl
  | cons write rest ih =>
    obtain ⟨address, value⟩ := write
    have head := outside (address, value) (by simp)
    have tail (other : Word × Word) (member : other ∈ rest) :
        byte < other.1.toNat ∨ other.1.toNat + 4 ≤ byte :=
      outside other (List.mem_cons_of_mem _ member)
    exact (ih (storeWord memory address.toNat value) tail).trans
      (storeWordOutside _ _ _ _ head)

structure ExtensionSetup (base : Word) (original : Machine) (memory : ByteMemory)
    (state : Snapshot) (key : Word) : Prop where
  low : Writable original state.s0
  high : Writable original (state.s0 + 4#32)
  stop : Writable original state.a3
  scratchData : Writable original (state.sp + 8#32)
  scratchLength : Writable original (state.sp + 12#32)
  scratchCapacity : Writable original (state.sp + 16#32)
  keyReadable : Readable original state.a1
  keyWord : WordAt memory state.a1.toNat key
  keyApart : ∀ byte, state.a1.toNat ≤ byte → byte < state.a1.toNat + 4 →
    ∀ write ∈ (extensionWrites state).take 2, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte
  codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
    ∀ write ∈ extensionWrites state, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte

def extensionHelperOffset : Word := 0xfffffe2c

def extensionCallState (base : Word) (state : Snapshot) (key : Word) : Snapshot :=
  { state with
    pc := extensionHelperOffset, ra := base + 0x1a8#32,
    a0 := state.sp + 4#32, a1 := state.s0, a2 := key, a3 := state.s1, a4 := state.sp + 8#32 }

/-- Thirteen instructions execute the six stores and call the helper at the
linked offset, with its map-reference and scratch-header arguments in the
outer frame. -/
theorem extensionSetup {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atStores : state.pc = 0x174#32) (key : Word)
    (setup : ExtensionSetup base original memory state key) :
    run 13 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := writeWords memory (extensionWrites state) }
        (extensionCallState base state key)) := by
  let prefixMemory (count : Nat) : ByteMemory := writeWords memory ((extensionWrites state).take count)
  have sameCode (count : Nat) : CodeAgreesFor (4 * instructions.length) base memory (prefixMemory count) := by
    intro byte low high
    exact writeWordsOutside _ _ byte fun write member =>
      setup.codeApart byte low high write (List.mem_of_mem_take member)
  have atPartial (count : Nat) : CodeImage instructions base { original with mem := prefixMemory count } :=
    image.withMemory (prefixMemory count) (sameCode count)
  have keyWord : WordAt (prefixMemory 2) state.a1.toNat key :=
    setup.keyWord.congr fun byte low high =>
      writeWordsOutside _ _ byte (setup.keyApart byte low high)
  refine runStep (step174 machine image _ atStores setup.low) ?_
  refine runStep (step178 machine (atPartial 1) _ rfl setup.high) ?_
  refine runStep (step17c machine (atPartial 2) _ rfl key setup.keyReadable keyWord) ?_
  refine runStep (step180 machine (atPartial 2) _ rfl setup.stop) ?_
  refine runStep (step184 machine (atPartial 3) _ rfl setup.scratchData) ?_
  refine runStep (step188 machine (atPartial 4) _ rfl setup.scratchLength) ?_
  refine runStep (step18c machine (atPartial 5) _ rfl setup.scratchCapacity) ?_
  refine runStep (step190 machine (atPartial 6) _ rfl) ?_
  refine runStep (step194 machine (atPartial 6) _ rfl) ?_
  refine runStep (step198 machine (atPartial 6) _ rfl) ?_
  refine runStep (step19c machine (atPartial 6) _ rfl) ?_
  refine runStep (step1a0 machine (atPartial 6) _ rfl) ?_
  exact runStep (step1a4 machine (atPartial 6) _ rfl rfl) rfl

end Riscfree.RangeInsert.Nonempty
