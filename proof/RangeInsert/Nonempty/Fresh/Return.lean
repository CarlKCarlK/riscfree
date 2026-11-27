import RangeInsert.Nonempty.Extension

/-! After the helper returns, fresh insertion adds the width of the
incoming range to the two-word cached count. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable)
open Empty (Snapshot)
open InsertTable (instructions)
open Mutation

def freshLow (low distance : Word) : Word := (distance + low) + 1#32

def freshHigh (low high distance : Word) : Word :=
  (high + Step.lessWord (distance + low) distance) + Step.lessWord (freshLow low distance) 1#32

/-- The low and high words add the inclusive width, including width
2^32 for the full endpoint domain. -/
theorem freshCacheAddition (low high distance : Word) :
    (freshHigh low high distance ++ freshLow low distance) =
      (high ++ low) + (0#32 ++ distance) + 1#64 := by
  have comparison (left right : Word) : Step.lessWord left right =
      (if left < right then 1#32 else 0#32) := by
    by_cases less : left < right
    · simp only [Step.lessWord, if_pos (BitVec.lt_def.mp less), if_pos less]
      rfl
    · have natural : ¬ left.toNat < right.toNat := fun bound => less (BitVec.lt_def.mpr bound)
      simp only [Step.lessWord, if_neg natural, if_neg less]
      rfl
  simp only [freshHigh, freshLow, comparison, BitVec.add_comm distance low]
  exact addInclusiveWords high low distance

def freshCacheState (state : Snapshot) (low high : Word) : Snapshot :=
  let distance := state.s1 - state.s2
  { state with
    pc := 0x11c#32, a0 := freshLow low distance, a1 := freshHigh low high distance
    a2 := Step.lessWord (freshLow low distance) 1#32 }

set_option maxHeartbeats 1000000 in
theorem freshArithmetic {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atReturn : state.pc = 0xf8#32) (low high : Word)
    (lowReadable : Readable original state.s0) (highReadable : Readable original (state.s0 + 4#32))
    (lowWord : WordAt memory state.s0.toNat low)
    (highWord : WordAt memory (state.s0 + 4#32).toNat high) :
    run 9 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } (freshCacheState state low high)) := by
  refine runStep (stepf8 machine image _ atReturn low lowReadable lowWord) ?_
  refine runStep (stepfc machine image _ rfl high highReadable highWord) ?_
  refine runStep (step100 machine image _ rfl) ?_
  refine runStep (step104 machine image _ rfl) ?_
  refine runStep (step108 machine image _ rfl) ?_
  refine runStep (step10c machine image _ rfl) ?_
  refine runStep (step110 machine image _ rfl) ?_
  refine runStep (step114 machine image _ rfl) ?_
  exact runStep (step118 machine image _ rfl) rfl

theorem freshStores {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atStores : state.pc = 0x11c#32)
    (lowWritable : Writable original state.s0) (highWritable : Writable original (state.s0 + 4#32))
    (apart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
      byte < state.s0.toNat ∨ state.s0.toNat + 4 ≤ byte) :
    run 2 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := (storeWord (storeWord memory state.s0.toNat state.a0)
        (state.s0 + 4#32).toNat state.a1) } { state with pc := 0x124#32 }) := by
  have nextImage := image.withMemory (storeWord memory state.s0.toNat state.a0)
    (fun byte low high => storeWordOutside _ _ _ _ (apart byte low high))
  exact runStep (step11c machine image _ atStores lowWritable)
    (runStep (step120 machine nextImage _ rfl highWritable) rfl)

end Riscfree.RangeInsert.Nonempty
