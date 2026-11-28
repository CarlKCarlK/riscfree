import RangeInsert.Bounded.HelperLoop

/-! The `delete_extra` scan loop's two exits and the extension of the selected
range. The loop leaves at `+0xf0` when the cursor reaches the end of the map,
or at `+0xf8` when the next successor starts beyond the limit. From `+0x11c`,
a running maximum beyond `stop` is added to the two-word cache and stored as
the selected range's end. -/

namespace Riscfree.RangeInsert.Bounded.HelperFinish

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable)
open Helper
open HelperLoop (Registers)
open DeleteExtra (Call distance extendedLow extendedHigh)

set_option maxHeartbeats 4000000

-- The memory after the extension's three stores.
def extended (memory : ByteMemory) (state : Snapshot) (low high : Word) : ByteMemory :=
  storeWord (storeWord (storeWord memory state.s2.toNat (extendedLow low state.s3 state.s5))
    (state.s2 + 0x4#32).toNat (extendedHigh low high state.s3 state.s5))
    (state.s4 + 0x4#32).toNat state.s5

/-- The cursor reached the end of the map: one instruction to `+0x11c`. -/
theorem exitAtEnd {base : Word} {original : Machine} {memory : ByteMemory}
    {initial : Snapshot} {call : Call} {t : Nat}
    (machine : MachineState original)
    (image : CodeImage DeleteTable.instructions base { original with mem := memory })
    (state : Snapshot) (registers : Registers initial call t state)
    (atEnd : call.position + 1 + t = call.length.toNat) :
    run 1 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x158#32 }) := by
  have same : state.a0 = state.s7 := by rw [registers.cursor, registers.last, atEnd]
  refine runStep (stepa0 machine image _ registers.pc) ?_
  rw [if_pos same]
  rfl

/-- The next successor starts beyond the limit: three instructions to
`+0x11c`. -/
theorem exitAtGap {base : Word} {original : Machine} {memory : ByteMemory}
    {initial : Snapshot} {call : Call} {t : Nat}
    (machine : MachineState original)
    (image : CodeImage DeleteTable.instructions base { original with mem := memory })
    (state : Snapshot) (registers : Registers initial call t state)
    (different : state.a0 ≠ state.s7) (key : Word) (keyReadable : Readable original state.a0)
    (keyWord : WordAt memory state.a0.toNat key) (gap : call.limit.toNat < key.toNat) :
    run 3 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x158#32, a1 := key }) := by
  refine runStep (stepa0 machine image _ registers.pc) ?_
  rw [if_neg different]
  refine runStep (stepa4 machine image _ rfl key keyReadable keyWord) ?_
  refine runStep (stepa8 machine image _ rfl) ?_
  rw [if_pos (by rw [registers.limit]; exact gap)]
  rfl

/-- No extension: one instruction from `+0x11c` to `+0x154`. -/
theorem keepEnd {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage DeleteTable.instructions base { original with mem := memory })
    (state : Snapshot) (atTest : state.pc = 0x158#32) (within : state.s5.toNat ≤ state.s3.toNat) :
    run 1 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0x190#32 }) := by
  refine runStep (step158 machine image _ atTest) ?_
  rw [if_pos within]
  rfl

/-- The extension: 14 instructions from `+0x11c` to `+0x154` that add the
growth beyond `stop` to the cache and store the new end. -/
theorem extendEnd {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (imageOf : ∀ other : ByteMemory, (∀ byte, base.toNat ≤ byte →
      byte < base.toNat + 4 * DeleteTable.instructions.length → other[byte]? = memory[byte]?) →
      CodeImage DeleteTable.instructions base { original with mem := other })
    (state : Snapshot) (atTest : state.pc = 0x158#32) (beyond : ¬ state.s5.toNat ≤ state.s3.toNat)
    (low high : Word) (lowReadable : Readable original state.s2)
    (lowWord : WordAt memory state.s2.toNat low)
    (highReadable : Readable original (state.s2 + 0x4#32))
    (highWord : WordAt memory (state.s2 + 0x4#32).toNat high)
    (lowWritable : Writable original state.s2) (highWritable : Writable original (state.s2 + 0x4#32))
    (endWritable : Writable original (state.s4 + 0x4#32))
    (codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * DeleteTable.instructions.length →
      (byte < state.s2.toNat ∨ state.s2.toNat + 4 ≤ byte) ∧
      (byte < (state.s2 + 0x4#32).toNat ∨ (state.s2 + 0x4#32).toNat + 4 ≤ byte) ∧
      (byte < (state.s4 + 0x4#32).toNat ∨ (state.s4 + 0x4#32).toNat + 4 ≤ byte)) :
    run 14 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := extended memory state low high }
        { state with
          pc := 0x190#32, a0 := extendedLow low state.s3 state.s5,
          a1 := extendedHigh low high state.s3 state.s5,
          a2 := Step.lessWord (extendedLow low state.s3 state.s5) 0x1#32 }) := by
  have image := imageOf memory fun _ _ _ => rfl
  let first := storeWord memory state.s2.toNat (extendedLow low state.s3 state.s5)
  let second := storeWord first (state.s2 + 0x4#32).toNat (extendedHigh low high state.s3 state.s5)
  have image1 := imageOf first fun byte low high =>
    storeWordOutside _ _ _ _ (codeApart byte low high).1
  have image2 := imageOf second fun byte low high => by
    change (storeWord first _ _)[byte]? = _
    rw [storeWordOutside _ _ _ _ (codeApart byte low high).2.1]
    exact storeWordOutside _ _ _ _ (codeApart byte low high).1
  refine runStep (step158 machine image _ atTest) ?_
  rw [if_neg beyond]
  refine runStep (step15c machine image _ rfl low lowReadable lowWord) ?_
  refine runStep (step160 machine image _ rfl) ?_
  refine runStep (step164 machine image _ rfl high highReadable highWord) ?_
  refine runStep (step168 machine image _ rfl) ?_
  refine runStep (step16c machine image _ rfl) ?_
  refine runStep (step170 machine image _ rfl) ?_
  refine runStep (step174 machine image _ rfl) ?_
  refine runStep (step178 machine image _ rfl) ?_
  refine runStep (step17c machine image _ rfl) ?_
  refine runStep (step180 machine image _ rfl) ?_
  refine runStep (step184 machine image _ rfl lowWritable) ?_
  refine runStep (step188 machine image1 _ rfl highWritable) ?_
  exact runStep (step18c machine image2 _ rfl endWritable) rfl

end Riscfree.RangeInsert.Bounded.HelperFinish
