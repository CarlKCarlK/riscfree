import RangeInsert.DeleteExtra.Steps

/-! The `delete_extra` helper's 48-byte stack frame: its 13-instruction
prologue saves `ra` and `s0`–`s10`, and its 14-instruction epilogue restores
them and returns. -/

namespace Riscfree.RangeInsert.DeleteExtra

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open DeleteTable (instructions)

set_option maxHeartbeats 2000000

def frameBase (sp : Word) : Word := sp - 48

def OutsideFrame (sp : Word) (byte : Nat) : Prop :=
  byte < sp.toNat - 48 ∨ sp.toNat ≤ byte

-- The saved registers' frame offsets, in prologue order.
def savedOffsets : List Word := [44, 40, 36, 32, 28, 24, 20, 16, 12, 8, 4, 0]

structure Frame (base returnAddress : Word) (original : Machine) (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  link : initial.ra = returnAddress
  mode : MachineMode original returnAddress
  code : CodeImage instructions base original
  frameFits : 48 ≤ initial.sp.toNat
  codeOutside : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
    OutsideFrame initial.sp byte
  readable : ∀ offset ∈ savedOffsets, Readable original (frameBase initial.sp + offset)
  writable : ∀ offset ∈ savedOffsets, Writable original (frameBase initial.sp + offset)

theorem frameAddress {sp : Word} (fits : 48 ≤ sp.toNat) (offset : Word)
    (small : offset.toNat ≤ 44) :
    (frameBase sp + offset).toNat = sp.toNat - 48 + offset.toNat := by
  have below := sp.isLt
  have noWrap : 48#32 ≤ sp := BitVec.le_def.mpr fits
  change ((sp - 48#32) + offset).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_sub_of_le noWrap]
  change (sp.toNat - 48 + offset.toNat) % 2 ^ 32 = _
  exact Nat.mod_eq_of_lt (by omega)

/-- Each saved register is in its frame slot. -/
structure Saved (memory : ByteMemory) (initial : Snapshot) : Prop where
  ra : WordAt memory (frameBase initial.sp + 44).toNat initial.ra
  s0 : WordAt memory (frameBase initial.sp + 40).toNat initial.s0
  s1 : WordAt memory (frameBase initial.sp + 36).toNat initial.s1
  s2 : WordAt memory (frameBase initial.sp + 32).toNat initial.s2
  s3 : WordAt memory (frameBase initial.sp + 28).toNat initial.s3
  s4 : WordAt memory (frameBase initial.sp + 24).toNat initial.s4
  s5 : WordAt memory (frameBase initial.sp + 20).toNat initial.s5
  s6 : WordAt memory (frameBase initial.sp + 16).toNat initial.s6
  s7 : WordAt memory (frameBase initial.sp + 12).toNat initial.s7
  s8 : WordAt memory (frameBase initial.sp + 8).toNat initial.s8
  s9 : WordAt memory (frameBase initial.sp + 4).toNat initial.s9
  s10 : WordAt memory (frameBase initial.sp).toNat initial.s10

theorem storeOutside {sp : Word} (fits : 48 ≤ sp.toNat) {offset : Word}
    (small : offset.toNat ≤ 44) {byte : Nat} (outside : OutsideFrame sp byte)
    (memory : ByteMemory) (value : Word) :
    (storeWord memory (frameBase sp + offset).toNat value)[byte]? = memory[byte]? := by
  apply storeWordOutside
  rw [frameAddress fits offset small]
  unfold OutsideFrame at outside
  omega

theorem storeBaseOutside {sp : Word} (fits : 48 ≤ sp.toNat) {byte : Nat}
    (outside : OutsideFrame sp byte) (memory : ByteMemory) (value : Word) :
    (storeWord memory (frameBase sp).toNat value)[byte]? = memory[byte]? := by
  rw [← addLiteralZero (frameBase sp)]
  exact storeOutside fits (by decide) outside memory value

/-- Close `memory[byte]? = original.mem[byte]?` when `memory` is `original.mem`
after stores into the frame. -/
macro "frame_agree" fits:term : tactic =>
  `(tactic| (intro byte outside; dsimp only
             simp (disch := first | decide | exact outside) only
               [storeOutside $fits, storeBaseOutside $fits]))

theorem storeOther {sp : Word} (fits : 48 ≤ sp.toNat) {offset other : Word} {memory : ByteMemory}
    {value written : Word} (small : offset.toNat ≤ 44) (otherSmall : other.toNat ≤ 44)
    (apart : other.toNat + 4 ≤ offset.toNat ∨ offset.toNat + 4 ≤ other.toNat)
    (word : WordAt memory (frameBase sp + offset).toNat value) :
    WordAt (storeWord memory (frameBase sp + other).toNat written) (frameBase sp + offset).toNat value := by
  apply word.storeOther
  rw [frameAddress fits offset small, frameAddress fits other otherSmall]
  omega

theorem storeBaseOther {sp : Word} (fits : 48 ≤ sp.toNat) {offset : Word} {memory : ByteMemory}
    {value written : Word} (small : offset.toNat ≤ 44) (apart : 4 ≤ offset.toNat)
    (word : WordAt memory (frameBase sp + offset).toNat value) :
    WordAt (storeWord memory (frameBase sp).toNat written) (frameBase sp + offset).toNat value := by
  have bottom : (frameBase sp).toNat = sp.toNat - 48 := by
    have zero := frameAddress fits 0 (by decide)
    rw [addLiteralZero] at zero
    simpa using zero
  apply word.storeOther
  rw [frameAddress fits offset small, bottom]
  omega

theorem Frame.imageAt {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (agrees : ∀ byte, OutsideFrame initial.sp byte → memory[byte]? = original.mem[byte]?) :
    CodeImage instructions base { original with mem := memory } :=
  frame.code.withMemory memory fun byte low high =>
    agrees byte (frame.codeOutside byte low high)

/-- The prologue saves `ra` and `s0`–`s10` and lowers `sp` by 48. Only the
frame changes. -/
theorem Frame.prologue {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) :
    ∃ memory, run 13 (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory }
          { initial with pc := 0x34, sp := frameBase initial.sp }) ∧
      (∀ byte, OutsideFrame initial.sp byte → memory[byte]? = original.mem[byte]?) ∧
      Saved memory initial := by
  let machine := frame.mode.toMachineState
  have image := frame.imageAt
  have fits := frame.frameFits
  have lowered : initial.sp + 0xffffffd0#32 = frameBase initial.sp := by
    rw [frameBase, BitVec.sub_eq_add_neg]
    rfl
  have lastWritable : Writable original (frameBase initial.sp) := by
    have slot := frame.writable 0 (by decide)
    rwa [addLiteralZero] at slot
  constructor
  refine ⟨?_, ?_, ?_⟩
  · refine runStep (step00 machine (image original.mem fun _ _ => rfl) _ rfl) ?_
    simp only [lowered]
    refine runStep (step04 machine (image original.mem fun _ _ => rfl) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step08 machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step0c machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step10 machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step14 machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step18 machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step1c machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step20 machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step24 machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step28 machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    refine runStep (step2c machine (image _ (by frame_agree fits)) _ rfl
      (frame.writable _ (by decide))) ?_
    exact runStep (step30 machine (image _ (by frame_agree fits)) _ rfl lastWritable) rfl
  · frame_agree fits
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wordAtStore _ _ _⟩
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 10 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 9 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 8 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 7 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 6 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 5 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 4 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 3 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 2 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      iterate 1 (refine storeOther fits (by decide) (by decide) (by decide) ?_)
      exact wordAtStore _ _ _
    · refine storeBaseOther fits (by decide) (by decide) ?_
      exact wordAtStore _ _ _

def restore (initial state : Snapshot) (pc : Word) : Snapshot :=
  { state with
    pc := pc, sp := initial.sp, ra := initial.ra,
    s0 := initial.s0, s1 := initial.s1, s2 := initial.s2, s3 := initial.s3,
    s4 := initial.s4, s5 := initial.s5, s6 := initial.s6, s7 := initial.s7,
    s8 := initial.s8, s9 := initial.s9, s10 := initial.s10 }

/-- From `+0x184`, the 14-instruction epilogue restores `ra` and `s0`–`s10` from any memory
that keeps the saved slots and the code, raises `sp` by 48, and returns. -/
theorem Frame.epilogue {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (image : CodeImage instructions base { original with mem := memory })
    (saved : Saved memory initial) (state : Snapshot) (atExit : state.pc = 0x184#32)
    (lowered : state.sp = frameBase initial.sp) :
    run 14 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        (restore initial state (returnAddress - base))) := by
  let machine := frame.mode.toMachineState
  have bottomReadable : Readable original (frameBase initial.sp) := by
    have slot := frame.readable 0 (by decide)
    rwa [addLiteralZero] at slot
  have raReadable : Readable original (state.sp + 0x2c#32) := by
    rw [lowered]; exact frame.readable 44 (by decide)
  have raSaved : WordAt memory (state.sp + 0x2c#32).toNat initial.ra := by
    rw [lowered]; exact saved.ra
  have s0Readable : Readable original (state.sp + 0x28#32) := by
    rw [lowered]; exact frame.readable 40 (by decide)
  have s0Saved : WordAt memory (state.sp + 0x28#32).toNat initial.s0 := by
    rw [lowered]; exact saved.s0
  have s1Readable : Readable original (state.sp + 0x24#32) := by
    rw [lowered]; exact frame.readable 36 (by decide)
  have s1Saved : WordAt memory (state.sp + 0x24#32).toNat initial.s1 := by
    rw [lowered]; exact saved.s1
  have s2Readable : Readable original (state.sp + 0x20#32) := by
    rw [lowered]; exact frame.readable 32 (by decide)
  have s2Saved : WordAt memory (state.sp + 0x20#32).toNat initial.s2 := by
    rw [lowered]; exact saved.s2
  have s3Readable : Readable original (state.sp + 0x1c#32) := by
    rw [lowered]; exact frame.readable 28 (by decide)
  have s3Saved : WordAt memory (state.sp + 0x1c#32).toNat initial.s3 := by
    rw [lowered]; exact saved.s3
  have s4Readable : Readable original (state.sp + 0x18#32) := by
    rw [lowered]; exact frame.readable 24 (by decide)
  have s4Saved : WordAt memory (state.sp + 0x18#32).toNat initial.s4 := by
    rw [lowered]; exact saved.s4
  have s5Readable : Readable original (state.sp + 0x14#32) := by
    rw [lowered]; exact frame.readable 20 (by decide)
  have s5Saved : WordAt memory (state.sp + 0x14#32).toNat initial.s5 := by
    rw [lowered]; exact saved.s5
  have s6Readable : Readable original (state.sp + 0x10#32) := by
    rw [lowered]; exact frame.readable 16 (by decide)
  have s6Saved : WordAt memory (state.sp + 0x10#32).toNat initial.s6 := by
    rw [lowered]; exact saved.s6
  have s7Readable : Readable original (state.sp + 0xc#32) := by
    rw [lowered]; exact frame.readable 12 (by decide)
  have s7Saved : WordAt memory (state.sp + 0xc#32).toNat initial.s7 := by
    rw [lowered]; exact saved.s7
  have s8Readable : Readable original (state.sp + 0x8#32) := by
    rw [lowered]; exact frame.readable 8 (by decide)
  have s8Saved : WordAt memory (state.sp + 0x8#32).toNat initial.s8 := by
    rw [lowered]; exact saved.s8
  have s9Readable : Readable original (state.sp + 0x4#32) := by
    rw [lowered]; exact frame.readable 4 (by decide)
  have s9Saved : WordAt memory (state.sp + 0x4#32).toNat initial.s9 := by
    rw [lowered]; exact saved.s9
  have s10Readable : Readable original state.sp := by
    rw [lowered]; exact bottomReadable
  have s10Saved : WordAt memory state.sp.toNat initial.s10 := by
    rw [lowered]; exact saved.s10
  refine runStep (step184 machine image _ atExit _ raReadable raSaved) ?_
  refine runStep (step188 machine image _ rfl _ s0Readable s0Saved) ?_
  refine runStep (step18c machine image _ rfl _ s1Readable s1Saved) ?_
  refine runStep (step190 machine image _ rfl _ s2Readable s2Saved) ?_
  refine runStep (step194 machine image _ rfl _ s3Readable s3Saved) ?_
  refine runStep (step198 machine image _ rfl _ s4Readable s4Saved) ?_
  refine runStep (step19c machine image _ rfl _ s5Readable s5Saved) ?_
  refine runStep (step1a0 machine image _ rfl _ s6Readable s6Saved) ?_
  refine runStep (step1a4 machine image _ rfl _ s7Readable s7Saved) ?_
  refine runStep (step1a8 machine image _ rfl _ s8Readable s8Saved) ?_
  refine runStep (step1ac machine image _ rfl _ s9Readable s9Saved) ?_
  refine runStep (step1b0 machine image _ rfl _ s10Readable s10Saved) ?_
  refine runStep (step1b4 machine image _ rfl) ?_
  refine runStep (step1b8 machine image _ rfl returnAddress (by exact frame.link)
    frame.mode.returnLow frame.mode.returnNext) ?_
  have restored : frameBase initial.sp + 0x30#32 = initial.sp := BitVec.sub_add_cancel _ _
  simp only [lowered, restored]
  rfl

end Riscfree.RangeInsert.DeleteExtra
