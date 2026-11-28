import RangeInsert.Bounded.Entry
import RangeInsert.Empty

/-! The bounded entry point uses the same saved stack layout as the
trapping routine. The empty arm now sets a0 to OK before the common return. -/

namespace Riscfree.RangeInsert.Bounded.EntryEmpty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Entry
open Empty (Snapshot frameBase frameAddress pushed pushedOutside OutsideFrame restore)

set_option maxHeartbeats 3000000

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

private def push (sp offset value : Word) (memory : ByteMemory) : ByteMemory :=
  storeWord memory (frameBase sp + offset).toNat value

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
    (atExit : state.pc = 0x1a4#32) (lowered : state.sp = frameBase initial.sp) :
    run 9 (sync base background state) =
      some (sync base background
        (restore initial state (returnAddress - base))) := by
  obtain ⟨ra, s0, s1, s2, s3, s4, s5⟩ := savedWords original.mem initial frame.frameFits
  refine runStep (step1a4 machine image _ atExit _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 44 _ (by decide) ra)) ?_
  refine runStep (step1a8 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 40 _ (by decide) s0)) ?_
  refine runStep (step1ac machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 36 _ (by decide) s1)) ?_
  refine runStep (step1b0 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 32 _ (by decide) s2)) ?_
  refine runStep (step1b4 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 28 _ (by decide) s3)) ?_
  refine runStep (step1b8 machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 24 _ (by decide) s4)) ?_
  refine runStep (step1bc machine image _ rfl _ (lowered ▸ readable _ (by decide)) (lowered ▸ saved 20 _ (by decide) s5)) ?_
  refine runStep (step1c0 machine image _ rfl) ?_
  refine runStep (step1c4 machine image _ rfl returnAddress frame.link
    frame.mode.returnLow frame.mode.returnNext) ?_
  have restored : frameBase initial.sp + 48#32 = initial.sp := BitVec.sub_add_cancel _ _
  simp only [lowered, restored]
  rfl

theorem Frame.epilogue {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (state : Snapshot)
    (atExit : state.pc = 0x1a4#32) (lowered : state.sp = frameBase initial.sp) :
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
    run 21 original =
      some (sync base { original with mem := pushed original.mem initial }
        { initial with pc := returnAddress - base, a0 := 0 }) := by
  conv_lhs => rw [premises.entry]
  rw [show 21 = 9 + (3 + 9) by decide, runAdd, premises.toFrame.prologue, Option.bind_some]
  let machine := premises.mode.toMachineState
  let image := premises.toFrame.pushedImage
  refine runStep (step24 machine image _ rfl) ?_
  rw [if_neg (Nat.not_le.mpr premises.empty)]
  refine runStep (step28 machine image _ rfl) ?_
  refine runStep (step2c machine image _ rfl) ?_
  exact premises.toFrame.epilogue _ rfl rfl

end Riscfree.RangeInsert.Bounded.EntryEmpty
