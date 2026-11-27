import RangeInsert.Nonempty.Contained
import RangeInsert.Nonempty.Correspondence
import RawVec.Model

/-! Concrete machines satisfy `ContainedPremises` for a strictly contained
input, an input that starts at its predecessor's start, and a predecessor
that ends at `u32::MAX`. The kernel applies `ContainedPremises.run` to each
machine. For the same maps, `Represents` holds for a concrete canonical set,
so the model correspondence `containedModel` is also exercised.

The model machine is the RawVec one (`RawVec/Model.lean`): the map header at
`0x3000` and the entries at `0x4000`. `sorted_map_upper_bound` is at
`0x1000`, and the entry point is at its linked distance, `0x208` bytes
later. The stack pointer is `0x2800`. -/

namespace Riscfree.RangeInsert.Nonempty.Contained.Nonvacuity

open LeanRV32D RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Empty (Snapshot)
open RangeSetBlazeValidation RangeSetBlazeValidation.RangeSetBlaze

def base : Word := 0x1208
def sp : Word := 0x2800

private theorem insertLength : instructions.length = 109 := rfl

def image : Model.Image where
  word index :=
    if index < 0x482 then Model.tableWord 0x400 (SortedMap.Search.instructions .upper) index
    else if index = 0x940 then some 15
    else if index = 0x941 then some 0
    else Model.tableWord 0x482 instructions index
  keys := List.range' 0x1000 (0x13bc - 0x1000) ++ List.range' 0x2500 8

def modelCall (length : Word) (old : Nat → Pair) (start stop : Word) : Call :=
  { header := 0x3000, length, data := 0x4000, old, start, stop }

def contents (call : Call) : Model.Contents Pair :=
  .ofRemove (Model.modelRemoveCall 0 call.length call.length call.old)

def initial (call : Call) : Snapshot :=
  { ra := Model.returnTo, sp, s0 := 17, s1 := 18, s2 := 19, s3 := 20, s4 := 21, s5 := 22,
    a0 := call.header, a1 := 0x2500, a2 := call.start, a3 := call.stop, a4 := 0x6000, a5 := 4 }

def machine (call : Call) : Machine :=
  sync base (Model.frame image (contents call)) (initial call)

private theorem dataFree (index : Nat) (above : 0xc00 ≤ index) : image.word index = none := by
  unfold image
  simp only [not_lt.mpr (show 0x482 ≤ index by omega), if_false,
    if_neg (show index ≠ 0x940 by omega), if_neg (show index ≠ 0x941 by omega)]
  exact Model.tableWordOutside _ _ (Or.inr (by rw [insertLength]; omega))

private theorem modelImages {call : Call} {state : Machine}
    (modeled : Model.Modeled image (contents call) state) :
    CodeImage instructions base state ∧
      CodeImage (SortedMap.Search.instructions .upper) (upperBoundBase base) state := by
  refine ⟨Model.tableImage modeled instructions base 0x1208 rfl (by decide) (by decide) ?_ ?_,
    Model.tableImage modeled (SortedMap.Search.instructions .upper) (upperBoundBase base) 0x1000 rfl
      (by decide) (by decide) ?_ ?_⟩
  · intro index inside byte small
    rw [insertLength] at inside
    simp only [image, List.mem_append, List.mem_range'_1]
    apply Or.inl
    omega
  · intro index inside
    have bound := inside
    rw [insertLength] at bound
    unfold image
    simp only [not_lt.mpr (show 0x482 ≤ 0x1208 / 4 + index by omega), if_false,
      if_neg (show 0x1208 / 4 + index ≠ 0x940 by omega),
      if_neg (show 0x1208 / 4 + index ≠ 0x941 by omega)]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    rw [SortedMap.Search.instructionsLength] at inside
    simp only [image, List.mem_append, List.mem_range'_1]
    apply Or.inl
    omega
  · intro index inside
    have bound := inside
    rw [SortedMap.Search.instructionsLength] at bound
    unfold image
    simp only [if_pos (show 0x1000 / 4 + index < 0x482 by omega)]
    exact Model.tableWordAt _ _ inside

-- `OutsideFrame` for bytes at or above the caller's stack pointer.
private theorem above {byte : Nat} (high : 0x2800 ≤ byte) : Empty.OutsideFrame sp byte :=
  Or.inr high

-- `OutsideFrame` for bytes below the frame.
private theorem below {byte : Nat} (low : byte < 0x2800 - 48) : Empty.OutsideFrame sp byte :=
  Or.inl low

theorem modelFrameMap {length : Word} {old : Nat → Pair} {start stop : Word}
    (small : length.toNat ≤ 1000) :
    let call := modelCall length old start stop
    Empty.Frame base Model.returnTo (machine call) (initial call) ∧
      Map base (machine call) (initial call).sp call := by
  let call := modelCall length old start stop
  have modeled : Model.Modeled image (contents call) (machine call) := Model.syncModeled _ base _
  have mode : MachineMode (machine call) Model.returnTo :=
    { (Model.frameState (contents call)).atSync base (initial call) with
      returnLow := by decide
      returnNext := by decide
      ra := syncRead (base := base) (frame := Model.frame image (contents call))
        (initial call) (index := 1) (by decide) }
  obtain ⟨insertCode, searchCode⟩ := modelImages modeled
  have header := Model.modelRemoveHeader modeled dataFree
  have buffer := Model.modelRemoveBuffer modeled dataFree (codeBytes := 0) (by decide)
    (by rw [pairBytes]; change 8 * length.toNat ≤ 0x100000; omega)
  have scaled (index : Nat) (inside : index < length.toNat) :
      Element.bytes Pair * (index + 1) ≤ 0x100000 := by
    rw [pairBytes]; omega
  have frame : Empty.Frame base Model.returnTo (machine call) (initial call) := by
    refine ⟨(syncSync _ _).symm, rfl, mode, insertCode, by change 48 ≤ sp.toNat; decide,
      ?_, ?_, ?_⟩
    · intro byte _ high
      rw [insertLength, show base.toNat = 0x1208 from rfl] at high
      exact below (by omega)
    · intro offset member
      change Readable (machine call) (Empty.frameBase sp + offset)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Model.readable modeled (by decide) (by decide)
    · intro offset member
      change Writable (machine call) (Empty.frameBase sp + offset)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Model.writable modeled (by decide) (by decide)
  have map : Map base (machine call) (initial call).sp call := by
    refine ⟨searchCode, fun byte _ high => below (by
        change byte < 0x1000 + 52 at high; omega),
      ⟨by change 0x3000 + 8 ≤ 2 ^ 32; decide, header.lengthReadable, header.lengthWord⟩,
      fun _ => ⟨buffer.fits, buffer.dataReadable, buffer.dataWord,
        fun index inside => (Model.elementReadable modeled (scaled index inside)).1,
        fun index inside => (buffer.live index inside).1⟩,
      fun byte low _ => above (by change 0x3000 ≤ byte at low; omega),
      fun index _ byte low _ => above (by
        change 0x4000 + 8 * index ≤ byte at low; omega),
      fun index inside => (Model.elementReadable modeled (scaled index inside)).2,
      fun index inside => (buffer.live index inside).2, by change 0 < (0x4000#32).toNat; decide⟩
  exact ⟨frame, map⟩

theorem modelPremises {length : Word} {old : Nat → Pair} {start stop : Word}
    (small : length.toNat ≤ 1000) (nonempty : start.toNat ≤ stop.toNat)
    (found : 0 < (modelCall length old start stop).rank)
    (covered : stop.toNat ≤ (modelCall length old start stop).predecessor.value.toNat) :
    ContainedPremises base Model.returnTo (machine (modelCall length old start stop))
      (initial (modelCall length old start stop)) (modelCall length old start stop) := by
  obtain ⟨frame, map⟩ := modelFrameMap (old := old) (start := start) (stop := stop) small
  exact ⟨frame, ⟨rfl, rfl, rfl⟩, map, nonempty, found, covered⟩

/-! ## One machine per covered case -/

-- The stored ranges 4..=9, 12..=16, 20..=23.
def ranges (index : Nat) : Pair :=
  match index with
  | 0 => ⟨4, 9⟩
  | 1 => ⟨12, 16⟩
  | _ => ⟨20, 23⟩

-- A single stored range 10..=u32::MAX.
def topRange (_ : Nat) : Pair := ⟨10, 0xffffffff⟩

-- 5..=7 lies strictly inside 4..=9.
def strictCall : Call := modelCall 3 ranges 5 7
-- 12..=14 starts where 12..=16 starts.
def equalStartCall : Call := modelCall 3 ranges 12 14
-- u32::MAX..=u32::MAX lies in a range that ends at u32::MAX, so the
-- strict-gap test must not overflow.
def topCall : Call := modelCall 1 topRange 0xffffffff 0xffffffff

theorem cases :
    (strictCall.rank = 1 ∧ strictCall.predecessor.value = 9 ∧ strictCall.containedCount = 56) ∧
    (equalStartCall.rank = 2 ∧ equalStartCall.predecessor.value = 16 ∧
      equalStartCall.containedCount = 61) ∧
    (topCall.rank = 1 ∧ topCall.predecessor.value = 0xffffffff ∧ topCall.containedCount = 55) := by
  decide

theorem strictSatisfiable :
    ContainedPremises base Model.returnTo (machine strictCall) (initial strictCall) strictCall :=
  modelPremises (by decide) (by decide) (by decide) (by decide)

theorem equalStartSatisfiable :
    ContainedPremises base Model.returnTo (machine equalStartCall) (initial equalStartCall)
      equalStartCall :=
  modelPremises (by decide) (by decide) (by decide) (by decide)

theorem topSatisfiable :
    ContainedPremises base Model.returnTo (machine topCall) (initial topCall) topCall :=
  modelPremises (by decide) (by decide) (by decide) (by decide)

theorem allCasesRun :
    ∀ call ∈ [strictCall, equalStartCall, topCall],
      ∃ final, Riscfree.RV32.run call.containedCount (machine call) = some final ∧
        final.regs.get? Register.PC = some Model.returnTo ∧
        final.regs.get? Register.x2 = some sp ∧
        ∀ byte, Empty.OutsideFrame sp byte → final.mem[byte]? = (machine call).mem[byte]? := by
  intro call member
  have premises : ContainedPremises base Model.returnTo (machine call) (initial call) call := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    exacts [strictSatisfiable, equalStartSatisfiable, topSatisfiable]
  obtain ⟨final, ran, pc, registers, memory⟩ := premises.run
  refine ⟨final, ran, pc, (registers _ (by decide)).trans ?_, memory⟩
  exact readReg_succ.mp (syncRead (base := base) (frame := Model.frame image (contents call))
    (initial call) (index := 2) (by decide))

/-! ## The same maps represent canonical sets -/

private def nr (lo hi : Int) (ordered : lo ≤ hi) : RangeSetBlazeValidation.IntRange.NR :=
  ⟨{ lo := lo, hi := hi }, ordered⟩

def threeRanges : RangeSetBlaze :=
  ⟨[nr 4 9 (by decide), nr 12 16 (by decide), nr 20 23 (by decide)],
    by simp [nr, IntRange.NR.before]⟩

def topSet : RangeSetBlaze := ⟨[nr 10 4294967295 (by decide)], by simp⟩

theorem represented :
    Represents threeRanges strictCall ∧ Represents threeRanges equalStartCall ∧
      Represents topSet topCall := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold Represents; decide +kernel)

theorem modelsUnchanged :
    internalAddProduction threeRanges 15 strictCall.input = ⟨threeRanges, 15⟩ ∧
      internalAddProduction threeRanges 15 equalStartCall.input = ⟨threeRanges, 15⟩ ∧
      internalAddProduction topSet 4294967286 topCall.input = ⟨topSet, 4294967286⟩ :=
  ⟨containedModel 15 represented.1 (by decide) (by decide) (by decide),
    containedModel 15 represented.2.1 (by decide) (by decide) (by decide),
    containedModel 4294967286 represented.2.2 (by decide) (by decide) (by decide)⟩

end Riscfree.RangeInsert.Nonempty.Contained.Nonvacuity
