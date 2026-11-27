import SortedMap.Remove
import SortedMap.Search.Nonvacuity

/-! # Satisfiable premises for the linked sorted-map removal -/

namespace Riscfree.SortedMap.Remove.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

structure Hypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  keyArgument : initial.a1 = call.key
  environment : Environment base returnAddress original
  header : RawVec.Remove.Header original call.vector
  stack : Stack base original call initial.sp
  keys : call.lengthValid → 0 < call.length.toNat → Search.Keys original call.search
  buffer : call.removes → PairRemove.Buffer (vectorBase base) original call.vector

theorem Hypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : Hypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, _⟩ := sortedMapRemoveSailCorrect base returnAddress original call
    initial premises.entry premises.headerArgument premises.keyArgument premises.environment
    premises.header premises.stack premises.keys premises.buffer
  exact ⟨final, ran, pc, status⟩

-- Keep the vector routine at the RawVec model's code base. The two map
-- routines go at their actual relative offsets, with the stack at 0x2800.
def base : Word := 0x11a4
def sp : Word := 0x2800

def image : Model.Image where
  word index :=
    if index < 0x45c then Model.tableWord 0x400 PairRemove.instructions index
    else if index < 0x469 then Model.tableWord 0x45c (Search.instructions .lower) index
    else Model.tableWord 0x469 instructions index
  keys := List.range' 0x1000 (0x1234 - 0x1000)

def modelCall (key length capacity : Word) : Call :=
  ⟨0x3000, key, length, capacity, 0x4000, Search.Nonvacuity.entries⟩

def contents (call : Call) : Model.Contents Pair := .ofRemove call.vector

def initial (call : Call) : Snapshot :=
  { ra := Model.returnTo, sp, t1 := 0, s0 := 17, s1 := 18, s2 := 19,
    a0 := call.header, a1 := call.key, a2 := 0, a3 := 0, a4 := 0, a5 := 0 }

def machine (call : Call) : Machine :=
  sync base (Model.frame image (contents call)) (initial call)

private theorem removeLength : instructions.length = 36 := rfl
private theorem vectorLength : PairRemove.instructions.length = 25 := rfl

private theorem dataFree (index : Nat) (above : 0xc00 ≤ index) : image.word index = none := by
  unfold image
  simp only [not_lt.mpr (show 0x45c ≤ index by omega), not_lt.mpr (show 0x469 ≤ index by omega), if_false]
  exact Model.tableWordOutside _ _ (Or.inr (by rw [removeLength]; omega))

private theorem modelImages {call : Call} {state : Machine}
    (modeled : Model.Modeled image (contents call) state) :
    CodeImage instructions base state ∧
      CodeImage (Search.instructions .lower) (searchBase base) state ∧
      CodeImage PairRemove.instructions (vectorBase base) state := by
  refine ⟨Model.tableImage modeled instructions base 0x11a4 rfl (by decide) (by decide) ?_ ?_,
    Model.tableImage modeled (Search.instructions .lower) (searchBase base) 0x1170 rfl
      (by decide) (by decide) ?_ ?_,
    Model.tableImage modeled PairRemove.instructions (vectorBase base) 0x1000 rfl
      (by decide) (by decide) ?_ ?_⟩
  · intro index inside byte small
    rw [removeLength] at inside
    simp only [image, List.mem_range'_1]
    omega
  · intro index inside
    unfold image
    simp only [not_lt.mpr (show 0x45c ≤ 0x11a4 / 4 + index by omega),
      not_lt.mpr (show 0x469 ≤ 0x11a4 / 4 + index by omega), if_false]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    rw [Search.instructionsLength] at inside
    simp only [image, List.mem_range'_1]
    omega
  · intro index inside
    have bound := inside
    rw [Search.instructionsLength] at bound
    unfold image
    simp only [not_lt.mpr (show 0x45c ≤ 0x1170 / 4 + index by omega), if_false,
      if_pos (show 0x1170 / 4 + index < 0x469 by omega)]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    rw [vectorLength] at inside
    simp only [image, List.mem_range'_1]
    omega
  · intro index inside
    have bound := inside
    rw [vectorLength] at bound
    unfold image
    simp only [if_pos (show 0x1000 / 4 + index < 0x45c by omega)]
    exact Model.tableWordAt _ _ inside

theorem modelHypotheses (key length capacity : Word) (small : length.toNat ≤ 1000) :
    Hypotheses base Model.returnTo (machine (modelCall key length capacity))
      (modelCall key length capacity) (initial (modelCall key length capacity)) := by
  let call := modelCall key length capacity
  have modeled : Model.Modeled image (contents call) (machine call) :=
    Model.syncModeled _ base _
  have mode : MachineMode (machine call) Model.returnTo :=
    { (Model.frameState (contents call)).atSync base (initial call) with
      returnLow := by decide
      returnNext := by decide
      ra := syncRead (base := base) (frame := Model.frame image (contents call))
        (initial call) (index := 1) (by decide) }
  obtain ⟨removeCode, searchCode, vectorCode⟩ := modelImages modeled
  have modeledVector : Model.Modeled image
      (.ofRemove (Model.modelRemoveCall call.vector.index length capacity Search.Nonvacuity.entries))
      (machine call) := modeled
  have header : RawVec.Remove.Header (machine call) call.vector :=
    Model.modelRemoveHeader modeledVector dataFree
  have vectorBuffer : PairRemove.Buffer (vectorBase base) (machine call) call.vector :=
    Model.modelRemoveBuffer modeledVector dataFree (by decide)
      (by rw [pairBytes]; change 8 * length.toNat ≤ 0x100000; omega)
  have stack : Stack base (machine call) call (initial call).sp := by
    refine ⟨by change 16 ≤ sp.toNat; decide, ?_, ?_,
      Or.inr (by change sp.toNat ≤ 0x3000; decide), ?_,
      Or.inl (by change base.toNat + 144 ≤ sp.toNat - 16; decide),
      Or.inl (by change (searchBase base).toNat + 52 ≤ sp.toNat - 16; decide),
      Or.inl (by change (vectorBase base).toNat + 100 ≤ sp.toNat - 16; decide)⟩
    · change ∀ offset ∈ [0, 4, 8, 12], Readable (machine call) (frameBase sp + BitVec.ofNat 32 offset)
      intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        exact Model.readable modeled (by decide) (by decide)
    · change ∀ offset ∈ [0, 4, 8, 12], Writable (machine call) (frameBase sp + BitVec.ofNat 32 offset)
      intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        exact Model.writable modeled (by decide) (by decide)
    · intro index _
      right
      change 0x2800 ≤ 0x4000 + 8 * index
      omega
  refine ⟨(syncSync _ _).symm, rfl, rfl, ⟨mode, removeCode, searchCode, vectorCode⟩,
    header, stack, fun _ _ => ?_, fun _ => vectorBuffer⟩
  refine ⟨vectorBuffer.fits, vectorBuffer.dataReadable, vectorBuffer.dataWord, ?_,
    fun index inside => (vectorBuffer.live index inside).1⟩
  intro index inside
  have below : index < length.toNat := inside
  have scaled : Element.bytes Pair * (index + 1) ≤ 0x100000 := by
    rw [pairBytes]
    omega
  exact (Model.elementReadable modeled scaled).1

-- Invalid length, empty search, search exhausted, a different key at the
-- stopping position, removal of the last entry, and removal with a shift.
def invalidCall : Call := modelCall 20 3 2
def emptyCall : Call := modelCall 20 0 0
def exhaustedCall : Call := modelCall 31 3 3
def differentCall : Call := modelCall 25 3 3
def lastCall : Call := modelCall 30 3 3
def shiftingCall : Call := modelCall 20 3 3

theorem allPaths :
    (¬ invalidCall.lengthValid ∧ invalidCall.status = 3) ∧
    (emptyCall.lengthValid ∧ emptyCall.position = 0 ∧ emptyCall.status = 5) ∧
    (exhaustedCall.lengthValid ∧ exhaustedCall.position = 3 ∧ exhaustedCall.status = 5) ∧
    (differentCall.lengthValid ∧ differentCall.position = 2 ∧ differentCall.status = 5) ∧
    (lastCall.removes ∧ lastCall.position = 2 ∧ lastCall.status = 0) ∧
    (shiftingCall.removes ∧ shiftingCall.position = 1 ∧ shiftingCall.status = 0) := by decide

theorem allPathsRun :
    ∀ call ∈ [invalidCall, emptyCall, exhaustedCall, differentCall, lastCall, shiftingCall],
      ∃ final, Riscfree.RV32.run call.count (machine call) = some final ∧
        final.regs.get? Register.PC = some Model.returnTo ∧
        final.regs.get? Register.x10 = some call.status := by
  intro call member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (modelHypotheses _ _ _ (by decide)).run

theorem mathematicalRemoval :
    entriesOf shiftingCall.vector.result 2 =
      erase (entriesOf Search.Nonvacuity.entries 3) 20 :=
  (sortedMapRemoveErases shiftingCall Search.Nonvacuity.entriesSorted).1 allPaths.2.2.2.2.2.1

theorem mathematicalAbsence :
    erase (entriesOf Search.Nonvacuity.entries 3) differentCall.key =
      entriesOf Search.Nonvacuity.entries 3 :=
  (sortedMapRemoveErases differentCall Search.Nonvacuity.entriesSorted).2 (by decide) (by decide)

end Riscfree.SortedMap.Remove.Nonvacuity
