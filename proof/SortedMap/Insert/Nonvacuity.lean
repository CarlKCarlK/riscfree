import SortedMap.Insert
import SortedMap.Search.Nonvacuity

/-! # Satisfiable premises for the linked sorted-map insertion -/

namespace Riscfree.SortedMap.Insert.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

structure Hypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  keyArgument : initial.a1 = call.value.key
  valueArgument : initial.a2 = call.value.value
  environment : Environment base returnAddress original
  header : RawVec.Insert.Header original call.vector
  stack : Stack base original call initial.sp
  keys : call.lengthValid → 0 < call.length.toNat → Search.Keys original call.search
  replace : call.replaces → Replacement base original call
  buffer : ¬ call.replaces → call.vector.valid → PairInsert.Buffer (vectorBase base) original call.vector

theorem Hypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : Hypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, _⟩ := sortedMapInsertSailCorrect base returnAddress original call
    initial premises.entry premises.headerArgument premises.keyArgument premises.valueArgument premises.environment
    premises.header premises.stack premises.keys premises.replace premises.buffer
  exact ⟨final, ran, pc, status⟩

-- Keep the vector routine at the RawVec model's code base. The two map
-- routines go at their actual relative offsets, with the stack at 0x2800.
def base : Word := 0x11bc
def sp : Word := 0x2800

def image : Model.Image where
  word index :=
    if index < 0x46f then Model.tableWord 0x400 PairInsert.instructions index
    else if index < 0x49b then Model.tableWord 0x46f instructions index
    else Model.tableWord 0x49b (Search.instructions .lower) index
  keys := List.range' 0x1000 (0x12a0 - 0x1000)

def modelCall (key length capacity : Word) : Call :=
  ⟨0x3000, ⟨key, 700⟩, length, capacity, 0x4000, Search.Nonvacuity.entries⟩

def contents (call : Call) : Model.Contents Pair := .ofInsert call.vector

def initial (call : Call) : Snapshot :=
  { ra := Model.returnTo, sp, t1 := 0, s0 := 17, s1 := 18, s2 := 19, s3 := 20,
    a0 := call.header, a1 := call.value.key, a2 := call.value.value, a3 := 0, a4 := 0, a5 := 0 }

def machine (call : Call) : Machine :=
  sync base (Model.frame image (contents call)) (initial call)

private theorem insertLength : instructions.length = 44 := rfl
private theorem vectorLength : PairInsert.instructions.length = 33 := rfl

private theorem dataFree (index : Nat) (above : 0xc00 ≤ index) : image.word index = none := by
  unfold image
  simp only [not_lt.mpr (show 0x49b ≤ index by omega), not_lt.mpr (show 0x46f ≤ index by omega), if_false]
  exact Model.tableWordOutside _ _ (Or.inr (by rw [Search.instructionsLength]; omega))

private theorem modelImages {call : Call} {state : Machine}
    (modeled : Model.Modeled image (contents call) state) :
    CodeImage instructions base state ∧
      CodeImage (Search.instructions .lower) (searchBase base) state ∧
      CodeImage PairInsert.instructions (vectorBase base) state := by
  refine ⟨Model.tableImage modeled instructions base 0x11bc rfl (by decide) (by decide) ?_ ?_,
    Model.tableImage modeled (Search.instructions .lower) (searchBase base) 0x126c rfl
      (by decide) (by decide) ?_ ?_,
    Model.tableImage modeled PairInsert.instructions (vectorBase base) 0x1000 rfl
      (by decide) (by decide) ?_ ?_⟩
  · intro index inside byte small
    rw [insertLength] at inside
    simp only [image, List.mem_range'_1]
    omega
  · intro index inside
    unfold image
    have bound := inside
    rw [insertLength] at bound
    simp only [not_lt.mpr (show 0x46f ≤ 0x11bc / 4 + index by omega), if_false,
      if_pos (show 0x11bc / 4 + index < 0x49b by omega)]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    rw [Search.instructionsLength] at inside
    simp only [image, List.mem_range'_1]
    omega
  · intro index inside
    have bound := inside
    rw [Search.instructionsLength] at bound
    unfold image
    simp only [not_lt.mpr (show 0x46f ≤ 0x126c / 4 + index by omega),
      not_lt.mpr (show 0x49b ≤ 0x126c / 4 + index by omega), if_false]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    rw [vectorLength] at inside
    simp only [image, List.mem_range'_1]
    omega
  · intro index inside
    have bound := inside
    rw [vectorLength] at bound
    unfold image
    simp only [if_pos (show 0x1000 / 4 + index < 0x46f by omega)]
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
  obtain ⟨insertCode, searchCode, vectorCode⟩ := modelImages modeled
  have modeledVector : Model.Modeled image
      (.ofInsert (Model.modelCall call.vector.index call.value length capacity Search.Nonvacuity.entries))
      (machine call) := modeled
  have header : RawVec.Insert.Header (machine call) call.vector :=
    Model.modelHeader modeledVector dataFree
  have vectorBuffer : PairInsert.Buffer (vectorBase base) (machine call) call.vector :=
    Model.modelBuffer modeledVector dataFree (by decide)
      (by rw [pairBytes]; change 8 * (length.toNat + 1) ≤ 0x100000; omega)
  have stack : Stack base (machine call) call (initial call).sp := by
    refine ⟨by change 32 ≤ sp.toNat; decide, ?_, ?_,
      Or.inr (by change sp.toNat ≤ 0x3000; decide), ?_,
      ?_, Or.inl (by change base.toNat + 176 ≤ sp.toNat - 32; decide),
      Or.inl (by change (searchBase base).toNat + 52 ≤ sp.toNat - 32; decide),
      Or.inl (by change (vectorBase base).toNat + 132 ≤ sp.toNat - 32; decide)⟩
    · change ∀ offset ∈ [12, 16, 20, 24, 28], Readable (machine call) (frameBase sp + BitVec.ofNat 32 offset)
      intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        exact Model.readable modeled (by decide) (by decide)
    · change ∀ offset ∈ [12, 16, 20, 24, 28], Writable (machine call) (frameBase sp + BitVec.ofNat 32 offset)
      intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        exact Model.writable modeled (by decide) (by decide)
    · intro index _
      right
      change 0x2800 ≤ 0x4000 + 8 * index
      omega
    · intro _
      right
      change 0x2800 ≤ 0x4000 + 8 * call.length.toNat
      omega
  have replacement (replaces : call.replaces) : Replacement base (machine call) call := by
    have inside : call.position < length.toNat := replaces.2.1
    have scaled : Element.bytes Pair * (call.position + 1) ≤ 0x100000 := by
      rw [pairBytes]
      omega
    refine ⟨Model.elementWritable modeled scaled, Or.inr ?_, Or.inr ?_, vectorBuffer.live⟩
    · change 0x11bc + 176 ≤ 0x4000 + 8 * call.position
      omega
    · change 0x3000 + 12 ≤ 0x4000 + 8 * call.position
      omega
  refine ⟨(syncSync _ _).symm, rfl, rfl, rfl, ⟨mode, insertCode, searchCode, vectorCode⟩,
    header, stack, fun _ _ => ?_, replacement, fun _ _ => vectorBuffer⟩
  refine ⟨(call.vector.slotMono (Nat.le_succ _)).trans vectorBuffer.fits, vectorBuffer.dataReadable, vectorBuffer.dataWord, ?_,
    fun index inside => (vectorBuffer.live index inside).1⟩
  intro index inside
  have below : index < length.toNat := inside
  have scaled : Element.bytes Pair * (index + 1) ≤ 0x100000 := by
    rw [pairBytes]
    omega
  exact (Model.elementReadable modeled scaled).1

-- Invalid length, replacement while full, an absent key in a full map,
-- insertion into an empty map, append, and insertion with a shift.
def invalidCall : Call := modelCall 20 3 2
def replacementCall : Call := modelCall 20 3 3
def fullCall : Call := modelCall 25 3 3
def emptyCall : Call := modelCall 20 0 1
def appendCall : Call := modelCall 31 3 4
def shiftingCall : Call := modelCall 25 3 4

theorem allPaths :
    (¬ invalidCall.lengthValid ∧ invalidCall.status = 3) ∧
    (replacementCall.replaces ∧ replacementCall.position = 1 ∧ replacementCall.status = 4) ∧
    (¬ fullCall.replaces ∧ ¬ fullCall.vector.valid ∧ fullCall.status = 1) ∧
    (emptyCall.vector.valid ∧ emptyCall.position = 0 ∧ emptyCall.status = 0) ∧
    (appendCall.vector.valid ∧ appendCall.position = 3 ∧ appendCall.status = 0) ∧
    (¬ shiftingCall.replaces ∧ shiftingCall.vector.valid ∧ shiftingCall.position = 2 ∧
      shiftingCall.status = 0) := by decide

theorem allPathsRun :
    ∀ call ∈ [invalidCall, replacementCall, fullCall, emptyCall, appendCall, shiftingCall],
      ∃ final, Riscfree.RV32.run call.count (machine call) = some final ∧
        final.regs.get? Register.PC = some Model.returnTo ∧
        final.regs.get? Register.x10 = some call.status := by
  intro call member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (modelHypotheses _ _ _ (by decide)).run

theorem mathematicalInsertion :
    entriesOf shiftingCall.vector.result 4 =
      insert (entriesOf Search.Nonvacuity.entries 3) shiftingCall.value :=
  (sortedMapInsertUpdates shiftingCall Search.Nonvacuity.entriesSorted).2
    allPaths.2.2.2.2.2.1 allPaths.2.2.2.2.2.2.1

theorem mathematicalReplacement :
    entriesOf replacementCall.replacedEntries 3 =
      insert (entriesOf Search.Nonvacuity.entries 3) replacementCall.value :=
  (sortedMapInsertUpdates replacementCall Search.Nonvacuity.entriesSorted).1 (by decide)

end Riscfree.SortedMap.Insert.Nonvacuity
