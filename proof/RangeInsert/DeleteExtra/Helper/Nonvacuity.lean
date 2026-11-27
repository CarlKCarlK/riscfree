import RangeInsert.DeleteExtra.Helper
import RawVec.Model

/-! Concrete helper machines use the linked distances between callees,
three map entries, and separate storage for the map reference, cached count,
temporary vector, and stack. -/

namespace Riscfree.RangeInsert.DeleteExtra.Nonvacuity

open LeanRV32D RV32IM
open Riscfree.RV32 Riscfree.RawVec

private def base : Word := 0x1400
private def stackTop : Word := 0x2800

private def scratch : Scratch := ⟨0x2130, 2⟩

private def ranges (stop : Word) (index : Nat) : Pair :=
  if index = 0 then ⟨4, stop⟩ else if index = 1 then ⟨12, 16⟩ else ⟨20, 23⟩

private def call (stop : Word) : Call :=
  { mapRef := 0x2100, header := 0x3000, length := 3, data := 0x4000, old := ranges stop,
    cache := 0x2110, low := BitVec.ofNat 32 (stop.toNat + 6),
    high := BitVec.ofNat 32 ((stop.toNat + 6) / 2 ^ 32), start := 4, stop, keys := 0x2120 }

private def image (stop : Word) : Model.Image where
  word index :=
    if index < 0x466 then Model.tableWord 0x448 RawVec.instructions index
    else if index < 0x4c2 then Model.tableWord 0x466 PairRemove.instructions index
    else if index < 0x4cf then Model.tableWord 0x4c2 (SortedMap.Search.instructions .lower) index
    else if index < 0x500 then Model.tableWord 0x4cf SortedMap.Remove.instructions index
    else if index < 0x800 then Model.tableWord 0x500 DeleteTable.instructions index
    else if index = 0x840 then some (call stop).header
    else if index = 0x844 then some (call stop).low
    else if index = 0x845 then some (call stop).high
    else if index = 0x848 then some scratch.data
    else if index = 0x849 then some 0#32
    else if index = 0x84a then some scratch.capacity
    else none
  keys := List.range' 0x1120 (0x15d4 - 0x1120) ++ List.range' 0x2100 0x38

private def contents (stop : Word) : Model.Contents Pair := ⟨3, 3, ranges stop⟩

private def initial (stop : Word) : Snapshot :=
  { ra := Model.returnTo, sp := stackTop, t1 := 0, s0 := 8, s1 := 9,
    a0 := (call stop).mapRef, a1 := (call stop).cache, a2 := (call stop).start, a3 := stop,
    a4 := (call stop).keys, a5 := 0, a6 := 0, a7 := 0, s2 := 18,
    s3 := 19, s4 := 20, s5 := 21, s6 := 22, s7 := 23, s8 := 24, s9 := 25, s10 := 26 }

private def machine (stop : Word) : Machine :=
  sync base (Model.frame (image stop) (contents stop)) (initial stop)

private theorem modeled (stop : Word) : Model.Modeled (image stop) (contents stop) (machine stop) :=
  Model.syncModeled _ _ _

private theorem dataFree (stop : Word) (index : Nat) (above : 0xc00 ≤ index) :
    (image stop).word index = none := by
  simp only [image, if_neg (show ¬ index < 0x466 by omega), if_neg (show ¬ index < 0x4c2 by omega),
    if_neg (show ¬ index < 0x4cf by omega), if_neg (show ¬ index < 0x500 by omega),
    if_neg (show ¬ index < 0x800 by omega), if_neg (show index ≠ 0x840 by omega),
    if_neg (show index ≠ 0x844 by omega), if_neg (show index ≠ 0x845 by omega),
    if_neg (show index ≠ 0x848 by omega), if_neg (show index ≠ 0x849 by omega),
    if_neg (show index ≠ 0x84a by omega)]

private theorem present (stop : Word) (address : Nat) (low : 0x1120 ≤ address)
    (high : address < 0x15d4) : address ∈ (image stop).keys := by
  simp only [image, List.mem_append, List.mem_range'_1]
  omega

private theorem images (stop : Word) :
    CodeImage DeleteTable.instructions base (machine stop) ∧
    CodeImage RawVec.instructions (rawVecBase base) (machine stop) ∧
    CodeImage (SortedMap.Search.instructions .lower) (lowerBoundBase base) (machine stop) ∧
    CodeImage SortedMap.Remove.instructions (removeBase base) (machine stop) ∧
    CodeImage PairRemove.instructions (SortedMap.Remove.vectorBase (removeBase base)) (machine stop) := by
  refine ⟨Model.tableImage (modeled stop) _ _ 0x1400 rfl (by decide) (by decide) ?_ ?_,
    Model.tableImage (modeled stop) _ _ 0x1120 rfl (by decide) (by decide) ?_ ?_,
    Model.tableImage (modeled stop) _ _ 0x1308 rfl (by decide) (by decide) ?_ ?_,
    Model.tableImage (modeled stop) _ _ 0x133c rfl (by decide) (by decide) ?_ ?_,
    Model.tableImage (modeled stop) _ _ 0x1198 rfl (by decide) (by decide) ?_ ?_⟩
  · intro index inside byte small
    change index < 117 at inside
    exact present stop _ (by omega) (by omega)
  · intro index inside
    have length : index < 117 := inside
    unfold image
    simp only [if_neg (show ¬ 0x1400 / 4 + index < 0x466 by omega),
      if_neg (show ¬ 0x1400 / 4 + index < 0x4c2 by omega),
      if_neg (show ¬ 0x1400 / 4 + index < 0x4cf by omega),
      if_neg (show ¬ 0x1400 / 4 + index < 0x500 by omega),
      if_pos (show 0x1400 / 4 + index < 0x800 by omega)]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    change index < 30 at inside
    exact present stop _ (by omega) (by omega)
  · intro index inside
    have length : index < 30 := inside
    unfold image
    simp only [if_pos (show 0x1120 / 4 + index < 0x466 by omega)]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    change index < 13 at inside
    exact present stop _ (by omega) (by omega)
  · intro index inside
    have length : index < 13 := inside
    unfold image
    simp only [if_neg (show ¬ 0x1308 / 4 + index < 0x466 by omega),
      if_neg (show ¬ 0x1308 / 4 + index < 0x4c2 by omega),
      if_pos (show 0x1308 / 4 + index < 0x4cf by omega)]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    change index < 36 at inside
    exact present stop _ (by omega) (by omega)
  · intro index inside
    have length : index < 36 := inside
    unfold image
    simp only [if_neg (show ¬ 0x133c / 4 + index < 0x466 by omega),
      if_neg (show ¬ 0x133c / 4 + index < 0x4c2 by omega),
      if_neg (show ¬ 0x133c / 4 + index < 0x4cf by omega),
      if_pos (show 0x133c / 4 + index < 0x500 by omega)]
    exact Model.tableWordAt _ _ inside
  · intro index inside byte small
    change index < 25 at inside
    exact present stop _ (by omega) (by omega)
  · intro index inside
    have length : index < 25 := inside
    unfold image
    simp only [if_neg (show ¬ 0x1198 / 4 + index < 0x466 by omega),
      if_pos (show 0x1198 / 4 + index < 0x4c2 by omega)]
    exact Model.tableWordAt _ _ inside

private theorem extraWord (stop : Word) (address : Nat) (value : Word)
    (small : 0x2100 ≤ address ∧ address + 4 ≤ 0x2138) (aligned : address % 4 = 0)
    (chosen : (image stop).word (address / 4) = some value) :
    WordAt (machine stop).mem address value := by
  rw [(modeled stop).mem]
  have word := wordMemoryWord (Model.keys (image stop) (contents stop))
    (Model.contents (image stop) (contents stop)) address aligned (by
      intro byte inside
      simp only [Model.keys, image, List.mem_append, List.mem_range'_1]
      omega)
  rw [Model.contents, chosen, Option.getD_some] at word
  exact word

private theorem position (stop : Word) : (call stop).position = 0 := by rfl

-- Some address goals still mention the endpoint parameter under a record
-- projection. The kernel reduces the projection before evaluating the decision.
local macro "model_decide" : tactic =>
  `(tactic| exact of_decide_eq_true rfl)

private theorem belowFrame {byte : Nat} (bound : byte < 0x27d0) : OutsideFrame stackTop byte :=
  Or.inl bound

private theorem aboveFrame {byte : Nat} (bound : 0x2800 ≤ byte) : OutsideFrame stackTop byte :=
  Or.inr bound

private theorem codeBelow {byte : Nat} (inside : InCode base byte) : byte < 0x1600 := by
  rcases inside with helper | remove | search | vector
  · have high : byte < 0x1400 + 4 * 117 := helper.2
    omega
  · have high : byte < 0x133c + 144 := remove.2
    omega
  · have high : byte < 0x1308 + 52 := search.2
    omega
  · have high : byte < 0x1198 + 100 := vector.2
    omega

private theorem scanRegion (stop : Word) {accepted byte : Nat}
    (bound : accepted ≤ 2) (inside : Footprint (call stop) scratch accepted byte) :
    0x2110 ≤ byte ∧ byte < 0x2138 := by
  rcases inside with cache | header | slots
  · change 0x2110 ≤ byte ∧ byte < 0x2110 + 8 at cache
    omega
  · change 0x2124 ≤ byte ∧ byte < 0x2128 at header
    omega
  · change 0x2130 ≤ byte ∧ byte < 0x2130 + 4 * accepted at slots
    omega

-- The nested stack writes, map length, and shifted entries are in three
-- separate intervals in this machine.
private theorem drainRegion (stop : Word) {byte : Nat}
    (inside : DrainFootprint (frameBase stackTop) (call stop).header (call stop).search
      (call stop).position (call stop).length.toNat byte) :
    (0x27c0 ≤ byte ∧ byte < 0x27d0) ∨
      (0x3004 ≤ byte ∧ byte < 0x3008) ∨ (0x4008 ≤ byte ∧ byte < 0x4018) := by
  rw [position] at inside
  exact inside

private theorem slotGeometry (stop : Word) (index : Nat) :
    (call stop).search.slot index = 0x4000 + 8 * index := rfl

private theorem scratchGeometry (index : Nat) : scratch.slot index = 0x2130 + 4 * index := rfl

private theorem scratchReadable (stop : Word) {index : Nat} (bound : index < 2) :
    Readable (machine stop) (scratch.wordSlot index) := by
  have address := scratch.wordSlotNat (index := index) (by rw [scratchGeometry]; omega)
  exact Model.readable (modeled stop) (by rw [address, scratchGeometry]; omega)
    (by rw [address, scratchGeometry]; omega)

private theorem scratchWritable (stop : Word) {index : Nat} (bound : index < 2) :
    Writable (machine stop) (scratch.wordSlot index) := by
  have address := scratch.wordSlotNat (index := index) (by rw [scratchGeometry]; omega)
  exact Model.writable (modeled stop) (by rw [address, scratchGeometry]; omega)
    (by rw [address, scratchGeometry]; omega)

private theorem strictlySorted (stop : Word) (accepted : Nat) :
    ∀ first second, first < second → second < (call stop).length.toNat →
    ((call stop).after accepted first).key.toNat < ((call stop).after accepted second).key.toNat := by
  intro first second ordered inside
  change second < 3 at inside
  rw [(call stop).after_key, (call stop).after_key]
  have cases : (first = 0 ∧ second = 1) ∨ (first = 0 ∧ second = 2) ∨
      (first = 1 ∧ second = 2) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> model_decide

private theorem modelPremises (stop : Word) (accepted : Nat) (bound : accepted ≤ 2)
    (accepts : ∀ t < accepted, (call stop).position + 1 + t < (call stop).length.toNat ∧
      ((call stop).successor t).key.toNat ≤ (call stop).limit.toNat)
    (stops : (call stop).position + 1 + accepted = (call stop).length.toNat ∨
      ((call stop).position + 1 + accepted < (call stop).length.toNat ∧
        (call stop).limit.toNat < ((call stop).successor accepted).key.toNat)) :
    Premises base Model.returnTo (machine stop) (initial stop) (call stop) scratch accepted 3 := by
  let spec := call stop
  have modeled := modeled stop
  have mode : MachineMode (machine stop) Model.returnTo :=
    { (Model.frameState (contents stop)).atSync base (initial stop) with
      returnLow := by model_decide
      returnNext := by model_decide
      ra := syncRead (base := base) (frame := Model.frame (image stop) (contents stop))
        (initial stop) (index := 1) (by model_decide) }
  obtain ⟨helperCode, rawCode, searchCode, removeCode, vectorCode⟩ := images stop
  have modelHeader := Model.modelRemoveHeader (index := 0#32) modeled (dataFree stop)
  have modelBuffer := Model.modelRemoveBuffer (index := 0#32) modeled (dataFree stop)
    (codeBytes := 0) (by model_decide) (by model_decide)
  have scaled (index : Nat) (inside : index < spec.length.toNat) :
      Element.bytes Pair * (index + 1) ≤ 0x100000 := by
    rw [pairBytes]
    change index < 3 at inside
    omega
  have pairReadable (index : Nat) (inside : index < spec.length.toNat) :
      Element.Mapped (α := Pair) (machine stop) (spec.search.wordSlot index)
        (fun region => region.attributes.readable = true) :=
    Model.elementReadable modeled (scaled index inside)
  have pairWritable (index : Nat) (inside : index < spec.length.toNat) :
      Element.Mapped (α := Pair) (machine stop) (spec.search.wordSlot index)
        (fun region => region.attributes.writable = true) :=
    Model.elementWritable modeled (scaled index inside)
  have lengthHeader : SortedMap.Search.Header (machine stop) spec.search :=
    ⟨by model_decide, modelHeader.lengthReadable, modelHeader.lengthWord⟩
  have mapKeys : SortedMap.Search.Keys (machine stop) spec.search :=
    ⟨by model_decide, modelBuffer.dataReadable, modelBuffer.dataWord, fun index inside =>
      (pairReadable index inside).1, fun index inside => (modelBuffer.live index inside).1⟩
  have frame : Frame base Model.returnTo (machine stop) (initial stop) := by
    refine ⟨(syncSync _ _).symm, rfl, mode, helperCode, by model_decide, ?_, ?_, ?_⟩
    · intro byte low high
      exact belowFrame (Nat.lt_trans (codeBelow (Or.inl ⟨low, high⟩)) (by model_decide))
    · intro offset member
      change Readable (machine stop) (frameBase stackTop + offset)
      simp only [savedOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Model.readable modeled (by decide) (by decide)
    · intro offset member
      change Writable (machine stop) (frameBase stackTop + offset)
      simp only [savedOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Model.writable modeled (by decide) (by decide)
  have entry : Entry base (machine stop) (initial stop).sp spec := by
    refine ⟨searchCode, ?_, Model.readable modeled (address := 0x2100) (by decide) (by decide),
      extraWord stop 0x2100 _ (by model_decide) (by model_decide) rfl, ?_, lengthHeader, mapKeys, ?_, ?_,
      by model_decide, Model.readable modeled (address := 0x2110) (by decide) (by decide),
      Model.readable modeled (address := 0x2114) (by decide) (by decide),
      extraWord stop 0x2110 _ (by model_decide) (by model_decide) rfl,
      extraWord stop 0x2114 _ (by model_decide) (by model_decide) rfl, ?_, by rw [position]; change 0 < 3; decide⟩
    · intro byte _ high
      change byte < 0x1308 + 52 at high
      exact belowFrame (by omega)
    · intro byte _ high
      change byte < 0x2100 + 4 at high
      exact belowFrame (by omega)
    · intro byte low _
      change 0x3000 ≤ byte at low
      exact aboveFrame (by omega)
    · intro index _ byte low _
      change 0x4000 + 8 * index ≤ byte at low
      exact aboveFrame (by omega)
    · intro byte _ high
      change byte < 0x2110 + 8 at high
      exact belowFrame (by omega)
  have collectedReadable : ∀ index < accepted, Readable (machine stop) (scratch.wordSlot index) :=
    fun _ inside => scratchReadable stop (by omega)
  have scan : Layout base (machine stop) spec scratch accepted (machine stop).mem := by
    refine ⟨rawCode, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, mapKeys.fits,
      mapKeys.readable, fun index inside => (pairReadable index inside).2, mapKeys.keyWord,
      fun index inside => (modelBuffer.live index inside).2, ?_,
      by model_decide, Model.writable modeled (address := 0x2110) (by decide) (by decide),
      Model.writable modeled (address := 0x2114) (by decide) (by decide), by model_decide,
      Model.readable modeled (address := 0x2120) (by decide) (by decide), Model.readable modeled (address := 0x2124) (by decide) (by decide),
      Model.readable modeled (address := 0x2128) (by decide) (by decide), Model.writable modeled (address := 0x2124) (by decide) (by decide),
      ?_, fun index inside => scratchWritable stop (by omega), ?_, Or.inl (by model_decide), Or.inl (by model_decide), bound⟩
    · intro byte low high written
      have := codeBelow (Or.inl ⟨low, high⟩)
      have := scanRegion stop bound written
      omega
    · intro byte _ high written
      change byte < 0x1120 + 4 * 30 at high
      have := scanRegion stop bound written
      omega
    · intro index _ byte low _ written
      change 0x4000 + 8 * index ≤ byte at low
      have := scanRegion stop bound written
      omega
    · rw [scratchGeometry]
      omega
    · intro index _
      right
      rw [scratchGeometry]
      change 0x2120 + 12 ≤ _
      omega
  have drain : DrainLayout base (machine stop) spec 3 (spec.after accepted) scratch accepted
      (frameBase stackTop) (machine stop).mem := by
    refine ⟨removeCode, searchCode, vectorCode, ?_, by model_decide, ?_, ?_,
      Or.inr (by model_decide), ?_, Or.inl (by model_decide), Or.inl (by model_decide), Or.inl (by model_decide),
      by model_decide, mapKeys.dataReadable, lengthHeader.lengthReadable, modelHeader.capacityReadable,
      modelBuffer.lengthWritable, mapKeys.dataWord, modelHeader.capacityWord, Or.inl (by model_decide),
      Or.inr (by model_decide), mapKeys.fits, mapKeys.readable, fun index _ inside => pairReadable index inside,
      fun index _ inside => pairWritable index (by omega), ?_, ?_, strictlySorted stop accepted,
      by model_decide, ?_, scan.slotsFit, by omega, collectedReadable, ?_⟩
    · intro byte inside
      refine ⟨rfl, fun written => ?_⟩
      have := codeBelow inside
      have := drainRegion stop written
      omega
    · intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact Model.readable modeled (by model_decide) (by model_decide)
    · intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact Model.writable modeled (by model_decide) (by model_decide)
    · intro index _
      right
      change 0x27d0 ≤ 0x4000 + 8 * index
      omega
    · intro index _
      right
      change 0x3000 + 12 ≤ 0x4000 + 8 * index
      omega
    · intro index _ _
      right
      change 0x1198 + 100 ≤ 0x4000 + 8 * index
      omega
    · rw [position]
      change 0 + 1 + accepted ≤ 3
      omega
    · intro index inside byte low high written
      rw [scratchGeometry] at low high
      have := drainRegion stop written
      omega
  refine ⟨frame, ⟨rfl, rfl, rfl, rfl, rfl⟩, entry, scan, drain, accepts, stops,
    extraWord stop 0x2120 _ (by model_decide) (by model_decide) rfl,
    extraWord stop 0x2124 _ (by model_decide) (by model_decide) rfl,
    extraWord stop 0x2128 _ (by model_decide) (by model_decide) rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [position]
    exact Model.writable modeled (address := 0x4004) (by decide) (by decide)
  · intro byte _ high
    change byte < 0x1120 + 4 * 30 at high
    exact belowFrame (by omega)
  · intro byte inside
    exact belowFrame (Nat.lt_trans (codeBelow inside) (by model_decide))
  · intro byte _ high
    change byte < 0x2120 + 12 at high
    exact belowFrame (by omega)
  · intro byte _ high
    rw [scratchGeometry] at high
    exact belowFrame (by omega)
  · intro byte low _
    change 0x3000 ≤ byte at low
    exact aboveFrame (by omega)
  · intro byte inside
    unfold InEnd at inside
    rw [position, slotGeometry] at inside
    exact aboveFrame (by omega)
  · intro byte inside written
    have := codeBelow inside
    have := scanRegion stop bound written
    omega
  · intro byte low _ written
    change 0x3000 ≤ byte at low
    have := scanRegion stop bound written
    omega
  · intro byte inside
    unfold InEnd at inside
    rw [position, slotGeometry] at inside
    refine ⟨fun written => ?_, fun code => ?_, ?_, ?_⟩
    · have := scanRegion stop bound written
      omega
    · have := codeBelow code
      omega
    · change ¬ (0x2120 ≤ byte ∧ byte < 0x2120 + 12)
      omega
    · change ¬ (0x3000 ≤ byte ∧ byte < 0x3000 + 12)
      omega
  · intro byte low high written
    change 0x2120 ≤ byte at low
    change byte < 0x2120 + 12 at high
    have := drainRegion stop written
    omega
  · intro byte low high written
    change 0x2110 ≤ byte at low
    change byte < 0x2110 + 8 at high
    have := drainRegion stop written
    omega

private theorem gapWithoutDeletion :
    Premises base Model.returnTo (machine 9) (initial 9) (call 9) scratch 0 3 :=
  modelPremises 9 0 (by decide) (fun index inside => by omega) (by decide)

private theorem growthThenGap :
    Premises base Model.returnTo (machine 11) (initial 11) (call 11) scratch 1 3 :=
  modelPremises 11 1 (by decide) (by
    intro index inside
    have zero : index = 0 := by omega
    subst index
    decide) (by decide)

private theorem growthAtEnd :
    Premises base Model.returnTo (machine 20) (initial 20) (call 20) scratch 2 3 :=
  modelPremises 20 2 (by decide) (by
    intro index inside
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> decide) (by decide)

private theorem maximumAtEnd :
    Premises base Model.returnTo (machine 0xffffffff) (initial 0xffffffff)
      (call 0xffffffff) scratch 2 3 :=
  modelPremises 0xffffffff 2 (by decide) (by
    intro index inside
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> decide) (by decide)

-- Keep the concrete entry and return together so every witness applies
-- the same theorem used by callers.
private def Returns (stop : Word) (accepted : Nat) : Prop :=
  ∃ state : Snapshot, ∃ memory : ByteMemory,
    run ((call stop).helperCount 3 accepted) (machine stop) =
      some (sync base { machine stop with mem := memory }
        (restore (initial stop) state (Model.returnTo - base))) ∧
    ResultMemory stackTop (call stop) scratch accepted (machine stop).mem memory

theorem pathWitnesses :
    Returns 9 0 ∧ Returns 11 1 ∧ Returns 20 2 ∧ Returns 0xffffffff 2 :=
  ⟨gapWithoutDeletion.run, growthThenGap.run, growthAtEnd.run, maximumAtEnd.run⟩

theorem branchWitnesses :
    ¬ (call 9).extended 0 ∧ (call 11).extended 1 ∧ (call 20).extended 2 ∧
      ¬ (call 0xffffffff).extended 2 ∧
      (call 0xffffffff).finalLow 2 = 0xfffffffc ∧ (call 0xffffffff).finalHigh 2 = 0 := by
  decide

end Riscfree.RangeInsert.DeleteExtra.Nonvacuity
