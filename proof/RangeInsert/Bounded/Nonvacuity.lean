import RangeInsert.Bounded.Theorem
import RangeInsert.Nonempty.Contained.Nonvacuity
import RawVec.Model

/-! The bounded theorem's premises hold on a concrete machine with every
linked bounded image, for each execution path and each capacity outcome,
including zero scratch capacity and a full map. The layout part is adapted
from the trapping routine's witness: the helper is 12 bytes longer, so the
entry point starts at 0x15e0 and every shared routine keeps its address. -/

namespace Riscfree.RangeInsert.Bounded.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec
open OuterLayout
open Unified
open Nonempty (Call Span MapStorage ScratchStorage CacheStorage StackSpace Represents mapAllocation Path)
open RangeSetBlazeValidation RangeSetBlazeValidation.RangeSetBlaze

set_option maxRecDepth 8192

private def base : Word := 0x15e0
private def stackTop : Word := 0x2800

private theorem pairInsertLength : RawVec.PairInsert.instructions.length = 33 := rfl
private theorem scratchInsertLength : RawVec.instructions.length = 30 := rfl
private theorem pairRemoveLength : RawVec.PairRemove.instructions.length = 25 := rfl
private theorem mapInsertLength : SortedMap.Insert.instructions.length = 44 := rfl
private theorem lowerLength : (SortedMap.Search.instructions .lower).length = 13 := rfl
private theorem mapRemoveLength : SortedMap.Remove.instructions.length = 36 := rfl
private theorem upperLength : (SortedMap.Search.instructions .upper).length = 13 := rfl
private theorem helperLength : DeleteTable.instructions.length = 120 := rfl
private theorem entryLength : InsertTable.instructions.length = 116 := rfl

private def image : Model.Image where
  word index :=
    if index < 0x448 then Model.tableWord 0x427 RawVec.PairInsert.instructions index
    else if index < 0x466 then Model.tableWord 0x448 RawVec.instructions index
    else if index < 0x47f then Model.tableWord 0x466 RawVec.PairRemove.instructions index
    else if index < 0x4c2 then Model.tableWord 0x496 SortedMap.Insert.instructions index
    else if index < 0x4cf then Model.tableWord 0x4c2 (SortedMap.Search.instructions .lower) index
    else if index < 0x4f3 then Model.tableWord 0x4cf SortedMap.Remove.instructions index
    else if index < 0x500 then Model.tableWord 0x4f3 (SortedMap.Search.instructions .upper) index
    else if index < 0x578 then Model.tableWord 0x500 DeleteTable.instructions index
    else if index < 0x5ec then Model.tableWord 0x578 InsertTable.instructions index
    else if index = 0x940 then some 15
    else if index = 0x941 then some 0
    else none
  keys := List.range' 0x109c (0x17b0 - 0x109c) ++ List.range' 0x2500 8

private def entries (index : Nat) : Pair :=
  match index with
  | 0 => ⟨4, 9⟩
  | 1 => ⟨12, 16⟩
  | _ => ⟨20, 23⟩

private def call (start stop : Word) : Nonempty.Call := ⟨0x3000, 3, 0x4000, entries, start, stop⟩
private def contents (capacity : Word) : Model.Contents Pair := ⟨3, capacity, entries⟩

private def initial (start stop room : Word) : Empty.Snapshot :=
  { ra := Model.returnTo, sp := stackTop, s0 := 17, s1 := 18, s2 := 19, s3 := 20, s4 := 21, s5 := 22,
    a0 := 0x3000, a1 := 0x2500, a2 := start, a3 := stop, a4 := 0x6000, a5 := room }

/-- The witnessed capacities: a map allocation of three or four entries and
up to three scratch words, including none. -/
structure Sizes (capacity room : Word) : Prop where
  atLeast : 3 ≤ capacity.toNat
  atMost : capacity.toNat ≤ 4
  scratch : room.toNat ≤ 3

private def machine (start stop capacity room : Word) : Machine :=
  sync base (Model.frame image (contents capacity)) (initial start stop room)

private theorem modeled (start stop capacity room : Word) :
    Model.Modeled image (contents capacity) (machine start stop capacity room) :=
  Model.syncModeled _ base _

private theorem modelCode {capacity : Word} {machine : Machine}
    (modeled : Model.Modeled image (contents capacity) machine) :
    CodeImages base machine := by
  have entry := Model.tableImage modeled InsertTable.instructions (0x15e0#32) 0x15e0
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [entryLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [entryLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x15e0 / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x15e0 / 4 + index < 0x466 by omega),
        if_neg (show ¬ 0x15e0 / 4 + index < 0x47f by omega),
        if_neg (show ¬ 0x15e0 / 4 + index < 0x4c2 by omega),
        if_neg (show ¬ 0x15e0 / 4 + index < 0x4cf by omega),
        if_neg (show ¬ 0x15e0 / 4 + index < 0x4f3 by omega),
        if_neg (show ¬ 0x15e0 / 4 + index < 0x500 by omega),
        if_neg (show ¬ 0x15e0 / 4 + index < 0x578 by omega),
        if_pos (show 0x15e0 / 4 + index < 0x5ec by omega)]
      exact Model.tableWordAt _ _ inside)
  have helper := Model.tableImage modeled DeleteTable.instructions (0x1400#32) 0x1400
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [helperLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [helperLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x1400 / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x1400 / 4 + index < 0x466 by omega),
        if_neg (show ¬ 0x1400 / 4 + index < 0x47f by omega),
        if_neg (show ¬ 0x1400 / 4 + index < 0x4c2 by omega),
        if_neg (show ¬ 0x1400 / 4 + index < 0x4cf by omega),
        if_neg (show ¬ 0x1400 / 4 + index < 0x4f3 by omega),
        if_neg (show ¬ 0x1400 / 4 + index < 0x500 by omega),
        if_pos (show 0x1400 / 4 + index < 0x578 by omega)]
      exact Model.tableWordAt _ _ inside)
  have upper := Model.tableImage modeled (SortedMap.Search.instructions .upper) (0x13cc#32) 0x13cc
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [upperLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [upperLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x13cc / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x13cc / 4 + index < 0x466 by omega),
        if_neg (show ¬ 0x13cc / 4 + index < 0x47f by omega),
        if_neg (show ¬ 0x13cc / 4 + index < 0x4c2 by omega),
        if_neg (show ¬ 0x13cc / 4 + index < 0x4cf by omega),
        if_neg (show ¬ 0x13cc / 4 + index < 0x4f3 by omega),
        if_pos (show 0x13cc / 4 + index < 0x500 by omega)]
      exact Model.tableWordAt _ _ inside)
  have lower := Model.tableImage modeled (SortedMap.Search.instructions .lower) (0x1308#32) 0x1308
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [lowerLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [lowerLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x1308 / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x1308 / 4 + index < 0x466 by omega),
        if_neg (show ¬ 0x1308 / 4 + index < 0x47f by omega),
        if_neg (show ¬ 0x1308 / 4 + index < 0x4c2 by omega),
        if_pos (show 0x1308 / 4 + index < 0x4cf by omega)]
      exact Model.tableWordAt _ _ inside)
  have mapInsert := Model.tableImage modeled SortedMap.Insert.instructions (0x1258#32) 0x1258
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [mapInsertLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [mapInsertLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x1258 / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x1258 / 4 + index < 0x466 by omega),
        if_neg (show ¬ 0x1258 / 4 + index < 0x47f by omega),
        if_pos (show 0x1258 / 4 + index < 0x4c2 by omega)]
      exact Model.tableWordAt _ _ inside)
  have mapRemove := Model.tableImage modeled SortedMap.Remove.instructions (0x133c#32) 0x133c
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [mapRemoveLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [mapRemoveLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x133c / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x133c / 4 + index < 0x466 by omega),
        if_neg (show ¬ 0x133c / 4 + index < 0x47f by omega),
        if_neg (show ¬ 0x133c / 4 + index < 0x4c2 by omega),
        if_neg (show ¬ 0x133c / 4 + index < 0x4cf by omega),
        if_pos (show 0x133c / 4 + index < 0x4f3 by omega)]
      exact Model.tableWordAt _ _ inside)
  have scratchInsert := Model.tableImage modeled RawVec.instructions (0x1120#32) 0x1120
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [scratchInsertLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [scratchInsertLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x1120 / 4 + index < 0x448 by omega),
        if_pos (show 0x1120 / 4 + index < 0x466 by omega)]
      exact Model.tableWordAt _ _ inside)
  have pairInsert := Model.tableImage modeled RawVec.PairInsert.instructions (0x109c#32) 0x109c
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [pairInsertLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [pairInsertLength] at bound
      unfold image
      simp only [if_pos (show 0x109c / 4 + index < 0x448 by omega)]
      exact Model.tableWordAt _ _ inside)
  have pairRemove := Model.tableImage modeled RawVec.PairRemove.instructions (0x1198#32) 0x1198
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [pairRemoveLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [pairRemoveLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x1198 / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x1198 / 4 + index < 0x466 by omega),
        if_pos (show 0x1198 / 4 + index < 0x47f by omega)]
      exact Model.tableWordAt _ _ inside)
  exact ⟨entry, helper, upper, lower, mapInsert, mapRemove, scratchInsert, pairInsert, pairRemove⟩

private theorem dataFree (index : Nat) (above : 0xc00 ≤ index) : image.word index = none := by
  have lt (limit : Nat) (bound : limit < 0xc00) : ¬ index < limit := by omega
  have neq (limit : Nat) (bound : limit < 0xc00) : index ≠ limit := by omega
  unfold image
  simp only [if_neg (lt 0x448 (by decide)), if_neg (lt 0x466 (by decide)),
    if_neg (lt 0x47f (by decide)), if_neg (lt 0x4c2 (by decide)),
    if_neg (lt 0x4cf (by decide)), if_neg (lt 0x4f3 (by decide)),
    if_neg (lt 0x500 (by decide)), if_neg (lt 0x578 (by decide)),
    if_neg (lt 0x5ec (by decide)), if_neg (neq 0x940 (by decide)), if_neg (neq 0x941 (by decide))]

private theorem cacheWord {capacity : Word} {machine : Machine}
    (modeled : Model.Modeled image (contents capacity) machine)
    (address : Nat) (value : Word) (low : 0x2500 ≤ address) (high : address + 4 ≤ 0x2508)
    (aligned : address % 4 = 0) (choice : image.word (address / 4) = some value) :
    WordAt machine.mem address value := by
  rw [modeled.mem]
  have word := wordMemoryWord (Model.keys image (contents capacity)) (Model.contents image (contents capacity))
    address aligned (by
      intro byte within
      simp only [Model.keys, image, List.mem_append, List.mem_range'_1]
      omega)
  rw [Model.contents, choice, Option.getD_some] at word
  exact word

private theorem mapStorage (start stop capacity room : Word) (sizes : Sizes capacity room) :
    MapStorage (machine start stop capacity room) (call start stop) capacity := by
  have modeled := modeled start stop capacity room
  have header := Model.modelRemoveHeader (index := 0) modeled dataFree
  have buffer := Model.modelRemoveBuffer (index := 0) modeled dataFree (codeBytes := 0) (by decide) (by decide)
  have atMost := sizes.atMost
  refine ⟨by exact of_decide_eq_true rfl, ?_, by exact of_decide_eq_true rfl, ?_, ?_, buffer.lengthWritable,
    buffer.dataWord, header.lengthWord, header.capacityWord, buffer.live, ?_, ?_⟩
  · change 0x4000 + 8 * capacity.toNat ≤ 2 ^ 32
    omega
  · exact sizes.atLeast
  · intro offset member
    change Readable (machine start stop capacity room) (0x3000#32 + offset)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact Model.readable modeled (by decide) (by decide)
  · intro index inside
    have small : Element.bytes Pair * (index + 1) ≤ 0x100000 := by
      rw [pairBytes]
      omega
    exact Model.elementReadable modeled small
  · intro index inside
    have small : Element.bytes Pair * (index + 1) ≤ 0x100000 := by
      rw [pairBytes]
      omega
    exact Model.elementWritable modeled small

private theorem scratchStorage (start stop capacity room : Word) (sizes : Sizes capacity room) :
    ScratchStorage (machine start stop capacity room) ⟨0x6000, room⟩ := by
  let scratch : DeleteExtra.Scratch := ⟨0x6000, room⟩
  have bound := sizes.scratch
  have geometry (index : Nat) (within : index < room.toNat) :
      (scratch.wordSlot index).toNat % 4 = 0 ∧ (scratch.wordSlot index).toNat + 4 ≤ 2 ^ 32 := by
    have withinAddress : scratch.slot index < 2 ^ 32 := by
      change 0x6000 + 4 * index < 2 ^ 32
      omega
    rw [scratch.wordSlotNat withinAddress]
    change (0x6000 + 4 * index) % 4 = 0 ∧ 0x6000 + 4 * index + 4 ≤ 2 ^ 32
    omega
  refine ⟨?_, fun index inside => Model.readable (modeled start stop capacity room)
    (geometry index inside).1 (geometry index inside).2,
    fun index inside => Model.writable (modeled start stop capacity room)
      (geometry index inside).1 (geometry index inside).2⟩
  change 0x6000 + 4 * room.toNat ≤ 2 ^ 32
  omega

private theorem stackStorage (start stop capacity room : Word) :
    StackSpace (machine start stop capacity room) stackTop := by
  have geometry (words : Nat) (high : words ≤ 28) :
      (stackTop - BitVec.ofNat 32 (4 * words)).toNat % 4 = 0 ∧
        (stackTop - BitVec.ofNat 32 (4 * words)).toNat + 4 ≤ 2 ^ 32 := by
    have natural : (BitVec.ofNat 32 (4 * words)).toNat = 4 * words := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have ordered : BitVec.ofNat 32 (4 * words) ≤ stackTop := BitVec.le_def.mpr (by
      rw [natural]
      change 4 * words ≤ 0x2800
      omega)
    rw [BitVec.toNat_sub_of_le ordered, natural]
    change (0x2800 - 4 * words) % 4 = 0 ∧ 0x2800 - 4 * words + 4 ≤ 2 ^ 32
    omega
  exact ⟨by decide, fun words _ high => Model.readable (modeled start stop capacity room)
    (geometry words high).1 (geometry words high).2,
    fun words _ high => Model.writable (modeled start stop capacity room) (geometry words high).1 (geometry words high).2⟩

private theorem cacheStorage (start stop capacity room : Word) :
    CacheStorage (machine start stop capacity room) 0x2500 15 0 := by
  have modeled := modeled start stop capacity room
  exact ⟨by decide, ⟨Model.readable modeled (by decide) (by decide), Model.readable modeled (by decide) (by decide)⟩,
    ⟨Model.writable modeled (by decide) (by decide), Model.writable modeled (by decide) (by decide)⟩,
    cacheWord modeled 0x2500 15 (by decide) (by decide) (by decide) (by decide),
    cacheWord modeled 0x2504 0 (by decide) (by decide) (by decide) (by decide)⟩

private theorem disjointBefore {left right : Span} (before : left.start + left.size ≤ right.start) :
    left.Disjoint right := by
  intro byte leftIn rightIn
  unfold Span.Contains at leftIn rightIn
  omega

private theorem separation (start stop capacity room : Word) (sizes : Sizes capacity room) :
    Separation base stackTop (call start stop) capacity 0x2500 ⟨0x6000, room⟩ := by
  have atMost := sizes.atMost
  have scratchBound := sizes.scratch
  have mapEnd : (mapAllocation (call start stop) capacity).start +
      (mapAllocation (call start stop) capacity).size ≤ 0x4020 := by
    change 0x4000 + 8 * capacity.toNat ≤ 0x4020
    omega
  refine ⟨disjointBefore (by exact of_decide_eq_true rfl), (disjointBefore (by exact of_decide_eq_true rfl)).symm,
    disjointBefore (by exact of_decide_eq_true rfl), (disjointBefore (by exact of_decide_eq_true rfl)).symm,
    (disjointBefore (by exact of_decide_eq_true rfl)).symm, disjointBefore (mapEnd.trans (by change 0x4020 ≤ (0x6000#32).toNat; decide)),
    (disjointBefore (by exact of_decide_eq_true rfl)).symm, disjointBefore (by exact of_decide_eq_true rfl),
    disjointBefore (by exact of_decide_eq_true rfl), (disjointBefore (by exact of_decide_eq_true rfl)).symm, ?_⟩
  have imageEnd (span : Span) (member : span ∈ linkedCode base) : span.start + span.size ≤ 0x17b0 := by
    simp only [linkedCode, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro span member
  have last := imageEnd span member
  refine ⟨disjointBefore ?_, disjointBefore ?_, disjointBefore ?_, disjointBefore ?_, disjointBefore ?_⟩
  · exact last.trans (by exact of_decide_eq_true rfl)
  · exact last.trans (by exact of_decide_eq_true rfl)
  · exact last.trans (by exact of_decide_eq_true rfl)
  · exact last.trans (by exact of_decide_eq_true rfl)
  · exact last.trans (by exact of_decide_eq_true rfl)

private theorem layout (start stop capacity room : Word) (sizes : Sizes capacity room) :
    InitialLayout base (machine start stop capacity room) (initial start stop room) (call start stop)
      capacity 15 0 :=
  ⟨modelCode (modeled start stop capacity room), mapStorage start stop capacity room sizes,
    scratchStorage start stop capacity room sizes, cacheStorage start stop capacity room,
    stackStorage start stop capacity room, separation start stop capacity room sizes⟩

private theorem mode (start stop capacity room : Word) :
    MachineMode (machine start stop capacity room) Model.returnTo :=
  { (Model.frameState (contents capacity)).atSync base (initial start stop room) with
    returnLow := by decide
    returnNext := by decide
    ra := syncRead (base := base) (frame := Model.frame image (contents capacity))
      (initial start stop room) (index := 1) (by decide) }

private theorem entry (start stop capacity room : Word) :
    machine start stop capacity room =
      sync base (machine start stop capacity room) { initial start stop room with pc := 0 } :=
  (syncSync _ _).symm

/-! ## The bundled premises -/

open Nonempty.Contained.Nonvacuity (threeRanges)

private theorem representsThree (start stop : Word) : Represents threeRanges (call start stop) :=
  show Represents threeRanges (call 0 0) by unfold Represents; decide +kernel

private theorem accurateThree : (BitVec.append (0#32) (15#32)).toNat = threeRanges.cardinality := by
  decide +kernel

/-- The bundle holds for every input range, map capacity 3 or 4, and up to
three scratch words. -/
theorem insertionSatisfiable (start stop capacity room : Word) (sizes : Sizes capacity room) :
    InsertionPremises base Model.returnTo (machine start stop capacity room) (initial start stop room)
      (call start stop) capacity 15 0 threeRanges :=
  ⟨entry start stop capacity room, mode start stop capacity room, ⟨rfl, rfl, rfl⟩,
    layout start stop capacity room sizes, representsThree start stop, accurateThree⟩

private def outcome (start stop capacity room : Word) : Nonempty.CapacityOutcome :=
  (call start stop).capacityOutcome (initial start stop room) 15 0 capacity

/-- The witnessed inputs cover every path and every capacity outcome. -/
theorem everyOutcome :
    (call 11 10).path = .empty ∧ outcome 11 10 4 3 = .success ∧
    (call 5 7).path = .contained ∧ outcome 5 7 4 3 = .success ∧
    (call 10 11).path = .extension ∧ outcome 10 11 4 3 = .success ∧ outcome 10 11 4 0 = .scratchFull ∧
    (call 1 2).path = .fresh ∧ outcome 1 2 4 3 = .success ∧ outcome 1 2 3 3 = .mapFull ∧
    (call 18 19).path = .fresh ∧ outcome 18 19 4 3 = .success ∧ outcome 18 19 4 0 = .scratchFull := by
  decide

/-- The bundle invokes the bounded theorem on the concrete machine. -/
theorem modelRuns (start stop capacity room : Word) (sizes : Sizes capacity room) :
    let result := boundedResult (call start stop) (initial start stop room) capacity 15 0
    let model := threeRanges.internalAddProduction 15 (call start stop).input
    ∃ final, run result.count (machine start stop capacity room) = some final ∧
      Claims Model.returnTo (machine start stop capacity room) final (initial start stop room)
        (call start stop) capacity 15 0 ∧
      WordAt final.mem (call start stop).header.toNat (call start stop).data ∧
      WordAt final.mem ((call start stop).header.toNat + 8) capacity ∧
      (outcome start stop capacity room = .success →
        result.Represents model ∧
        model.setResult.toSet = threeRanges.toSet ∪ (call start stop).input.toSet ∧
        model.cachedLength = model.setResult.cardinality) :=
  (insertionSatisfiable start stop capacity room sizes).run

/-- A concrete machine on which the bundle holds, with the stated path and
capacity outcome. `modelRuns` then gives the bounded theorem's conclusion. -/
def Witness (start stop capacity room : Word) (path : Path) (result : Nonempty.CapacityOutcome) : Prop :=
  (call start stop).path = path ∧ outcome start stop capacity room = result ∧
    InsertionPremises base Model.returnTo (machine start stop capacity room) (initial start stop room)
      (call start stop) capacity 15 0 threeRanges

/-- Every path and every capacity outcome has a witness: the four
successful paths (two causes of fresh insertion), a full map, and zero
scratch on both modifying paths. -/
theorem allOutcomes :
    Witness 11 10 4 3 .empty .success ∧ Witness 5 7 4 3 .contained .success ∧
    Witness 10 11 4 3 .extension .success ∧ Witness 10 11 4 0 .extension .scratchFull ∧
    Witness 1 2 4 3 .fresh .success ∧ Witness 1 2 3 3 .fresh .mapFull ∧
    Witness 18 19 4 3 .fresh .success ∧ Witness 18 19 4 0 .fresh .scratchFull := by
  have large : Sizes 4 3 := ⟨by decide, by decide, by decide⟩
  have noScratch : Sizes 4 0 := ⟨by decide, by decide, by decide⟩
  have fullMap : Sizes 3 3 := ⟨by decide, by decide, by decide⟩
  obtain ⟨empty, emptyOk, contained, containedOk, extension, extensionOk, extensionFull,
    first, firstOk, firstFull, gap, gapOk, gapFull⟩ := everyOutcome
  exact ⟨⟨empty, emptyOk, insertionSatisfiable _ _ _ _ large⟩,
    ⟨contained, containedOk, insertionSatisfiable _ _ _ _ large⟩,
    ⟨extension, extensionOk, insertionSatisfiable _ _ _ _ large⟩,
    ⟨extension, extensionFull, insertionSatisfiable _ _ _ _ noScratch⟩,
    ⟨first, firstOk, insertionSatisfiable _ _ _ _ large⟩,
    ⟨first, firstFull, insertionSatisfiable _ _ _ _ fullMap⟩,
    ⟨gap, gapOk, insertionSatisfiable _ _ _ _ large⟩,
    ⟨gap, gapFull, insertionSatisfiable _ _ _ _ noScratch⟩⟩

end Riscfree.RangeInsert.Bounded.Nonvacuity
