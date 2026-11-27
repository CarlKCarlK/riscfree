import RangeInsert.Correct
import RawVec.Model

/-! A machine with every linked image and the shared stack, cache, scratch,
and map regions. Its same memory layout serves both modifying prefixes. -/

namespace Riscfree.RangeInsert.Nonempty.Layout.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec

private def base : Word := 0x15d4
private def stackTop : Word := 0x2800

private theorem pairInsertLength : RawVec.PairInsert.instructions.length = 33 := rfl
private theorem scratchInsertLength : RawVec.instructions.length = 30 := rfl
private theorem pairRemoveLength : RawVec.PairRemove.instructions.length = 25 := rfl
private theorem mapInsertLength : SortedMap.Insert.instructions.length = 44 := rfl
private theorem lowerLength : (SortedMap.Search.instructions .lower).length = 13 := rfl
private theorem mapRemoveLength : SortedMap.Remove.instructions.length = 36 := rfl
private theorem upperLength : (SortedMap.Search.instructions .upper).length = 13 := rfl
private theorem helperLength : DeleteTable.instructions.length = 117 := rfl
private theorem entryLength : InsertTable.instructions.length = 109 := rfl

private def image : Model.Image where
  word index :=
    if index < 0x448 then Model.tableWord 0x427 RawVec.PairInsert.instructions index
    else if index < 0x466 then Model.tableWord 0x448 RawVec.instructions index
    else if index < 0x47f then Model.tableWord 0x466 RawVec.PairRemove.instructions index
    else if index < 0x4c2 then Model.tableWord 0x496 SortedMap.Insert.instructions index
    else if index < 0x4cf then Model.tableWord 0x4c2 (SortedMap.Search.instructions .lower) index
    else if index < 0x4f3 then Model.tableWord 0x4cf SortedMap.Remove.instructions index
    else if index < 0x500 then Model.tableWord 0x4f3 (SortedMap.Search.instructions .upper) index
    else if index < 0x575 then Model.tableWord 0x500 DeleteTable.instructions index
    else if index < 0x5e2 then Model.tableWord 0x575 InsertTable.instructions index
    else if index = 0x940 then some 15
    else if index = 0x941 then some 0
    else none
  keys := List.range' 0x109c (0x1788 - 0x109c) ++ List.range' 0x2500 8

private def entries (index : Nat) : Pair :=
  match index with
  | 0 => ⟨4, 9⟩
  | 1 => ⟨12, 16⟩
  | _ => ⟨20, 23⟩

private def call (start stop : Word) : Call := ⟨0x3000, 3, 0x4000, entries, start, stop⟩
private def contents : Model.Contents Pair := ⟨3, 4, entries⟩

private def initial (start stop : Word) : Empty.Snapshot :=
  { ra := Model.returnTo, sp := stackTop, s0 := 17, s1 := 18, s2 := 19, s3 := 20, s4 := 21, s5 := 22,
    a0 := 0x3000, a1 := 0x2500, a2 := start, a3 := stop, a4 := 0x6000, a5 := 3 }

private def machine (start stop : Word) : Machine :=
  sync base (Model.frame image contents) (initial start stop)

private theorem modeled (start stop : Word) : Model.Modeled image contents (machine start stop) :=
  Model.syncModeled _ base _

private theorem modelCode {machine : Machine} (modeled : Model.Modeled image contents machine) :
    CodeImages base machine := by
  have entry := Model.tableImage modeled InsertTable.instructions (0x15d4#32) 0x15d4
    rfl (by decide) (by decide) (by
      intro index inside byte small
      rw [entryLength] at inside
      simp only [image, List.mem_append, List.mem_range'_1]
      exact Or.inl (by omega)) (by
      intro index inside
      have bound := inside
      rw [entryLength] at bound
      unfold image
      simp only [if_neg (show ¬ 0x15d4 / 4 + index < 0x448 by omega),
        if_neg (show ¬ 0x15d4 / 4 + index < 0x466 by omega),
        if_neg (show ¬ 0x15d4 / 4 + index < 0x47f by omega),
        if_neg (show ¬ 0x15d4 / 4 + index < 0x4c2 by omega),
        if_neg (show ¬ 0x15d4 / 4 + index < 0x4cf by omega),
        if_neg (show ¬ 0x15d4 / 4 + index < 0x4f3 by omega),
        if_neg (show ¬ 0x15d4 / 4 + index < 0x500 by omega),
        if_neg (show ¬ 0x15d4 / 4 + index < 0x575 by omega),
        if_pos (show 0x15d4 / 4 + index < 0x5e2 by omega)]
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
        if_pos (show 0x1400 / 4 + index < 0x575 by omega)]
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
    if_neg (lt 0x500 (by decide)), if_neg (lt 0x575 (by decide)),
    if_neg (lt 0x5e2 (by decide)), if_neg (neq 0x940 (by decide)), if_neg (neq 0x941 (by decide))]

private theorem cacheWord {machine : Machine} (modeled : Model.Modeled image contents machine)
    (address : Nat) (value : Word) (low : 0x2500 ≤ address) (high : address + 4 ≤ 0x2508)
    (aligned : address % 4 = 0) (choice : image.word (address / 4) = some value) :
    WordAt machine.mem address value := by
  rw [modeled.mem]
  have word := wordMemoryWord (Model.keys image contents) (Model.contents image contents)
    address aligned (by
      intro byte within
      simp only [Model.keys, image, List.mem_append, List.mem_range'_1]
      omega)
  rw [Model.contents, choice, Option.getD_some] at word
  exact word

private theorem mapStorage (start stop : Word) : MapStorage (machine start stop) (call start stop) 4 := by
  have modeled := modeled start stop
  have header := Model.modelRemoveHeader (index := 0) modeled dataFree
  have buffer := Model.modelRemoveBuffer (index := 0) modeled dataFree (codeBytes := 0) (by decide) (by decide)
  refine ⟨by exact of_decide_eq_true rfl, by exact of_decide_eq_true rfl, by exact of_decide_eq_true rfl, by exact of_decide_eq_true rfl, ?_, buffer.lengthWritable, buffer.dataWord,
    header.lengthWord, header.capacityWord, buffer.live, ?_, ?_⟩
  · intro offset member
    change Readable (machine start stop) (0x3000#32 + offset)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact Model.readable modeled (by decide) (by decide)
  · intro index inside
    have small : Element.bytes Pair * (index + 1) ≤ 0x100000 := by
      rw [pairBytes]
      change index < 4 at inside
      omega
    exact Model.elementReadable modeled small
  · intro index inside
    have small : Element.bytes Pair * (index + 1) ≤ 0x100000 := by
      rw [pairBytes]
      change index < 4 at inside
      omega
    exact Model.elementWritable modeled small

private theorem scratchStorage (start stop : Word) :
    ScratchStorage (machine start stop) ⟨0x6000, 3⟩ := by
  let scratch : DeleteExtra.Scratch := ⟨0x6000, 3⟩
  have geometry (index : Nat) (within : index < 3) :
      (scratch.wordSlot index).toNat % 4 = 0 ∧ (scratch.wordSlot index).toNat + 4 ≤ 2 ^ 32 := by
    have withinAddress : scratch.slot index < 2 ^ 32 := by
      change 0x6000 + 4 * index < 2 ^ 32
      omega
    rw [scratch.wordSlotNat withinAddress]
    change (0x6000 + 4 * index) % 4 = 0 ∧ 0x6000 + 4 * index + 4 ≤ 2 ^ 32
    omega
  exact ⟨by decide, fun index inside => Model.readable (modeled start stop)
    (geometry index inside).1 (geometry index inside).2,
    fun index inside => Model.writable (modeled start stop) (geometry index inside).1 (geometry index inside).2⟩

private theorem stackStorage (start stop : Word) : StackSpace (machine start stop) stackTop := by
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
  exact ⟨by decide, fun words _ high => Model.readable (modeled start stop)
    (geometry words high).1 (geometry words high).2,
    fun words _ high => Model.writable (modeled start stop) (geometry words high).1 (geometry words high).2⟩

private theorem cacheStorage (start stop : Word) : CacheStorage (machine start stop) 0x2500 15 0 := by
  have modeled := modeled start stop
  exact ⟨by decide, ⟨Model.readable modeled (by decide) (by decide), Model.readable modeled (by decide) (by decide)⟩,
    ⟨Model.writable modeled (by decide) (by decide), Model.writable modeled (by decide) (by decide)⟩,
    cacheWord modeled 0x2500 15 (by decide) (by decide) (by decide) (by decide),
    cacheWord modeled 0x2504 0 (by decide) (by decide) (by decide) (by decide)⟩

private theorem disjointBefore {left right : Span} (before : left.start + left.size ≤ right.start) :
    left.Disjoint right := by
  intro byte leftIn rightIn
  unfold Span.Contains at leftIn rightIn
  omega

private theorem separation (start stop : Word) :
    Separation base stackTop (call start stop) 4 0x2500 ⟨0x6000, 3⟩ := by
  refine ⟨disjointBefore (by exact of_decide_eq_true rfl), (disjointBefore (by exact of_decide_eq_true rfl)).symm, disjointBefore (by exact of_decide_eq_true rfl),
    (disjointBefore (by exact of_decide_eq_true rfl)).symm, (disjointBefore (by exact of_decide_eq_true rfl)).symm, disjointBefore (by exact of_decide_eq_true rfl),
    (disjointBefore (by exact of_decide_eq_true rfl)).symm, disjointBefore (by exact of_decide_eq_true rfl), disjointBefore (by exact of_decide_eq_true rfl),
    (disjointBefore (by exact of_decide_eq_true rfl)).symm, ?_⟩
  have imageEnd (span : Span) (member : span ∈ linkedCode base) : span.start + span.size ≤ 0x1788 := by
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

private theorem layout (start stop : Word) :
    InitialLayout base (machine start stop) (initial start stop) (call start stop) 4 15 0 :=
  ⟨modelCode (modeled start stop), mapStorage start stop, scratchStorage start stop, cacheStorage start stop,
    stackStorage start stop, separation start stop⟩

private theorem mode (start stop : Word) : MachineMode (machine start stop) Model.returnTo :=
  { (Model.frameState contents).atSync base (initial start stop) with
    returnLow := by decide
    returnNext := by decide
    ra := syncRead (base := base) (frame := Model.frame image contents)
      (initial start stop) (index := 1) (by decide) }

private theorem entry (start stop : Word) :
    machine start stop = sync base (machine start stop) { initial start stop with pc := 0 } :=
  (syncSync _ _).symm

private theorem modelFresh (start stop : Word) (ordered : start.toNat ≤ stop.toNat)
    (fresh : (call start stop).rank = 0 ∨
      (0 < (call start stop).rank ∧ (call start stop).predecessor.value.toNat + 1 < start.toNat)) :
    FreshPrefix base Model.returnTo (machine start stop) (initial start stop) (call start stop) :=
  (layout start stop).freshPrefix (entry start stop) rfl (mode start stop) ⟨rfl, rfl, rfl⟩ ordered fresh

private def ReachesMapInsert (start stop : Word) : Prop :=
  ∃ state : Empty.Snapshot,
    run (insertionPrefixCount (call start stop)) (machine start stop) = some
      (sync base { (machine start stop) with mem := (freshStored (initial start stop)
        (Empty.pushed (machine start stop).mem (initial start stop))) } state) ∧
    FreshCalling base (initial start stop) (call start stop) state

private theorem fromFresh {start stop : Word}
    (premises : FreshPrefix base Model.returnTo (machine start stop) (initial start stop) (call start stop)) :
    ReachesMapInsert start stop := by
  obtain ⟨state, reached, arguments⟩ := premises.toInsert
  have initialRun := congrArg (run (insertionPrefixCount (call start stop))) (entry start stop)
  exact ⟨state, initialRun.trans reached, arguments⟩

theorem noPredecessor : ReachesMapInsert 1 2 :=
  fromFresh (modelFresh 1 2 (by decide) (Or.inl (by decide)))

theorem strictGap : ReachesMapInsert 18 19 :=
  fromFresh (modelFresh 18 19 (by decide) (Or.inr ⟨by decide, by decide⟩))

private theorem modelExtension :
    ExtensionPrefix base Model.returnTo (machine 10 11) (initial 10 11) (call 10 11) 15 0 :=
  (layout 10 11).extensionPrefix (entry 10 11) rfl (mode 10 11) ⟨rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide)

theorem adjacentReachesHelper :
    ∃ state : Empty.Snapshot,
      run (58 + (call 10 11).search.count .upper) (machine 10 11) =
        some (sync base { (machine 10 11) with mem := (extensionStored (initial 10 11) (call 10 11) 15 0
          (Empty.pushed (machine 10 11).mem (initial 10 11))) } state) ∧
      ExtensionCalling base (initial 10 11) (call 10 11) state := by
  obtain ⟨state, reached, arguments⟩ := modelExtension.toHelper
  have initialRun := congrArg (run (58 + (call 10 11).search.count .upper)) (entry 10 11)
  exact ⟨state, initialRun.trans reached, arguments⟩

private theorem adjacentSorted :
    SortedMap.Sorted (SortedMap.entriesOf (call 10 11).old (call 10 11).length.toNat) := by
  unfold SortedMap.Sorted
  decide

private theorem adjacentScratch :
    ((call 10 11).extensionHelper (initial 10 11) 15 0).acceptCount ≤ (initial 10 11).a5.toNat := by
  decide

/-- The machine merges the first two ranges, keeps the third, and returns
an accurate cache of 17 in exactly 276 instructions. -/
theorem adjacentReturns :
    ∃ final, run 276 (machine 10 11) = some final ∧
      final.regs.get? Register.PC = some Model.returnTo ∧
      WordAt final.mem 0x3004 2#32 ∧
      PairAt final.mem 0x4000 ⟨4, 16⟩ ∧ PairAt final.mem 0x4008 ⟨20, 23⟩ ∧
      WordAt final.mem 0x2500 17#32 ∧ WordAt final.mem 0x2504 0#32 := by
  obtain ⟨final, ran, returned, effects, _, _⟩ :=
    modelExtension.run (layout 10 11) adjacentSorted adjacentScratch
  have ⟨lengthWord, entries, low, high, _, _, _, _⟩ := effects
  exact ⟨final, ran, returned, lengthWord, entries 0 (by decide), entries 1 (by decide), low, high⟩

private theorem orderedRanges (start stop : Word) :
    ∀ index < (call start stop).length.toNat,
      ((call start stop).old index).key.toNat ≤ ((call start stop).old index).value.toNat := by
  intro index inside
  change index < 3 at inside
  have indices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases indices with rfl | rfl | rfl <;> exact of_decide_eq_true rfl

private theorem sortedRanges (start stop : Word) :
    SortedMap.Sorted (SortedMap.entriesOf (call start stop).old (call start stop).length.toNat) := by
  unfold SortedMap.Sorted
  exact of_decide_eq_true rfl

theorem firstRangeReturns :
    ∃ final, run 215 (machine 1 2) = some final ∧
      final.regs.get? Register.PC = some Model.returnTo ∧
      WordAt final.mem 0x3004 4#32 ∧ PairAt final.mem 0x4000 ⟨1, 2⟩ ∧
      PairAt final.mem 0x4008 ⟨4, 9⟩ ∧ PairAt final.mem 0x4010 ⟨12, 16⟩ ∧
      PairAt final.mem 0x4018 ⟨20, 23⟩ ∧ WordAt final.mem 0x2500 17#32 ∧
      WordAt final.mem 0x2504 0#32 := by
  have premises := modelFresh 1 2 (by decide) (Or.inl (by decide))
  obtain ⟨final, ran, returned, result, _, _⟩ := premises.run (layout 1 2)
    (by decide) (sortedRanges 1 2) (orderedRanges 1 2) (by decide)
  exact ⟨final, ran, returned, result.length, result.entries 0 (by decide),
    result.entries 1 (by decide), result.entries 2 (by decide), result.entries 3 (by decide),
    result.cacheLow, result.cacheHigh⟩

theorem strictGapReturns :
    ∃ final, run 364 (machine 18 19) = some final ∧
      final.regs.get? Register.PC = some Model.returnTo ∧
      WordAt final.mem 0x3004 3#32 ∧ PairAt final.mem 0x4000 ⟨4, 9⟩ ∧
      PairAt final.mem 0x4008 ⟨12, 16⟩ ∧ PairAt final.mem 0x4010 ⟨18, 23⟩ ∧
      WordAt final.mem 0x2500 17#32 ∧ WordAt final.mem 0x2504 0#32 := by
  have premises := modelFresh 18 19 (by decide) (Or.inr ⟨by decide, by decide⟩)
  obtain ⟨final, ran, returned, result, _, _⟩ := premises.run (layout 18 19)
    (by decide) (sortedRanges 18 19) (orderedRanges 18 19) (by decide)
  exact ⟨final, ran, returned, result.length, result.entries 0 (by decide),
    result.entries 1 (by decide), result.entries 2 (by decide), result.cacheLow, result.cacheHigh⟩

private def Runs (start stop : Word) (path : Path) : Prop :=
  (call start stop).path = path ∧
    ∃ final, run ((call start stop).result (initial start stop) 4 15 0).count (machine start stop) = some final ∧
      final.regs.get? Register.PC = some Model.returnTo ∧
      ((call start stop).result (initial start stop) 4 15 0).inMemory (initial start stop) (call start stop) final.mem

private theorem fromLayout (start stop : Word) (path : Path) (select : (call start stop).path = path)
    (freshRoom : (call start stop).path = .fresh →
      ((call start stop).freshHelper 4 (initial start stop) 15 0).acceptCount ≤ (initial start stop).a5.toNat)
    (extensionRoom : (call start stop).path = .extension →
      ((call start stop).extensionHelper (initial start stop) 15 0).acceptCount ≤ (initial start stop).a5.toNat) :
    Runs start stop path := by
  have premises : Nonempty.Premises base Model.returnTo (machine start stop) (initial start stop)
      (call start stop) 4 15 0 :=
    ⟨entry start stop, mode start stop, ⟨rfl, rfl, rfl⟩, layout start stop, sortedRanges start stop,
      orderedRanges start stop, fun _ => of_decide_eq_true rfl, freshRoom, extensionRoom⟩
  obtain ⟨final, ran, returned, result, _, _⟩ := premises.run
  exact ⟨select, final, ran, returned, result⟩

/-- The same top-level theorem applies to a concrete machine on every
successful branch, including both causes of fresh insertion. -/
theorem allBranches :
    Runs 11 10 .empty ∧ Runs 5 7 .contained ∧ Runs 10 11 .extension ∧
      Runs 1 2 .fresh ∧ Runs 18 19 .fresh :=
  ⟨fromLayout 11 10 .empty (by decide) (by decide) (by decide),
    fromLayout 5 7 .contained (by decide) (by decide) (by decide),
    fromLayout 10 11 .extension (by decide) (by decide) (by decide),
    fromLayout 1 2 .fresh (by decide) (by decide) (by decide),
    fromLayout 18 19 .fresh (by decide) (by decide) (by decide)⟩

end Riscfree.RangeInsert.Nonempty.Layout.Nonvacuity
