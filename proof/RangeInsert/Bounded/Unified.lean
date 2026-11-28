import RangeInsert.Bounded.EntryContained
import RangeInsert.Bounded.FreshRun
import RangeInsert.Capacity

/-! Every path of the bounded linked range insertion, for every map and
scratch capacity. The status is OK exactly when the path's transient storage
fits (`Call.capacityOutcome`); otherwise it is FULL. Either way the routine
returns to its caller with the ABI's saved registers and stack restored and
writes only the declared regions. On OK the map and cache hold the result;
on FULL the allocation can be disposed of. -/

namespace Riscfree.RangeInsert.Bounded.Unified

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Pair PairAt)
open Empty (Snapshot)
open EntryEmpty (Frame)
open OuterLayout
open Nonempty (Call Arguments Result Path CapacityOutcome MapStorage WritableByte mapHeader mapLengthWord
  stackAllocation stackDisjointOuter)

set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

/-- The entry machine, the initial layout, and a sorted map of ranges. No
capacity premise: map and scratch capacities may be anything the layout
allows, including zero. -/
structure Premises (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) (capacity low high : Word) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  mode : MachineMode original returnAddress
  arguments : Arguments initial call
  layout : InitialLayout base original initial call capacity low high
  sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)
  ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat

/-- The exact instruction count of the path and outcome that run. -/
def boundedCount (call : Call) (initial : Snapshot) (capacity low high : Word) : Nat :=
  match call.path with
  | .empty => 21
  | .contained => EntryContained.containedCount call
  | .extension =>
    let helper := call.extensionHelper initial low high
    if helper.acceptCount ≤ initial.a5.toNat then
      EntryExtension.toHelperCount call + HelperRun.successCount helper capacity helper.acceptCount + 11
    else EntryExtension.toHelperCount call + HelperRun.fullCount helper initial.a5.toNat + 11
  | .fresh =>
    let helper := call.freshHelper capacity initial low high
    if call.length = capacity then FreshPath.mapFullCount call capacity
    else if helper.acceptCount ≤ initial.a5.toNat then FreshPath.successCount call capacity helper
    else FreshPath.fullCount call capacity helper initial.a5.toNat

/-- The trapping routine's result on each path, with the bounded routine's count. -/
def boundedResult (call : Call) (initial : Snapshot) (capacity low high : Word) : Result :=
  { call.result initial capacity low high with count := boundedCount call initial capacity low high }

/-- Safe disposal after FULL: the header still names the allocation, and the
stored length is within its capacity. -/
def Disposable (call : Call) (capacity : Word) (memory : ByteMemory) : Prop :=
  ∃ length : Word, WordAt memory (call.header.toNat + 4) length ∧ length.toNat ≤ capacity.toNat

def status (outcome : CapacityOutcome) : Word :=
  if outcome = .success then 0#32 else 1#32

private theorem Premises.link {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word}
    (premises : Premises base returnAddress original initial call capacity low high) :
    initial.ra = returnAddress := by
  have read := syncRead (base := base) (frame := original) { initial with pc := 0 } (index := 1) (by decide)
  rw [← premises.entry] at read
  exact Option.some.inj ((readReg_succ.mp read).symm.trans (readReg_succ.mp premises.mode.ra))

/-- Preserving the outer frame preserves the unchanged result. -/
private theorem unchangedResult {base : Word} {original final : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high)
    (count : Nat) (keeps : ∀ byte, Empty.OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]?) :
    (Result.unchanged call count low high).inMemory initial call final.mem := by
  have header (byte : Nat) (low : call.header.toNat ≤ byte) (high : byte < call.header.toNat + 12) :
      Empty.OutsideFrame initial.sp byte :=
    stackDisjointOuter layout.stack.fits (layout.apart.headerStack byte ⟨low, high⟩)
  have cache (byte : Nat) (low : initial.a1.toNat ≤ byte) (high : byte < initial.a1.toNat + 8) :
      Empty.OutsideFrame initial.sp byte :=
    stackDisjointOuter layout.stack.fits (layout.apart.cacheStack byte ⟨low, high⟩)
  refine ⟨layout.map.lengthWord.congr (fun byte low high => keeps byte (header byte (by omega) (by omega))),
    ?_, layout.cache.low.congr (fun byte low high => keeps byte (cache byte low (by omega))),
    layout.cache.high.congr (fun byte low high => keeps byte (cache byte (by omega) (by omega)))⟩
  intro index inside
  have pair := layout.map.live index inside
  have apart (byte : Nat) (low : call.search.slot index ≤ byte) (high : byte < call.search.slot index + 8) :
      Empty.OutsideFrame initial.sp byte :=
    stackDisjointOuter layout.stack.fits (layout.apart.mapStack byte (layout.map.entryContained inside low high))
  exact ⟨pair.1.congr fun byte low high => keeps byte (apart byte low (by omega)),
    pair.2.congr fun byte low high => keeps byte (apart byte (by omega) (by omega))⟩

/-- Every byte outside the map header's length word that the routine may
not write keeps its value, so the allocation pointer and capacity survive. -/
theorem metadataKept {base : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high) {after : ByteMemory}
    (keep : ∀ byte, ¬ WritableByte initial call capacity byte → after[byte]? = original.mem[byte]?) :
    WordAt after call.header.toNat call.data ∧ WordAt after (call.header.toNat + 8) capacity := by
  apply layout.map.metadataKept
  intro byte inHeader notLength
  apply keep byte
  intro writable
  rcases writable with stack | cache | scratch | length | map
  · exact layout.apart.headerStack byte inHeader stack
  · exact layout.apart.headerCache byte inHeader cache
  · exact layout.apart.headerScratch byte inHeader scratch
  · exact notLength length
  · exact layout.apart.headerMap byte inHeader map

/-- An unchanged header leaves the original length, which fits. -/
private theorem headerDisposable {base : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high) {after : ByteMemory}
    (header : ∀ byte, (mapHeader call).Contains byte → after[byte]? = original.mem[byte]?) :
    Disposable call capacity after :=
  ⟨call.length, layout.map.lengthWord.congr fun byte low high => header byte (by
    change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
    change call.header.toNat + 4 ≤ byte at low
    change byte < call.header.toNat + 4 + 4 at high
    omega), layout.map.lengthFits⟩

/-- The claims made about the final machine. -/
structure Claims (returnAddress : Word) (original final : Machine) (initial : Snapshot) (call : Call)
    (capacity low high : Word) : Prop where
  pc : final.regs.get? Register.PC = some returnAddress
  status : final.regs.get? Register.x10 =
    some (status (call.capacityOutcome initial low high capacity))
  registers : ∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
    final.regs.get? key = original.regs.get? key
  kept : ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]?
  success : call.capacityOutcome initial low high capacity = .success →
    (boundedResult call initial capacity low high).inMemory initial call final.mem
  full : call.capacityOutcome initial low high capacity ≠ .success → Disposable call capacity final.mem

private theorem outcomeOf {call : Call} {initial : Snapshot} {low high capacity : Word}
    (valid : call.length.toNat ≤ capacity.toNat) :
    call.capacityOutcome initial low high capacity =
      if call.path = .fresh ∧ call.length = capacity then .mapFull
      else if initial.a5.toNat < call.scratchNeeded initial low high then .scratchFull
      else .success := by
  have mapShort : capacity.toNat < call.mapNeeded ↔ call.path = .fresh ∧ call.length = capacity := by
    unfold Call.mapNeeded
    by_cases fresh : call.path = .fresh
    · simp only [fresh, if_true, true_and]
      constructor
      · intro short
        exact BitVec.eq_of_toNat_eq (by omega)
      · intro same
        rw [same]
        omega
    · simp [fresh, Nat.not_lt.mpr valid]
  unfold Call.capacityOutcome
  by_cases short : capacity.toNat < call.mapNeeded
  · rw [if_pos short, if_pos (mapShort.mp short)]
  · rw [if_neg short, if_neg (fun both => short (mapShort.mpr both))]

/-- The live map and cache do not depend on the instruction count. -/
theorem boundedInMemory (call : Call) (initial : Snapshot) (capacity low high : Word) (memory : ByteMemory) :
    (boundedResult call initial capacity low high).inMemory initial call memory ↔
      (call.result initial capacity low high).inMemory initial call memory := Iff.rfl

set_option maxHeartbeats 6000000 in
/-- The bounded linked range insertion terminates after the exact count of
its path, returns at the link register with the ABI's saved registers and
stack restored, writes only the declared regions, and returns OK exactly
when the transient map and scratch storage fit. On OK the map and cache hold
the path's result; on FULL the allocation can be disposed of. -/
theorem Premises.run {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word}
    (premises : Premises base returnAddress original initial call capacity low high) :
    ∃ final, Riscfree.RV32.run (boundedResult call initial capacity low high).count original = some final ∧
      Claims returnAddress original final initial call capacity low high := by
  have layout := premises.layout
  have link := premises.link
  have frame := layout.outerFrame premises.entry link premises.mode
  have valid := layout.map.lengthFits
  have outcome := outcomeOf (initial := initial) (low := low) (high := high) valid
  have fromFrame {final : Machine}
      (keeps : ∀ byte, Empty.OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]?) :
      ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
    intro byte outside
    exact keeps byte (stackDisjointOuter layout.stack.fits (fun stack => outside (Or.inl stack)))
  have frameRegisters {final : Machine}
      (regs : ∀ key ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15],
        final.regs.get? key = original.regs.get? key) :
      ∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key := by
    intro key outside
    apply regs key
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
    tauto
  by_cases empty : call.stop.toNat < call.start.toNat
  · have path : call.path = .empty := if_pos empty
    have ok : call.capacityOutcome initial low high capacity = .success := by
      rw [outcome, if_neg (by rw [path]; simp), if_neg (by simp [Call.scratchNeeded, path])]
    let final := sync base { original with mem := Empty.pushed original.mem initial }
      (Empty.restore initial { initial with a0 := 0 } (returnAddress - base))
    have p : EntryEmpty.Premises base returnAddress original initial :=
      ⟨frame, by rw [premises.arguments.stop, premises.arguments.start]; exact empty⟩
    have keeps (byte : Nat) (outside : Empty.OutsideFrame initial.sp byte) :
        final.mem[byte]? = original.mem[byte]? := by
      rw [syncMem]
      exact Empty.pushedOutside original.mem initial frame.frameFits byte outside
    refine ⟨final, ?_, ⟨?_, ?_, ?_, fromFrame keeps, fun _ => ?_, fun failed => (failed ok).elim⟩⟩
    · rw [boundedResult, boundedCount, path]
      exact EntryEmpty.runEmpty p
    · exact Empty.returnPc (base := base) _ _ rfl
    · rw [ok]
      exact readReg_succ.mp (syncRead (base := base) (frame := { original with mem := Empty.pushed original.mem initial })
        _ (index := 10) (by decide))
    · exact frameRegisters (Empty.restoreRegisters premises.entry _ { initial with a0 := 0 } _
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    · rw [boundedInMemory, Call.result, path]
      exact unchangedResult layout 19 keeps
  have nonempty := Nat.le_of_not_gt empty
  -- The fresh path, with any map and scratch capacity.
  have fresh (select : call.path = .fresh) :
      ∃ final, Riscfree.RV32.run (boundedResult call initial capacity low high).count original = some final ∧
        Claims returnAddress original final initial call capacity low high := by
    have p := FreshPath.freshPrefix layout premises.entry link premises.mode premises.arguments nonempty select
    have count : (boundedResult call initial capacity low high).count =
        let helper := call.freshHelper capacity initial low high
        if call.length = capacity then FreshPath.mapFullCount call capacity
        else if helper.acceptCount ≤ initial.a5.toNat then FreshPath.successCount call capacity helper
        else FreshPath.fullCount call capacity helper initial.a5.toNat := by
      rw [boundedResult, boundedCount, select]
    by_cases full : call.length = capacity
    · have mapFull : call.capacityOutcome initial low high capacity = .mapFull := by
        rw [outcome, if_pos ⟨select, full⟩]
      obtain ⟨final, ran, pc, a0, regs, keeps⟩ := p.runMapFull layout premises.sorted premises.ordered full
      refine ⟨final, ?_, ⟨pc, ?_, regs, fun byte outside => keeps byte (fun stack => outside (Or.inl stack)),
        (fun ok => by rw [mapFull] at ok; cases ok), fun _ => ?_⟩⟩
      · rw [count]
        simp only [if_pos full]
        exact ran
      · rw [mapFull]; exact a0
      · exact headerDisposable layout fun byte inHeader =>
          keeps byte (layout.apart.headerStack byte inHeader)
    have spare : call.length.toNat < capacity.toNat := by
      rcases Nat.lt_or_eq_of_le valid with less | same
      · exact less
      · exact absurd (BitVec.eq_of_toNat_eq same) full
    have needed : call.scratchNeeded initial low high = (call.freshHelper capacity initial low high).acceptCount := by
      simp only [Call.scratchNeeded, select]
      rfl
    by_cases room : (call.freshHelper capacity initial low high).acceptCount ≤ initial.a5.toNat
    · have ok : call.capacityOutcome initial low high capacity = .success := by
        rw [outcome, if_neg (fun both => full both.2), needed, if_neg (by omega)]
      obtain ⟨final, ran, pc, a0, result, regs, keeps⟩ :=
        p.runSuccess layout spare premises.sorted premises.ordered room
      refine ⟨final, ?_, ⟨pc, ?_, regs, keeps, fun _ => ?_, fun failed => (failed ok).elim⟩⟩
      · rw [count]
        simp only [if_neg full, if_pos room]
        exact ran
      · rw [ok]; exact a0
      · rw [boundedInMemory, Call.result, select]
        refine ⟨result.length, ?_, result.cacheLow, result.cacheHigh⟩
        intro index inside
        rw [Result.afterHelperLength] at inside
        exact result.entries index inside
    · have scratchFull : call.capacityOutcome initial low high capacity = .scratchFull := by
        rw [outcome, if_neg (fun both => full both.2), needed, if_pos (by omega)]
      obtain ⟨final, ran, pc, a0, regs, disposable⟩ :=
        p.runFull layout spare premises.sorted premises.ordered (Nat.lt_of_not_le room)
      refine ⟨final, ?_, ⟨pc, ?_, regs, disposable.kept, (fun ok => by rw [scratchFull] at ok; cases ok),
        fun _ => disposable.lengthWord⟩⟩
      · rw [count]
        simp only [if_neg full, if_neg room]
        exact ran
      · rw [scratchFull]; exact a0
  by_cases none : call.rank = 0
  · exact fresh (by simp only [Call.path, if_neg empty, if_pos none])
  have found := Nat.pos_of_ne_zero none
  by_cases gap : call.predecessor.value.toNat + 1 < call.start.toNat
  · exact fresh (by simp only [Call.path, if_neg empty, if_neg none, if_pos gap])
  by_cases grows : call.predecessor.value.toNat < call.stop.toNat
  · have path : call.path = .extension := by
      simp only [Call.path, if_neg empty, if_neg none, if_neg gap, if_pos grows]
    have p := EntryExtension.InitialLayout.extensionPrefix layout premises.entry link premises.mode
      premises.arguments nonempty found (Nat.le_of_not_gt gap) grows
    have count : (boundedResult call initial capacity low high).count =
        let helper := call.extensionHelper initial low high
        if helper.acceptCount ≤ initial.a5.toNat then
          EntryExtension.toHelperCount call + HelperRun.successCount helper capacity helper.acceptCount + 11
        else EntryExtension.toHelperCount call + HelperRun.fullCount helper initial.a5.toNat + 11 := by
      rw [boundedResult, boundedCount, path]
    have needed : call.scratchNeeded initial low high = (call.extensionHelper initial low high).acceptCount := by
      simp only [Call.scratchNeeded, path]
    have notFresh : ¬ (call.path = .fresh ∧ call.length = capacity) := fun both => by
      rw [path] at both; cases both.1
    by_cases room : (call.extensionHelper initial low high).acceptCount ≤ initial.a5.toNat
    · have ok : call.capacityOutcome initial low high capacity = .success := by
        rw [outcome, if_neg notFresh, needed, if_neg (by omega)]
      obtain ⟨final, ran, pc, a0, result, regs, keeps⟩ := p.runSuccess layout premises.sorted room
      refine ⟨final, ?_, ⟨pc, ?_, regs, keeps, fun _ => ?_, fun failed => (failed ok).elim⟩⟩
      · rw [count]
        simp only [if_pos room]
        exact ran
      · rw [ok]; exact a0
      · rw [boundedInMemory, Call.result, path]
        refine ⟨result.lengthWord, ?_, result.cacheLow, result.cacheHigh⟩
        intro index inside
        rw [Result.afterHelperLength] at inside
        exact result.entries index inside
    · have scratchFull : call.capacityOutcome initial low high capacity = .scratchFull := by
        rw [outcome, if_neg notFresh, needed, if_pos (by omega)]
      obtain ⟨final, ran, pc, a0, regs, result⟩ := p.runFull layout premises.sorted (Nat.lt_of_not_le room)
      refine ⟨final, ?_, ⟨pc, ?_, regs, result.kept, (fun ok => by rw [scratchFull] at ok; cases ok),
        fun _ => headerDisposable layout result.header⟩⟩
      · rw [count]
        simp only [if_neg room]
        exact ran
      · rw [scratchFull]; exact a0
  · have path : call.path = .contained := by
      simp only [Call.path, if_neg empty, if_neg none, if_neg gap, if_neg grows]
    have ok : call.capacityOutcome initial low high capacity = .success := by
      rw [outcome, if_neg (by rw [path]; simp), if_neg (by simp [Call.scratchNeeded, path])]
    have p : EntryContained.Premises base returnAddress original initial call :=
      ⟨frame, premises.arguments, layout.predecessorMap, nonempty, found, Nat.le_of_not_gt grows⟩
    obtain ⟨final, ran, pc, a0, regs, keeps⟩ := p.run
    refine ⟨final, ?_, ⟨pc, ?_, frameRegisters regs, fromFrame keeps, fun _ => ?_,
      fun failed => (failed ok).elim⟩⟩
    · rw [boundedResult, boundedCount, path]
      exact ran
    · rw [ok]; exact a0
    · rw [boundedInMemory, Call.result, path]
      exact unchangedResult layout _ keeps

end Riscfree.RangeInsert.Bounded.Unified
