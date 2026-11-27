import RangeInsert.Nonempty.Contained
import RangeInsert.Nonempty.Extension.Run
import RangeInsert.Nonempty.Fresh.Run

/-! All successful paths of the linked range insertion entry point. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Pair PairAt)
open Empty (Snapshot)

inductive Path where
  | empty
  | contained
  | extension
  | fresh
  deriving DecidableEq

def Call.path (call : Call) : Path :=
  if call.stop.toNat < call.start.toNat then .empty
  else if call.rank = 0 then .fresh
  else if call.predecessor.value.toNat + 1 < call.start.toNat then .fresh
  else if call.predecessor.value.toNat < call.stop.toNat then .extension
  else .contained

structure Result where
  count : Nat
  length : Word
  entries : Nat → Pair
  low : Word
  high : Word

namespace Result

def unchanged (call : Call) (count : Nat) (low high : Word) : Result :=
  ⟨count, call.length, call.old, low, high⟩

def afterHelper (helper : DeleteExtra.Call) (count : Nat) (low high : Word) : Result :=
  ⟨count, BitVec.ofNat 32 (helper.length.toNat - helper.acceptCount),
    DeleteExtra.drained (helper.after helper.acceptCount) helper.position helper.acceptCount, low, high⟩

def inMemory (result : Result) (initial : Snapshot) (call : Call) (memory : ByteMemory) : Prop :=
  WordAt memory (call.header.toNat + 4) result.length ∧
    (∀ index < result.length.toNat, PairAt memory (call.search.slot index) (result.entries index)) ∧
    WordAt memory initial.a1.toNat result.low ∧ WordAt memory (initial.a1.toNat + 4) result.high

theorem afterHelperLength (helper : DeleteExtra.Call) (count : Nat) (low high : Word) :
    (afterHelper helper count low high).length.toNat = helper.length.toNat - helper.acceptCount := by
  change (BitVec.ofNat 32 (helper.length.toNat - helper.acceptCount)).toNat = _
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := helper.length.isLt; omega)

end Result

def Call.result (call : Call) (initial : Snapshot) (capacity low high : Word) : Result :=
  match call.path with
  | .empty => Result.unchanged call 19 low high
  | .contained => Result.unchanged call call.containedCount low high
  | .extension =>
    let helper := call.extensionHelper initial low high
    Result.afterHelper helper (68 + call.search.count .upper + helper.helperCount capacity helper.acceptCount)
      (helper.finalLow helper.acceptCount) (helper.finalHigh helper.acceptCount)
  | .fresh =>
    let helper := call.freshHelper capacity initial low high
    Result.afterHelper helper (freshToHelperCount call capacity + helper.helperCount capacity helper.acceptCount + 20)
      (freshLow (helper.finalLow helper.acceptCount) (call.stop - call.start))
      (freshHigh (helper.finalLow helper.acceptCount) (helper.finalHigh helper.acceptCount) (call.stop - call.start))

/-- The initial analyzed layout and success conditions. The spare map slot
is needed only for fresh insertion. Scratch capacity is the computed
number of accepted successors on the path that actually runs. -/
structure Premises (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) (capacity low high : Word) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  mode : MachineMode original returnAddress
  arguments : Arguments initial call
  layout : InitialLayout base original initial call capacity low high
  sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)
  ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat
  spare : call.path = .fresh → call.length.toNat < capacity.toNat
  freshScratch : call.path = .fresh →
    (call.freshHelper capacity initial low high).acceptCount ≤ initial.a5.toNat
  extensionScratch : call.path = .extension →
    (call.extensionHelper initial low high).acceptCount ≤ initial.a5.toNat

private theorem Premises.link {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word} (premises : Premises base returnAddress original initial call capacity low high) :
    initial.ra = returnAddress := by
  have read := syncRead (base := base) (frame := original) { initial with pc := 0 } (index := 1) (by decide)
  rw [← premises.entry] at read
  exact Option.some.inj ((readReg_succ.mp read).symm.trans (readReg_succ.mp premises.mode.ra))

private theorem InitialLayout.unchangedResult {base : Word} {original final : Machine}
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

set_option maxHeartbeats 1800000 in
/-- Each successful path returns at the original link register, has its
exact dynamic cost, preserves the ABI's saved registers, and writes only
the declared regions. The live entries and cache are the result selected
by the same branch test as the linked binary. -/
theorem Premises.run {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word} (premises : Premises base returnAddress original initial call capacity low high) :
    ∃ final, Riscfree.RV32.run (call.result initial capacity low high).count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (call.result initial capacity low high).inMemory initial call final.mem ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
  have layout := premises.layout
  have frame := layout.outerFrame premises.entry premises.link premises.mode
  have fromFrame {final : Machine}
      (keeps : ∀ byte, Empty.OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]?) :
      ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
    intro byte outside
    exact keeps byte (stackDisjointOuter layout.stack.fits (fun stack => outside (Or.inl stack)))
  by_cases empty : call.stop.toNat < call.start.toNat
  · have p : Empty.Premises base returnAddress original initial :=
      ⟨frame, by rw [premises.arguments.stop, premises.arguments.start]; exact empty⟩
    obtain ⟨final, ran, returned, regs, keep⟩ := p.run
    rw [Call.result, show call.path = .empty from if_pos empty]
    exact ⟨final, ran, returned, layout.unchangedResult 19 keep,
      fun key outside => regs key (by intro equal; subst key; exact outside (List.mem_cons_self ..))
        (by intro equal; subst key; exact outside (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      fromFrame keep⟩
  have nonempty := Nat.le_of_not_gt empty
  have fresh (select : call.path = .fresh)
      (branch : call.rank = 0 ∨ (0 < call.rank ∧ call.predecessor.value.toNat + 1 < call.start.toNat)) :
      ∃ final, Riscfree.RV32.run (call.result initial capacity low high).count original = some final ∧
        final.regs.get? Register.PC = some returnAddress ∧
        (call.result initial capacity low high).inMemory initial call final.mem ∧
        (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
          final.regs.get? key = original.regs.get? key) ∧
        ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
    have p := layout.freshPrefix premises.entry premises.link premises.mode premises.arguments nonempty branch
    obtain ⟨final, ran, returned, result, regs, keep⟩ :=
      p.run layout (premises.spare select) premises.sorted premises.ordered (premises.freshScratch select)
    rw [Call.result, select]
    refine ⟨final, ran, returned, ⟨result.length, ?_, result.cacheLow, result.cacheHigh⟩, regs, keep⟩
    intro index inside
    rw [Result.afterHelperLength] at inside
    exact result.entries index inside
  by_cases none : call.rank = 0
  · exact fresh (by simp only [Call.path, if_neg empty, if_pos none]) (Or.inl none)
  have found := Nat.pos_of_ne_zero none
  by_cases gap : call.predecessor.value.toNat + 1 < call.start.toNat
  · exact fresh (by simp only [Call.path, if_neg empty, if_neg none, if_pos gap]) (Or.inr ⟨found, gap⟩)
  by_cases grows : call.predecessor.value.toNat < call.stop.toNat
  · have path : call.path = .extension := by simp only [Call.path, if_neg empty, if_neg none, if_neg gap, if_pos grows]
    have p := layout.extensionPrefix premises.entry premises.link premises.mode premises.arguments
      nonempty found (Nat.le_of_not_gt gap) grows
    obtain ⟨final, ran, returned, result, regs, keep⟩ :=
      p.run layout premises.sorted (premises.extensionScratch path)
    rw [Call.result, path]
    refine ⟨final, ran, returned, ⟨result.lengthWord, ?_, result.cacheLow, result.cacheHigh⟩, regs, keep⟩
    intro index inside
    rw [Result.afterHelperLength] at inside
    exact result.entries index inside
  · have path : call.path = .contained := by simp only [Call.path, if_neg empty, if_neg none, if_neg gap, if_neg grows]
    have p : ContainedPremises base returnAddress original initial call :=
      ⟨frame, premises.arguments, layout.predecessorMap, nonempty, found, Nat.le_of_not_gt grows⟩
    obtain ⟨final, ran, returned, regs, keep⟩ := p.run
    rw [Call.result, path]
    refine ⟨final, ran, returned, layout.unchangedResult call.containedCount keep, ?_, fromFrame keep⟩
    intro key outside
    apply regs key
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
    tauto

end Riscfree.RangeInsert.Nonempty
