import Riscfree.Elf
import SortedMap.Search.Instructions

/-!
# `sorted_map_lower_bound` and `sorted_map_upper_bound` are correct against Sail

One proof covers both routines. It composes the step lemmas of
`SortedMap/Search/Instructions.lean`, which are stated for either `Bound`.

For any contents, the routine returns `call.result bound`, the scan of
`SortedMap/Search.lean`, after exactly `call.count bound` instructions:
4 for an empty map, `7 + 5r` when the scan stops at entry `r`, and
`6 + 5 * length` when it passes every entry. It writes no memory and keeps every
register except the PC, `nextPC`, and `a0`, `a2`–`a4`. For a sorted map the result is
the mathematical `rank` (`sortedMapSearchSailCorrectSorted`).
-/

namespace Riscfree.SortedMap.Search

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

section Run

variable {bound : Bound} {base returnAddress : Word} {original : Machine} {call : Call}

-- The loop head at entry `index`.
private def Head (call : Call) (state : Snapshot) (index : Nat) : Prop :=
  state.pc = 16#32 ∧ state.a0 = BitVec.ofNat 32 index ∧ state.a1 = call.key ∧
    state.a2 = call.length ∧ state.a3 = call.wordSlot index

private def passed (call : Call) (state : Snapshot) (index : Nat) : Snapshot :=
  { state with
    pc := 16#32
    a0 := BitVec.ofNat 32 (index + 1)
    a3 := call.wordSlot (index + 1)
    a4 := (call.old index).key }

-- Five instructions pass an entry that is not the last.
private theorem onePass (environment : Environment bound base returnAddress original)
    (keys : Keys original call) (state : Snapshot) (index : Nat) (atHead : Head call state index)
    (passes : bound.passes (call.old index).key call.key = true)
    (notLast : index + 1 < call.length.toNat) :
    run 5 (sync base original state) = some (sync base original (passed call state index)) := by
  obtain ⟨pc, counter, key, length, pointer⟩ := atHead
  have platform := environment.platform original.mem (fun _ _ _ => rfl)
  have read : Readable original state.a3 := pointer ▸ keys.readable index (by omega)
  have word : WordAt original.mem state.a3.toNat (call.old index).key := by
    rw [pointer, slotNat keys (by omega)]
    exact keys.keyWord index (by omega)
  have passing : bound.passes (call.old index).key state.a1 = true := key ▸ passes
  refine runStep (step10 platform state pc _ read word) ?_
  refine runStep (step14 platform _ rfl) ?_
  simp only [passing, if_true]
  refine runStep (step18 platform _ rfl) (runStep (step1c platform _ rfl) ?_)
  refine runStep (step20 platform _ rfl) ?_
  have differs : ¬ state.a2 = state.a0 + 1#32 := by
    rw [length, counter, counterNext]
    exact fun same =>
      absurd ((counterReached (show index + 1 ≤ call.length.toNat by omega)).mp same) (by omega)
  simp only [differs, if_false]
  rw [counter, counterNext, pointer, call.slotNext]
  rfl

private theorem passLoop (environment : Environment bound base returnAddress original)
    (keys : Keys original call) (target : Nat)
    (passes : ∀ index < target, bound.passes (call.old index).key call.key = true)
    (notLast : target < call.length.toNat) (state : Snapshot) (atHead : Head call state 0) :
    ∃ final : Snapshot, run (5 * target) (sync base original state) = some (sync base original final) ∧
      Head call final target := by
  let Invariant (remaining : Nat) (position : Snapshot) : Prop :=
    ∃ index, index + remaining = target ∧ Head call position index
  obtain ⟨final, ran, index, sum, head⟩ := runCountdown (sync base original) Invariant 0 5
    (fun remaining position holds => by
      obtain ⟨index, sum, head⟩ := holds
      exact ⟨passed call position index,
        onePass environment keys position index head (passes index (by omega)) (by omega),
        index + 1, by omega, rfl, rfl, head.2.2.1, head.2.2.2.1, rfl⟩)
    target state ⟨0, by omega, atHead⟩
  rw [show index = target by omega] at head
  exact ⟨final, ran, head⟩

private def returned (base returnAddress : Word) (state : Snapshot) (result : Nat) : Snapshot :=
  { state with pc := returnAddress - base, a0 := BitVec.ofNat 32 result }

theorem searchRun (environment : Environment bound base returnAddress original)
    (header : Header original call) (keys : 0 < call.length.toNat → Keys original call)
    (state : Snapshot) (atEntry : state.pc = 0) (headerArgument : state.a0 = call.header)
    (keyArgument : state.a1 = call.key) :
    ∃ final : Snapshot, run (call.count bound) (sync base original state) =
        some (sync base original final) ∧
      final.pc = returnAddress - base ∧ final.a0 = BitVec.ofNat 32 (call.result bound) ∧
      final.a1 = state.a1 := by
  have platform := environment.platform original.mem (fun _ _ _ => rfl)
  have lengthRead : Readable original (state.a0 + 4#32) := headerArgument ▸ header.lengthReadable
  have lengthWord : WordAt original.mem (state.a0 + 4#32).toNat call.length := by
    rw [headerArgument, headerOffset header]
    exact header.lengthWord
  have first := step00 platform state atEntry call.length lengthRead lengthWord
  have second := step04 platform { state with pc := 4#32, a2 := call.length } rfl
  by_cases empty : call.length.toNat = 0
  · have zero : call.length = 0#32 := BitVec.eq_of_toNat_eq empty
    have result : call.result bound = 0 := by simp [Call.result, empty, scan]
    refine ⟨returned base returnAddress { state with pc := 4#32, a2 := call.length } 0, ?_, rfl,
      by rw [result]; rfl, rfl⟩
    simp only [Call.count, empty, if_true]
    refine runStep first (runStep second ?_)
    simp only [zero, if_true]
    exact runStep (step2c platform _ rfl) (runStep (step30 platform _ rfl) rfl)
  · have keys := keys (by omega)
    have nonzero : ¬ call.length = 0#32 := fun same => empty (by rw [same]; rfl)
    have dataRead : Readable original state.a0 := headerArgument ▸ keys.dataReadable
    have dataWord : WordAt original.mem state.a0.toNat call.data := headerArgument ▸ keys.dataWord
    let start : Snapshot := { state with pc := 16#32, a0 := 0#32, a2 := call.length, a3 := call.data }
    have setup : run 4 (sync base original state) = some (sync base original start) := by
      refine runStep first (runStep second ?_)
      simp only [nonzero, if_false]
      exact runStep (step08 platform _ rfl _ dataRead dataWord) (runStep (step0c platform _ rfl) rfl)
    have atStart : Head call start 0 := ⟨rfl, rfl, keyArgument, rfl, call.slotZero.symm⟩
    let result := call.result bound
    have bounds := call.result_le bound
    have passes (index : Nat) (below : index < result) :
        bound.passes (call.old index).key call.key = true :=
      scan_passes 0 call.length.toNat index (by omega) below
    by_cases early : result < call.length.toNat
    · -- The scan stops at entry `result`: two more instructions and the return.
      obtain ⟨looped, loop, ⟨pc, counter, key, length, pointer⟩⟩ :=
        passLoop environment keys result passes early start atStart
      have fails : bound.passes (call.old result).key call.key = false :=
        scan_stops 0 call.length.toNat (by simpa using early)
      have read : Readable original looped.a3 := pointer ▸ keys.readable result early
      have word : WordAt original.mem looped.a3.toNat (call.old result).key := by
        rw [pointer, slotNat keys early]
        exact keys.keyWord result early
      let loaded : Snapshot := { looped with pc := 20#32, a4 := (call.old result).key }
      refine ⟨{ loaded with pc := returnAddress - base }, ?_, rfl, counter, key.trans keyArgument.symm⟩
      have exit : run 3 (sync base original looped) =
          some (sync base original { loaded with pc := returnAddress - base }) := by
        refine runStep (step10 platform looped pc _ read word) (runStep (step14 platform loaded rfl) ?_)
        simp only [loaded, key, fails]
        exact runStep (step30 platform _ rfl) rfl
      simp only [Call.count, empty, if_false, show call.result bound < call.length.toNat from early,
        if_true]
      rw [show 7 + 5 * call.result bound = 4 + (5 * result + 3) by omega, runAdd, setup,
        Option.bind_some, runAdd, loop, Option.bind_some, exit]
    · -- Every entry passes: the last pass falls through to `mv a0, a2`.
      have whole : result = call.length.toNat := by omega
      let last := call.length.toNat - 1
      obtain ⟨looped, loop, ⟨pc, counter, key, length, pointer⟩⟩ :=
        passLoop environment keys last (fun index below => passes index (by omega)) (by omega) start atStart
      have lastPasses := passes last (by omega)
      have read : Readable original looped.a3 := pointer ▸ keys.readable last (by omega)
      have word : WordAt original.mem looped.a3.toNat (call.old last).key := by
        rw [pointer, slotNat keys (by omega)]
        exact keys.keyWord last (by omega)
      let loaded : Snapshot := { looped with pc := 20#32, a4 := (call.old last).key }
      let counted : Snapshot :=
        { loaded with pc := 32#32, a0 := looped.a0 + 1#32, a3 := looped.a3 + 8#32 }
      have reached : call.length = BitVec.ofNat 32 (last + 1) :=
        (counterReached (show last + 1 ≤ call.length.toNat by omega)).mpr (by omega)
      refine ⟨{ counted with pc := returnAddress - base, a0 := looped.a2 }, ?_, rfl, ?_,
        key.trans keyArgument.symm⟩
      · have exit : run 7 (sync base original looped) =
            some (sync base original { counted with pc := returnAddress - base, a0 := looped.a2 }) := by
          refine runStep (step10 platform looped pc _ read word) (runStep (step14 platform loaded rfl) ?_)
          have passing : bound.passes loaded.a4 loaded.a1 = true := by
            show bound.passes (call.old last).key looped.a1 = true
            rw [key]
            exact lastPasses
          rw [if_pos passing]
          refine runStep (step18 platform _ rfl) (runStep (step1c platform _ rfl) ?_)
          refine runStep (step20 platform counted rfl) ?_
          have same : counted.a2 = counted.a0 := by
            show looped.a2 = looped.a0 + 1#32
            rw [length, counter, counterNext, ← reached]
          rw [if_pos same]
          exact runStep (step24 platform _ rfl) (runStep (step28 platform _ rfl) rfl)
        simp only [Call.count, empty, if_false, show ¬ call.result bound < call.length.toNat from early]
        rw [show 6 + 5 * call.length.toNat = 4 + (5 * last + 7) by omega, runAdd, setup,
          Option.bind_some, runAdd, loop, Option.bind_some, exit]
      · show looped.a2 = BitVec.ofNat 32 (call.result bound)
        rw [length, show call.result bound = call.length.toNat from whole, Insert.ofWordNat]

end Run

/-! ## Guarantees -/

private theorem readA0 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x10 = some state.a0 :=
  readReg_succ.mp (syncRead state (index := 10) (by decide))

private theorem readA1 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x11 = some state.a1 :=
  readReg_succ.mp (syncRead state (index := 11) (by decide))

-- The run as `searchRun` gives it, from the routine's entry machine.
theorem sortedMapSearchSailRun (bound : Bound) (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (keyArgument : initial.a1 = call.key)
    (environment : Environment bound base returnAddress original)
    (header : Header original call)
    (keys : 0 < call.length.toNat → Keys original call) :
    ∃ endState : Snapshot, run (call.count bound) original = some (sync base original endState) ∧
      endState.pc = returnAddress - base ∧ endState.a0 = BitVec.ofNat 32 (call.result bound) ∧
      endState.a1 = initial.a1 := by
  obtain ⟨final, ran, pc, result, key⟩ :=
    searchRun environment header keys { initial with pc := 0 } rfl headerArgument keyArgument
  exact ⟨final, (congrArg (run (call.count bound)) entry).trans ran, pc, result, key⟩

theorem sortedMapSearchSailCorrect (bound : Bound) (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (keyArgument : initial.a1 = call.key)
    (environment : Environment bound base returnAddress original)
    (header : Header original call)
    (keys : 0 < call.length.toNat → Keys original call) :
    ∃ final, run (call.count bound) original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some (BitVec.ofNat 32 (call.result bound)) ∧
      final.mem = original.mem ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x12, .x13, .x14],
        final.regs.get? register = original.regs.get? register) := by
  obtain ⟨endState, ran, pc, result, key⟩ := sortedMapSearchSailRun bound base returnAddress original
    call initial entry headerArgument keyArgument environment header keys
  refine ⟨_, ran, pcReadReturned _ _ _ _ pc, (readA0 _ _ _).trans (congrArg some result),
    syncMem _, fun register outside => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨pc, next, a0, a2, a3, a4⟩ := outside
  by_cases isA1 : register = Register.x11
  · subst isA1
    rw [readA1, key, entry, readA1]
  refine syncFrame endState register pc next ?_
  intro index member
  change index ∈ ([10, 11, 12, 13, 14] : List (Fin 32)) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  exacts [Ne.symm a0, Ne.symm isA1, Ne.symm a2, Ne.symm a3, Ne.symm a4]

-- The same guarantee with the code mapping derived from machine mode and the
-- code image, as `rawVecPairRemoveSailCorrectInMachineMode` does.
theorem sortedMapSearchSailCorrectInMachineMode (bound : Bound) (base returnAddress : Word)
    (original : Machine) (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (keyArgument : initial.a1 = call.key)
    (mode : MachineMode original returnAddress)
    (image : CodeImage (instructions bound) base original)
    (header : Header original call)
    (keys : 0 < call.length.toNat → Keys original call) :
    ∃ final, run (call.count bound) original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some (BitVec.ofNat 32 (call.result bound)) ∧
      final.mem = original.mem ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x12, .x13, .x14],
        final.regs.get? register = original.regs.get? register) :=
  sortedMapSearchSailCorrect bound base returnAddress original call initial entry headerArgument
    keyArgument (Environment.ofMachine mode image) header keys

-- For a sorted map, the result is the mathematical rank: the number of keys
-- below the search key for `lower`, and at most it for `upper`.
theorem result_eq_rank (bound : Bound) (call : Call)
    (sorted : Sorted (entriesOf call.old call.length.toNat)) :
    call.result bound = rank bound (entriesOf call.old call.length.toNat) call.key :=
  scan_eq_rank sorted

theorem sortedMapSearchSailCorrectSorted (bound : Bound) (base returnAddress : Word)
    (original : Machine) (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (keyArgument : initial.a1 = call.key)
    (mode : MachineMode original returnAddress)
    (image : CodeImage (instructions bound) base original)
    (header : Header original call)
    (keys : 0 < call.length.toNat → Keys original call)
    (sorted : Sorted (entriesOf call.old call.length.toNat)) :
    ∃ final, run (call.count bound) original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 =
        some (BitVec.ofNat 32 (rank bound (entriesOf call.old call.length.toNat) call.key)) ∧
      final.mem = original.mem := by
  obtain ⟨final, ran, pc, result, memory, -⟩ := sortedMapSearchSailCorrectInMachineMode bound base
    returnAddress original call initial entry headerArgument keyArgument mode image header keys
  exact ⟨final, ran, pc, by rw [← result_eq_rank bound call sorted]; exact result, memory⟩

end Riscfree.SortedMap.Search

namespace Riscfree.SortedMap.LowerBound

def verifyElf (path : String) : IO Unit :=
  Riscfree.verifyElf path "sorted_map_lower_bound" (Search.lowerInstructions.map Prod.fst)

end Riscfree.SortedMap.LowerBound

namespace Riscfree.SortedMap.UpperBound

def verifyElf (path : String) : IO Unit :=
  Riscfree.verifyElf path "sorted_map_upper_bound" (Search.upperInstructions.map Prod.fst)

end Riscfree.SortedMap.UpperBound
