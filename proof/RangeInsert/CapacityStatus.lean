import RangeInsert.Capacity

/-! The only allocating operations of range insertion return `OK` or
`FULL` on their legitimate call states. These facts let the caller
compose the existing collection execution theorems for either outcome. -/

namespace Riscfree.RangeInsert.Nonempty

open Riscfree.RV32
open Riscfree.RawVec (Word)

theorem Call.freshHasGap {call : Call} (path : call.path = .fresh) :
    call.rank = 0 ∨ (0 < call.rank ∧ call.predecessor.value.toNat + 1 < call.start.toNat) := by
  unfold Call.path at path
  split at path
  · cases path
  · split at path
    · exact Or.inl (by assumption)
    · split at path
      · exact Or.inr ⟨by omega, by assumption⟩
      · split at path <;> cases path

/-- A full map cannot replace an entry on a fresh insertion. The underlying
vector call has a valid rank and returns `FULL` exactly at capacity. -/
theorem Call.freshCapacityStatus {call : Call} {capacity : Word} (path : call.path = .fresh)
    (valid : call.length.toNat ≤ capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat) :
    (call.freshInsert capacity).status = if call.length = capacity then 1 else 0 := by
  let insertion := call.freshInsert capacity
  have validLength : insertion.lengthValid := valid
  have absent := Call.freshKeyAbsent (Call.freshHasGap path) sorted ordered
  have newKey := Call.freshDoesNotReplace capacity absent
  have indexFits : insertion.vector.index.toNat ≤ insertion.vector.length.toNat := by
    rw [SortedMap.Insert.Call.vectorIndex]
    exact insertion.position_le
  have lengthFits : insertion.vector.length.toNat ≤ insertion.vector.capacity.toNat := valid
  change insertion.status = (if insertion.vector.length = insertion.vector.capacity then 1 else 0)
  rw [SortedMap.Insert.Call.status, if_neg (not_not_intro validLength), if_neg newKey,
    RawVec.Insert.Call.status, if_neg (Nat.not_lt.mpr lengthFits), if_neg (Nat.not_lt.mpr indexFits)]

/-- The fresh insertion call returns FULL with only its own frame modified
when no map slot is available. No spare-slot access is required. -/
theorem Call.freshFullRun {base returnAddress : Word} {original : Machine} {call : Call}
    {capacity : Word} {initial : SortedMap.Insert.Snapshot}
    (path : call.path = .fresh) (full : call.length = capacity)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header) (keyArgument : initial.a1 = call.start)
    (valueArgument : initial.a2 = call.stop)
    (environment : SortedMap.Insert.Environment base returnAddress original)
    (header : RawVec.Insert.Header original (call.freshInsert capacity).vector)
    (stack : SortedMap.Insert.Stack base original (call.freshInsert capacity) initial.sp)
    (keys : 0 < call.length.toNat → SortedMap.Search.Keys original (call.freshInsert capacity).search) :
    ∃ state : SortedMap.Insert.Snapshot,
      let memory := SortedMap.Insert.pushed original.mem initial.sp initial
      run (call.freshInsert capacity).count original = some (sync base { original with mem := memory } state) ∧
      state.pc = returnAddress - base ∧ state.a0 = 1 ∧
      state.ra = initial.ra ∧ state.sp = initial.sp ∧ state.s0 = initial.s0 ∧
      state.s1 = initial.s1 ∧ state.s2 = initial.s2 ∧ state.s3 = initial.s3 := by
  have absent := Call.freshKeyAbsent (Call.freshHasGap path) sorted ordered
  have newKey := Call.freshDoesNotReplace capacity absent
  have noSpare : ¬ (call.freshInsert capacity).vector.valid := by
    intro valid
    have spare : call.length.toNat < capacity.toNat := valid.2
    rw [full] at spare
    exact (Nat.lt_irrefl _) spare
  obtain ⟨state, memory, ran, pc, status, ra, sp, s0, s1, s2, s3, effects⟩ :=
    SortedMap.Insert.sortedMapInsertSailRun base returnAddress original (call.freshInsert capacity)
      initial entry headerArgument keyArgument valueArgument environment header stack
      (fun _ => keys) (fun replaced => (newKey replaced).elim) (fun _ valid => (noSpare valid).elim)
  have same := effects.2.1 newKey (Or.inl noSpare)
  have expected := Call.freshCapacityStatus path (by rw [full]) sorted ordered
  rw [if_pos full] at expected
  exact ⟨state, same ▸ ran, pc, status.trans expected, ra, sp, s0, s1, s2, s3⟩

end Riscfree.RangeInsert.Nonempty

namespace Riscfree.RangeInsert.DeleteExtra

open Riscfree.RV32
open Riscfree.RawVec (Word)

/-- An append at the deletion buffer's logical length fails only when all
slots are already used. This includes the first eligible successor when
the scratch capacity is zero. -/
theorem scratchAppendStatus {append : RawVec.Call} (atEnd : append.index = append.length)
    (valid : append.length.toNat ≤ append.capacity.toNat) :
    append.status = if append.length = append.capacity then 1 else 0 := by
  rw [RawVec.Insert.Call.status, if_neg (Nat.not_lt.mpr valid), atEnd,
    if_neg (Nat.lt_irrefl _)]

/-- On a full append the verified RawVec routine requires the header alone.
There is no spare slot and no need to map the data pointer at capacity zero. -/
theorem scratchAppendFull {append : RawVec.Call} (atEnd : append.index = append.length)
    (full : append.length = append.capacity) :
    append.status = 1 ∧ append.count = 7 ∧ ¬ append.valid := by
  refine ⟨?_, ?_, fun valid => ?_⟩
  · rw [scratchAppendStatus atEnd (by rw [full]), if_pos full]
  · simp [RawVec.Call.count, atEnd, full]
  · exact (Nat.ne_of_lt valid.2) (congrArg BitVec.toNat full)

/-- The rejected append runs without touching scratch storage, including
when the data pointer designates no bytes. -/
theorem scratchAppendFullRun {base returnAddress : Word} {original : Machine}
    {append : RawVec.Call} {initial : RawVec.Snapshot}
    (atEnd : append.index = append.length) (full : append.length = append.capacity)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = append.header) (indexArgument : initial.a1 = append.index)
    (valueArgument : initial.a2 = append.value)
    (environment : RawVec.Environment base returnAddress original) (header : RawVec.Header original append) :
    ∃ state : RawVec.Snapshot,
      run 7 original = some (sync base original state) ∧
      state.pc = returnAddress - base ∧ state.a0 = 1 := by
  obtain ⟨status, count, noSpare⟩ := scratchAppendFull atEnd full
  obtain ⟨state, memory, ran, pc, returned, unchanged, _⟩ :=
    RawVec.rawVecU32InsertSailRun base returnAddress original append initial entry
      headerArgument indexArgument valueArgument environment header (fun valid => (noSpare valid).elim)
  rw [count, unchanged noSpare] at ran
  exact ⟨state, ran, pc, returned.trans status⟩

end Riscfree.RangeInsert.DeleteExtra
