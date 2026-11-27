import RangeInsert.DeleteExtra.Helper

/-! The number of successors the scan accepts, computed from the map. The
helper's `accepts` and `stops` premises hold for it by construction. -/

namespace Riscfree.RangeInsert.DeleteExtra

namespace Call

-- The successors from the selected entry to the end of the map.
def candidates (call : Call) : List Nat :=
  List.range (call.length.toNat - (call.position + 1))

-- How many leading successors start within the limit.
def acceptCount (call : Call) : Nat :=
  (call.candidates.takeWhile fun t => decide ((call.successor t).key.toNat ≤ call.limit.toNat)).length

-- The successor test the scan applies.
def accepts (call : Call) (t : Nat) : Bool :=
  decide ((call.successor t).key.toNat ≤ call.limit.toNat)

theorem acceptCount_eq (call : Call) :
    call.acceptCount = (call.candidates.takeWhile call.accepts).length := rfl

/-- The scan accepts at most the successors left in the map. -/
theorem acceptCount_le (call : Call) :
    call.acceptCount ≤ call.length.toNat - (call.position + 1) := by
  rw [acceptCount_eq]
  have shorter := (List.takeWhile_sublist call.accepts (l := call.candidates)).length_le
  unfold candidates at shorter
  simpa using shorter

/-- Every counted successor is in the map and starts within the limit. -/
theorem accepted (call : Call) : ∀ t < call.acceptCount,
    call.position + 1 + t < call.length.toNat ∧ (call.successor t).key.toNat ≤ call.limit.toNat := by
  intro t bound
  rw [acceptCount_eq] at bound
  have prefixOf := List.takeWhile_prefix call.accepts (l := call.candidates)
  have element : (call.candidates.takeWhile call.accepts)[t] = t := by
    rw [prefixOf.getElem bound]
    exact List.getElem_range _
  have member := List.getElem_mem bound
  rw [element] at member
  have test := List.mem_takeWhile_imp member
  have inRange := List.mem_range.mp (prefixOf.sublist.subset member)
  unfold candidates at inRange
  unfold accepts at test
  exact ⟨by omega, of_decide_eq_true test⟩

/-- The scan stops at the end of the map or at a successor beyond the limit. -/
theorem stops (call : Call) (inside : call.position < call.length.toNat) :
    call.position + 1 + call.acceptCount = call.length.toNat ∨
      (call.position + 1 + call.acceptCount < call.length.toNat ∧
        call.limit.toNat < (call.successor call.acceptCount).key.toNat) := by
  have split := List.takeWhile_append_dropWhile (p := call.accepts) (l := call.candidates)
  have lengths := congrArg List.length split
  rw [List.length_append] at lengths
  have total : call.candidates.length = call.length.toNat - (call.position + 1) := List.length_range
  rw [acceptCount_eq]
  cases rest : call.candidates.dropWhile call.accepts with
  | nil =>
    rw [rest] at lengths
    left
    simp only [List.length_nil, Nat.add_zero] at lengths
    omega
  | cons first others =>
    right
    have nonempty : call.candidates.dropWhile call.accepts ≠ [] := by rw [rest]; simp
    have fails := List.head_dropWhile_not call.accepts nonempty
    have bound : (call.candidates.takeWhile call.accepts).length < call.candidates.length := by
      rw [rest] at lengths; simp only [List.length_cons] at lengths; omega
    have firstFails : call.accepts first = false := by
      have := fails
      simp only [rest, List.head_cons] at this
      simpa using this
    have located : (call.candidates.takeWhile call.accepts ++ first :: others)[
        (call.candidates.takeWhile call.accepts).length]? = some first := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [← rest, split] at located
    have indexed (index : Nat) (below : index < call.candidates.length) :
        call.candidates[index]? = some index := by
      unfold candidates at below ⊢
      exact List.getElem?_range (by simpa using below)
    rw [indexed _ bound] at located
    have same := Option.some.inj located
    rw [← same] at firstFails
    unfold accepts at firstFails
    refine ⟨by omega, ?_⟩
    simpa using firstFails

end Call

end Riscfree.RangeInsert.DeleteExtra
