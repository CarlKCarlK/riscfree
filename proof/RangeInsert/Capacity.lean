import RangeInsert.Correct

/-! The intermediate storage required by the bounded insertion, derived
from the same fixed-end scan that the execution proof uses. -/

namespace Riscfree.RangeInsert.Nonempty

open Riscfree.RV32 (Machine)
open Riscfree.RawVec (Word)
open Empty (Snapshot)

/-- The first capacity failure, if any, in insertion order. -/
inductive CapacityOutcome where
  | success
  | mapFull
  | scratchFull
  deriving DecidableEq

/-- Fresh insertion reserves its slot before deleting any successors. -/
def Call.mapNeeded (call : Call) : Nat :=
  call.length.toNat + if call.path = .fresh then 1 else 0

/-- The fixed-end scan needs one word per accepted successor. The fresh
helper models the logical insertion even when the physical map is full:
its entries use the vector insertion's pure result, independent of capacity. -/
def Call.scratchNeeded (call : Call) (initial : Snapshot) (low high : Word) : Nat :=
  match call.path with
  | .empty | .contained => 0
  | .extension => (call.extensionHelper initial low high).acceptCount
  | .fresh => (call.freshHelper 0 initial low high).acceptCount

theorem Call.freshHelper_capacity (call : Call) (initial : Snapshot) (low high capacity : Word) :
    call.freshHelper 0 initial low high = call.freshHelper capacity initial low high := by
  rfl

/-- The logical insertion length fits in one word even if the map has
no spare slot. An eight-byte allocation cannot have a word's worth of
entries in the RV32 address space. -/
theorem MapStorage.logicalFreshLength {original : Machine} {call : Call} {capacity : Word}
    (storage : MapStorage original call capacity) (initial : Snapshot) (low high : Word) :
    (call.freshHelper 0 initial low high).length.toNat = call.length.toNat + 1 := by
  have layout : call.data.toNat + 8 * capacity.toNat ≤ 2 ^ 32 := storage.allocationFits
  have valid := storage.lengthFits
  change (BitVec.ofNat 32 (call.length.toNat + 1)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

def Call.capacityOutcome (call : Call) (initial : Snapshot) (low high capacity : Word) :
    CapacityOutcome :=
  if capacity.toNat < call.mapNeeded then .mapFull
  else if initial.a5.toNat < call.scratchNeeded initial low high then .scratchFull
  else .success

theorem Call.capacitySuccess {call : Call} {initial : Snapshot} {low high capacity : Word} :
    call.capacityOutcome initial low high capacity = .success ↔
      call.mapNeeded ≤ capacity.toNat ∧ call.scratchNeeded initial low high ≤ initial.a5.toNat := by
  unfold Call.capacityOutcome
  split <;> simp_all

theorem Call.capacityMapFull {call : Call} {initial : Snapshot} {low high capacity : Word}
    (valid : call.length.toNat ≤ capacity.toNat) :
    call.capacityOutcome initial low high capacity = .mapFull ↔
      call.path = .fresh ∧ call.length = capacity := by
  have mapShort : capacity.toNat < call.mapNeeded ↔ call.path = .fresh ∧ call.length = capacity := by
    unfold Call.mapNeeded
    by_cases fresh : call.path = .fresh
    · simp only [fresh, if_true, true_and]
      constructor
      · intro short
        exact BitVec.eq_of_toNat_eq (by omega)
      · intro full
        rw [full]
        omega
    · simp [fresh, Nat.not_lt.mpr valid]
  unfold Call.capacityOutcome
  rw [← mapShort]
  by_cases short : capacity.toNat < call.mapNeeded
  · simp [short]
  · rw [if_neg short]
    split <;> simp [short]

theorem Call.capacityScratchFull {call : Call} {initial : Snapshot} {low high capacity : Word} :
    call.capacityOutcome initial low high capacity = .scratchFull ↔
      call.mapNeeded ≤ capacity.toNat ∧ initial.a5.toNat < call.scratchNeeded initial low high := by
  unfold Call.capacityOutcome
  split <;> simp_all

theorem Call.capacitySuccess_iff_pathRoom {call : Call} {initial : Snapshot} {low high capacity : Word}
    (valid : call.length.toNat ≤ capacity.toNat) :
    call.capacityOutcome initial low high capacity = .success ↔
      (call.path = .fresh → call.length.toNat < capacity.toNat) ∧
      (call.path = .fresh → (call.freshHelper capacity initial low high).acceptCount ≤ initial.a5.toNat) ∧
      (call.path = .extension → (call.extensionHelper initial low high).acceptCount ≤ initial.a5.toNat) := by
  rw [Call.capacitySuccess]
  cases path : call.path <;> simp [Call.mapNeeded, Call.scratchNeeded, path, valid]
  intro _
  exact Iff.rfl

section
private def modelCall (start stop length : Word) : Call :=
  ⟨0x3000, length, 0x4000, fun index => if index = 0 then ⟨4, 9⟩ else ⟨12, 16⟩,
    start, stop⟩

private def modelScratch (capacity : Word) : Snapshot :=
  { ra := 0, sp := 0, s0 := 0, s1 := 0, a0 := 0, a1 := 0, a2 := 0, a3 := 0,
    a4 := 0, a5 := capacity, s2 := 0, s3 := 0, s4 := 0, s5 := 0 }

-- At zero map and scratch capacity, an empty insertion succeeds and a
-- singleton needs a map slot.
example : (modelCall 2 1 0).capacityOutcome (modelScratch 0) 0 0 0 = .success := by decide
example : (modelCall 2 2 0).capacityOutcome (modelScratch 0) 0 0 0 = .mapFull := by decide

-- Fresh insertion with two accepted successors needs one transient map
-- slot and both scratch words.
example : (modelCall 2 11 2).capacityOutcome (modelScratch 1) 11 0 2 = .mapFull := by decide
example : (modelCall 2 11 2).capacityOutcome (modelScratch 1) 11 0 3 = .scratchFull := by decide
example : (modelCall 2 11 2).capacityOutcome (modelScratch 2) 11 0 3 = .success := by decide

end

end Riscfree.RangeInsert.Nonempty
