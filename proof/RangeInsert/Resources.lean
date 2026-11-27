import RangeInsert.Nonempty.Extension
import SortedMap.Insert

/-! Checked bounds on the dynamic search, insertion, and deletion costs and on the nested stack addresses. -/

namespace Riscfree.RangeInsert

theorem searchCountBound (call : SortedMap.Search.Call) (bound : SortedMap.Bound) :
    call.count bound ≤ 7 + 5 * call.length.toNat := by
  unfold SortedMap.Search.Call.count
  split
  · omega
  · split <;> omega

theorem pairRemoveCountBound (call : RawVec.PairRemove.Call) :
    RawVec.PairRemove.Call.count call ≤ 15 + 6 * call.length.toNat := by
  unfold RawVec.PairRemove.Call.count
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem mapRemoveCountBound (call : SortedMap.Remove.Call) :
    call.count ≤ 50 + 11 * call.length.toNat := by
  have search := searchCountBound call.search .lower
  have vector := pairRemoveCountBound call.vector
  change call.search.count .lower ≤ 7 + 5 * call.length.toNat at search
  change RawVec.PairRemove.Call.count call.vector ≤ 15 + 6 * call.length.toNat at vector
  unfold SortedMap.Remove.Call.count
  split
  · omega
  · split
    · omega
    · split <;> omega

private theorem scanCountBound (call : DeleteExtra.Call) (accepted : Nat) :
    call.scanCount accepted ≤ 44 * accepted := by
  induction accepted with
  | zero => rfl
  | succ accepted previous =>
    simp only [DeleteExtra.Call.scanCount, DeleteExtra.Call.iterationCount]
    split <;> omega

private theorem drainCountBound (call : DeleteExtra.Call) (capacity : RawVec.Word)
    (before : Nat → RawVec.Pair) (accepted : Nat) :
    DeleteExtra.drainCount call capacity before accepted ≤ accepted * (58 + 11 * call.length.toNat) := by
  induction accepted with
  | zero => simp [DeleteExtra.drainCount]
  | succ accepted previous =>
    have this := mapRemoveCountBound (DeleteExtra.drainCall call capacity before accepted)
    have remaining : (DeleteExtra.drainCall call capacity before accepted).length.toNat ≤ call.length.toNat := by
      have length := call.length.isLt
      change (BitVec.ofNat 32 (call.length.toNat - accepted)).toNat ≤ call.length.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [DeleteExtra.drainCount, Nat.succ_mul]
    omega

/-- If the map has `n` entries and the helper accepts `k` successors, its
checked count is bounded by a linear search plus `k` removal costs. -/
theorem helperCountBound (call : DeleteExtra.Call) (capacity : RawVec.Word) (accepted : Nat) :
    call.helperCount capacity accepted ≤
      83 + 5 * call.length.toNat + accepted * (102 + 11 * call.length.toNat) := by
  have search := searchCountBound call.search .lower
  change call.search.count .lower ≤ 7 + 5 * call.length.toNat at search
  have scan := scanCountBound call accepted
  have drain := drainCountBound call capacity (call.after accepted) accepted
  rw [show 102 + 11 * call.length.toNat = 44 + (58 + 11 * call.length.toNat) by omega, Nat.mul_add]
  simp only [DeleteExtra.Call.helperCount, DeleteExtra.Call.entryCount]
  repeat' split
  all_goals omega

theorem pairInsertCountBound (call : RawVec.PairInsert.Call) :
    RawVec.PairInsert.Call.count call ≤ 19 + 8 * call.length.toNat := by
  unfold RawVec.PairInsert.Call.count
  repeat' split
  all_goals omega

theorem mapInsertCountBound (call : SortedMap.Insert.Call) :
    call.count ≤ 58 + 13 * call.length.toNat := by
  have search := searchCountBound call.search .lower
  have vector := pairInsertCountBound call.vector
  change call.search.count .lower ≤ 7 + 5 * call.length.toNat at search
  change RawVec.PairInsert.Call.count call.vector ≤ 19 + 8 * call.length.toNat at vector
  unfold SortedMap.Insert.Call.count
  repeat' split
  all_goals omega

open Riscfree.RawVec (Word)

/-- From the entry stack pointer, a 112-byte region contains the outer
frame and either of the nested call chains. The sorted-map insertion
returns before the helper runs. -/
theorem stackGeometry (sp : Word) (fits : 112 ≤ sp.toNat) :
    let outer := Empty.frameBase sp
    let helper := DeleteExtra.frameBase outer
    outer.toNat = sp.toNat - 48 ∧
      (SortedMap.Insert.frameBase outer).toNat = sp.toNat - 80 ∧
      helper.toNat = sp.toNat - 96 ∧
      (SortedMap.Remove.frameBase helper).toNat = sp.toNat - 112 := by
  let outer := Empty.frameBase sp
  let helper := DeleteExtra.frameBase outer
  have outerAddress : outer.toNat = sp.toNat - 48 := by
    have zero := Empty.frameAddress (sp := sp) (by omega) 0#32 (by decide)
    simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero
  have helperAddress : helper.toNat = sp.toNat - 96 := by
    have zero := DeleteExtra.frameAddress (sp := outer) (by omega) 0#32 (by decide)
    simp only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero, outerAddress] at zero
    change helper.toNat = _ at zero
    rw [zero]
    omega
  refine ⟨outerAddress, ?_, helperAddress, ?_⟩
  · have zero := SortedMap.Insert.frameAddress (sp := outer) (by omega) 0#32 (by decide)
    simp only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero, outerAddress] at zero
    rw [zero]
    omega
  · have zero := SortedMap.Remove.frameAddress (sp := helper) (by omega) 0#32 (by decide)
    simp only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero, helperAddress] at zero
    rw [zero]
    omega

end Riscfree.RangeInsert
