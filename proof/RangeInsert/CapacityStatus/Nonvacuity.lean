import RangeInsert.CapacityStatus
import RawVec.Nonvacuity
import SortedMap.Insert.Nonvacuity

/-! Concrete invocations of the full collection calls used by range
insertion, including calls with no backing slots. -/

namespace Riscfree.RangeInsert.CapacityStatus.Nonvacuity

open Riscfree.RV32
open Riscfree.RawVec (Word)
open RawVec.Model (codeBase returnTo)
open Nonempty (Call)

structure ScratchFull (base ret : Word) (original : Machine) (append : RawVec.Call)
    (initial : RawVec.Snapshot) : Prop where
  call : RawVec.Nonvacuity.Hypotheses base ret original append initial
  atEnd : append.index = append.length
  full : append.length = append.capacity

theorem ScratchFull.run {base ret : Word} {original : Machine} {append : RawVec.Call}
    {initial : RawVec.Snapshot} (premises : ScratchFull base ret original append initial) :
    ∃ state : RawVec.Snapshot,
      Riscfree.RV32.run 7 original = some (sync base original state) ∧
      state.pc = ret - base ∧ state.a0 = 1 :=
  DeleteExtra.scratchAppendFullRun premises.atEnd premises.full premises.call.entry
    premises.call.headerArgument premises.call.indexArgument premises.call.valueArgument
    premises.call.environment premises.call.header

private def appendCall (capacity : Word) : RawVec.Call :=
  RawVec.Nonvacuity.modelCall capacity 123 capacity capacity RawVec.Nonvacuity.elements

private theorem scratchFull (capacity : Word) (small : capacity.toNat ≤ 1000) :
    ScratchFull codeBase returnTo (RawVec.Nonvacuity.machine (appendCall capacity))
      (appendCall capacity) (RawVec.Nonvacuity.initial (appendCall capacity)) :=
  ⟨RawVec.Nonvacuity.modelHypotheses small, rfl, rfl⟩

example := (scratchFull 0 (by decide)).run
example := (scratchFull 1 (by decide)).run

structure MapFull (base ret : Word) (original : Machine) (call : Call) (capacity : Word)
    (initial : SortedMap.Insert.Snapshot) : Prop where
  insert : SortedMap.Insert.Nonvacuity.Hypotheses base ret original (call.freshInsert capacity) initial
  fresh : call.path = .fresh
  full : call.length = capacity
  sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)
  ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat

theorem MapFull.run {base ret : Word} {original : Machine} {call : Call} {capacity : Word}
    {initial : SortedMap.Insert.Snapshot} (premises : MapFull base ret original call capacity initial) :
    ∃ state : SortedMap.Insert.Snapshot,
      let memory := SortedMap.Insert.pushed original.mem initial.sp initial
      Riscfree.RV32.run (call.freshInsert capacity).count original =
        some (sync base { original with mem := memory } state) ∧
      state.pc = ret - base ∧ state.a0 = 1 ∧
      state.ra = initial.ra ∧ state.sp = initial.sp ∧ state.s0 = initial.s0 ∧
      state.s1 = initial.s1 ∧ state.s2 = initial.s2 ∧ state.s3 = initial.s3 :=
  Call.freshFullRun premises.fresh premises.full premises.sorted premises.ordered
    premises.insert.entry premises.insert.headerArgument premises.insert.keyArgument
    premises.insert.valueArgument premises.insert.environment premises.insert.header
    premises.insert.stack (premises.insert.keys (by
      change call.length.toNat ≤ capacity.toNat
      rw [premises.full]))

open SortedMap.Insert.Nonvacuity (base modelCall machine initial modelHypotheses)

private def rangeCall (key capacity : Word) : Call :=
  let insert := modelCall key capacity capacity
  ⟨insert.header, insert.length, insert.data, insert.old, insert.value.key, insert.value.value⟩

private theorem mapFull (key capacity : Word) (small : capacity.toNat ≤ 1000)
    (fresh : (rangeCall key capacity).path = .fresh)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf (rangeCall key capacity).old capacity.toNat))
    (ordered : ∀ index < capacity.toNat,
      ((rangeCall key capacity).old index).key.toNat ≤ ((rangeCall key capacity).old index).value.toNat) :
    MapFull base returnTo (machine (modelCall key capacity capacity)) (rangeCall key capacity) capacity
      (initial (modelCall key capacity capacity)) :=
  ⟨modelHypotheses key capacity capacity small, fresh, rfl, sorted, ordered⟩

private theorem sortedSlots (key : Word) (capacity : Word) (small : capacity.toNat ≤ 1) :
    SortedMap.Sorted (SortedMap.entriesOf (rangeCall key capacity).old capacity.toNat) := by
  rw [← SortedMap.entriesOf_length (rangeCall key capacity).old capacity.toNat] at small
  exact List.pairwise_iff_getElem.mpr fun first second firstIn secondIn increasing => by omega

example := (mapFull 5 0 (by decide) (by decide) (sortedSlots 5 0 (by decide)) (by
  intro index outside
  change index < 0 at outside
  omega)).run

private theorem oneRange :
    ∀ index < (1#32).toNat,
      ((rangeCall 5 1).old index).key.toNat ≤ ((rangeCall 5 1).old index).value.toNat := by
  intro index inside
  change index < 1 at inside
  have zero : index = 0 := by omega
  subst index
  decide

example := (mapFull 5 1 (by decide) (by decide) (sortedSlots 5 1 (by decide)) oneRange).run
example := (mapFull 400 1 (by decide) (by decide) (sortedSlots 400 1 (by decide)) oneRange).run

end Riscfree.RangeInsert.CapacityStatus.Nonvacuity
