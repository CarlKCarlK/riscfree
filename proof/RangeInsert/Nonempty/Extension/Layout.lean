import RangeInsert.Nonempty.Extension
import RangeInsert.Nonempty.Correspondence

namespace Riscfree.RangeInsert.Nonempty

open Riscfree.RV32
open Riscfree.RawVec (Word Pair)
open Empty (Snapshot)
open RangeSetBlazeValidation

/-- The map after extending before the deletion helper runs. Only the
predecessor's end changes. -/
def Call.extendedEntries (call : Call) (index : Nat) : Pair :=
  if index = call.rank - 1 then ⟨(call.old index).key, call.stop⟩ else call.old index

theorem Call.extendedKey (call : Call) (index : Nat) :
    (call.extendedEntries index).key = (call.old index).key := by
  unfold Call.extendedEntries
  split <;> rfl

def Call.extensionHelper (call : Call) (initial : Snapshot) (low high : Word) : DeleteExtra.Call :=
  let sp := Empty.frameBase initial.sp
  { mapRef := sp + 4, header := call.header, length := call.length, data := call.data,
    old := call.extendedEntries, cache := initial.a1, low := extendLow call low,
    high := extendHigh call low high, start := call.predecessor.key, stop := call.stop, keys := sp + 8 }

/-- The helper's lower bound selects the entry whose end the caller wrote. -/
theorem Call.extensionPosition {call : Call} (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (found : 0 < call.rank) (initial : Snapshot) (low high : Word) :
    (call.extensionHelper initial low high).position = call.rank - 1 := by
  let index := call.rank - 1
  have bound := call.rank_le
  have inside : index < call.length.toNat := by dsimp [index]; omega
  change SortedMap.scan .lower call.predecessor.key call.extendedEntries 0 call.length.toNat = index
  refine DeleteExtra.scan_stopsAt call.predecessor.key call.extendedEntries index ?_ ?_
    0 call.length.toNat (Nat.zero_le _) (by omega)
  · intro before earlier
    rw [call.extendedKey]
    have beforeBound : before < (SortedMap.entriesOf call.old call.length.toNat).length := by
      rw [SortedMap.entriesOf_length]
      omega
    have indexBound : index < (SortedMap.entriesOf call.old call.length.toNat).length := by
      rw [SortedMap.entriesOf_length]
      exact inside
    have ordered := (List.pairwise_iff_getElem.mp sorted) before index beforeBound indexBound earlier
    simpa only [SortedMap.entriesOf_getElem] using ordered
  · rw [call.extendedKey]
    exact Nat.lt_irrefl _

theorem ExtensionCalling.helperArguments {base : Word} {initial : Snapshot} {call : Call}
    {caller : Snapshot} {helper : DeleteExtra.Snapshot} {low high : Word}
    (calling : ExtensionCalling base initial call caller)
    (a0 : helper.a0 = caller.a0) (a1 : helper.a1 = caller.a1)
    (a2 : helper.a2 = caller.a2) (a3 : helper.a3 = caller.a3) (a4 : helper.a4 = caller.a4) :
    DeleteExtra.Arguments helper (call.extensionHelper initial low high) :=
  ⟨a0.trans (calling.mapRef.trans (congrArg (· + 4#32) calling.sp)),
    a1.trans calling.cache, a2.trans calling.start, a3.trans calling.stop,
    a4.trans (calling.keys.trans (congrArg (· + 8#32) calling.sp))⟩

end Riscfree.RangeInsert.Nonempty
