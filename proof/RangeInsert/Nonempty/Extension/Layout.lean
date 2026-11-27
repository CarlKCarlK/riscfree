import RangeInsert.Nonempty.Layout
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

theorem InitialLayout.extensionPrefix {base returnAddress : Word} {original : Machine}
    {initial : Empty.Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high)
    (entry : original = sync base original { initial with pc := 0 })
    (link : initial.ra = returnAddress) (mode : MachineMode original returnAddress)
    (arguments : Arguments initial call) (nonempty : call.start.toNat ≤ call.stop.toNat)
    (found : 0 < call.rank) (touches : call.start.toNat ≤ call.predecessor.value.toNat + 1)
    (grows : call.predecessor.value.toNat < call.stop.toNat) :
    ExtensionPrefix base returnAddress original initial call low high := by
  have mapLength := layout.map.lengthFits
  have rankBound := call.rank_le
  have indexIn : call.rank - 1 < call.length.toNat := by omega
  have indexFits : call.rank - 1 < capacity.toNat := by omega
  refine ⟨layout.outerFrame entry link mode, arguments, layout.predecessorMap, nonempty, found, touches, grows,
    layout.cache.fits, ?_, layout.cache.low, layout.cache.high, layout.cache.readable.1, layout.cache.readable.2,
    layout.cache.writable.1, layout.cache.writable.2, (layout.map.pairsWritable _ indexFits).2,
    layout.stack.scratchWritable, ?_, ?_⟩
  · intro byte first last
    exact stackDisjointOuter layout.stack.fits (layout.apart.cacheStack byte ⟨first, last⟩)
  · intro byte first last
    have codeApart := layout.apart.code _ (List.mem_cons_self ..)
    have cacheAway := codeApart.2.2.1 byte ⟨first, last⟩
    have mapAway := codeApart.2.1 byte ⟨first, last⟩
    change ¬ (initial.a1.toNat ≤ byte ∧ byte < initial.a1.toNat + 8) at cacheAway
    constructor
    · omega
    · by_contra inside
      push_neg at inside
      exact mapAway (layout.map.entryContained indexIn (by omega) inside.2)
  · intro byte first last
    have apart := layout.apart.mapCache byte (layout.map.entryContained indexIn first (by omega))
    change ¬ (initial.a1.toNat ≤ byte ∧ byte < initial.a1.toNat + 8) at apart
    omega

end Riscfree.RangeInsert.Nonempty
