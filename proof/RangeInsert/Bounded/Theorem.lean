import RangeInsert.Bounded.Unified
import RangeInsert.Theorem

/-! The bounded linked range insertion against the production model, for
every map and scratch capacity. -/

namespace Riscfree.RangeInsert.Bounded.Unified

open RangeSetBlazeValidation RangeSetBlazeValidation.RangeSetBlaze
open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word)
open Empty (Snapshot)
open OuterLayout
open Nonempty (Call Arguments Result Represents WritableByte)

/-- The bounded routine's premises: the entry machine, the initial layout,
a map that represents a canonical set, and an accurate cached count. There
is no spare-slot or scratch-capacity premise. -/
structure InsertionPremises (base returnAddress : Word) (original : Machine)
    (initial : Snapshot) (call : Call) (capacity low high : Word) (set : RangeSetBlaze) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  mode : MachineMode original returnAddress
  arguments : Arguments initial call
  layout : InitialLayout base original initial call capacity low high
  represents : Represents set call
  accurate : (BitVec.append high low).toNat = set.cardinality

theorem InsertionPremises.toPremises {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word} {set : RangeSetBlaze}
    (premises : InsertionPremises base returnAddress original initial call capacity low high set) :
    Premises base returnAddress original initial call capacity low high :=
  ⟨premises.entry, premises.mode, premises.arguments, premises.layout,
    premises.represents.sorted, premises.represents.ordered⟩

/-- The bounded linked range insertion returns to its caller after the exact
count of its path, with every register outside the caller-saved list and
every byte it may not write unchanged, and the map header's data pointer and
capacity intact. It returns OK exactly when the transient map and scratch
storage fit, with no spurious FULL. On OK, it stores the production model's
result: the canonical union of the set and the input, with its cardinality
cached. On FULL, the header's length is within its capacity, so the caller
can dispose of the allocation. -/
theorem InsertionPremises.run {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word} {set : RangeSetBlaze}
    (premises : InsertionPremises base returnAddress original initial call capacity low high set) :
    let result := boundedResult call initial capacity low high
    let model := internalAddProduction set (BitVec.append high low).toNat call.input
    let outcome := call.capacityOutcome initial low high capacity
    ∃ final, Riscfree.RV32.run result.count original = some final ∧
      Claims returnAddress original final initial call capacity low high ∧
      WordAt final.mem call.header.toNat call.data ∧
      WordAt final.mem (call.header.toNat + 8) capacity ∧
      (outcome = .success →
        result.Represents model ∧
        model.setResult.toSet = set.toSet ∪ call.input.toSet ∧
        model.cachedLength = model.setResult.cardinality) := by
  intro result model outcome
  obtain ⟨final, ran, claims⟩ := premises.toPremises.run
  obtain ⟨dataKept, capacityKept⟩ := metadataKept premises.layout claims.kept
  refine ⟨final, ran, claims, dataKept, capacityKept, fun ok => ⟨?_, ?_⟩⟩
  · have spare : call.path = .fresh → call.length.toNat < capacity.toNat :=
      fun fresh => ((Call.capacitySuccess_iff_pathRoom premises.layout.map.lengthFits).mp ok).1 fresh
    exact call.resultRepresents initial premises.represents premises.accurate spare
  · exact internalAddProduction_correct set (BitVec.append high low).toNat call.input premises.accurate

end Riscfree.RangeInsert.Bounded.Unified
