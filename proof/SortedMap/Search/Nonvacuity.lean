import SortedMap.Search.Correct
import RawVec.Model

/-!
# The sorted-map search premises can all hold

`sortedMapSearchSailCorrect`, its machine-mode form, and
`sortedMapSearchSailCorrectSorted` are conditional. This module exhibits
machines that satisfy every premise at once, for both bounds and each of the
three execution paths (an empty map, a scan that stops early, and a scan that
passes every entry), and applies the theorems to them. `Hypotheses` and
`MachineHypotheses` collect the premises in the theorems' order, and their
`run` lemmas apply the theorems, so neither bundle can hold fewer premises
than its theorem.

The model machine is the RawVec one (`RawVec/Model.lean`): the 13 linked
instruction words at `0x1000`, the map header at `0x3000`, the entries at
`0x4000`, and the return address `0x2000`. Its capacity word equals the length;
the searches never read it.
-/

namespace Riscfree.SortedMap.Search.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

structure Hypotheses (bound : Bound) (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  keyArgument : initial.a1 = call.key
  environment : Environment bound base returnAddress original
  header : Header original call
  keys : 0 < call.length.toNat → Keys original call

theorem Hypotheses.run {bound : Bound} {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : Hypotheses bound base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run (call.count bound) original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some (BitVec.ofNat 32 (call.result bound)) ∧
      final.mem = original.mem := by
  obtain ⟨final, ran, pc, result, memory, -⟩ := sortedMapSearchSailCorrect bound base returnAddress
    original call initial premises.entry premises.headerArgument premises.keyArgument
    premises.environment premises.header premises.keys
  exact ⟨final, ran, pc, result, memory⟩

structure MachineHypotheses (bound : Bound) (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  keyArgument : initial.a1 = call.key
  mode : MachineMode original returnAddress
  image : CodeImage (instructions bound) base original
  header : Header original call
  keys : 0 < call.length.toNat → Keys original call

theorem MachineHypotheses.run {bound : Bound} {base returnAddress : Word} {original : Machine}
    {call : Call} {initial : Snapshot}
    (premises : MachineHypotheses bound base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run (call.count bound) original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some (BitVec.ofNat 32 (call.result bound)) ∧
      final.mem = original.mem := by
  obtain ⟨final, ran, pc, result, memory, -⟩ := sortedMapSearchSailCorrectInMachineMode bound base
    returnAddress original call initial premises.entry premises.headerArgument premises.keyArgument
    premises.mode premises.image premises.header premises.keys
  exact ⟨final, ran, pc, result, memory⟩

theorem MachineHypotheses.runSorted {bound : Bound} {base returnAddress : Word} {original : Machine}
    {call : Call} {initial : Snapshot}
    (premises : MachineHypotheses bound base returnAddress original call initial)
    (sorted : Sorted (entriesOf call.old call.length.toNat)) :
    ∃ final, Riscfree.RV32.run (call.count bound) original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 =
        some (BitVec.ofNat 32 (rank bound (entriesOf call.old call.length.toNat) call.key)) ∧
      final.mem = original.mem :=
  sortedMapSearchSailCorrectSorted bound base returnAddress original call initial premises.entry
    premises.headerArgument premises.keyArgument premises.mode premises.image premises.header
    premises.keys sorted

/-! ## The model machine -/

open Model (codeBase returnTo Modeled syncModeled tableImage tableWordAt tableWordOutside)

def modelCall (key length : Word) (old : Nat → Pair) : Call :=
  { header := 0x3000, key, length, data := 0x4000, old }

-- The model's memory, with a capacity word equal to the length.
def contents (call : Call) : Model.Contents Pair :=
  .ofRemove (Model.modelRemoveCall 0 call.length call.length call.old)

-- The routine at word indices `0x400`–`0x40c`.
def image (bound : Bound) : Model.Image where
  word := Model.tableWord 0x400 (instructions bound)
  keys := List.range' 0x1000 52

def frame (bound : Bound) (call : Call) : Machine := Model.frame (image bound) (contents call)

def initial (call : Call) : Snapshot := { a0 := call.header, a1 := call.key }

def machine (bound : Bound) (call : Call) : Machine :=
  sync codeBase (frame bound call) { initial call with pc := 0 }

section Model

variable {bound : Bound} {key length : Word} {old : Nat → Pair}

private theorem dataFree : ∀ index, 0xc00 ≤ index → (image bound).word index = none :=
  fun _ above => tableWordOutside 0x400 (instructions bound)
    (Or.inr (by rw [instructionsLength]; omega))

private theorem routineImage {state : Machine} {call : Call}
    (modeled : Modeled (image bound) (contents call) state) :
    CodeImage (instructions bound) codeBase state :=
  tableImage modeled (instructions bound) codeBase 0x1000 rfl (by decide)
    (by rw [instructionsLength]; decide)
    (fun index inside byte small => by
      rw [instructionsLength] at inside
      simp only [image, List.mem_range'_1]; omega)
    (fun index inside => tableWordAt 0x400 (instructions bound) inside)

private theorem modelMode (call : Call) : MachineMode (machine bound call) returnTo :=
  Model.modelMode (contents call) codeBase _ (by decide)

theorem modelMachineHypotheses (small : length.toNat ≤ 1000) :
    MachineHypotheses bound codeBase returnTo (machine bound (modelCall key length old))
      (modelCall key length old) (initial (modelCall key length old)) := by
  let call := modelCall key length old
  have modeled : Modeled (image bound) (contents call) (machine bound call) := syncModeled _ codeBase _
  have header := Model.modelRemoveHeader modeled dataFree
  refine ⟨(syncSync _ _).symm, rfl, rfl, modelMode _, routineImage modeled,
    ⟨by change 0x3000 + 8 ≤ 2 ^ 32; decide, header.lengthReadable, header.lengthWord⟩,
    fun _ => ?_⟩
  have buffer := Model.modelRemoveBuffer modeled dataFree (codeBytes := 52) (by decide)
    (by rw [pairBytes]; change 8 * length.toNat ≤ 0x100000; omega)
  refine ⟨buffer.fits, buffer.dataReadable, buffer.dataWord, fun index inside => ?_,
    fun index inside => (buffer.live index inside).1⟩
  have below : index < length.toNat := inside
  have small : Element.bytes Pair * (index + 1) ≤ 0x100000 := by
    rw [pairBytes]; omega
  exact (Model.elementReadable modeled small).1

theorem modelHypotheses (small : length.toNat ≤ 1000) :
    Hypotheses bound codeBase returnTo (machine bound (modelCall key length old))
      (modelCall key length old) (initial (modelCall key length old)) :=
  let premises := modelMachineHypotheses (bound := bound) (key := key) (old := old) small
  ⟨premises.entry, premises.headerArgument, premises.keyArgument,
    Environment.ofMachine premises.mode premises.image, premises.header, premises.keys⟩

end Model

/-! ## One machine per execution path

The entries are (10, 100), (20, 200), (30, 300). Each theorem shows the
premises hold on a concrete machine that takes the named path, and that the
contents are sorted.
-/

def entries (index : Nat) : Pair :=
  ⟨BitVec.ofNat 32 (10 * (index + 1)), BitVec.ofNat 32 (100 * (index + 1))⟩

theorem entriesSorted : Sorted (entriesOf entries 3) := by
  unfold Sorted entriesOf entries
  decide

-- The lower bound of 25 stops at 30, after passing two entries.
def lowerStopCall : Call := modelCall 25 3 entries
-- The lower bound of 31 passes every entry.
def lowerAllCall : Call := modelCall 31 3 entries
-- The upper bound of 20 passes 10 and 20 and stops at 30.
def upperStopCall : Call := modelCall 20 3 entries
-- The upper bound of 30 passes every entry.
def upperAllCall : Call := modelCall 30 3 entries
-- An empty map, for either bound.
def emptyCall : Call := modelCall 7 0 entries

theorem lowerStopSatisfiable :
    MachineHypotheses .lower codeBase returnTo (machine .lower lowerStopCall) lowerStopCall
        (initial lowerStopCall) ∧
      lowerStopCall.result .lower = 2 ∧ lowerStopCall.result .lower < lowerStopCall.length.toNat ∧
      lowerStopCall.count .lower = 17 :=
  ⟨modelMachineHypotheses (by decide), by decide, by decide, by decide⟩

theorem lowerAllSatisfiable :
    MachineHypotheses .lower codeBase returnTo (machine .lower lowerAllCall) lowerAllCall
        (initial lowerAllCall) ∧
      lowerAllCall.result .lower = 3 ∧ lowerAllCall.count .lower = 21 :=
  ⟨modelMachineHypotheses (by decide), by decide, by decide⟩

theorem upperStopSatisfiable :
    MachineHypotheses .upper codeBase returnTo (machine .upper upperStopCall) upperStopCall
        (initial upperStopCall) ∧
      upperStopCall.result .upper = 2 ∧ upperStopCall.result .upper < upperStopCall.length.toNat ∧
      upperStopCall.count .upper = 17 :=
  ⟨modelMachineHypotheses (by decide), by decide, by decide, by decide⟩

theorem upperAllSatisfiable :
    MachineHypotheses .upper codeBase returnTo (machine .upper upperAllCall) upperAllCall
        (initial upperAllCall) ∧
      upperAllCall.result .upper = 3 ∧ upperAllCall.count .upper = 21 :=
  ⟨modelMachineHypotheses (by decide), by decide, by decide⟩

theorem emptySatisfiable (bound : Bound) :
    MachineHypotheses bound codeBase returnTo (machine bound emptyCall) emptyCall (initial emptyCall) ∧
      emptyCall.length.toNat = 0 ∧ emptyCall.result bound = 0 ∧ emptyCall.count bound = 4 := by
  refine ⟨modelMachineHypotheses (by decide), by decide, ?_, ?_⟩ <;> cases bound <;> decide

/-! ## The theorems' conclusions on each machine -/

theorem lowerStopRuns : ∃ final, Riscfree.RV32.run 17 (machine .lower lowerStopCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  let ⟨final, ran, pc, result, _⟩ := lowerStopSatisfiable.1.run
  ⟨final, ran, pc, result⟩

theorem lowerAllRuns : ∃ final, Riscfree.RV32.run 21 (machine .lower lowerAllCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 3 :=
  let ⟨final, ran, pc, result, _⟩ := lowerAllSatisfiable.1.run
  ⟨final, ran, pc, result⟩

theorem upperStopRuns : ∃ final, Riscfree.RV32.run 17 (machine .upper upperStopCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  let ⟨final, ran, pc, result, _⟩ := upperStopSatisfiable.1.run
  ⟨final, ran, pc, result⟩

theorem upperAllRuns : ∃ final, Riscfree.RV32.run 21 (machine .upper upperAllCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 3 :=
  let ⟨final, ran, pc, result, _⟩ := upperAllSatisfiable.1.run
  ⟨final, ran, pc, result⟩

theorem emptyRuns (bound : Bound) :
    ∃ final, Riscfree.RV32.run 4 (machine bound emptyCall) = some final ∧
      final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 := by
  obtain ⟨premises, _, result, count⟩ := emptySatisfiable bound
  obtain ⟨final, ran, pc, value, _⟩ := premises.run
  rw [count] at ran
  rw [result] at value
  exact ⟨final, ran, pc, value⟩

-- The `Environment` form of the theorem holds on the same machines.
theorem environmentRuns : ∃ final, Riscfree.RV32.run 17 (machine .lower lowerStopCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  let ⟨final, ran, pc, result, _⟩ :=
    (modelHypotheses (bound := .lower) (by decide) : Hypotheses _ _ _ _ lowerStopCall _).run
  ⟨final, ran, pc, result⟩

-- The sorted form: on the sorted entries the result is the rank.
theorem sortedRanks :
    rank .lower (entriesOf entries 3) 25 = 2 ∧ rank .upper (entriesOf entries 3) 20 = 2 := by
  unfold rank entriesOf entries
  decide

theorem lowerStopRanks : ∃ final, Riscfree.RV32.run 17 (machine .lower lowerStopCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 := by
  obtain ⟨final, ran, pc, result, _⟩ := lowerStopSatisfiable.1.runSorted entriesSorted
  exact ⟨final, ran, pc, by rw [result]; rfl⟩

end Riscfree.SortedMap.Search.Nonvacuity
