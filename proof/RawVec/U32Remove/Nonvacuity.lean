import RawVec.U32Remove
import RawVec.Model

/-!
# The `raw_vec_u32_remove` premises can all hold

`rawVecU32RemoveSailCorrect` is conditional. This module exhibits machines
that satisfy every premise at once, for each of the routine's four execution
paths, and applies the theorem to them. `Hypotheses` collects the theorem's
premises in the theorem's order, and `Hypotheses.run` applies the theorem to
them, so `Hypotheses` cannot contain fewer premises than the theorem.

The model machine (`RawVec/Model.lean`) holds the 23 linked instruction words
at `0x1000`, the vector header at `0x3000`, and the live words at `0x4000`.
The return address is `0x2000`. `modelHypotheses` proves every premise for
any index, capacity, and contents whenever the length is at most 1000.
-/

namespace Riscfree.RawVec.U32Remove.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

structure Hypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  indexArgument : initial.a1 = call.index
  environment : Environment base returnAddress original
  header : Header original call
  buffer : call.valid → Buffer base original call

theorem Hypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : Hypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, -⟩ := rawVecU32RemoveSailCorrect base returnAddress original call
    initial premises.entry premises.headerArgument premises.indexArgument premises.environment
    premises.header premises.buffer
  exact ⟨final, ran, pc, status⟩

/-! ## The model machine -/

open Model (codeBase returnTo Modeled syncModeled tableImage tableWordAt tableWordOutside)

def modelCall (index length capacity : Word) (old : Nat → Word) : Call :=
  Model.modelRemoveCall index length capacity old

-- The routine at word indices `0x400`–`0x416`.
def image : Model.Image where
  word := Model.tableWord 0x400 instructions
  keys := List.range' 0x1000 92

def frame (call : Call) : Machine := Model.frame image (.ofRemove call)

def initial (call : Call) : Snapshot := { a0 := call.header, a1 := call.index }

def machine (call : Call) : Machine := sync codeBase (frame call) { initial call with pc := 0 }

/-! ## The model satisfies every premise -/

section Model

variable {index length capacity : Word} {old : Nat → Word}

private theorem routineLength : instructions.length = 23 := rfl

private theorem dataFree : ∀ index, 0xc00 ≤ index → image.word index = none :=
  fun _ above => tableWordOutside 0x400 instructions (Or.inr (by have := routineLength; omega))

private theorem modelMode (call : Call) : MachineMode (machine call) returnTo :=
  Model.modelMode (.ofRemove call) codeBase _ (by decide)

private theorem routineImage {state : Machine} {call : Call}
    (modeled : Modeled image (.ofRemove call) state) : CodeImage instructions codeBase state :=
  tableImage modeled instructions codeBase 0x1000 rfl (by decide) (by decide)
    (fun index bound byte small => by change index < 23 at bound; simp [image]; omega)
    (fun index bound => tableWordAt 0x400 instructions bound)

theorem modelHypotheses (small : length.toNat ≤ 1000) :
    Hypotheses codeBase returnTo (machine (modelCall index length capacity old))
      (modelCall index length capacity old) (initial (modelCall index length capacity old)) :=
  let modeled := syncModeled _ codeBase _
  ⟨(syncSync _ _).symm, rfl, rfl, Environment.ofMachine (modelMode _) (routineImage modeled),
    Model.modelRemoveHeader modeled dataFree,
    fun _ => Model.modelRemoveBuffer modeled dataFree (by decide) (by rw [wordBytes]; omega)⟩

end Model

/-! ## One machine per execution path

The elements are 10, 20, 30, ... . Each theorem below shows the premises hold
on a concrete machine that takes the named path, and then applies
`rawVecU32RemoveSailCorrect` to that machine.
-/

def elements (index : Nat) : Word := BitVec.ofNat 32 (10 * (index + 1))

-- Remove index 1 of four words: shift the two after it.
def shiftCall : Call := modelCall 1 4 4 elements
-- Remove index 3 of four words: the last, so nothing shifts.
def lastCall : Call := modelCall 3 4 4 elements
-- Length 5 exceeds capacity 4: invalid length.
def invalidLengthCall : Call := modelCall 0 5 4 elements
-- Index 4 is not below length 4: invalid index.
def invalidIndexCall : Call := modelCall 4 4 4 elements
-- An empty vector takes the invalid-index path for every index.
def emptyCall : Call := modelCall 0 0 4 elements

theorem shiftSatisfiable :
    Hypotheses codeBase returnTo (machine shiftCall) shiftCall (initial shiftCall) ∧
      shiftCall.valid ∧ shiftCall.index.toNat + 1 < shiftCall.length.toNat ∧
      shiftCall.count = 23 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide⟩

theorem lastSatisfiable :
    Hypotheses codeBase returnTo (machine lastCall) lastCall (initial lastCall) ∧
      lastCall.valid ∧ lastCall.index.toNat + 1 = lastCall.length.toNat ∧ lastCall.count = 9 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide⟩

theorem invalidLengthSatisfiable :
    Hypotheses codeBase returnTo (machine invalidLengthCall) invalidLengthCall
        (initial invalidLengthCall) ∧
      invalidLengthCall.capacity.toNat < invalidLengthCall.length.toNat ∧
      invalidLengthCall.status = 3 ∧ invalidLengthCall.count = 5 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide⟩

theorem invalidIndexSatisfiable :
    Hypotheses codeBase returnTo (machine invalidIndexCall) invalidIndexCall
        (initial invalidIndexCall) ∧
      invalidIndexCall.length.toNat ≤ invalidIndexCall.capacity.toNat ∧
      invalidIndexCall.length.toNat ≤ invalidIndexCall.index.toNat ∧
      invalidIndexCall.status = 2 ∧ invalidIndexCall.count = 6 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide, by decide⟩

theorem emptySatisfiable :
    Hypotheses codeBase returnTo (machine emptyCall) emptyCall (initial emptyCall) ∧
      emptyCall.length.toNat = 0 ∧ emptyCall.status = 2 ∧ emptyCall.count = 6 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide⟩

/-! ## The theorem's conclusion on each machine -/

theorem shiftRuns : ∃ final, Riscfree.RV32.run 23 (machine shiftCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  shiftSatisfiable.1.run

theorem lastRuns : ∃ final, Riscfree.RV32.run 9 (machine lastCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  lastSatisfiable.1.run

theorem invalidLengthRuns : ∃ final, Riscfree.RV32.run 5 (machine invalidLengthCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 3 :=
  invalidLengthSatisfiable.1.run

theorem invalidIndexRuns : ∃ final, Riscfree.RV32.run 6 (machine invalidIndexCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  invalidIndexSatisfiable.1.run

theorem emptyRuns : ∃ final, Riscfree.RV32.run 6 (machine emptyCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  emptySatisfiable.1.run

/-! ## The machine-mode premises can all hold

`MachineHypotheses` collects the premises of
`rawVecU32RemoveSailCorrectInMachineMode`, which replaces `Environment` with
machine-mode registers and the code image. The same model satisfies them.
-/

structure MachineHypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  indexArgument : initial.a1 = call.index
  mode : MachineMode original returnAddress
  image : CodeImage instructions base original
  header : Header original call
  buffer : call.valid → Buffer base original call

theorem MachineHypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : MachineHypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, -⟩ := rawVecU32RemoveSailCorrectInMachineMode base returnAddress
    original call initial premises.entry premises.headerArgument premises.indexArgument
    premises.mode premises.image premises.header premises.buffer
  exact ⟨final, ran, pc, status⟩

theorem modelMachineHypotheses {index length capacity : Word} {old : Nat → Word}
    (small : length.toNat ≤ 1000) :
    MachineHypotheses codeBase returnTo (machine (modelCall index length capacity old))
      (modelCall index length capacity old) (initial (modelCall index length capacity old)) :=
  let premises := modelHypotheses (index := index) (capacity := capacity) (old := old) small
  let modeled := syncModeled _ codeBase _
  ⟨premises.entry, rfl, rfl, modelMode _, routineImage modeled, premises.header, premises.buffer⟩

theorem machineShiftRuns : ∃ final, Riscfree.RV32.run 23 (machine shiftCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ shiftCall _).run

theorem machineLastRuns : ∃ final, Riscfree.RV32.run 9 (machine lastCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ lastCall _).run

theorem machineInvalidLengthRuns :
    ∃ final, Riscfree.RV32.run 5 (machine invalidLengthCall) = some final ∧
      final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 3 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ invalidLengthCall _).run

theorem machineInvalidIndexRuns :
    ∃ final, Riscfree.RV32.run 6 (machine invalidIndexCall) = some final ∧
      final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ invalidIndexCall _).run

theorem machineEmptyRuns : ∃ final, Riscfree.RV32.run 6 (machine emptyCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ emptyCall _).run

end Riscfree.RawVec.U32Remove.Nonvacuity
