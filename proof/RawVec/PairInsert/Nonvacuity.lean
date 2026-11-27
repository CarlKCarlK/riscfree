import RawVec.PairInsert
import RawVec.Model

/-!
# The `RawVec<Pair>` premises can all hold

`rawVecPairInsertSailCorrect` is conditional. This module exhibits machines
that satisfy every premise at once, for each of the routine's five execution
paths, and applies the theorem to them. `Hypotheses` collects the theorem's
premises in the theorem's order, and `Hypotheses.run` applies the theorem to
them, so `Hypotheses` cannot contain fewer premises than the theorem.

The model machine (`RawVec/Model.lean`) holds the 33 linked instruction words
at `0x1000`, the vector header at `0x3000`, and the live pairs at `0x4000`.
The return address is `0x2000`. `modelHypotheses` proves every premise for
any index, value, capacity, and contents whenever the length is at most 1000.
-/

namespace Riscfree.RawVec.PairInsert.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

structure Hypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  indexArgument : initial.a1 = call.index
  keyArgument : initial.a2 = call.value.key
  valueArgument : initial.a3 = call.value.value
  environment : Environment base returnAddress original
  header : Header original call
  buffer : call.valid → Buffer base original call

theorem Hypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : Hypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, -⟩ := rawVecPairInsertSailCorrect base returnAddress original call
    initial premises.entry premises.headerArgument premises.indexArgument premises.keyArgument
    premises.valueArgument premises.environment premises.header premises.buffer
  exact ⟨final, ran, pc, status⟩

/-! ## The model machine -/

open Model (codeBase returnTo Modeled syncModeled tableImage tableWordAt tableWordOutside)

def modelCall (index : Word) (value : Pair) (length capacity : Word) (old : Nat → Pair) : Call :=
  Model.modelCall index value length capacity old

-- The routine at word indices `0x400`–`0x420`.
def image : Model.Image where
  word := Model.tableWord 0x400 instructions
  keys := List.range' 0x1000 132

def frame (call : Call) : Machine := Model.frame image (.ofInsert call)

def initial (call : Call) : Snapshot :=
  { a0 := call.header, a1 := call.index, a2 := call.value.key, a3 := call.value.value }

def machine (call : Call) : Machine := sync codeBase (frame call) { initial call with pc := 0 }

/-! ## The model satisfies every premise -/

section Model

variable {index length capacity : Word} {value : Pair} {old : Nat → Pair}

private theorem routineLength : instructions.length = 33 := rfl

private theorem dataFree : ∀ index, 0xc00 ≤ index → image.word index = none :=
  fun _ above => tableWordOutside 0x400 instructions (Or.inr (by have := routineLength; omega))

private theorem modelMode (call : Call) : MachineMode (machine call) returnTo :=
  Model.modelMode (.ofInsert call) codeBase _ (by decide)

private theorem routineImage {state : Machine} {call : Call} (modeled : Modeled image (.ofInsert call) state) :
    CodeImage instructions codeBase state :=
  tableImage modeled instructions codeBase 0x1000 rfl (by decide) (by decide)
    (fun index bound byte small => by change index < 33 at bound; simp [image]; omega)
    (fun index bound => tableWordAt 0x400 instructions bound)

theorem modelHypotheses (small : length.toNat ≤ 1000) :
    Hypotheses codeBase returnTo (machine (modelCall index value length capacity old))
      (modelCall index value length capacity old) (initial (modelCall index value length capacity old)) :=
  let modeled := syncModeled _ codeBase _
  ⟨(syncSync _ _).symm, rfl, rfl, rfl, rfl, Environment.ofMachine (modelMode _) (routineImage modeled),
    Model.modelHeader modeled dataFree,
    fun _ => Model.modelBuffer modeled dataFree (by decide) (by rw [pairBytes]; omega)⟩

end Model

/-! ## One machine per execution path

The pairs are (10, 100), (20, 200), (30, 300), ... . Each theorem below shows
the premises hold on a concrete machine that takes the named path, and then
applies `rawVecPairInsertSailCorrect` to that machine.
-/

def elements (index : Nat) : Pair :=
  ⟨BitVec.ofNat 32 (10 * (index + 1)), BitVec.ofNat 32 (100 * (index + 1))⟩

-- Insert (25, 250) at the end of two pairs in capacity 4: append.
def appendCall : Call := modelCall 2 ⟨25, 250⟩ 2 4 elements
-- Insert (5, 50) at the front of two pairs in capacity 4: shift both pairs.
def shiftCall : Call := modelCall 0 ⟨5, 50⟩ 2 4 elements
-- Length 5 exceeds capacity 4: invalid length.
def invalidLengthCall : Call := modelCall 0 ⟨5, 50⟩ 5 4 elements
-- Index 3 exceeds length 2: invalid index.
def invalidIndexCall : Call := modelCall 3 ⟨5, 50⟩ 2 4 elements
-- Length 4 equals capacity 4: full.
def fullCall : Call := modelCall 0 ⟨5, 50⟩ 4 4 elements

theorem appendSatisfiable :
    Hypotheses codeBase returnTo (machine appendCall) appendCall (initial appendCall) ∧
      appendCall.valid ∧ appendCall.index = appendCall.length ∧ appendCall.count = 15 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide⟩

theorem shiftSatisfiable :
    Hypotheses codeBase returnTo (machine shiftCall) shiftCall (initial shiftCall) ∧
      shiftCall.valid ∧ shiftCall.index.toNat < shiftCall.length.toNat ∧ shiftCall.count = 35 :=
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
      invalidIndexCall.length.toNat < invalidIndexCall.index.toNat ∧
      invalidIndexCall.status = 2 ∧ invalidIndexCall.count = 6 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide, by decide⟩

theorem fullSatisfiable :
    Hypotheses codeBase returnTo (machine fullCall) fullCall (initial fullCall) ∧
      fullCall.index.toNat ≤ fullCall.length.toNat ∧ fullCall.length = fullCall.capacity ∧
      fullCall.status = 1 ∧ fullCall.count = 7 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide, by decide⟩

/-! ## The theorem's conclusion on each machine -/

theorem appendRuns : ∃ final, Riscfree.RV32.run 15 (machine appendCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  appendSatisfiable.1.run

theorem shiftRuns : ∃ final, Riscfree.RV32.run 35 (machine shiftCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  shiftSatisfiable.1.run

theorem invalidLengthRuns : ∃ final, Riscfree.RV32.run 5 (machine invalidLengthCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 3 :=
  invalidLengthSatisfiable.1.run

theorem invalidIndexRuns : ∃ final, Riscfree.RV32.run 6 (machine invalidIndexCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  invalidIndexSatisfiable.1.run

theorem fullRuns : ∃ final, Riscfree.RV32.run 7 (machine fullCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 1 :=
  fullSatisfiable.1.run

/-! ## The machine-mode premises can all hold

`MachineHypotheses` collects the premises of
`rawVecPairInsertSailCorrectInMachineMode`, which replaces `Environment` with
machine-mode registers and the code image. The same model satisfies them.
-/

structure MachineHypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  indexArgument : initial.a1 = call.index
  keyArgument : initial.a2 = call.value.key
  valueArgument : initial.a3 = call.value.value
  mode : MachineMode original returnAddress
  image : CodeImage instructions base original
  header : Header original call
  buffer : call.valid → Buffer base original call

theorem MachineHypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : MachineHypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, -⟩ := rawVecPairInsertSailCorrectInMachineMode base returnAddress
    original call initial premises.entry premises.headerArgument premises.indexArgument
    premises.keyArgument premises.valueArgument premises.mode premises.image premises.header
    premises.buffer
  exact ⟨final, ran, pc, status⟩

theorem modelMachineHypotheses {index length capacity : Word} {value : Pair} {old : Nat → Pair}
    (small : length.toNat ≤ 1000) :
    MachineHypotheses codeBase returnTo (machine (modelCall index value length capacity old))
      (modelCall index value length capacity old) (initial (modelCall index value length capacity old)) :=
  let premises := modelHypotheses (index := index) (value := value) (capacity := capacity)
    (old := old) small
  let modeled := syncModeled _ codeBase _
  ⟨premises.entry, rfl, rfl, rfl, rfl, modelMode _, routineImage modeled, premises.header,
    premises.buffer⟩

theorem machineAppendRuns : ∃ final, Riscfree.RV32.run 15 (machine appendCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ appendCall _).run

theorem machineShiftRuns : ∃ final, Riscfree.RV32.run 35 (machine shiftCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ shiftCall _).run

theorem machineInvalidLengthRuns :
    ∃ final, Riscfree.RV32.run 5 (machine invalidLengthCall) = some final ∧
      final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 3 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ invalidLengthCall _).run

theorem machineInvalidIndexRuns :
    ∃ final, Riscfree.RV32.run 6 (machine invalidIndexCall) = some final ∧
      final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ invalidIndexCall _).run

theorem machineFullRuns : ∃ final, Riscfree.RV32.run 7 (machine fullCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 1 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ fullCall _).run

end Riscfree.RawVec.PairInsert.Nonvacuity
