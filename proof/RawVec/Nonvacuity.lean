import RawVec.Shim
import RawVec.Model

/-!
# The RawVec premises can all hold

`rawVecU32InsertSailCorrect` is conditional. If its premises could never hold
together, it would be vacuously true. This module exhibits machines that
satisfy every premise at once, for each of the routine's five execution paths,
and applies the theorem to them.

`Hypotheses` collects the theorem's premises in the theorem's order.
`Hypotheses.run` applies the theorem to them, so `Hypotheses` cannot contain
fewer premises than the theorem.

The model machine (`RawVec/Model.lean`) holds the 30 linked instruction words
at `0x1000`, the vector header at `0x3000`, and the live elements at `0x4000`.
The return address is `0x2000`. `modelHypotheses` proves every premise for any index, value, capacity, and
contents whenever the length is at most 1000.
-/

namespace Riscfree.RawVec.Nonvacuity

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

structure Hypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  indexArgument : initial.a1 = call.index
  valueArgument : initial.a2 = call.value
  environment : Environment base returnAddress original
  header : Header original call
  buffer : call.valid → Buffer base original call

theorem Hypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : Hypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, -⟩ := rawVecU32InsertSailCorrect base returnAddress original call
    initial premises.entry premises.headerArgument premises.indexArgument premises.valueArgument
    premises.environment premises.header premises.buffer
  exact ⟨final, ran, pc, status⟩

/-! ## The model machine

`RawVec/Model.lean` builds the machine. This routine's image places the shim at
word indices `0x3d1`–`0x3d7` and the routine at `0x400`–`0x41d`.
-/

open Model (codeBase returnTo Modeled syncModeled frameState tableImage tableWordAt
  tableWordOutside readable writable)

-- The shim's `call` reaches `shimModelBase + routineOffset`, which is `codeBase`.
def shimModelBase : Word := 0xf44
def stackTop : Word := 0x5000

def modelCall (index value length capacity : Word) (old : Nat → Word) : Call :=
  Model.modelCall index value length capacity old

def image : Model.Image where
  word index := (Model.tableWord 0x3d1 shimInstructions index).or (Model.tableWord 0x400 instructions index)
  keys := List.range' 0xf44 28 ++ List.range' 0x1000 120

def frame (call : Call) : Machine := Model.frame image call

def initial (call : Call) : Snapshot := { a0 := call.header, a1 := call.index, a2 := call.value }

def machine (call : Call) : Machine := sync codeBase (frame call) { initial call with pc := 0 }

/-! ## The model satisfies every premise -/

section Model

variable {index value length capacity : Word} {old : Nat → Word}

private theorem shimLength : shimInstructions.length = 7 := rfl

private theorem routineLength : instructions.length = 30 := rfl

private theorem dataFree : ∀ index, 0xc00 ≤ index → image.word index = none := by
  intro index above
  change (Model.tableWord 0x3d1 shimInstructions index).or (Model.tableWord 0x400 instructions index) = none
  rw [tableWordOutside 0x3d1 shimInstructions (Or.inr (by have := shimLength; omega)),
    tableWordOutside 0x400 instructions (Or.inr (by have := routineLength; omega)), Option.none_or]

private theorem modelMode (call : Call) : MachineMode (machine call) returnTo :=
  Model.modelMode call codeBase _ (by decide)

private theorem routineImage {state : Machine} {call : Call} (modeled : Modeled image call state) :
    CodeImage instructions codeBase state := by
  refine tableImage modeled instructions codeBase 0x1000 rfl (by decide) (by decide)
    (fun index bound byte small => by change index < 30 at bound; simp [image]; omega)
    (fun index bound => ?_)
  change (Model.tableWord 0x3d1 shimInstructions (0x400 + index)).or
    (Model.tableWord 0x400 instructions (0x400 + index)) = _
  rw [tableWordOutside 0x3d1 shimInstructions (Or.inr (by have := shimLength; omega)), Option.none_or,
    tableWordAt 0x400 instructions bound]

private theorem shimCodeImage {state : Machine} {call : Call} (modeled : Modeled image call state) :
    CodeImage shimInstructions shimModelBase state := by
  refine tableImage modeled shimInstructions shimModelBase 0xf44 rfl (by decide) (by decide)
    (fun index bound byte small => by change index < 7 at bound; simp [image]; omega)
    (fun index bound => ?_)
  change (Model.tableWord 0x3d1 shimInstructions (0x3d1 + index)).or _ = _
  rw [tableWordAt 0x3d1 shimInstructions bound, Option.some_or]

private theorem modelHeader {state : Machine}
    (modeled : Modeled image (modelCall index value length capacity old) state) :
    Header state (modelCall index value length capacity old) :=
  Model.modelHeader modeled dataFree

private theorem modelBuffer {state : Machine}
    (modeled : Modeled image (modelCall index value length capacity old) state)
    (small : length.toNat ≤ 1000) (valid : (modelCall index value length capacity old).valid) :
    Buffer codeBase state (modelCall index value length capacity old) :=
  Model.modelBuffer modeled dataFree (by decide) (by rw [wordBytes]; omega) valid

theorem modelHypotheses (small : length.toNat ≤ 1000) :
    Hypotheses codeBase returnTo (machine (modelCall index value length capacity old))
      (modelCall index value length capacity old) (initial (modelCall index value length capacity old)) :=
  let modeled := syncModeled _ codeBase _
  ⟨(syncSync _ _).symm, rfl, rfl, rfl, Environment.ofMachine (modelMode _) (routineImage modeled),
    modelHeader modeled, modelBuffer modeled small⟩

end Model

/-! ## One machine per execution path

The elements are 10, 20, 30, ... . Each theorem below shows the premises hold
on a concrete machine that takes the named path, and then applies
`rawVecU32InsertSailCorrect` to that machine.
-/

def elements (index : Nat) : Word := BitVec.ofNat 32 (10 * (index + 1))

-- Insert 25 at the end of [10, 20] in capacity 4: append.
def appendCall : Call := modelCall 2 25 2 4 elements
-- Insert 5 at the front of [10, 20] in capacity 4: shift both elements.
def shiftCall : Call := modelCall 0 5 2 4 elements
-- Length 5 exceeds capacity 4: invalid length.
def invalidLengthCall : Call := modelCall 0 5 5 4 elements
-- Index 3 exceeds length 2: invalid index.
def invalidIndexCall : Call := modelCall 3 5 2 4 elements
-- Length 4 equals capacity 4: full.
def fullCall : Call := modelCall 0 5 4 4 elements

theorem appendSatisfiable :
    Hypotheses codeBase returnTo (machine appendCall) appendCall (initial appendCall) ∧
      appendCall.valid ∧ appendCall.index = appendCall.length ∧ appendCall.count = 14 :=
  ⟨modelHypotheses (by decide), by decide, by decide, by decide⟩

theorem shiftSatisfiable :
    Hypotheses codeBase returnTo (machine shiftCall) shiftCall (initial shiftCall) ∧
      shiftCall.valid ∧ shiftCall.index.toNat < shiftCall.length.toNat ∧ shiftCall.count = 30 :=
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

theorem appendRuns : ∃ final, Riscfree.RV32.run 14 (machine appendCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  appendSatisfiable.1.run

theorem shiftRuns : ∃ final, Riscfree.RV32.run 30 (machine shiftCall) = some final ∧
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
`rawVecU32InsertSailCorrectInMachineMode`, which replaces `Environment` with
machine-mode registers and the code image. The same model satisfies them.
-/

structure MachineHypotheses (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot) : Prop where
  entry : original = sync base original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  indexArgument : initial.a1 = call.index
  valueArgument : initial.a2 = call.value
  mode : MachineMode original returnAddress
  image : CodeImage instructions base original
  header : Header original call
  buffer : call.valid → Buffer base original call

theorem MachineHypotheses.run {base returnAddress : Word} {original : Machine} {call : Call}
    {initial : Snapshot} (premises : MachineHypotheses base returnAddress original call initial) :
    ∃ final, Riscfree.RV32.run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, -⟩ := rawVecU32InsertSailCorrectInMachineMode base returnAddress
    original call initial premises.entry premises.headerArgument premises.indexArgument
    premises.valueArgument premises.mode premises.image premises.header premises.buffer
  exact ⟨final, ran, pc, status⟩

theorem modelMachineHypotheses {index value length capacity : Word} {old : Nat → Word}
    (small : length.toNat ≤ 1000) :
    MachineHypotheses codeBase returnTo (machine (modelCall index value length capacity old))
      (modelCall index value length capacity old) (initial (modelCall index value length capacity old)) :=
  let modeled := syncModeled _ codeBase _
  ⟨(syncSync _ _).symm, rfl, rfl, rfl, modelMode _, routineImage modeled, modelHeader modeled,
    modelBuffer modeled small⟩

theorem machineAppendRuns : ∃ final, Riscfree.RV32.run 14 (machine appendCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  (modelMachineHypotheses (by decide) : MachineHypotheses _ _ _ appendCall _).run

theorem machineShiftRuns : ∃ final, Riscfree.RV32.run 30 (machine shiftCall) = some final ∧
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

/-! ## The shim's premises can all hold

`ShimReturnHypotheses` collects the premises of
`callRawVecU32InsertSailAtReturn`. `ShimHypotheses` adds the word-aligned
return address that `callRawVecU32InsertSailCorrect` also needs. The model
places the shim at `0xf44`, so its `call` reaches the routine at `0x1000`. The
caller's stack pointer is `0x5000`, so the shim saves `ra` at `0x4ffc`. The
caller returns to `0x2000`, or to `0x2002` in the halfword-aligned case.
-/

-- The premises of `callRawVecU32InsertSailAtReturn`, which allows any caller.
structure ShimReturnHypotheses (shimBase : Word) (original : Machine) (call : Call)
    (initial : ShimSnapshot) : Prop where
  entry : original = sync shimBase original { initial with pc := 0 }
  headerArgument : initial.a0 = call.header
  indexArgument : initial.a1 = call.index
  valueArgument : initial.a2 = call.value
  environment : ShimEnvironment shimBase original
  layout : ShimLayout shimBase original call initial.sp
  header : Header original call
  buffer : call.valid → Buffer (shimBase + routineOffset) original call

-- The premises of `callRawVecU32InsertSailCorrect`: a word-aligned caller.
structure ShimHypotheses (shimBase : Word) (original : Machine) (call : Call)
    (initial : ShimSnapshot) : Prop extends ShimReturnHypotheses shimBase original call initial where
  returnLow : initial.ra &&& 0xfffffffe = initial.ra
  returnNext : initial.ra[1] = false

theorem ShimHypotheses.run {shimBase : Word} {original : Machine} {call : Call}
    {initial : ShimSnapshot} (premises : ShimHypotheses shimBase original call initial) :
    ∃ final, Riscfree.RV32.run (call.count + 7) original = some final ∧
      final.regs.get? Register.PC = some initial.ra ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, status, -⟩ := callRawVecU32InsertSailCorrect shimBase original call initial
    premises.entry premises.headerArgument premises.indexArgument premises.valueArgument
    premises.returnLow premises.returnNext premises.environment premises.layout premises.header
    premises.buffer
  exact ⟨final, ran, pc, status⟩

theorem ShimReturnHypotheses.atReturn {shimBase : Word} {original : Machine} {call : Call}
    {initial : ShimSnapshot} (premises : ShimReturnHypotheses shimBase original call initial) :
    ∃ final, Riscfree.RV32.run (call.count + 6) original = some final ∧
      final.regs.get? Register.PC = some (shimBase + 24#32) ∧
      final.regs.get? Register.x1 = some initial.ra ∧
      final.regs.get? Register.x10 = some call.status := by
  obtain ⟨final, ran, pc, ra, status, -⟩ := callRawVecU32InsertSailAtReturn shimBase original call
    initial premises.entry premises.headerArgument premises.indexArgument premises.valueArgument
    premises.environment premises.layout premises.header premises.buffer
  exact ⟨final, ran, pc, ra, status⟩

def shimInitial (returnAddress : Word) (call : Call) : ShimSnapshot :=
  { ra := returnAddress, sp := stackTop, a0 := call.header, a1 := call.index, a2 := call.value,
    a3 := 0, a4 := 0, a5 := 0, a6 := 0, a7 := 0 }

def shimMachine (returnAddress : Word) (call : Call) : Machine :=
  sync shimModelBase (frame call) { shimInitial returnAddress call with pc := 0 }

section ShimModel

variable {index value length capacity : Word} {old : Nat → Word}

private theorem routineAtCodeBase : shimModelBase + routineOffset = codeBase := by decide

private theorem saveSlotNat : (saveSlot stackTop).toNat = 0x4ffc := by decide

private theorem returnToLow : returnTo &&& 0xfffffffe = returnTo := by decide

private theorem returnToNext : returnTo[1] = false := by decide

-- Any return address, even one with bit 1 set.
theorem shimModelReturnHypotheses (returnAddress : Word) (small : length.toNat ≤ 1000) :
    ShimReturnHypotheses shimModelBase
      (shimMachine returnAddress (modelCall index value length capacity old))
      (modelCall index value length capacity old)
      (shimInitial returnAddress (modelCall index value length capacity old)) := by
  let call := modelCall index value length capacity old
  have modeled := syncModeled (image := image) call shimModelBase { shimInitial returnAddress call with pc := 0 }
  have slotAt : (saveSlot (shimInitial returnAddress call).sp).toNat = 0x4ffc := saveSlotNat
  refine ⟨(syncSync _ _).symm, rfl, rfl, rfl, ⟨(frameState call).atSync _ _, shimCodeImage modeled,
      routineAtCodeBase ▸ routineImage modeled⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    modelHeader modeled, routineAtCodeBase ▸ modelBuffer modeled small⟩
  · exact readable modeled (by rw [slotAt]) (by rw [slotAt]; decide)
  · exact writable modeled (by rw [slotAt]) (by rw [slotAt]; decide)
  · rw [slotAt]
    right
    change 0x3000 + 12 ≤ 0x4ffc
    decide
  · intro _ slot bound
    rw [slotAt]
    right
    change 0x4000 + 4 * slot + 4 ≤ 0x4ffc
    change slot ≤ length.toNat at bound
    omega
  · rw [slotAt]
    right
    change 0xf44 + 28 ≤ 0x4ffc
    decide
  · rw [slotAt, routineAtCodeBase]
    right
    change 0x1000 + 120 ≤ 0x4ffc
    decide
  · intro _
    refine ⟨Or.inr (by change 0xf44 + 28 ≤ 0x3000 + 4; decide), fun slot _ _ => Or.inr ?_⟩
    change 0xf44 + 28 ≤ 0x4000 + 4 * slot
    omega

theorem shimModelHypotheses (small : length.toNat ≤ 1000) :
    ShimHypotheses shimModelBase (shimMachine returnTo (modelCall index value length capacity old))
      (modelCall index value length capacity old)
      (shimInitial returnTo (modelCall index value length capacity old)) :=
  { shimModelReturnHypotheses returnTo small with returnLow := returnToLow, returnNext := returnToNext }

end ShimModel

/-! ### One shim machine per execution path -/

theorem shimAppendRuns : ∃ final, Riscfree.RV32.run 21 (shimMachine returnTo appendCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  (shimModelHypotheses (by decide) : ShimHypotheses _ _ appendCall _).run

theorem shimShiftRuns : ∃ final, Riscfree.RV32.run 37 (shimMachine returnTo shiftCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 0 :=
  (shimModelHypotheses (by decide) : ShimHypotheses _ _ shiftCall _).run

theorem shimInvalidLengthRuns :
    ∃ final, Riscfree.RV32.run 12 (shimMachine returnTo invalidLengthCall) = some final ∧
      final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 3 :=
  (shimModelHypotheses (by decide) : ShimHypotheses _ _ invalidLengthCall _).run

theorem shimInvalidIndexRuns :
    ∃ final, Riscfree.RV32.run 13 (shimMachine returnTo invalidIndexCall) = some final ∧
      final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 2 :=
  (shimModelHypotheses (by decide) : ShimHypotheses _ _ invalidIndexCall _).run

theorem shimFullRuns : ∃ final, Riscfree.RV32.run 14 (shimMachine returnTo fullCall) = some final ∧
    final.regs.get? Register.PC = some returnTo ∧ final.regs.get? Register.x10 = some 1 :=
  (shimModelHypotheses (by decide) : ShimHypotheses _ _ fullCall _).run

/-! ### A caller that returns to a halfword-aligned address

The demo's Rust caller can return to an address with bit 1 set. For such a
caller, `callRawVecU32InsertSailAtReturn` still applies: the premises hold with
return address `0x2002`, and the shim reaches its `ret` with `ra = 0x2002`.
-/

def halfwordReturn : Word := 0x2002

theorem halfwordAppendAtReturn :
    ∃ final, Riscfree.RV32.run 20 (shimMachine halfwordReturn appendCall) = some final ∧
      final.regs.get? Register.PC = some (shimModelBase + 24#32) ∧
      final.regs.get? Register.x1 = some halfwordReturn ∧ final.regs.get? Register.x10 = some 0 :=
  (shimModelReturnHypotheses halfwordReturn (by decide) : ShimReturnHypotheses _ _ appendCall _).atReturn

theorem halfwordShiftAtReturn :
    ∃ final, Riscfree.RV32.run 36 (shimMachine halfwordReturn shiftCall) = some final ∧
      final.regs.get? Register.PC = some (shimModelBase + 24#32) ∧
      final.regs.get? Register.x1 = some halfwordReturn ∧ final.regs.get? Register.x10 = some 0 :=
  (shimModelReturnHypotheses halfwordReturn (by decide) : ShimReturnHypotheses _ _ shiftCall _).atReturn

theorem halfwordInvalidLengthAtReturn :
    ∃ final, Riscfree.RV32.run 11 (shimMachine halfwordReturn invalidLengthCall) = some final ∧
      final.regs.get? Register.PC = some (shimModelBase + 24#32) ∧
      final.regs.get? Register.x1 = some halfwordReturn ∧ final.regs.get? Register.x10 = some 3 :=
  (shimModelReturnHypotheses halfwordReturn (by decide) :
    ShimReturnHypotheses _ _ invalidLengthCall _).atReturn

theorem halfwordInvalidIndexAtReturn :
    ∃ final, Riscfree.RV32.run 12 (shimMachine halfwordReturn invalidIndexCall) = some final ∧
      final.regs.get? Register.PC = some (shimModelBase + 24#32) ∧
      final.regs.get? Register.x1 = some halfwordReturn ∧ final.regs.get? Register.x10 = some 2 :=
  (shimModelReturnHypotheses halfwordReturn (by decide) :
    ShimReturnHypotheses _ _ invalidIndexCall _).atReturn

theorem halfwordFullAtReturn :
    ∃ final, Riscfree.RV32.run 13 (shimMachine halfwordReturn fullCall) = some final ∧
      final.regs.get? Register.PC = some (shimModelBase + 24#32) ∧
      final.regs.get? Register.x1 = some halfwordReturn ∧ final.regs.get? Register.x10 = some 1 :=
  (shimModelReturnHypotheses halfwordReturn (by decide) : ShimReturnHypotheses _ _ fullCall _).atReturn

end Riscfree.RawVec.Nonvacuity
