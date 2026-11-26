import RawVec.Shim
import Riscfree.RV32.Model

/-!
# The RawVec premises can all hold

`rawVecU32InsertSailCorrect` is conditional. If its premises could never hold
together, it would be vacuously true. This module exhibits machines that
satisfy every premise at once, for each of the routine's five execution paths,
and applies the theorem to them.

`Hypotheses` collects the theorem's premises in the theorem's order.
`Hypotheses.run` applies the theorem to them, so `Hypotheses` cannot contain
fewer premises than the theorem.

The model machine is in machine mode with `MPRV` clear, landing pads and the
host interface disabled, and one PMA region covering the address space. Its
memory holds the 30 linked instruction words at `0x1000`, the vector header at
`0x3000`, and the live elements at `0x4000`. The return address is `0x2000`.
`modelHypotheses` proves every premise for any index, value, capacity, and
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

/-! ## The model machine -/

def codeBase : Word := 0x1000
def returnTo : Word := 0x2000
-- The shim's `call` reaches `shimModelBase + routineOffset`, which is `codeBase`.
def shimModelBase : Word := 0x2a0
def stackTop : Word := 0x5000

def modelCall (index value length capacity : Word) (old : Nat → Word) : Call :=
  { header := 0x3000, index, value, length, capacity, data := 0x4000, old }

-- RV32 (`MXL = 1`) with the I and M extensions.
def misaValue : BitVec 32 := 0x40001100

def registers : Std.ExtDHashMap Register RegisterType :=
  ((((((((∅ : Std.ExtDHashMap Register RegisterType).insert Register.x1 returnTo).insert
    Register.cur_privilege Privilege.Machine).insert Register.misa misaValue).insert
    Register.mseccfg (0 : BitVec 64)).insert Register.mstatus (0 : BitVec 64)).insert
    Register.htif_tohost_base none).insert Register.pma_regions [wholeSpaceRegion])

-- Word indices: the shim at `0xa8`–`0xae`, the routine at `0x400`–`0x41d`, the
-- header at `0xc00`–`0xc02`, and the elements from `0x1000`.
def contents (call : Call) (index : Nat) : Word :=
  if 0xa8 ≤ index ∧ index < 0xa8 + 7 then ((shimInstructions[index - 0xa8]?).map Prod.fst).getD 0
  else if 0x400 ≤ index ∧ index < 0x400 + 30 then ((instructions[index - 0x400]?).map Prod.fst).getD 0
  else if index = 0xc00 then call.data
  else if index = 0xc01 then call.length
  else if index = 0xc02 then call.capacity
  else call.old (index - 0x1000)

def keys (call : Call) : List Nat :=
  List.range' 0x2a0 28 ++ List.range' 0x1000 120 ++ List.range' 0x3000 12 ++
    List.range' 0x4000 (4 * call.length.toNat)

def frame (call : Call) : Machine :=
  { (default : Machine) with regs := registers, mem := wordMemory (keys call) (contents call) }

def initial (call : Call) : Snapshot := { a0 := call.header, a1 := call.index, a2 := call.value }

def machine (call : Call) : Machine := sync codeBase (frame call) { initial call with pc := 0 }

/-! ## The model satisfies every premise -/

section Model

variable {index value length capacity : Word} {old : Nat → Word}

-- A machine with the model's memory and PMA region.
private structure Modeled (call : Call) (state : Machine) : Prop where
  mem : state.mem = wordMemory (keys call) (contents call)
  regions : Sail.readReg Register.pma_regions state = .ok [wholeSpaceRegion] state

private theorem frameRead {key : Register} {value : RegisterType key} (call : Call)
    (stored : registers.get? key = some value) :
    Sail.readReg key (frame call) = .ok value (frame call) :=
  readReg_succ.mpr stored

private theorem frameState (call : Call) : MachineState (frame call) := by
  have configRead : Sail.readReg Register.mseccfg (frame call) = .ok 0 (frame call) :=
    frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert])
  exact {
    privilege := frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert])
    misa := ⟨misaValue, frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert])⟩
    mseccfg := ⟨0, configRead⟩
    landingPad := by
      simp [get_xLPE, configRead]
      decide
    status := ⟨0, frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert]), by decide⟩
    htif := frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert]) }

-- Every synchronized model machine is modeled.
private theorem syncModeled {S : Type} [RegisterView S] (call : Call) (base : Word) (state : S) :
    Modeled call (sync base (frame call) state) :=
  ⟨by simp only [syncMem, frame],
    Platform.systemRead state (by decide) (by decide) (by decide) (frameRead call (by simp [registers]))⟩

private theorem modelMode (call : Call) : MachineMode (machine call) returnTo :=
  { (frameState call).atSync codeBase _ with
    returnLow := by decide
    returnNext := by decide
    ra := syncReadFrame _ _ (by decide) (by decide) (by decide)
      (frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert])) }

private theorem codeAddress (base : Word) (start count index : Nat) (bound : index < count)
    (baseNat : base.toNat = start) (fits : start + 4 * count ≤ 2 ^ 32) :
    (base + BitVec.ofNat 32 (index * 4)).toNat = start + index * 4 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index * 4 < 2 ^ 32), baseNat]
  exact Nat.mod_eq_of_lt (by omega)

private theorem tableImage {state : Machine} {call : Call} (modeled : Modeled call state)
    (table : List (Word × instruction)) (base : Word) (start : Nat) (baseNat : base.toNat = start)
    (aligned : start % 4 = 0) (fits : start + 4 * table.length ≤ 2 ^ 32)
    (present : ∀ index < table.length, ∀ byte < 4, start + index * 4 + byte ∈ keys call)
    (selected : ∀ (index : Nat) (bound : index < table.length),
      contents call (start / 4 + index) = table[index].1) :
    CodeImage table base state := by
  refine ⟨by omega, by omega, ⟨[wholeSpaceRegion], modeled.regions, fun index bound => ?_⟩, ?_⟩
  · have address := codeAddress base start table.length index bound baseNat fits
    refine ⟨wholeSpaceExecutable _ (by omega), wholeSpaceExecutable _ ?_⟩
    rw [BitVec.toNat_add, address]
    simp
    omega
  · intro index bound
    rw [modeled.mem, baseNat]
    have word := wordMemoryWord (keys call) (contents call) (start + index * 4) (by omega)
      (present index bound)
    rw [show (start + index * 4) / 4 = start / 4 + index by omega, selected index bound] at word
    exact word

private theorem routineImage {state : Machine} {call : Call} (modeled : Modeled call state) :
    CodeImage instructions codeBase state := by
  refine tableImage modeled instructions codeBase 0x1000 rfl (by decide) (by decide)
    (fun index bound byte small => by change index < 30 at bound; simp [keys]; omega)
    (fun index bound => ?_)
  change index < 30 at bound
  have notShim : ¬ (0xa8 ≤ 0x1000 / 4 + index ∧ 0x1000 / 4 + index < 0xa8 + 7) := by omega
  have inCode : 0x400 ≤ 0x1000 / 4 + index ∧ 0x1000 / 4 + index < 0x400 + 30 := by omega
  have item : instructions[0x1000 / 4 + index - 0x400]? = some instructions[index] := by
    rw [show 0x1000 / 4 + index - 0x400 = index by omega]
    exact List.getElem?_eq_getElem _
  simp only [contents, notShim, inCode, item, if_false, if_true, and_self]
  rfl

private theorem shimCodeImage {state : Machine} {call : Call} (modeled : Modeled call state) :
    CodeImage shimInstructions shimModelBase state := by
  refine tableImage modeled shimInstructions shimModelBase 0x2a0 rfl (by decide) (by decide)
    (fun index bound byte small => by change index < 7 at bound; simp [keys]; omega)
    (fun index bound => ?_)
  change index < 7 at bound
  have inShim : 0xa8 ≤ 0x2a0 / 4 + index ∧ 0x2a0 / 4 + index < 0xa8 + 7 := by omega
  have item : shimInstructions[0x2a0 / 4 + index - 0xa8]? = some shimInstructions[index] := by
    rw [show 0x2a0 / 4 + index - 0xa8 = index by omega]
    exact List.getElem?_eq_getElem _
  simp only [contents, inShim, item, if_true, and_self]
  rfl

private theorem readable {state : Machine} {call : Call} (modeled : Modeled call state)
    {address : Word} (aligned : address.toNat % 4 = 0) (fits : address.toNat + 4 ≤ 2 ^ 32) :
    Readable state address :=
  ⟨aligned, _, _, modeled.regions, wholeSpaceMatches address 4 (by decide) fits, rfl⟩

private theorem writable {state : Machine} {call : Call} (modeled : Modeled call state)
    {address : Word} (aligned : address.toNat % 4 = 0) (fits : address.toNat + 4 ≤ 2 ^ 32) :
    Writable state address :=
  ⟨aligned, _, _, modeled.regions, wholeSpaceMatches address 4 (by decide) fits, rfl⟩

private theorem headerWord {state : Machine} {call : Call} (modeled : Modeled call state)
    (offset : Nat) (small : offset < 3) (header : call.header = 0x3000) :
    WordAt state.mem (call.header.toNat + 4 * offset) (contents call (0xc00 + offset)) := by
  rw [modeled.mem, header]
  have word := wordMemoryWord (keys call) (contents call) (0x3000 + 4 * offset) (by omega)
    (fun byte bound => by simp [keys]; omega)
  have quotient : (0x3000 + 4 * offset) / 4 = 0xc00 + offset := by omega
  rw [quotient] at word
  exact word

private theorem slotNat (call : Call) (data : call.data = 0x4000) (slot : Nat)
    (small : slot ≤ 1001) : (call.wordSlot slot).toNat = 0x4000 + 4 * slot := by
  simp only [Call.wordSlot, Call.slot, data, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by change 0x4000 + 4 * slot < 2 ^ 32; omega)

private theorem modelHeader {state : Machine}
    (modeled : Modeled (modelCall index value length capacity old) state) :
    Header state (modelCall index value length capacity old) :=
  ⟨by simp [modelCall], readable modeled (by simp [modelCall]) (by simp [modelCall]),
    readable modeled (by simp [modelCall]) (by simp [modelCall]),
    by simpa using headerWord modeled 1 (by decide) rfl,
    by simpa using headerWord modeled 2 (by decide) rfl⟩

private theorem modelBuffer {state : Machine}
    (modeled : Modeled (modelCall index value length capacity old) state)
    (small : length.toNat ≤ 1000) (valid : (modelCall index value length capacity old).valid) :
    Buffer codeBase state (modelCall index value length capacity old) := by
  let call := modelCall index value length capacity old
  have data : call.data = 0x4000 := rfl
  have spare := valid.2
  refine ⟨?_, readable modeled (by simp [modelCall]) (by simp [modelCall]),
    by simpa using headerWord modeled 0 (by decide) rfl,
    writable modeled (by simp [modelCall]) (by simp [modelCall]),
    by simp [Call.outsideCode, modelCall, codeBase], fun slot bound => ?_, fun slot _ bound => ?_,
    fun slot _ bound => ?_, fun slot bound => ?_, fun slot _ bound => ?_⟩
  · change 0x4000 + 4 * (length.toNat + 1) ≤ 2 ^ 32
    omega
  · change slot < length.toNat at bound
    rw [modeled.mem]
    have word := wordMemoryWord (keys call) (contents call) (0x4000 + 4 * slot) (by omega)
      (fun byte small => by simp [keys, call, modelCall]; omega)
    have quotient : (0x4000 + 4 * slot) / 4 = 0x1000 + slot := by omega
    have selected : contents call (0x1000 + slot) = old slot := by
      have notShim : ¬ (0xa8 ≤ 0x1000 + slot ∧ 0x1000 + slot < 0xa8 + 7) := by omega
      have notCode : ¬ (0x400 ≤ 0x1000 + slot ∧ 0x1000 + slot < 0x400 + 30) := by omega
      have notData : 0x1000 + slot ≠ 0xc00 := by omega
      have notLength : 0x1000 + slot ≠ 0xc01 := by omega
      have notCapacity : 0x1000 + slot ≠ 0xc02 := by omega
      simp [contents, notShim, notCode, notData, notLength, notCapacity, call, modelCall]
    rw [quotient, selected] at word
    exact word
  · change slot < length.toNat at bound
    exact readable modeled (by rw [slotNat call data slot (by omega)]; omega)
      (by rw [slotNat call data slot (by omega)]; omega)
  · change slot ≤ length.toNat at bound
    exact writable modeled (by rw [slotNat call data slot (by omega)]; omega)
      (by rw [slotNat call data slot (by omega)]; omega)
  · change slot ≤ length.toNat at bound
    right
    change 0x3000 + 12 ≤ 0x4000 + 4 * slot
    omega
  · right
    change 0x1000 + 120 ≤ 0x4000 + 4 * slot
    omega

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
places the shim at `0x2a0`, so its `call` reaches the routine at `0x1000`. The
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
  have modeled := syncModeled call shimModelBase { shimInitial returnAddress call with pc := 0 }
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
    change 0x2a0 + 28 ≤ 0x4ffc
    decide
  · rw [slotAt, routineAtCodeBase]
    right
    change 0x1000 + 120 ≤ 0x4ffc
    decide
  · intro _
    refine ⟨Or.inr (by change 0x2a0 + 28 ≤ 0x3000 + 4; decide), fun slot _ _ => Or.inr ?_⟩
    change 0x2a0 + 28 ≤ 0x4000 + 4 * slot
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
