import RawVec.Shim

/-!
# The generic refactoring keeps the u32 theorems

`raw_vec_u32_insert` was first proved with its own definitions of `Call`,
`Header`, `Buffer`, and `Environment`. The proof now instantiates the generic
insertion of `RawVec/Insert.lean` instead. This module keeps a verbatim copy of
the original definitions and theorem statements from before that change, and
derives each original theorem from the current one. So the refactoring added
no premise and weakened no conclusion.

The copies refer to the current `instructions`, `Snapshot`, `shimInstructions`,
and `routineOffset`. The first two are unchanged. The shim's two linked `call`
words and `routineOffset` changed in the same commit, because the demo's link
layout moved. They describe the newly linked shim, not a refactoring.
-/

namespace Riscfree.RawVec.Original

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

/-! ## The original definitions, verbatim -/

-- The memory system maps these executable bytes independently of data writes.
def CodeAgrees (base : Word) (original memory : ByteMemory) : Prop :=
  ∀ byte, base.toNat ≤ byte → byte < base.toNat + 120 →
    memory[byte]? = original[byte]?

def Mapped (frame : Machine) (address : Word) (permission : PMA_Region → Prop) : Prop :=
  address.toNat % 4 = 0 ∧ ∃ regions region,
    Sail.readReg Register.pma_regions frame = .ok regions frame ∧
    matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region ∧ permission region

abbrev Readable (frame : Machine) (address : Word) :=
  Mapped frame address (fun region => region.attributes.readable = true)

abbrev Writable (frame : Machine) (address : Word) :=
  Mapped frame address (fun region => region.attributes.writable = true)

structure Environment (base returnAddress : Word) (original : Machine) : Prop where
  codeFits : base.toNat + 120 ≤ 2 ^ 32
  platform : ∀ memory, CodeAgrees base original.mem memory →
    Platform Snapshot instructions base { original with mem := memory } [] returnAddress (fun _ => 0)

structure Call where
  header : Word
  index : Word
  value : Word
  length : Word
  capacity : Word
  data : Word
  old : Nat → Word

namespace Call

def slot (call : Call) (index : Nat) : Nat := call.data.toNat + 4 * index

def wordSlot (call : Call) (index : Nat) : Word := BitVec.ofNat 32 (call.slot index)

def valid (call : Call) : Prop :=
  call.index.toNat ≤ call.length.toNat ∧ call.length.toNat < call.capacity.toNat

instance (call : Call) : Decidable call.valid :=
  inferInstanceAs (Decidable (call.index.toNat ≤ call.length.toNat ∧
    call.length.toNat < call.capacity.toNat))

def status (call : Call) : Word :=
  if call.capacity.toNat < call.length.toNat then 3
  else if call.length.toNat < call.index.toNat then 2
  else if call.length = call.capacity then 1
  else 0

def count (call : Call) : Nat :=
  if call.capacity.toNat < call.length.toNat then 5
  else if call.length.toNat < call.index.toNat then 6
  else if call.length = call.capacity then 7
  else if call.index = call.length then 14
  else 18 + 6 * (call.length.toNat - call.index.toNat)

def result (call : Call) (index : Nat) : Word :=
  if index < call.index.toNat then call.old index
  else if index = call.index.toNat then call.value
  else call.old (index - 1)

def outsideHeader (call : Call) (address : Nat) : Prop :=
  address + 4 ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ address

def outsideCode (base : Word) (address : Nat) : Prop :=
  address + 4 ≤ base.toNat ∨ base.toNat + 120 ≤ address

def unchanged (call : Call) (before after : ByteMemory) : Prop :=
  ∀ byte, (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) →
    (byte < call.slot call.index.toNat ∨ call.slot (call.length.toNat + 1) ≤ byte) →
    after[byte]? = before[byte]?

end Call

-- Rejected calls need only the two readable header words used in the checks.
-- A successful call needs access to the live prefix and a single spare slot.
-- Permissions for the rest of the capacity are irrelevant to this routine.
structure Header (original : Machine) (call : Call) : Prop where
  fits : call.header.toNat + 12 ≤ 2 ^ 32
  lengthReadable : Readable original (call.header + 4)
  capacityReadable : Readable original (call.header + 8)
  lengthWord : WordAt original.mem (call.header.toNat + 4) call.length
  capacityWord : WordAt original.mem (call.header.toNat + 8) call.capacity

structure Buffer (base : Word) (original : Machine) (call : Call) : Prop where
  fits : call.slot (call.length.toNat + 1) ≤ 2 ^ 32
  dataReadable : Readable original call.header
  dataWord : WordAt original.mem call.header.toNat call.data
  lengthWritable : Writable original (call.header + 4)
  lengthAwayFromCode : Call.outsideCode base (call.header.toNat + 4)
  live : ∀ index, index < call.length.toNat →
    WordAt original.mem (call.slot index) (call.old index)
  readable : ∀ index, call.index.toNat ≤ index → index < call.length.toNat →
    Readable original (call.wordSlot index)
  writable : ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
    Writable original (call.wordSlot index)
  separated : ∀ index, index ≤ call.length.toNat →
    call.outsideHeader (call.slot index)
  awayFromCode : ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
    Call.outsideCode base (call.slot index)

def Call.outsideShim (shimBase : Word) (address : Nat) : Prop :=
  address + 4 ≤ shimBase.toNat ∨ shimBase.toNat + 28 ≤ address

-- The stack word where the shim saves `ra`, and its separation from the data
-- and code. The routine's own writes must also miss the shim's code.
structure ShimLayout (shimBase : Word) (original : Machine) (call : Call)
    (stackPointer : Word) : Prop where
  slotReadable : Readable original (saveSlot stackPointer)
  slotWritable : Writable original (saveSlot stackPointer)
  slotApartHeader : call.outsideHeader (saveSlot stackPointer).toNat
  slotApartBuffer : call.valid → ∀ index ≤ call.length.toNat,
    (saveSlot stackPointer).toNat + 4 ≤ call.slot index ∨
      call.slot index + 4 ≤ (saveSlot stackPointer).toNat
  slotApartShim : Call.outsideShim shimBase (saveSlot stackPointer).toNat
  slotApartRoutine : Call.outsideCode (shimBase + routineOffset) (saveSlot stackPointer).toNat
  writesApartShim : call.valid → Call.outsideShim shimBase (call.header.toNat + 4) ∧
    ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
      Call.outsideShim shimBase (call.slot index)

/-! ## Each original premise gives the current one -/

def Call.current (call : Call) : RawVec.Call :=
  ⟨call.header, call.index, call.value, call.length, call.capacity, call.data, call.old⟩

section Premises

variable {base returnAddress shimBase stackPointer : Word} {original : Machine} {call : Call}

theorem Environment.current (environment : Environment base returnAddress original) :
    RawVec.Environment base returnAddress original :=
  ⟨environment.codeFits, environment.platform⟩

theorem Header.current (header : Header original call) : RawVec.Header original call.current :=
  ⟨header.fits, header.lengthReadable, header.capacityReadable, header.lengthWord,
    header.capacityWord⟩

theorem Buffer.current (buffer : Buffer base original call) : RawVec.Buffer base original call.current :=
  ⟨buffer.fits, buffer.dataReadable, buffer.dataWord, buffer.lengthWritable,
    buffer.lengthAwayFromCode, buffer.live, buffer.readable, buffer.writable, buffer.separated,
    buffer.awayFromCode⟩

theorem ShimLayout.current (layout : ShimLayout shimBase original call stackPointer) :
    RawVec.ShimLayout shimBase original call.current stackPointer :=
  ⟨layout.slotReadable, layout.slotWritable, layout.slotApartHeader, layout.slotApartBuffer,
    layout.slotApartShim, layout.slotApartRoutine, layout.writesApartShim⟩

end Premises

/-! ## The original theorems -/

theorem rawVecU32InsertSailCorrect (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
    (environment : Environment base returnAddress original)
    (header : Header original call)
    (buffer : call.valid → Buffer base original call) :
    ∃ final, run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = original.mem) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged original.mem final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register)  :=
  RawVec.rawVecU32InsertSailCorrect base returnAddress original call.current initial entry
    headerArgument indexArgument valueArgument environment.current header.current
    fun valid => (buffer valid).current

theorem rawVecU32InsertSailCorrectInMachineMode (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
    (mode : MachineMode original returnAddress)
    (image : CodeImage instructions base original)
    (header : Header original call)
    (buffer : call.valid → Buffer base original call) :
    ∃ final, run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = original.mem) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged original.mem final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register)  :=
  RawVec.rawVecU32InsertSailCorrectInMachineMode base returnAddress original call.current initial
    entry headerArgument indexArgument valueArgument mode image header.current
    fun valid => (buffer valid).current

theorem callRawVecU32InsertSailAtReturn (shimBase : Word) (original : Machine) (call : Call)
    (initial : ShimSnapshot)
    (entry : original = sync shimBase original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
    (environment : ShimEnvironment shimBase original)
    (layout : ShimLayout shimBase original call initial.sp)
    (header : Header original call)
    (buffer : call.valid → Buffer (shimBase + routineOffset) original call) :
    ∃ final, run (call.count + 6) original = some final ∧
      final.regs.get? Register.PC = some (shimBase + 24#32) ∧
      final.regs.get? Register.x1 = some initial.ra ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = storeWord original.mem (saveSlot initial.sp).toNat initial.ra) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged (storeWord original.mem (saveSlot initial.sp).toNat initial.ra) final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register)  :=
  RawVec.callRawVecU32InsertSailAtReturn shimBase original call.current initial entry
    headerArgument indexArgument valueArgument environment layout.current header.current
    fun valid => (buffer valid).current

theorem callRawVecU32InsertSailCorrect (shimBase : Word) (original : Machine) (call : Call)
    (initial : ShimSnapshot)
    (entry : original = sync shimBase original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
    (returnLow : initial.ra &&& 0xfffffffe = initial.ra)
    (returnNext : initial.ra[1] = false)
    (environment : ShimEnvironment shimBase original)
    (layout : ShimLayout shimBase original call initial.sp)
    (header : Header original call)
    (buffer : call.valid → Buffer (shimBase + routineOffset) original call) :
    ∃ final, run (call.count + 7) original = some final ∧
      final.regs.get? Register.PC = some initial.ra ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = storeWord original.mem (saveSlot initial.sp).toNat initial.ra) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged (storeWord original.mem (saveSlot initial.sp).toNat initial.ra) final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register)  :=
  RawVec.callRawVecU32InsertSailCorrect shimBase original call.current initial entry
    headerArgument indexArgument valueArgument returnLow returnNext environment layout.current
    header.current fun valid => (buffer valid).current

end Riscfree.RawVec.Original
