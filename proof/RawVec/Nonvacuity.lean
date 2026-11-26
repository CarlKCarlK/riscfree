import RawVec
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

def modelCall (index value length capacity : Word) (old : Nat → Word) : Call :=
  { header := 0x3000, index, value, length, capacity, data := 0x4000, old }

-- RV32 (`MXL = 1`) with the I and M extensions.
def misaValue : BitVec 32 := 0x40001100

def registers : Std.ExtDHashMap Register RegisterType :=
  ((((((((∅ : Std.ExtDHashMap Register RegisterType).insert Register.x1 returnTo).insert
    Register.cur_privilege Privilege.Machine).insert Register.misa misaValue).insert
    Register.mseccfg (0 : BitVec 64)).insert Register.mstatus (0 : BitVec 64)).insert
    Register.htif_tohost_base none).insert Register.pma_regions [wholeSpaceRegion])

-- Word indices: code at `0x400`–`0x41d`, the header at `0xc00`–`0xc02`, and
-- the elements from `0x1000`.
def contents (call : Call) (index : Nat) : Word :=
  if 0x400 ≤ index ∧ index < 0x400 + 30 then ((instructions[index - 0x400]?).map Prod.fst).getD 0
  else if index = 0xc00 then call.data
  else if index = 0xc01 then call.length
  else if index = 0xc02 then call.capacity
  else call.old (index - 0x1000)

def keys (call : Call) : List Nat :=
  List.range' 0x1000 120 ++ List.range' 0x3000 12 ++ List.range' 0x4000 (4 * call.length.toNat)

def frame (call : Call) : Machine :=
  { (default : Machine) with regs := registers, mem := wordMemory (keys call) (contents call) }

def initial (call : Call) : Snapshot := { a0 := call.header, a1 := call.index, a2 := call.value }

def machine (call : Call) : Machine := sync codeBase (frame call) { initial call with pc := 0 }

/-! ## The model satisfies every premise -/

section Model

variable {index value length capacity : Word} {old : Nat → Word}

private theorem machineMem (call : Call) :
    (machine call).mem = wordMemory (keys call) (contents call) := by
  simp only [machine, syncMem, frame]

private theorem frameRead {key : Register} {value : RegisterType key} (call : Call)
    (stored : registers.get? key = some value) :
    Sail.readReg key (frame call) = .ok value (frame call) :=
  readReg_succ.mpr stored

private theorem systemAt (call : Call) {key : Register} {value : RegisterType key}
    (notX : ∀ index : Fin 32, reg_of_fin index ≠ key) (notPC : key ≠ Register.PC)
    (notNext : key ≠ Register.nextPC) (stored : registers.get? key = some value) :
    Sail.readReg key (machine call) = .ok value (machine call) :=
  Platform.systemRead _ notX notPC notNext (frameRead call stored)

private theorem regionsAt (call : Call) :
    Sail.readReg Register.pma_regions (machine call) = .ok [wholeSpaceRegion] (machine call) :=
  systemAt call (by decide) (by decide) (by decide)
    (by simp [registers])

private theorem modelMode (call : Call) : MachineMode (machine call) returnTo := by
  have configRead : Sail.readReg Register.mseccfg (machine call) = .ok 0 (machine call) :=
    systemAt call (by decide) (by decide) (by decide) (by simp [registers, Std.ExtDHashMap.get?_insert])
  refine ⟨by decide, by decide, ?_, ?_, ⟨misaValue, ?_⟩, ⟨0, configRead⟩, ?_, ⟨0, ?_, by decide⟩, ?_⟩
  · exact syncReadFrame _ _ (by decide) (by decide) (by decide)
      (frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert]))
  · exact systemAt call (by decide) (by decide) (by decide)
      (by simp [registers, Std.ExtDHashMap.get?_insert])
  · exact systemAt call (by decide) (by decide) (by decide)
      (by simp [registers, Std.ExtDHashMap.get?_insert])
  · simp [get_xLPE, configRead]
    decide
  · exact systemAt call (by decide) (by decide) (by decide)
      (by simp [registers, Std.ExtDHashMap.get?_insert])
  · exact systemAt call (by decide) (by decide) (by decide)
      (by simp [registers, Std.ExtDHashMap.get?_insert])

private theorem codeAddress (index : Nat) (bound : index < 30) :
    (codeBase + BitVec.ofNat 32 (index * 4)).toNat = 0x1000 + index * 4 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index * 4 < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by change 0x1000 + index * 4 < 2 ^ 32; omega)

private theorem modelImage (call : Call) : CodeImage instructions codeBase (machine call) := by
  refine ⟨by decide, by decide, ⟨[wholeSpaceRegion], regionsAt call, fun index bound => ?_⟩, ?_⟩
  · change index < 30 at bound
    refine ⟨wholeSpaceExecutable _ (by rw [codeAddress index bound]; omega),
      wholeSpaceExecutable _ ?_⟩
    rw [BitVec.toNat_add, codeAddress index bound]
    simp
    omega
  · intro index bound
    change index < 30 at bound
    rw [machineMem]
    have word := wordMemoryWord (keys call) (contents call) (0x1000 + index * 4) (by omega)
      (fun byte small => by simp [keys]; omega)
    have selected : contents call ((0x1000 + index * 4) / 4) = instructions[index].1 := by
      have quotient : (0x1000 + index * 4) / 4 = 0x400 + index := by omega
      have inCode : 0x400 + index < 0x400 + 30 := by omega
      have present : instructions[index]? = some instructions[index] := List.getElem?_eq_getElem _
      simp [contents, quotient, inCode, present]
    rw [selected] at word
    exact word

private theorem mapped (call : Call) (address : Word) (aligned : address.toNat % 4 = 0)
    (fits : address.toNat + 4 ≤ 2 ^ 32) :
    Mapped (machine call) address
      (fun region => region.attributes.readable = true ∧ region.attributes.writable = true) :=
  ⟨aligned, _, _, regionsAt call, wholeSpaceMatches address 4 (by decide) fits, rfl, rfl⟩

private theorem readable {call : Call} {address : Word} (aligned : address.toNat % 4 = 0)
    (fits : address.toNat + 4 ≤ 2 ^ 32) : Readable (machine call) address :=
  let ⟨aligned, regions, region, read, matched, readable, _⟩ := mapped call address aligned fits
  ⟨aligned, regions, region, read, matched, readable⟩

private theorem writable {call : Call} {address : Word} (aligned : address.toNat % 4 = 0)
    (fits : address.toNat + 4 ≤ 2 ^ 32) : Writable (machine call) address :=
  let ⟨aligned, regions, region, read, matched, _, writable⟩ := mapped call address aligned fits
  ⟨aligned, regions, region, read, matched, writable⟩

private theorem headerWord (call : Call) (offset : Nat) (small : offset < 3)
    (header : call.header = 0x3000) :
    WordAt (machine call).mem (call.header.toNat + 4 * offset) (contents call (0xc00 + offset)) := by
  rw [machineMem, header]
  have word := wordMemoryWord (keys call) (contents call) (0x3000 + 4 * offset) (by omega)
    (fun byte bound => by simp [keys]; omega)
  have quotient : (0x3000 + 4 * offset) / 4 = 0xc00 + offset := by omega
  rw [quotient] at word
  exact word

private theorem slotNat (call : Call) (data : call.data = 0x4000) (slot : Nat)
    (small : slot ≤ 1001) : (call.wordSlot slot).toNat = 0x4000 + 4 * slot := by
  simp only [Call.wordSlot, Call.slot, data, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by change 0x4000 + 4 * slot < 2 ^ 32; omega)

theorem modelHypotheses (small : length.toNat ≤ 1000) :
    Hypotheses codeBase returnTo (machine (modelCall index value length capacity old))
      (modelCall index value length capacity old) (initial (modelCall index value length capacity old)) := by
  let call := modelCall index value length capacity old
  have header : call.header = 0x3000 := rfl
  have data : call.data = 0x4000 := rfl
  refine ⟨(syncSync _ _).symm, rfl, rfl, rfl, Environment.ofMachine (modelMode call) (modelImage call),
    ⟨by simp [modelCall], readable (by simp [modelCall]) (by simp [modelCall]),
      readable (by simp [modelCall]) (by simp [modelCall]),
      by simpa using headerWord call 1 (by decide) header,
      by simpa using headerWord call 2 (by decide) header⟩, fun valid => ?_⟩
  have spare := valid.2
  refine ⟨?_, readable (by simp [modelCall]) (by simp [modelCall]),
    by simpa using headerWord call 0 (by decide) header,
    writable (by simp [modelCall]) (by simp [modelCall]),
    by simp [Call.outsideCode, modelCall, codeBase], fun slot bound => ?_, fun slot _ bound => ?_,
    fun slot _ bound => ?_, fun slot bound => ?_, fun slot _ bound => ?_⟩
  · change 0x4000 + 4 * (length.toNat + 1) ≤ 2 ^ 32
    omega
  · change slot < length.toNat at bound
    rw [machineMem]
    have word := wordMemoryWord (keys call) (contents call) (0x4000 + 4 * slot) (by omega)
      (fun byte small => by simp [keys, call, modelCall]; omega)
    have quotient : (0x4000 + 4 * slot) / 4 = 0x1000 + slot := by omega
    have selected : contents call (0x1000 + slot) = old slot := by
      have notCode : ¬ (0x400 ≤ 0x1000 + slot ∧ 0x1000 + slot < 0x400 + 30) := by omega
      have notData : 0x1000 + slot ≠ 0xc00 := by omega
      have notLength : 0x1000 + slot ≠ 0xc01 := by omega
      have notCapacity : 0x1000 + slot ≠ 0xc02 := by omega
      simp [contents, notCode, notData, notLength, notCapacity, call, modelCall]
    rw [quotient, selected] at word
    exact word
  · change slot < length.toNat at bound
    exact readable (by rw [slotNat call data slot (by omega)]; omega)
      (by rw [slotNat call data slot (by omega)]; omega)
  · change slot ≤ length.toNat at bound
    exact writable (by rw [slotNat call data slot (by omega)]; omega)
      (by rw [slotNat call data slot (by omega)]; omega)
  · change slot ≤ length.toNat at bound
    right
    change 0x3000 + 12 ≤ 0x4000 + 4 * slot
    omega
  · right
    change 0x1000 + 120 ≤ 0x4000 + 4 * slot
    omega

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

end Riscfree.RawVec.Nonvacuity
