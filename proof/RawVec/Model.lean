import RawVec.Insert
import Riscfree.RV32.Model

/-!
# A model machine for the RawVec nonvacuity proofs

Every RawVec theorem is conditional. Its nonvacuity proof exhibits machines that
satisfy all its premises at once. This module builds those machines for any
element type and any code layout, and proves the shared premises `Header` and
`Buffer` on them.

The model machine is in machine mode with `MPRV` clear, landing pads and the
host interface disabled, and one PMA region covering the address space. Its
memory holds the code words that an `Image` places, the vector header at
`0x3000`, and the live elements from `0x4000`. The return address is `0x2000`.
-/

namespace Riscfree.RawVec.Model

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

def codeBase : Word := 0x1000
def returnTo : Word := 0x2000

-- The word that a table starting at word index `start` puts at `index`.
def tableWord (start : Nat) (table : List (Word × instruction)) (index : Nat) : Option Word :=
  if start ≤ index then (table[index - start]?).map Prod.fst else none

theorem tableWordAt (start : Nat) (table : List (Word × instruction)) {index : Nat}
    (bound : index < table.length) : tableWord start table (start + index) = some table[index].1 := by
  simp [tableWord, List.getElem?_eq_getElem bound]

theorem tableWordOutside (start : Nat) (table : List (Word × instruction)) {index : Nat}
    (outside : index < start ∨ start + table.length ≤ index) : tableWord start table index = none := by
  unfold tableWord
  split
  · rw [List.getElem?_eq_none (by omega), Option.map_none]
  · rfl

-- The code in the model memory: a word for each code word index, and the
-- bytes that hold those words.
structure Image where
  word : Nat → Option Word
  keys : List Nat

def modelCall {α : Type} (index : Word) (value : α) (length capacity : Word) (old : Nat → α) :
    Insert.Call α :=
  { header := 0x3000, index, value, length, capacity, data := 0x4000, old }

-- RV32 (`MXL = 1`) with the I and M extensions.
def misaValue : BitVec 32 := 0x40001100

def registers : Std.ExtDHashMap Register RegisterType :=
  ((((((((∅ : Std.ExtDHashMap Register RegisterType).insert Register.x1 returnTo).insert
    Register.cur_privilege Privilege.Machine).insert Register.misa misaValue).insert
    Register.mseccfg (0 : BitVec 64)).insert Register.mstatus (0 : BitVec 64)).insert
    Register.htif_tohost_base none).insert Register.pma_regions [wholeSpaceRegion])

variable {α : Type} [Element α]

-- Word indices: the header at `0xc00`–`0xc02` and the elements from `0x1000`.
def dataContents (call : Insert.Call α) (index : Nat) : Word :=
  if index = 0xc00 then call.data
  else if index = 0xc01 then call.length
  else if index = 0xc02 then call.capacity
  else Element.word (call.old ((index - 0x1000) / Element.words α)) ((index - 0x1000) % Element.words α)

def contents (image : Image) (call : Insert.Call α) (index : Nat) : Word :=
  (image.word index).getD (dataContents call index)

def keys (image : Image) (call : Insert.Call α) : List Nat :=
  image.keys ++ List.range' 0x3000 12 ++ List.range' 0x4000 (Element.bytes α * call.length.toNat)

def frame (image : Image) (call : Insert.Call α) : Machine :=
  { (default : Machine) with regs := registers, mem := wordMemory (keys image call) (contents image call) }

/-! ## The model satisfies the shared premises -/

-- A machine with the model's memory and PMA region.
structure Modeled (image : Image) (call : Insert.Call α) (state : Machine) : Prop where
  mem : state.mem = wordMemory (keys image call) (contents image call)
  regions : Sail.readReg Register.pma_regions state = .ok [wholeSpaceRegion] state

section Machine

variable {image : Image}

theorem frameRead {key : Register} {value : RegisterType key} (call : Insert.Call α)
    (stored : registers.get? key = some value) :
    Sail.readReg key (frame image call) = .ok value (frame image call) :=
  readReg_succ.mpr stored

theorem frameState (call : Insert.Call α) : MachineState (frame image call) := by
  have configRead : Sail.readReg Register.mseccfg (frame image call) = .ok 0 (frame image call) :=
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
theorem syncModeled {S : Type} [RegisterView S] (call : Insert.Call α) (base : Word) (state : S) :
    Modeled image call (sync base (frame image call) state) :=
  ⟨by simp only [syncMem, frame],
    Platform.systemRead state (by decide) (by decide) (by decide) (frameRead call (by simp [registers]))⟩

-- A snapshot that does not track `ra` keeps the model's return address.
theorem modelMode {S : Type} [RegisterView S] (call : Insert.Call α) (base : Word) (state : S)
    (untracked : ∀ index ∈ tracked S, reg_of_fin index ≠ Register.x1) :
    MachineMode (sync base (frame image call) state) returnTo :=
  { (frameState call).atSync base _ with
    returnLow := by decide
    returnNext := by decide
    ra := syncReadFrame _ _ (by decide) (by decide) untracked
      (frameRead call (by simp [registers, Std.ExtDHashMap.get?_insert])) }

end Machine

private theorem codeAddress (base : Word) (start count index : Nat) (bound : index < count)
    (baseNat : base.toNat = start) (fits : start + 4 * count ≤ 2 ^ 32) :
    (base + BitVec.ofNat 32 (index * 4)).toNat = start + index * 4 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index * 4 < 2 ^ 32), baseNat]
  exact Nat.mod_eq_of_lt (by omega)

-- A table whose words the image places at byte address `start` is a code image.
theorem tableImage {state : Machine} {image : Image} {call : Insert.Call α}
    (modeled : Modeled image call state)
    (table : List (Word × instruction)) (base : Word) (start : Nat) (baseNat : base.toNat = start)
    (aligned : start % 4 = 0) (fits : start + 4 * table.length ≤ 2 ^ 32)
    (present : ∀ index < table.length, ∀ byte < 4, start + index * 4 + byte ∈ image.keys)
    (selected : ∀ (index : Nat) (bound : index < table.length),
      image.word (start / 4 + index) = some table[index].1) :
    CodeImage table base state := by
  refine ⟨by omega, by omega, ⟨[wholeSpaceRegion], modeled.regions, fun index bound => ?_⟩, ?_⟩
  · have address := codeAddress base start table.length index bound baseNat fits
    refine ⟨wholeSpaceExecutable _ (by omega), wholeSpaceExecutable _ ?_⟩
    rw [BitVec.toNat_add, address]
    simp
    omega
  · intro index bound
    rw [modeled.mem, baseNat]
    have word := wordMemoryWord (keys image call) (contents image call) (start + index * 4) (by omega)
      (fun byte small => by
        simp only [keys, List.mem_append]
        exact Or.inl (Or.inl (present index bound byte small)))
    rw [show (start + index * 4) / 4 = start / 4 + index by omega, contents,
      selected index bound, Option.getD_some] at word
    exact word

section Premises

variable {image : Image} {state : Machine}

theorem readable {call : Insert.Call α} (modeled : Modeled image call state)
    {address : Word} (aligned : address.toNat % 4 = 0) (fits : address.toNat + 4 ≤ 2 ^ 32) :
    Readable state address :=
  ⟨aligned, _, _, modeled.regions, wholeSpaceMatches address 4 (by decide) fits, rfl⟩

theorem writable {call : Insert.Call α} (modeled : Modeled image call state)
    {address : Word} (aligned : address.toNat % 4 = 0) (fits : address.toNat + 4 ≤ 2 ^ 32) :
    Writable state address :=
  ⟨aligned, _, _, modeled.regions, wholeSpaceMatches address 4 (by decide) fits, rfl⟩

private theorem headerWord {call : Insert.Call α} (modeled : Modeled image call state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none)
    (offset : Nat) (small : offset < 3) (header : call.header = 0x3000) :
    WordAt state.mem (call.header.toNat + 4 * offset) (dataContents call (0xc00 + offset)) := by
  rw [modeled.mem, header]
  have word := wordMemoryWord (keys image call) (contents image call) (0x3000 + 4 * offset) (by omega)
    (fun byte bound => by simp [keys]; omega)
  have quotient : (0x3000 + 4 * offset) / 4 = 0xc00 + offset := by omega
  rw [quotient, contents, dataFree _ (by omega), Option.getD_none] at word
  exact word

theorem modelHeader {index length capacity : Word} {value : α} {old : Nat → α}
    (modeled : Modeled image (modelCall index value length capacity old) state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none) :
    Insert.Header state (modelCall index value length capacity old) :=
  ⟨by simp [modelCall], readable modeled (by simp [modelCall]) (by simp [modelCall]),
    readable modeled (by simp [modelCall]) (by simp [modelCall]),
    by simpa [dataContents] using headerWord modeled dataFree 1 (by decide) rfl,
    by simpa [dataContents] using headerWord modeled dataFree 2 (by decide) rfl⟩

private theorem slotNat {call : Insert.Call α} (data : call.data = 0x4000) {slot offset : Nat}
    (small : 0x4000 + Element.bytes α * slot + offset < 2 ^ 32) :
    (call.wordSlot slot + BitVec.ofNat 32 offset).toNat = 0x4000 + Element.bytes α * slot + offset := by
  have dataNat : call.data.toNat = 0x4000 := by rw [data]; rfl
  simp only [Insert.Call.wordSlot, Insert.Call.slot, dataNat, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 0x4000 + Element.bytes α * slot < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show offset < 2 ^ 32 by omega)]
  exact Nat.mod_eq_of_lt small

theorem modelBuffer {codeBytes : Nat} {index length capacity : Word} {value : α} {old : Nat → α}
    (modeled : Modeled image (modelCall index value length capacity old) state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none)
    (codeFits : 0x1000 + codeBytes ≤ 0x3000)
    (small : Element.bytes α * (length.toNat + 1) ≤ 0x100000)
    (valid : (modelCall index value length capacity old).valid) :
    Insert.Buffer codeBytes codeBase state (modelCall index value length capacity old) := by
  let call := modelCall index value length capacity old
  have data : call.data = 0x4000 := rfl
  have spare := valid.2
  have words := Element.bytesWords (α := α)
  have positive := Element.positive (α := α)
  have succ := Nat.mul_add_one (Element.bytes α) length.toNat
  -- Each element's words are mapped, and each lies far below the top of memory.
  have element (slot part : Nat) (bound : slot ≤ length.toNat) (inside : part < Element.words α) :
      (call.wordSlot slot + BitVec.ofNat 32 (4 * part)).toNat =
        0x4000 + Element.bytes α * slot + 4 * part ∧
      (0x4000 + Element.bytes α * slot + 4 * part) % 4 = 0 ∧
      0x4000 + Element.bytes α * slot + 4 * part + 4 ≤ 2 ^ 32 := by
    have scaled := Nat.mul_le_mul_left (Element.bytes α) (show slot + 1 ≤ length.toNat + 1 by omega)
    have next := Nat.mul_add_one (Element.bytes α) slot
    have quarter : Element.bytes α * slot = 4 * (Element.words α * slot) := by
      rw [words, Nat.mul_assoc]
    refine ⟨slotNat data (by omega), by omega, by omega⟩
  refine ⟨?_, readable modeled (by simp [modelCall]) (by simp [modelCall]),
    by simpa [dataContents] using headerWord modeled dataFree 0 (by decide) rfl,
    writable modeled (by simp [modelCall]) (by simp [modelCall]),
    Or.inr (by change 0x1000 + codeBytes ≤ 0x3000 + 4; omega), fun slot bound => ?_,
    fun slot _ bound => ?_, fun slot _ bound => ?_, fun slot bound => ?_, fun slot _ bound => ?_⟩
  · change 0x4000 + Element.bytes α * (length.toNat + 1) ≤ 2 ^ 32
    omega
  · change slot < length.toNat at bound
    refine Element.atOfWords fun part inside => ?_
    have scaled := Nat.mul_le_mul_left (Element.bytes α) (show slot + 1 ≤ length.toNat by omega)
    have next := Nat.mul_add_one (Element.bytes α) slot
    have quarter : Element.bytes α * slot = 4 * (Element.words α * slot) := by
      rw [words, Nat.mul_assoc]
    rw [modeled.mem]
    have word := wordMemoryWord (keys image call) (contents image call)
      (0x4000 + Element.bytes α * slot + 4 * part) (by omega)
      (fun byte small => by simp only [keys, call, modelCall, List.mem_append, List.mem_range'_1]; omega)
    have quotient : (0x4000 + Element.bytes α * slot + 4 * part) / 4 =
        0x1000 + (Element.words α * slot + part) := by omega
    have selected : contents image call (0x1000 + (Element.words α * slot + part)) =
        Element.word (old slot) part := by
      rw [contents, dataFree _ (by omega), Option.getD_none, dataContents,
        if_neg (by omega), if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
        Nat.mul_add_div positive, Nat.div_eq_of_lt inside, Nat.add_zero,
        Nat.mul_add_mod, Nat.mod_eq_of_lt inside]
      rfl
    rw [quotient, selected] at word
    exact word
  · change slot < length.toNat at bound
    exact Element.mappedOfWords fun part inside =>
      have facts := element slot part (by omega) inside
      readable modeled (by rw [facts.1]; exact facts.2.1) (by rw [facts.1]; exact facts.2.2)
  · change slot ≤ length.toNat at bound
    exact Element.mappedOfWords fun part inside =>
      have facts := element slot part bound inside
      writable modeled (by rw [facts.1]; exact facts.2.1) (by rw [facts.1]; exact facts.2.2)
  · right
    change 0x3000 + 12 ≤ 0x4000 + Element.bytes α * slot
    omega
  · right
    change 0x1000 + codeBytes ≤ 0x4000 + Element.bytes α * slot
    omega

end Premises

end Riscfree.RawVec.Model
