import RawVec.Remove
import Riscfree.RV32.Model

/-!
# A model machine for the RawVec nonvacuity proofs

Every RawVec theorem is conditional. Its nonvacuity proof exhibits machines that
satisfy all its premises at once. This module builds those machines for any
element type, any code layout, and both operations, and proves the shared
premises `Header` and `Buffer` of insertion and of removal on them.

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

def modelRemoveCall {α : Type} (index length capacity : Word) (old : Nat → α) : Remove.Call α :=
  { header := 0x3000, index, length, capacity, data := 0x4000, old }

-- What the model memory holds besides the code: the header's length and
-- capacity words and the elements, for either operation's call.
structure Contents (α : Type) where
  length : Word
  capacity : Word
  old : Nat → α

def Contents.ofInsert {α : Type} (call : Insert.Call α) : Contents α :=
  ⟨call.length, call.capacity, call.old⟩

def Contents.ofRemove {α : Type} (call : Remove.Call α) : Contents α :=
  ⟨call.length, call.capacity, call.old⟩

-- RV32 (`MXL = 1`) with the I and M extensions.
def misaValue : BitVec 32 := 0x40001100

def registers : Std.ExtDHashMap Register RegisterType :=
  ((((((((∅ : Std.ExtDHashMap Register RegisterType).insert Register.x1 returnTo).insert
    Register.cur_privilege Privilege.Machine).insert Register.misa misaValue).insert
    Register.mseccfg (0 : BitVec 64)).insert Register.mstatus (0 : BitVec 64)).insert
    Register.htif_tohost_base none).insert Register.pma_regions [wholeSpaceRegion])

variable {α : Type} [Element α]

-- Word indices: the header at `0xc00`–`0xc02`, whose data pointer is
-- `0x4000`, and the elements from `0x1000`.
def dataContents (call : Contents α) (index : Nat) : Word :=
  if index = 0xc00 then 0x4000
  else if index = 0xc01 then call.length
  else if index = 0xc02 then call.capacity
  else Element.word (call.old ((index - 0x1000) / Element.words α)) ((index - 0x1000) % Element.words α)

def contents (image : Image) (call : Contents α) (index : Nat) : Word :=
  (image.word index).getD (dataContents call index)

def keys (image : Image) (call : Contents α) : List Nat :=
  image.keys ++ List.range' 0x3000 12 ++ List.range' 0x4000 (Element.bytes α * call.length.toNat)

def frame (image : Image) (call : Contents α) : Machine :=
  { (default : Machine) with regs := registers, mem := wordMemory (keys image call) (contents image call) }

/-! ## The model satisfies the shared premises -/

-- A machine with the model's memory and PMA region.
structure Modeled (image : Image) (call : Contents α) (state : Machine) : Prop where
  mem : state.mem = wordMemory (keys image call) (contents image call)
  regions : Sail.readReg Register.pma_regions state = .ok [wholeSpaceRegion] state

section Machine

variable {image : Image}

theorem frameRead {key : Register} {value : RegisterType key} (call : Contents α)
    (stored : registers.get? key = some value) :
    Sail.readReg key (frame image call) = .ok value (frame image call) :=
  readReg_succ.mpr stored

theorem frameState (call : Contents α) : MachineState (frame image call) := by
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
theorem syncModeled {S : Type} [RegisterView S] (call : Contents α) (base : Word) (state : S) :
    Modeled image call (sync base (frame image call) state) :=
  ⟨by simp only [syncMem, frame],
    Platform.systemRead state (by decide) (by decide) (by decide) (frameRead call (by simp [registers]))⟩

-- A snapshot that does not track `ra` keeps the model's return address.
theorem modelMode {S : Type} [RegisterView S] (call : Contents α) (base : Word) (state : S)
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
theorem tableImage {state : Machine} {image : Image} {call : Contents α}
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

theorem readable {call : Contents α} (modeled : Modeled image call state)
    {address : Word} (aligned : address.toNat % 4 = 0) (fits : address.toNat + 4 ≤ 2 ^ 32) :
    Readable state address :=
  ⟨aligned, _, _, modeled.regions, wholeSpaceMatches address 4 (by decide) fits, rfl⟩

theorem writable {call : Contents α} (modeled : Modeled image call state)
    {address : Word} (aligned : address.toNat % 4 = 0) (fits : address.toNat + 4 ≤ 2 ^ 32) :
    Writable state address :=
  ⟨aligned, _, _, modeled.regions, wholeSpaceMatches address 4 (by decide) fits, rfl⟩

private theorem headerWord {call : Contents α} (modeled : Modeled image call state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none)
    (offset : Nat) (small : offset < 3) :
    WordAt state.mem (0x3000 + 4 * offset) (dataContents call (0xc00 + offset)) := by
  rw [modeled.mem]
  have word := wordMemoryWord (keys image call) (contents image call) (0x3000 + 4 * offset) (by omega)
    (fun byte bound => by simp [keys]; omega)
  have quotient : (0x3000 + 4 * offset) / 4 = 0xc00 + offset := by omega
  rw [quotient, contents, dataFree _ (by omega), Option.getD_none] at word
  exact word

-- Each live element of the model sits at `0x4000 + bytes * slot`.
theorem modelElement {call : Contents α} (modeled : Modeled image call state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none)
    (small : Element.bytes α * call.length.toNat ≤ 0x100000) {slot : Nat}
    (bound : slot < call.length.toNat) :
    Element.At state.mem (0x4000 + Element.bytes α * slot) (call.old slot) := by
  have words := Element.bytesWords (α := α)
  have positive := Element.positive (α := α)
  refine Element.atOfWords fun part inside => ?_
  have scaled := Nat.mul_le_mul_left (Element.bytes α) (show slot + 1 ≤ call.length.toNat by omega)
  have next := Nat.mul_add_one (Element.bytes α) slot
  have quarter : Element.bytes α * slot = 4 * (Element.words α * slot) := by
    rw [words, Nat.mul_assoc]
  rw [modeled.mem]
  have word := wordMemoryWord (keys image call) (contents image call)
    (0x4000 + Element.bytes α * slot + 4 * part) (by omega)
    (fun byte small => by simp only [keys, List.mem_append, List.mem_range'_1]; omega)
  have quotient : (0x4000 + Element.bytes α * slot + 4 * part) / 4 =
      0x1000 + (Element.words α * slot + part) := by omega
  have selected : contents image call (0x1000 + (Element.words α * slot + part)) =
      Element.word (call.old slot) part := by
    rw [contents, dataFree _ (by omega), Option.getD_none, dataContents,
      if_neg (by omega), if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
      Nat.mul_add_div positive, Nat.div_eq_of_lt inside, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt inside]
  rw [quotient, selected] at word
  exact word

-- Each word of an element slot far below the top of memory is aligned and
-- addressable.
private theorem elementWord {slot part : Nat} (small : Element.bytes α * (slot + 1) ≤ 0x100000)
    (inside : part < Element.words α) :
    (BitVec.ofNat 32 (0x4000 + Element.bytes α * slot) + BitVec.ofNat 32 (4 * part)).toNat =
        0x4000 + Element.bytes α * slot + 4 * part ∧
      (0x4000 + Element.bytes α * slot + 4 * part) % 4 = 0 ∧
      0x4000 + Element.bytes α * slot + 4 * part + 4 ≤ 2 ^ 32 := by
  have words := Element.bytesWords (α := α)
  have next := Nat.mul_add_one (Element.bytes α) slot
  have quarter : Element.bytes α * slot = 4 * (Element.words α * slot) := by
    rw [words, Nat.mul_assoc]
  refine ⟨?_, by omega, by omega⟩
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 0x4000 + Element.bytes α * slot < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show 4 * part < 2 ^ 32 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem elementReadable {call : Contents α} (modeled : Modeled image call state) {slot : Nat}
    (small : Element.bytes α * (slot + 1) ≤ 0x100000) :
    Element.Mapped (α := α) state (BitVec.ofNat 32 (0x4000 + Element.bytes α * slot))
      (fun region => region.attributes.readable = true) :=
  Element.mappedOfWords fun _ inside =>
    have facts := elementWord small inside
    readable modeled (by rw [facts.1]; exact facts.2.1) (by rw [facts.1]; exact facts.2.2)

theorem elementWritable {call : Contents α} (modeled : Modeled image call state) {slot : Nat}
    (small : Element.bytes α * (slot + 1) ≤ 0x100000) :
    Element.Mapped (α := α) state (BitVec.ofNat 32 (0x4000 + Element.bytes α * slot))
      (fun region => region.attributes.writable = true) :=
  Element.mappedOfWords fun _ inside =>
    have facts := elementWord small inside
    writable modeled (by rw [facts.1]; exact facts.2.1) (by rw [facts.1]; exact facts.2.2)

/-! ### Insertion -/

theorem modelHeader {index length capacity : Word} {value : α} {old : Nat → α}
    (modeled : Modeled image (.ofInsert (modelCall index value length capacity old)) state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none) :
    Insert.Header state (modelCall index value length capacity old) :=
  ⟨by simp [modelCall], readable modeled (by simp [modelCall]) (by simp [modelCall]),
    readable modeled (by simp [modelCall]) (by simp [modelCall]),
    by simpa [dataContents, Contents.ofInsert] using headerWord modeled dataFree 1 (by decide),
    by simpa [dataContents, Contents.ofInsert] using headerWord modeled dataFree 2 (by decide)⟩

theorem modelBuffer {codeBytes : Nat} {index length capacity : Word} {value : α} {old : Nat → α}
    (modeled : Modeled image (.ofInsert (modelCall index value length capacity old)) state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none)
    (codeFits : 0x1000 + codeBytes ≤ 0x3000)
    (small : Element.bytes α * (length.toNat + 1) ≤ 0x100000) :
    Insert.Buffer codeBytes codeBase state (modelCall index value length capacity old) := by
  have succ := Nat.mul_add_one (Element.bytes α) length.toNat
  have scaled (slot : Nat) (bound : slot ≤ length.toNat) :
      Element.bytes α * (slot + 1) ≤ 0x100000 :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) small
  refine ⟨?_, readable modeled (by simp [modelCall]) (by simp [modelCall]),
    by simpa [dataContents] using headerWord modeled dataFree 0 (by decide),
    writable modeled (by simp [modelCall]) (by simp [modelCall]),
    Or.inr (by change 0x1000 + codeBytes ≤ 0x3000 + 4; omega), fun slot bound => ?_,
    fun slot _ bound => elementReadable modeled (scaled slot (by change slot < length.toNat at bound; omega)),
    fun slot _ bound => elementWritable modeled (scaled slot bound),
    fun slot bound => ?_, fun slot _ bound => ?_⟩
  · change 0x4000 + Element.bytes α * (length.toNat + 1) ≤ 2 ^ 32
    omega
  · exact modelElement modeled dataFree (show Element.bytes α * length.toNat ≤ 0x100000 by omega) bound
  · right
    change 0x3000 + 12 ≤ 0x4000 + Element.bytes α * slot
    omega
  · right
    change 0x1000 + codeBytes ≤ 0x4000 + Element.bytes α * slot
    omega

/-! ### Removal -/

theorem modelRemoveHeader {index length capacity : Word} {old : Nat → α}
    (modeled : Modeled image (.ofRemove (modelRemoveCall index length capacity old)) state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none) :
    Remove.Header state (modelRemoveCall index length capacity old) :=
  ⟨by simp [modelRemoveCall], readable modeled (by simp [modelRemoveCall]) (by simp [modelRemoveCall]),
    readable modeled (by simp [modelRemoveCall]) (by simp [modelRemoveCall]),
    by simpa [dataContents, Contents.ofRemove] using headerWord modeled dataFree 1 (by decide),
    by simpa [dataContents, Contents.ofRemove] using headerWord modeled dataFree 2 (by decide)⟩

theorem modelRemoveBuffer {codeBytes : Nat} {index length capacity : Word} {old : Nat → α}
    (modeled : Modeled image (.ofRemove (modelRemoveCall index length capacity old)) state)
    (dataFree : ∀ index, 0xc00 ≤ index → image.word index = none)
    (codeFits : 0x1000 + codeBytes ≤ 0x3000)
    (small : Element.bytes α * length.toNat ≤ 0x100000) :
    Remove.Buffer codeBytes codeBase state (modelRemoveCall index length capacity old) := by
  have scaled (slot : Nat) (bound : slot < length.toNat) :
      Element.bytes α * (slot + 1) ≤ 0x100000 :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) small
  refine ⟨?_, readable modeled (by simp [modelRemoveCall]) (by simp [modelRemoveCall]),
    by simpa [dataContents] using headerWord modeled dataFree 0 (by decide),
    writable modeled (by simp [modelRemoveCall]) (by simp [modelRemoveCall]),
    Or.inr (by change 0x1000 + codeBytes ≤ 0x3000 + 4; omega),
    fun slot bound => modelElement modeled dataFree small bound,
    fun slot _ bound => elementReadable modeled (scaled slot bound),
    fun slot _ bound => elementWritable modeled
      (scaled slot (by change slot + 1 < length.toNat at bound; omega)),
    fun slot bound => ?_, fun slot _ bound => ?_⟩
  · change 0x4000 + Element.bytes α * length.toNat ≤ 2 ^ 32
    omega
  · right
    change 0x3000 + 12 ≤ 0x4000 + Element.bytes α * slot
    omega
  · right
    change 0x1000 + codeBytes ≤ 0x4000 + Element.bytes α * slot
    omega

end Premises

end Riscfree.RawVec.Model
