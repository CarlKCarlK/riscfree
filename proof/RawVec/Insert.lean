import RawVec.Access

/-!
# The size-independent part of `RawVec<T>::insert`

Every linked instance of `RawVec<T>::insert` (`research/vec-ffi/linked/raw_vec.rs`)
has the same specification, the same memory footprint, and the same copy-loop
invariant. Only the element layout differs. `Element` records that layout.
Each routine then supplies its own instruction table, step lemmas, register
snapshot, and step count, and instantiates everything here.

For `Word` elements the definitions here unfold to the original
`raw_vec_u32_insert` statement. `RawVec/Compatibility.lean` checks that.
-/

namespace Riscfree.RawVec

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

-- How one element is laid out: `words` little-endian words, `bytes` bytes.
class Element (α : Type) where
  bytes : Nat
  words : Nat
  word : α → Nat → Word
  At : ByteMemory → Nat → α → Prop
  -- Every word of the element at this address has the permission.
  Mapped : Machine → Word → (PMA_Region → Prop) → Prop
  store : ByteMemory → Nat → α → ByteMemory
  bytesWords : bytes = 4 * words
  positive : 0 < words
  atOfWords {memory : ByteMemory} {address : Nat} {value : α} :
    (∀ part < words, WordAt memory (address + 4 * part) (word value part)) → At memory address value
  atFrame {memory other : ByteMemory} {address : Nat} {value : α} :
    At memory address value →
    (∀ byte, address ≤ byte → byte < address + bytes → other[byte]? = memory[byte]?) →
    At other address value
  atStore (memory : ByteMemory) (address : Nat) (value : α) :
    At (store memory address value) address value
  storeOutside (memory : ByteMemory) (address : Nat) (value : α) (byte : Nat) :
    byte < address ∨ address + bytes ≤ byte → (store memory address value)[byte]? = memory[byte]?
  mappedOfWords {frame : Machine} {address : Word} {permission : PMA_Region → Prop} :
    (∀ part < words, RawVec.Mapped frame (address + BitVec.ofNat 32 (4 * part)) permission) →
    Mapped frame address permission

instance : Element Word where
  bytes := 4
  words := 1
  word value _ := value
  At := WordAt
  Mapped := RawVec.Mapped
  store := storeWord
  bytesWords := rfl
  positive := by decide
  atOfWords words := by simpa using words 0 (by decide)
  atFrame word same := word.congr same
  atStore := wordAtStore
  storeOutside := storeWordOutside
  mappedOfWords mapped := by simpa using mapped 0 (by decide)

theorem bytesPositive {α : Type} [Element α] : 0 < Element.bytes α := by
  have := Element.positive (α := α)
  rw [Element.bytesWords]
  omega

theorem wordBytes : Element.bytes Word = 4 := rfl

-- The element of `RawVec<Pair>`: `#[repr(C)] struct Pair { key: u32, value: u32 }`.
structure Pair where
  key : Word
  value : Word

def PairAt (memory : ByteMemory) (address : Nat) (pair : Pair) : Prop :=
  WordAt memory address pair.key ∧ WordAt memory (address + 4) pair.value

def storePair (memory : ByteMemory) (address : Nat) (pair : Pair) : ByteMemory :=
  storeWord (storeWord memory address pair.key) (address + 4) pair.value

instance : Element Pair where
  bytes := 8
  words := 2
  word pair part := if part = 0 then pair.key else pair.value
  At := PairAt
  Mapped frame address permission :=
    RawVec.Mapped frame address permission ∧ RawVec.Mapped frame (address + 4) permission
  store := storePair
  bytesWords := rfl
  positive := by decide
  atOfWords words := ⟨by simpa using words 0 (by decide), by simpa using words 1 (by decide)⟩
  atFrame pair same :=
    ⟨pair.1.congr fun byte low high => same byte low (by omega),
      pair.2.congr fun byte low high => same byte (by omega) (by omega)⟩
  atStore memory address pair :=
    ⟨(wordAtStore memory address pair.key).storeOther (Or.inl (Nat.le_refl _)),
      wordAtStore _ _ pair.value⟩
  storeOutside memory address pair byte outside := by
    rw [storePair, storeWordOutside _ _ _ _ (by omega), storeWordOutside _ _ _ _ (by omega)]
  mappedOfWords mapped := ⟨by simpa using mapped 0 (by decide), by simpa using mapped 1 (by decide)⟩

theorem pairBytes : Element.bytes Pair = 8 := rfl

section Frame

variable {α : Type} [Element α]

-- Storing an element leaves a word outside it unchanged.
theorem wordStoreElement {memory : ByteMemory} {address written : Nat} {value : Word}
    {element : α} (word : WordAt memory address value)
    (apart : address + 4 ≤ written ∨ written + Element.bytes α ≤ address) :
    WordAt (Element.store memory written element) address value :=
  word.congr fun _ _ _ => Element.storeOutside _ _ _ _ (by omega)

-- Storing a word leaves an element outside it unchanged.
theorem elementStoreWord {memory : ByteMemory} {address written : Nat} {element : α}
    {value : Word} (stored : Element.At memory address element)
    (apart : address + Element.bytes α ≤ written ∨ written + 4 ≤ address) :
    Element.At (storeWord memory written value) address element :=
  Element.atFrame stored fun _ _ _ => storeWordOutside _ _ _ _ (by omega)

-- Storing an element leaves another element outside it unchanged.
theorem elementStoreElement {memory : ByteMemory} {address written : Nat} {element other : α}
    (stored : Element.At memory address element)
    (apart : address + Element.bytes α ≤ written ∨ written + Element.bytes α ≤ address) :
    Element.At (Element.store memory written other) address element :=
  Element.atFrame stored fun _ _ _ => Element.storeOutside _ _ _ _ (by omega)

end Frame

namespace Insert

variable {α : Type}

structure Call (α : Type) where
  header : Word
  index : Word
  value : α
  length : Word
  capacity : Word
  data : Word
  old : Nat → α

-- A store of `width` bytes at `address` misses the `codeBytes` bytes at `base`.
def outsideCode (codeBytes : Nat) (base : Word) (width address : Nat) : Prop :=
  address + width ≤ base.toNat ∨ base.toNat + codeBytes ≤ address

-- Rejected calls need only the two readable header words used in the checks.
-- A successful call needs access to the live prefix and a single spare slot.
-- Permissions for the rest of the capacity are irrelevant to this routine.
structure Header (original : Machine) (call : Call α) : Prop where
  fits : call.header.toNat + 12 ≤ 2 ^ 32
  lengthReadable : Readable original (call.header + 4)
  capacityReadable : Readable original (call.header + 8)
  lengthWord : WordAt original.mem (call.header.toNat + 4) call.length
  capacityWord : WordAt original.mem (call.header.toNat + 8) call.capacity

theorem ofWordNat (word : Word) : BitVec.ofNat 32 word.toNat = word := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem headerOffset {original : Machine} {call : Call α} (header : Header original call) (offset : Nat) (bound : offset ≤ 8) :
    (call.header + BitVec.ofNat 32 offset).toNat = call.header.toNat + offset := by
  have fits := header.fits
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

variable [Element α]

-- A store inside a wider one that misses the code misses it too.
theorem outsideCode.narrow {codeBytes : Nat} {base : Word} {width narrower address : Nat}
    (apart : outsideCode codeBytes base width address) (le : narrower ≤ width) :
    outsideCode codeBytes base narrower address := by
  unfold outsideCode at *
  omega

namespace Call

def slot (call : Call α) (index : Nat) : Nat := call.data.toNat + Element.bytes α * index

def wordSlot (call : Call α) (index : Nat) : Word := BitVec.ofNat 32 (call.slot index)

def valid (call : Call α) : Prop :=
  call.index.toNat ≤ call.length.toNat ∧ call.length.toNat < call.capacity.toNat

instance (call : Call α) : Decidable call.valid :=
  inferInstanceAs (Decidable (call.index.toNat ≤ call.length.toNat ∧
    call.length.toNat < call.capacity.toNat))

def status (call : Call α) : Word :=
  if call.capacity.toNat < call.length.toNat then 3
  else if call.length.toNat < call.index.toNat then 2
  else if call.length = call.capacity then 1
  else 0

def result (call : Call α) (index : Nat) : α :=
  if index < call.index.toNat then call.old index
  else if index = call.index.toNat then call.value
  else call.old (index - 1)

-- An element at `address` misses the three header words.
def outsideHeader (call : Call α) (address : Nat) : Prop :=
  address + Element.bytes α ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ address

def unchanged (call : Call α) (before after : ByteMemory) : Prop :=
  ∀ byte, (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) →
    (byte < call.slot call.index.toNat ∨ call.slot (call.length.toNat + 1) ≤ byte) →
    after[byte]? = before[byte]?

theorem slotSucc (call : Call α) (index : Nat) :
    call.slot (index + 1) = call.slot index + Element.bytes α := by
  unfold slot
  rw [Nat.mul_succ]
  omega

theorem slotMono (call : Call α) {low high : Nat} (le : low ≤ high) :
    call.slot low ≤ call.slot high := by
  unfold slot
  have := Nat.mul_le_mul_left (Element.bytes α) le
  omega

theorem slotBefore (call : Call α) {low high : Nat} (lt : low < high) :
    call.slot low + Element.bytes α ≤ call.slot high := by
  rw [← slotSucc]
  exact call.slotMono lt

end Call

structure Buffer (codeBytes : Nat) (base : Word) (original : Machine) (call : Call α) : Prop where
  fits : call.slot (call.length.toNat + 1) ≤ 2 ^ 32
  dataReadable : Readable original call.header
  dataWord : WordAt original.mem call.header.toNat call.data
  lengthWritable : Writable original (call.header + 4)
  lengthAwayFromCode : outsideCode codeBytes base 4 (call.header.toNat + 4)
  live : ∀ index, index < call.length.toNat →
    Element.At original.mem (call.slot index) (call.old index)
  readable : ∀ index, call.index.toNat ≤ index → index < call.length.toNat →
    Element.Mapped (α := α) original (call.wordSlot index) (fun region => region.attributes.readable = true)
  writable : ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
    Element.Mapped (α := α) original (call.wordSlot index) (fun region => region.attributes.writable = true)
  separated : ∀ index, index ≤ call.length.toNat →
    call.outsideHeader (call.slot index)
  awayFromCode : ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
    outsideCode codeBytes base (Element.bytes α) (call.slot index)

section Arithmetic

variable {codeBytes : Nat} {base : Word} {original : Machine} {call : Call α}

-- Every byte of every element up to the spare slot is addressable.
theorem slotFits (buffer : Buffer codeBytes base original call) {index : Nat}
    (bound : index ≤ call.length.toNat) : call.slot index + Element.bytes α ≤ 2 ^ 32 := by
  have before := call.slotBefore (show index < call.length.toNat + 1 by omega)
  have fits := buffer.fits
  omega

theorem slotNat (buffer : Buffer codeBytes base original call) {index : Nat}
    (bound : index ≤ call.length.toNat) : (call.wordSlot index).toNat = call.slot index := by
  have fits := slotFits buffer bound
  have positive := bytesPositive (α := α)
  change call.slot index % 2 ^ 32 = call.slot index
  exact Nat.mod_eq_of_lt (show call.slot index < 2 ^ 32 by omega)

-- A word inside an element lies at the element's address plus its offset.
theorem slotOffset (buffer : Buffer codeBytes base original call) {index offset : Nat}
    (bound : index ≤ call.length.toNat) (inside : offset < Element.bytes α) :
    (call.wordSlot index + BitVec.ofNat 32 offset).toNat = call.slot index + offset := by
  have fits := slotFits buffer bound
  rw [BitVec.toNat_add, slotNat buffer bound, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2 ^ 32 by omega)]
  exact Nat.mod_eq_of_lt (show call.slot index + offset < 2 ^ 32 by omega)

-- `slli` by `shift` and `add` compute an element's address when elements
-- occupy `2 ^ shift` bytes.
theorem slotAdd (buffer : Buffer codeBytes base original call) (shift : Nat)
    (scale : Element.bytes α = 2 ^ shift) {index : Nat} (bound : index ≤ call.length.toNat) :
    call.data + (BitVec.ofNat 32 index <<< shift) = call.wordSlot index := by
  have indexFits : index < 2 ^ 32 := by have := call.length.isLt; omega
  have addressFits := slotFits buffer bound
  unfold Call.slot at addressFits
  rw [scale, Nat.mul_comm] at addressFits
  have positive := Nat.two_pow_pos shift
  have offsetFits : index * 2 ^ shift < 2 ^ 32 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [slotNat buffer bound, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt indexFits, Nat.shiftLeft_eq, Nat.mod_eq_of_lt offsetFits,
    Nat.mod_eq_of_lt (show call.data.toNat + index * 2 ^ shift < 2 ^ 32 by omega)]
  unfold Call.slot
  rw [scale, Nat.mul_comm]

-- Adding `negative`, the two's complement of the element size, steps one slot back.
theorem slotPrev (call : Call α) (index : Nat) (negative : Word)
    (cancel : BitVec.ofNat 32 (Element.bytes α) + negative = 0) :
    call.wordSlot (index + 1) + negative = call.wordSlot index := by
  rw [Call.wordSlot, Call.wordSlot, call.slotSucc, BitVec.ofNat_add, BitVec.add_assoc, cancel]
  exact BitVec.add_zero _

theorem counterPrev (index : Nat) :
    BitVec.ofNat 32 (index + 1) + 0xffffffff#32 = BitVec.ofNat 32 index := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  exact BitVec.add_zero _

-- A memory change confined to `width` bytes at `address` keeps the code.
theorem keepsCode {originalMemory memory updated : ByteMemory}
    (agrees : CodeAgreesFor codeBytes base originalMemory memory) {width address : Nat}
    (same : ∀ byte, byte < address ∨ address + width ≤ byte → updated[byte]? = memory[byte]?)
    (apart : outsideCode codeBytes base width address) :
    CodeAgreesFor codeBytes base originalMemory updated := by
  intro byte low high
  rw [same byte (by unfold outsideCode at apart; omega)]
  exact agrees byte low high

theorem storeKeepsCode {originalMemory memory : ByteMemory}
    (agrees : CodeAgreesFor codeBytes base originalMemory memory) {address : Nat}
    (apart : outsideCode codeBytes base 4 address) (value : Word) :
    CodeAgreesFor codeBytes base originalMemory (storeWord memory address value) :=
  keepsCode agrees (storeWordOutside _ _ _) apart

theorem elementKeepsCode {originalMemory memory : ByteMemory}
    (agrees : CodeAgreesFor codeBytes base originalMemory memory) {address : Nat}
    (apart : outsideCode codeBytes base (Element.bytes α) address) (value : α) :
    CodeAgreesFor codeBytes base originalMemory (Element.store memory address value) :=
  keepsCode agrees (Element.storeOutside _ _ _) apart

end Arithmetic

/-! ## The copy loop

The loop moves elements one slot up, from the end down to `call.index`.
`Progress current memory` holds at the loop head once every element above
`current` has moved. Bytes outside the moved region keep their values.
-/

section Loop

variable {codeBytes : Nat} {base : Word} {original : Machine} {call : Call α}

structure Progress (codeBytes : Nat) (base : Word) (original : Machine) (call : Call α)
    (current : Nat) (memory : ByteMemory) : Prop where
  code : CodeAgreesFor codeBytes base original.mem memory
  data : WordAt memory call.header.toNat call.data
  capacity : WordAt memory (call.header.toNat + 8) call.capacity
  shifted : ∀ index, current < index → index ≤ call.length.toNat →
    Element.At memory (call.slot index) (call.old (index - 1))
  outside : ∀ byte, byte < call.slot (current + 1) ∨ call.slot (call.length.toNat + 1) ≤ byte →
    memory[byte]? = original.mem[byte]?

theorem initialProgress (header : Header original call) (buffer : Buffer codeBytes base original call) :
    Progress codeBytes base original call call.length.toNat original.mem :=
  ⟨fun _ _ _ => rfl, buffer.dataWord, header.capacityWord,
    fun _ greater less => (Nat.not_lt_of_ge less greater).elim, fun _ _ => rfl⟩

theorem Progress.source {memory : ByteMemory} {current index : Nat}
    (progress : Progress codeBytes base original call current memory)
    (buffer : Buffer codeBytes base original call) (before : index ≤ current)
    (live : index < call.length.toNat) :
    Element.At memory (call.slot index) (call.old index) := by
  have below := call.slotBefore (show index < current + 1 by omega)
  exact Element.atFrame (buffer.live index live) fun byte _ high =>
    progress.outside byte (Or.inl (by omega))

theorem Progress.copy {memory : ByteMemory} {index : Nat}
    (progress : Progress codeBytes base original call (index + 1) memory)
    (buffer : Buffer codeBytes base original call)
    (afterIndex : call.index.toNat ≤ index) (live : index < call.length.toNat) :
    Progress codeBytes base original call index
      (Element.store memory (call.slot (index + 1)) (call.old index)) := by
  have apart := buffer.separated (index + 1) (by omega)
  unfold Call.outsideHeader at apart
  have spare := call.slotBefore (show index + 1 < call.length.toNat + 1 by omega)
  have next := call.slotSucc (index + 1)
  constructor
  · exact elementKeepsCode progress.code (buffer.awayFromCode _ (by omega) (by omega)) _
  · exact wordStoreElement progress.data (by omega)
  · exact wordStoreElement progress.capacity (by omega)
  · intro observed afterCurrent inBounds
    by_cases same : observed = index + 1
    · subst observed
      simpa only [Nat.add_sub_cancel] using
        Element.atStore memory (call.slot (index + 1)) (call.old index)
    · have later := call.slotBefore (show index + 1 < observed by omega)
      exact elementStoreElement (progress.shifted observed (by omega) inBounds) (by omega)
  · intro byte outside
    rw [Element.storeOutside _ _ _ _ (by omega)]
    apply progress.outside
    omega

def insertedMemory (call : Call α) (memory : ByteMemory) : ByteMemory :=
  Element.store memory (call.slot call.index.toNat) call.value

def finalMemory (call : Call α) (memory : ByteMemory) : ByteMemory :=
  storeWord (insertedMemory call memory) (call.header.toNat + 4) (call.length + 1)

-- After the loop, storing the new element and the new length gives the result.
theorem finalWords (buffer : Buffer codeBytes base original call)
    (memory : ByteMemory) (progress : Progress codeBytes base original call call.index.toNat memory)
    (indexBound : call.index.toNat ≤ call.length.toNat) :
    WordAt (finalMemory call memory) call.header.toNat call.data ∧
    WordAt (finalMemory call memory) (call.header.toNat + 4) (call.length + 1) ∧
    WordAt (finalMemory call memory) (call.header.toNat + 8) call.capacity ∧
    (∀ index, index ≤ call.length.toNat →
      Element.At (finalMemory call memory) (call.slot index) (call.result index)) ∧
    call.unchanged original.mem (finalMemory call memory) := by
  have indexApart := buffer.separated call.index.toNat indexBound
  unfold Call.outsideHeader at indexApart
  refine ⟨?_, wordAtStore _ _ _, ?_, ?_, ?_⟩
  · exact (wordStoreElement progress.data (by omega)).storeOther (Or.inl (by omega))
  · exact (wordStoreElement progress.capacity (by omega)).storeOther (Or.inr (by omega))
  · intro index bound
    have apart := buffer.separated index bound
    unfold Call.outsideHeader at apart
    apply elementStoreWord ?_ (by omega)
    by_cases before : index < call.index.toNat
    · rw [Call.result, if_pos before]
      have lower := call.slotBefore before
      exact elementStoreElement (progress.source buffer (by omega) (by omega)) (Or.inl lower)
    · by_cases same : index = call.index.toNat
      · subst index
        simpa only [Call.result, lt_irrefl, if_false, if_true] using
          Element.atStore memory (call.slot call.index.toNat) call.value
      · rw [Call.result, if_neg before, if_neg same]
        have higher := call.slotBefore (show call.index.toNat < index by omega)
        exact elementStoreElement (progress.shifted index (by omega) bound) (Or.inr higher)
  · intro byte outsideLength outsideData
    have next := call.slotSucc call.index.toNat
    have tail := call.slotBefore (show call.index.toNat < call.length.toNat + 1 by omega)
    unfold finalMemory insertedMemory
    rw [storeWordOutside _ _ _ _ (by omega), Element.storeOutside _ _ _ _ (by omega)]
    apply progress.outside
    omega

end Loop

end Insert

end Riscfree.RawVec
