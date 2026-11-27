import RawVec.Insert

/-!
# The size-independent part of `RawVec<T>::remove`

Every linked instance of `RawVec<T>::remove`
(`research/vec-ffi/linked/raw_vec_remove.rs`) has the same specification, the
same memory footprint, and the same copy-loop invariant. Only the element
layout differs. Each routine supplies its own instruction table, step
lemmas, register snapshot, and step count, and instantiates everything here.

The element layout (`Element`), the frame lemmas for element stores, and the
code-preservation lemmas come from `RawVec/Insert.lean`. The call record,
premises, and loop invariant are separate from insertion's: a removal has no
inserted value, needs one slot fewer, and moves elements the other way.
-/

namespace Riscfree.RawVec

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

namespace Remove

open Insert (outsideCode elementKeepsCode)

variable {α : Type}

structure Call (α : Type) where
  header : Word
  index : Word
  length : Word
  capacity : Word
  data : Word
  old : Nat → α

-- Rejected calls need only the two readable header words used in the checks.
structure Header (original : Machine) (call : Call α) : Prop where
  fits : call.header.toNat + 12 ≤ 2 ^ 32
  lengthReadable : Readable original (call.header + 4)
  capacityReadable : Readable original (call.header + 8)
  lengthWord : WordAt original.mem (call.header.toNat + 4) call.length
  capacityWord : WordAt original.mem (call.header.toNat + 8) call.capacity

theorem headerOffset {original : Machine} {call : Call α} (header : Header original call)
    (offset : Nat) (bound : offset ≤ 8) :
    (call.header + BitVec.ofNat 32 offset).toNat = call.header.toNat + offset := by
  have fits := header.fits
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

namespace Call

def newLength (call : Call α) : Word := BitVec.ofNat 32 (call.length.toNat - 1)

-- `addi rd, rs, -1` on a positive length gives the new length.
theorem decrement (call : Call α) (positive : 0 < call.length.toNat) :
    call.length + 0xffffffff#32 = call.newLength := by
  have whole : BitVec.ofNat 32 (call.length.toNat - 1 + 1) = call.length := by
    rw [Nat.sub_add_cancel positive]
    exact Insert.ofWordNat _
  rw [newLength, ← Insert.counterPrev (call.length.toNat - 1), whole]

end Call

variable [Element α]

namespace Call

def slot (call : Call α) (index : Nat) : Nat := call.data.toNat + Element.bytes α * index

def wordSlot (call : Call α) (index : Nat) : Word := BitVec.ofNat 32 (call.slot index)

def valid (call : Call α) : Prop :=
  call.index.toNat < call.length.toNat ∧ call.length.toNat ≤ call.capacity.toNat

instance (call : Call α) : Decidable call.valid :=
  inferInstanceAs (Decidable (call.index.toNat < call.length.toNat ∧
    call.length.toNat ≤ call.capacity.toNat))

-- The routine checks the length before the index, as `insert` does.
def status (call : Call α) : Word :=
  if call.capacity.toNat < call.length.toNat then 3
  else if call.length.toNat ≤ call.index.toNat then 2
  else 0

-- The new logical sequence: the old one without the element at `call.index`.
def result (call : Call α) (index : Nat) : α :=
  if index < call.index.toNat then call.old index else call.old (index + 1)

-- An element at `address` misses the three header words.
def outsideHeader (call : Call α) (address : Nat) : Prop :=
  address + Element.bytes α ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ address

-- Only the length word and the slots from `call.index` to the new length
-- may change. The vacated last slot keeps its old element.
def unchanged (call : Call α) (before after : ByteMemory) : Prop :=
  ∀ byte, (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) →
    (byte < call.slot call.index.toNat ∨ call.slot (call.length.toNat - 1) ≤ byte) →
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

-- `slli` by `shift` and `add` compute an element's address when elements
-- occupy `2 ^ shift` bytes. Both sides wrap modulo `2 ^ 32`, so this needs no
-- bound.
theorem slotShift (call : Call α) (shift : Nat) (scale : Element.bytes α = 2 ^ shift)
    (index : Word) : index <<< shift + call.data = call.wordSlot index.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [wordSlot, slot, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_add_mod, scale]
  rw [Nat.add_comm, Nat.mul_comm]

-- Adding the element size steps one slot forward, and adding `negative`, its
-- two's complement, one slot back.
theorem slotNext (call : Call α) (index : Nat) :
    call.wordSlot index + BitVec.ofNat 32 (Element.bytes α) = call.wordSlot (index + 1) := by
  rw [wordSlot, wordSlot, call.slotSucc, BitVec.ofNat_add]

theorem slotPrev (call : Call α) (index : Nat) (negative : Word)
    (cancel : BitVec.ofNat 32 (Element.bytes α) + negative = 0) :
    call.wordSlot (index + 1) + negative = call.wordSlot index := by
  rw [← slotNext, BitVec.add_assoc, cancel]
  exact BitVec.add_zero _

end Call

/-! ## The premises of a successful call -/

structure Buffer (codeBytes : Nat) (base : Word) (original : Machine) (call : Call α) : Prop where
  fits : call.slot call.length.toNat ≤ 2 ^ 32
  dataReadable : Readable original call.header
  dataWord : WordAt original.mem call.header.toNat call.data
  lengthWritable : Writable original (call.header + 4)
  lengthAwayFromCode : outsideCode codeBytes base 4 (call.header.toNat + 4)
  live : ∀ index, index < call.length.toNat →
    Element.At original.mem (call.slot index) (call.old index)
  -- The loop reads every element after the removed one ...
  readable : ∀ index, call.index.toNat < index → index < call.length.toNat →
    Element.Mapped (α := α) original (call.wordSlot index) (fun region => region.attributes.readable = true)
  -- ... and writes each one slot lower.
  writable : ∀ index, call.index.toNat ≤ index → index + 1 < call.length.toNat →
    Element.Mapped (α := α) original (call.wordSlot index) (fun region => region.attributes.writable = true)
  separated : ∀ index, index + 1 < call.length.toNat → call.outsideHeader (call.slot index)
  awayFromCode : ∀ index, call.index.toNat ≤ index → index + 1 < call.length.toNat →
    outsideCode codeBytes base (Element.bytes α) (call.slot index)

section Arithmetic

variable {codeBytes : Nat} {base : Word} {original : Machine} {call : Call α}

-- Every byte of every live element is addressable.
theorem slotFits (buffer : Buffer codeBytes base original call) {index : Nat}
    (bound : index < call.length.toNat) : call.slot index + Element.bytes α ≤ 2 ^ 32 := by
  have before := call.slotBefore bound
  have fits := buffer.fits
  omega

theorem slotNat (buffer : Buffer codeBytes base original call) {index : Nat}
    (bound : index < call.length.toNat) : (call.wordSlot index).toNat = call.slot index := by
  have fits := slotFits buffer bound
  have positive := bytesPositive (α := α)
  change call.slot index % 2 ^ 32 = call.slot index
  exact Nat.mod_eq_of_lt (show call.slot index < 2 ^ 32 by omega)

-- A word inside an element lies at the element's address plus its offset.
theorem slotOffset (buffer : Buffer codeBytes base original call) {index offset : Nat}
    (bound : index < call.length.toNat) (inside : offset < Element.bytes α) :
    (call.wordSlot index + BitVec.ofNat 32 offset).toNat = call.slot index + offset := by
  have fits := slotFits buffer bound
  rw [BitVec.toNat_add, slotNat buffer bound, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2 ^ 32 by omega)]
  exact Nat.mod_eq_of_lt (show call.slot index + offset < 2 ^ 32 by omega)

-- The loop's pointer reaches the end pointer exactly at the length. The end
-- pointer `call.slot call.length.toNat` may be `2 ^ 32` and wrap to 0, but no
-- earlier slot after the first is 0.
theorem slotReached (buffer : Buffer codeBytes base original call) {index : Nat}
    (positive : 0 < index) (bound : index ≤ call.length.toNat) :
    call.wordSlot index = call.wordSlot call.length.toNat ↔ index = call.length.toNat := by
  refine ⟨fun same => ?_, fun same => by rw [same]⟩
  apply Classical.byContradiction
  intro differs
  have before := call.slotBefore (show index < call.length.toNat by omega)
  have fits := buffer.fits
  have bytes := bytesPositive (α := α)
  have least : Element.bytes α ≤ call.slot index := by
    unfold Call.slot
    have := Nat.le_mul_of_pos_right (Element.bytes α) positive
    omega
  have toNat := congrArg BitVec.toNat same
  simp only [Call.wordSlot, BitVec.toNat_ofNat] at toNat
  rw [Nat.mod_eq_of_lt (show call.slot index < 2 ^ 32 by omega)] at toNat
  by_cases top : call.slot call.length.toNat = 2 ^ 32
  · rw [top, Nat.mod_self] at toNat
    omega
  · rw [Nat.mod_eq_of_lt (show call.slot call.length.toNat < 2 ^ 32 by omega)] at toNat
    omega

end Arithmetic

/-! ## The copy loop

The loop moves elements one slot down, from `call.index + 1` up to the end.
`Progress current memory` holds at the loop head once the elements from
`call.index` below `current` hold their successors. Bytes outside the written
region keep their values.
-/

section Loop

variable {codeBytes : Nat} {base : Word} {original : Machine} {call : Call α}

structure Progress (codeBytes : Nat) (base : Word) (original : Machine) (call : Call α)
    (current : Nat) (memory : ByteMemory) : Prop where
  code : CodeAgreesFor codeBytes base original.mem memory
  data : WordAt memory call.header.toNat call.data
  capacity : WordAt memory (call.header.toNat + 8) call.capacity
  shifted : ∀ index, call.index.toNat ≤ index → index < current →
    Element.At memory (call.slot index) (call.old (index + 1))
  outside : ∀ byte, byte < call.slot call.index.toNat ∨ call.slot current ≤ byte →
    memory[byte]? = original.mem[byte]?

theorem initialProgress (header : Header original call) (buffer : Buffer codeBytes base original call) :
    Progress codeBytes base original call call.index.toNat original.mem :=
  ⟨fun _ _ _ => rfl, buffer.dataWord, header.capacityWord,
    fun _ low high => (Nat.not_lt_of_ge low high).elim, fun _ _ => rfl⟩

-- An element at or after the loop's position still has its original value.
theorem Progress.source {memory : ByteMemory} {current index : Nat}
    (progress : Progress codeBytes base original call current memory)
    (buffer : Buffer codeBytes base original call) (after : current ≤ index)
    (live : index < call.length.toNat) :
    Element.At memory (call.slot index) (call.old index) :=
  Element.atFrame (buffer.live index live) fun byte low _ =>
    progress.outside byte (Or.inr (Nat.le_trans (call.slotMono after) low))

theorem Progress.copy {memory : ByteMemory} {current : Nat}
    (progress : Progress codeBytes base original call current memory)
    (buffer : Buffer codeBytes base original call)
    (afterIndex : call.index.toNat ≤ current) (bound : current + 1 < call.length.toNat) :
    Progress codeBytes base original call (current + 1)
      (Element.store memory (call.slot current) (call.old (current + 1))) := by
  have apart := buffer.separated current bound
  unfold Call.outsideHeader at apart
  have next := call.slotSucc current
  have first := call.slotMono afterIndex
  constructor
  · exact elementKeepsCode progress.code (buffer.awayFromCode _ afterIndex bound) _
  · exact wordStoreElement progress.data (by omega)
  · exact wordStoreElement progress.capacity (by omega)
  · intro observed low high
    by_cases same : observed = current
    · subst observed
      exact Element.atStore memory (call.slot current) (call.old (current + 1))
    · have earlier := call.slotBefore (show observed < current by omega)
      exact elementStoreElement (progress.shifted observed low (by omega)) (Or.inl earlier)
  · intro byte outside
    rw [Element.storeOutside _ _ _ _ (by omega)]
    apply progress.outside
    omega

def finalMemory (call : Call α) (memory : ByteMemory) : ByteMemory :=
  storeWord memory (call.header.toNat + 4) call.newLength

-- After the loop, storing the new length gives the result.
theorem finalWords (buffer : Buffer codeBytes base original call) (memory : ByteMemory)
    (progress : Progress codeBytes base original call (call.length.toNat - 1) memory)
    (valid : call.valid) :
    WordAt (finalMemory call memory) call.header.toNat call.data ∧
    WordAt (finalMemory call memory) (call.header.toNat + 4) call.newLength ∧
    WordAt (finalMemory call memory) (call.header.toNat + 8) call.capacity ∧
    (∀ index, index < call.length.toNat - 1 →
      Element.At (finalMemory call memory) (call.slot index) (call.result index)) ∧
    call.unchanged original.mem (finalMemory call memory) := by
  obtain ⟨indexBound, _⟩ := valid
  refine ⟨progress.data.storeOther (Or.inl (by omega)), wordAtStore _ _ _,
    progress.capacity.storeOther (Or.inr (by omega)), fun index bound => ?_, ?_⟩
  · have apart := buffer.separated index (by omega)
    unfold Call.outsideHeader at apart
    apply elementStoreWord ?_ (by omega)
    by_cases before : index < call.index.toNat
    · rw [Call.result, if_pos before]
      have lower := call.slotBefore before
      exact Element.atFrame (buffer.live index (by omega)) fun byte _ high =>
        progress.outside byte (Or.inl (by omega))
    · rw [Call.result, if_neg before]
      exact progress.shifted index (by omega) bound
  · intro byte outsideLength outsideData
    unfold finalMemory
    rw [storeWordOutside _ _ _ _ (by omega)]
    exact progress.outside byte outsideData

end Loop

end Remove

end Riscfree.RawVec
