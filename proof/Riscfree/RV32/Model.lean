import Riscfree.RV32.Fetch

/-!
# Concrete machine states

Building blocks for exhibiting machines that satisfy a theorem's premises. A
nonvacuity proof uses them to show that the premises can all hold at once.

* `wordMemory` fills the listed byte addresses from a function that gives the
  little-endian word at each word index.
* `wholeSpaceRegion` is one readable, writable, executable PMA region covering
  the 32-bit physical address space.
-/

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

/-! ## Memory -/

-- Byte `address` of a memory whose word at index `index` is `word index`.
def wordByte (word : Nat → BitVec 32) (address : Nat) : BitVec 8 :=
  (word (address / 4)).extractLsb' (8 * (address % 4)) 8

def wordMemory (keys : List Nat) (word : Nat → BitVec 32) : ByteMemory :=
  keys.foldl (fun memory key => memory.insert key (wordByte word key)) ∅

private theorem foldInsert (keys : List Nat) (word : Nat → BitVec 32) (start : ByteMemory)
    (address : Nat) :
    (keys.foldl (fun memory key => memory.insert key (wordByte word key)) start)[address]? =
      if address ∈ keys then some (wordByte word address) else start[address]? := by
  induction keys generalizing start with
  | nil => simp
  | cons key rest previous =>
    rw [List.foldl_cons, previous, Std.ExtHashMap.getElem?_insert]
    by_cases inRest : address ∈ rest
    · simp [inRest]
    · by_cases same : key = address
      · subst same
        simp
      · simp [inRest, same, Ne.symm same]

theorem wordMemoryGet (keys : List Nat) (word : Nat → BitVec 32) (address : Nat) :
    (wordMemory keys word)[address]? =
      if address ∈ keys then some (wordByte word address) else none := by
  simp [wordMemory, foldInsert]

-- A word-aligned address whose four bytes are present holds the word at its index.
theorem wordMemoryWord (keys : List Nat) (word : Nat → BitVec 32) (address : Nat)
    (aligned : address % 4 = 0) (present : ∀ byte < 4, address + byte ∈ keys) :
    WordAt (wordMemory keys word) address (word (address / 4)) := by
  intro byte
  rw [wordMemoryGet, if_pos (present byte.val byte.isLt), wordByte]
  have index : (address + byte.val) / 4 = address / 4 := by have := byte.isLt; omega
  have offset : (address + byte.val) % 4 = byte.val := by have := byte.isLt; omega
  rw [index, offset]

/-! ## Physical memory attributes -/

def wholeSpaceRegion : PMA_Region :=
  { base := 0
    size := 0x100000000
    -- Cacheable, coherent, executable, readable, writable, read- and
    -- write-idempotent; misaligned accesses fault; no reservations; no
    -- `cbo.zero`.
    attributes := ⟨true, true, true, true, true, true, true, .AccessFault, .RsrvNone, false⟩
    include_in_device_tree := false }

theorem wholeSpaceMatches (address : BitVec 32) (width : Nat) (small : width ≤ 4)
    (fits : address.toNat + width ≤ 2 ^ 32) :
    matching_pma [wholeSpaceRegion] (.Physaddr (address.setWidth 34)) width =
      some wholeSpaceRegion := by
  simp [matching_pma, matching_pma_bits_range, range_subset, wholeSpaceRegion, zopz0zIzJ_u,
    bits_of_physaddr, zero_extend, to_bits, BitVec.toNat_add]
  omega

theorem wholeSpaceExecutable (address : BitVec 32) (fits : address.toNat + 2 ≤ 2 ^ 32) :
    ExecutableHalfword [wholeSpaceRegion] address :=
  ⟨_, wholeSpaceMatches address 2 (by decide) fits, rfl⟩

end Riscfree.RV32
