import RangeInsert.Nonempty.Fresh.Setup
import SortedMap.Insert

/-! The initial memory layout used by both modifying paths. Initialized
words and access permissions are separate, so a spare map slot or a
scratch slot does not have to hold a value at entry. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable PairAt)

structure Span where
  start : Nat
  size : Nat

namespace Span

def Contains (span : Span) (byte : Nat) : Prop :=
  span.start ≤ byte ∧ byte < span.start + span.size

def Disjoint (left right : Span) : Prop :=
  ∀ byte, left.Contains byte → ¬ right.Contains byte

theorem Disjoint.symm {left right : Span} (apart : left.Disjoint right) : right.Disjoint left :=
  fun byte inRight inLeft => apart byte inLeft inRight

end Span

def mapHeader (call : Call) : Span := ⟨call.header.toNat, 12⟩
def mapAllocation (call : Call) (capacity : Word) : Span := ⟨call.data.toNat, 8 * capacity.toNat⟩
def cacheWords (address : Word) : Span := ⟨address.toNat, 8⟩
def scratchAllocation (scratch : DeleteExtra.Scratch) : Span :=
  ⟨scratch.data.toNat, 4 * scratch.capacity.toNat⟩
def stackAllocation (sp : Word) : Span := ⟨sp.toNat - 112, 112⟩
def codeSpan (base : Word) (instructionCount : Nat) : Span := ⟨base.toNat, 4 * instructionCount⟩

/-- The only map header word the routine writes: the length at offset 4.
The data pointer at offset 0 and the capacity at offset 8 are not writable. -/
def mapLengthWord (call : Call) : Span := ⟨call.header.toNat + 4, 4⟩

theorem lengthInHeader {call : Call} {byte : Nat} (inside : (mapLengthWord call).Contains byte) :
    (mapHeader call).Contains byte := by
  change call.header.toNat + 4 ≤ byte ∧ byte < call.header.toNat + 4 + 4 at inside
  change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
  omega

/-- The bytes the routine may write. Of the map header, only the length
word is included, so the data pointer and capacity words are preserved. -/
def WritableByte (initial : Empty.Snapshot) (call : Call) (capacity : Word) (byte : Nat) : Prop :=
  (stackAllocation initial.sp).Contains byte ∨ (cacheWords initial.a1).Contains byte ∨
    (scratchAllocation ⟨initial.a4, initial.a5⟩).Contains byte ∨
    (mapLengthWord call).Contains byte ∨ (mapAllocation call capacity).Contains byte

def helperBase (base : Word) : Word := base + extensionHelperOffset
def mapInsertBase (base : Word) : Word := base + insertOffset

/-- The decoded code images at the actual linked offsets. The lower-bound
routine is shared by the helper, sorted insertion, and sorted removal. -/
structure CodeImages (base : Word) (original : Machine) : Prop where
  entry : CodeImage InsertTable.instructions base original
  helper : CodeImage DeleteTable.instructions (helperBase base) original
  upper : CodeImage (SortedMap.Search.instructions .upper) (upperBoundBase base) original
  lower : CodeImage (SortedMap.Search.instructions .lower) (DeleteExtra.lowerBoundBase (helperBase base)) original
  mapInsert : CodeImage SortedMap.Insert.instructions (mapInsertBase base) original
  mapRemove : CodeImage SortedMap.Remove.instructions (DeleteExtra.removeBase (helperBase base)) original
  scratchInsert : CodeImage RawVec.instructions (DeleteExtra.rawVecBase (helperBase base)) original
  pairInsert : CodeImage RawVec.PairInsert.instructions (SortedMap.Insert.vectorBase (mapInsertBase base)) original
  pairRemove : CodeImage RawVec.PairRemove.instructions
    (SortedMap.Remove.vectorBase (DeleteExtra.removeBase (helperBase base))) original

def linkedCode (base : Word) : List Span :=
  [codeSpan base InsertTable.instructions.length,
    codeSpan (helperBase base) DeleteTable.instructions.length,
    codeSpan (upperBoundBase base) (SortedMap.Search.instructions .upper).length,
    codeSpan (DeleteExtra.lowerBoundBase (helperBase base)) (SortedMap.Search.instructions .lower).length,
    codeSpan (mapInsertBase base) SortedMap.Insert.instructions.length,
    codeSpan (DeleteExtra.removeBase (helperBase base)) SortedMap.Remove.instructions.length,
    codeSpan (DeleteExtra.rawVecBase (helperBase base)) RawVec.instructions.length,
    codeSpan (SortedMap.Insert.vectorBase (mapInsertBase base)) RawVec.PairInsert.instructions.length,
    codeSpan (SortedMap.Remove.vectorBase (DeleteExtra.removeBase (helperBase base)))
      RawVec.PairRemove.instructions.length]

/-- The map's initialized prefix and capacity, including access to a spare
slot during fresh insertion. -/
structure MapStorage (original : Machine) (call : Call) (capacity : Word) : Prop where
  headerFits : call.header.toNat + 12 ≤ 2 ^ 32
  allocationFits : call.data.toNat + 8 * capacity.toNat ≤ 2 ^ 32
  dataNonnull : 0 < call.data.toNat
  lengthFits : call.length.toNat ≤ capacity.toNat
  headerReadable : ∀ offset ∈ ([0, 4, 8] : List Word), Readable original (call.header + offset)
  lengthWritable : Writable original (call.header + 4#32)
  dataWord : WordAt original.mem call.header.toNat call.data
  lengthWord : WordAt original.mem (call.header.toNat + 4) call.length
  capacityWord : WordAt original.mem (call.header.toNat + 8) capacity
  live : ∀ index < call.length.toNat, PairAt original.mem (call.search.slot index) (call.old index)
  pairsReadable : ∀ index < capacity.toNat,
    Readable original (call.search.wordSlot index) ∧ Readable original (call.search.wordSlot index + 4#32)
  pairsWritable : ∀ index < capacity.toNat,
    Writable original (call.search.wordSlot index) ∧ Writable original (call.search.wordSlot index + 4#32)

/-- Deletion scratch can be uninitialized at entry. -/
structure ScratchStorage (original : Machine) (scratch : DeleteExtra.Scratch) : Prop where
  fits : scratch.slot scratch.capacity.toNat ≤ 2 ^ 32
  readable : ∀ index < scratch.capacity.toNat, Readable original (scratch.wordSlot index)
  writable : ∀ index < scratch.capacity.toNat, Writable original (scratch.wordSlot index)

/-- The two words of the cached cardinality. -/
structure CacheStorage (original : Machine) (address low high : Word) : Prop where
  fits : address.toNat + 8 ≤ 2 ^ 32
  readable : Readable original address ∧ Readable original (address + 4#32)
  writable : Writable original address ∧ Writable original (address + 4#32)
  low : WordAt original.mem address.toNat low
  high : WordAt original.mem (address.toNat + 4) high

/-- The 112-byte stack region covers the deepest uncompressed call chain. -/
structure StackSpace (original : Machine) (sp : Word) : Prop where
  fits : 112 ≤ sp.toNat
  readable : ∀ words : Nat, 1 ≤ words → words ≤ 28 →
    Readable original (sp - BitVec.ofNat 32 (4 * words))
  writable : ∀ words : Nat, 1 ≤ words → words ≤ 28 →
    Writable original (sp - BitVec.ofNat 32 (4 * words))

/-- Every writable region is disjoint from each other region and all code. -/
structure Separation (base : Word) (sp : Word) (call : Call) (capacity cache : Word)
    (scratch : DeleteExtra.Scratch) : Prop where
  headerMap : (mapHeader call).Disjoint (mapAllocation call capacity)
  headerCache : (mapHeader call).Disjoint (cacheWords cache)
  headerScratch : (mapHeader call).Disjoint (scratchAllocation scratch)
  headerStack : (mapHeader call).Disjoint (stackAllocation sp)
  mapCache : (mapAllocation call capacity).Disjoint (cacheWords cache)
  mapScratch : (mapAllocation call capacity).Disjoint (scratchAllocation scratch)
  mapStack : (mapAllocation call capacity).Disjoint (stackAllocation sp)
  cacheScratch : (cacheWords cache).Disjoint (scratchAllocation scratch)
  cacheStack : (cacheWords cache).Disjoint (stackAllocation sp)
  scratchStack : (scratchAllocation scratch).Disjoint (stackAllocation sp)
  code : ∀ span ∈ linkedCode base,
    span.Disjoint (mapHeader call) ∧ span.Disjoint (mapAllocation call capacity) ∧
      span.Disjoint (cacheWords cache) ∧ span.Disjoint (scratchAllocation scratch) ∧
      span.Disjoint (stackAllocation sp)

/-- The caller's initial storage and the linked code shared by extension
and fresh insertion. Transient capacity depends on the chosen path. -/
structure InitialLayout (base : Word) (original : Machine) (initial : Empty.Snapshot)
    (call : Call) (capacity low high : Word) : Prop where
  code : CodeImages base original
  map : MapStorage original call capacity
  scratch : ScratchStorage original ⟨initial.a4, initial.a5⟩
  cache : CacheStorage original initial.a1 low high
  stack : StackSpace original initial.sp
  apart : Separation base initial.sp call capacity initial.a1 ⟨initial.a4, initial.a5⟩

/-- The three callers of the lower bound resolve to the same linked image. -/
theorem lowerBoundFromRemove (base : Word) :
    SortedMap.Remove.searchBase (DeleteExtra.removeBase (helperBase base)) =
      DeleteExtra.lowerBoundBase (helperBase base) := by
  unfold SortedMap.Remove.searchBase DeleteExtra.removeBase DeleteExtra.lowerBoundBase
  rw [BitVec.add_assoc]
  rfl

theorem lowerBoundFromInsert (base : Word) :
    SortedMap.Insert.searchBase (mapInsertBase base) = DeleteExtra.lowerBoundBase (helperBase base) := by
  unfold SortedMap.Insert.searchBase mapInsertBase DeleteExtra.lowerBoundBase helperBase
  rw [BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem stackDisjointOuter {sp : Word} (fits : 112 ≤ sp.toNat) {byte : Nat}
    (outside : ¬ (stackAllocation sp).Contains byte) : Empty.OutsideFrame sp byte := by
  change ¬ (sp.toNat - 112 ≤ byte ∧ byte < sp.toNat - 112 + 112) at outside
  unfold Empty.OutsideFrame
  omega

theorem stackOffset (sp : Word) (frame offset : Word) (words : Nat)
    (geometry : offset - frame = -BitVec.ofNat 32 (4 * words)) :
    sp - frame + offset = sp - BitVec.ofNat 32 (4 * words) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-frame) offset,
    ← BitVec.sub_eq_add_neg, geometry, ← BitVec.sub_eq_add_neg]

theorem StackSpace.outerReadable {original : Machine} {sp : Word} (stack : StackSpace original sp)
    (offset : Word) (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word)) :
    Readable original (Empty.frameBase sp + offset) := by
  change Readable original (sp - 48#32 + offset)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (congrArg (Readable original) (stackOffset sp 48#32 44#32 1 (by decide))).mpr
      (stack.readable 1 (by decide) (by decide))
  · exact (congrArg (Readable original) (stackOffset sp 48#32 40#32 2 (by decide))).mpr
      (stack.readable 2 (by decide) (by decide))
  · exact (congrArg (Readable original) (stackOffset sp 48#32 36#32 3 (by decide))).mpr
      (stack.readable 3 (by decide) (by decide))
  · exact (congrArg (Readable original) (stackOffset sp 48#32 32#32 4 (by decide))).mpr
      (stack.readable 4 (by decide) (by decide))
  · exact (congrArg (Readable original) (stackOffset sp 48#32 28#32 5 (by decide))).mpr
      (stack.readable 5 (by decide) (by decide))
  · exact (congrArg (Readable original) (stackOffset sp 48#32 24#32 6 (by decide))).mpr
      (stack.readable 6 (by decide) (by decide))
  · exact (congrArg (Readable original) (stackOffset sp 48#32 20#32 7 (by decide))).mpr
      (stack.readable 7 (by decide) (by decide))

theorem StackSpace.outerWritable {original : Machine} {sp : Word} (stack : StackSpace original sp)
    (offset : Word) (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20, 4] : List Word)) :
    Writable original (Empty.frameBase sp + offset) := by
  change Writable original (sp - 48#32 + offset)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (congrArg (Writable original) (stackOffset sp 48#32 44#32 1 (by decide))).mpr
      (stack.writable 1 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 40#32 2 (by decide))).mpr
      (stack.writable 2 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 36#32 3 (by decide))).mpr
      (stack.writable 3 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 32#32 4 (by decide))).mpr
      (stack.writable 4 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 28#32 5 (by decide))).mpr
      (stack.writable 5 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 24#32 6 (by decide))).mpr
      (stack.writable 6 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 20#32 7 (by decide))).mpr
      (stack.writable 7 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 4#32 11 (by decide))).mpr
      (stack.writable 11 (by decide) (by decide))

theorem StackSpace.scratchWritable {original : Machine} {sp : Word} (stack : StackSpace original sp)
    (offset : Word) (member : offset ∈ ([8, 12, 16] : List Word)) :
    Writable original (Empty.frameBase sp + offset) := by
  change Writable original (sp - 48#32 + offset)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (congrArg (Writable original) (stackOffset sp 48#32 8#32 10 (by decide))).mpr
      (stack.writable 10 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 12#32 9 (by decide))).mpr
      (stack.writable 9 (by decide) (by decide))
  · exact (congrArg (Writable original) (stackOffset sp 48#32 16#32 8 (by decide))).mpr
      (stack.writable 8 (by decide) (by decide))

theorem MapStorage.entryContained {original : Machine} {call : Call} {capacity : Word}
    (map : MapStorage original call capacity) {index byte : Nat} (inside : index < call.length.toNat)
    (low : call.search.slot index ≤ byte) (high : byte < call.search.slot index + 8) :
    (mapAllocation call capacity).Contains byte := by
  have fits := map.lengthFits
  change call.data.toNat + 8 * index ≤ byte at low
  change byte < call.data.toNat + 8 * index + 8 at high
  change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
  omega

theorem InitialLayout.outerFrame {base returnAddress : Word} {original : Machine}
    {initial : Empty.Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high)
    (entry : original = sync base original { initial with pc := 0 })
    (link : initial.ra = returnAddress) (mode : MachineMode original returnAddress) :
    Empty.Frame base returnAddress original initial := by
  have fits := layout.stack.fits
  refine ⟨entry, link, mode, layout.code.entry, by omega, ?_,
    layout.stack.outerReadable, layout.stack.outerWritable⟩
  intro byte low high
  apply stackDisjointOuter fits
  exact (layout.apart.code _ (List.mem_cons_self ..)).2.2.2.2 byte ⟨low, high⟩

theorem InitialLayout.predecessorMap {base : Word} {original : Machine}
    {initial : Empty.Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high) :
    Map base original initial.sp call := by
  have map := layout.map
  have lengthFits := map.lengthFits
  have headerFits := map.headerFits
  refine ⟨layout.code.upper, ?_, ⟨by change call.header.toNat + 8 ≤ 2 ^ 32; omega,
    map.headerReadable 4 (by decide), map.lengthWord⟩, ?_, ?_, ?_, ?_, ?_, map.dataNonnull⟩
  · intro byte low high
    apply stackDisjointOuter layout.stack.fits
    have member : codeSpan (upperBoundBase base) (SortedMap.Search.instructions .upper).length ∈
        linkedCode base := by
      unfold linkedCode
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact (layout.apart.code _ member).2.2.2.2 byte ⟨low, by
      rw [SortedMap.Search.instructionsLength]; exact high⟩
  · intro _
    refine ⟨?_, ?_, map.dataWord, ?_, fun index inside => (map.live index inside).1⟩
    · have allocation := map.allocationFits
      change call.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32
      omega
    · change Readable original call.header
      have dataReadable : Readable original (call.header + 0#32) := map.headerReadable 0#32 (by decide)
      rw [BitVec.add_zero] at dataReadable
      exact dataReadable
    · intro index inside
      change index < call.length.toNat at inside
      exact (map.pairsReadable index (by omega)).1
  · intro byte low high
    exact stackDisjointOuter layout.stack.fits (layout.apart.headerStack byte ⟨low, by
      change byte < call.header.toNat + 12; omega⟩)
  · intro index inside byte low high
    exact stackDisjointOuter layout.stack.fits
      (layout.apart.mapStack byte (map.entryContained inside low high))
  · intro index inside
    exact (map.pairsReadable index (by omega)).2
  · exact fun index inside => (map.live index inside).2

/-- Preserve all linked images when a caller changes data and stack words. -/
theorem CodeImages.withMemory {base : Word} {original : Machine}
    (images : CodeImages base original) (memory : ByteMemory)
    (kept : ∀ span ∈ linkedCode base, ∀ byte, span.Contains byte →
      memory[byte]? = original.mem[byte]?) :
    CodeImages base { original with mem := memory } := by
  have preserve {table : List (Word × instruction)} {address : Word}
      (image : CodeImage table address original) (member : codeSpan address table.length ∈ linkedCode base) :
      CodeImage table address { original with mem := memory } :=
    image.withMemory memory fun byte low high => kept _ member byte ⟨low, high⟩
  exact ⟨preserve images.entry (by simp [linkedCode]),
    preserve images.helper (by simp [linkedCode]), preserve images.upper (by simp [linkedCode]),
    preserve images.lower (by simp [linkedCode]), preserve images.mapInsert (by simp [linkedCode]),
    preserve images.mapRemove (by simp [linkedCode]), preserve images.scratchInsert (by simp [linkedCode]),
    preserve images.pairInsert (by simp [linkedCode]), preserve images.pairRemove (by simp [linkedCode])⟩

theorem CodeImages.atSync {base callerBase : Word} {original : Machine}
    (images : CodeImages base original) (state : Empty.Snapshot) :
    CodeImages base (sync callerBase original state) :=
  ⟨images.entry.atSync callerBase state, images.helper.atSync callerBase state,
    images.upper.atSync callerBase state, images.lower.atSync callerBase state,
    images.mapInsert.atSync callerBase state, images.mapRemove.atSync callerBase state,
    images.scratchInsert.atSync callerBase state, images.pairInsert.atSync callerBase state,
    images.pairRemove.atSync callerBase state⟩

theorem StackSpace.transfer {original other : Machine} {sp : Word}
    (stack : StackSpace original sp)
    (regions : other.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions) :
    StackSpace other sp :=
  ⟨stack.fits, fun words low high => mappedTransfer (stack.readable words low high) regions,
    fun words low high => mappedTransfer (stack.writable words low high) regions⟩

theorem ScratchStorage.transfer {original other : Machine} {scratch : DeleteExtra.Scratch}
    (storage : ScratchStorage original scratch)
    (regions : other.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions) :
    ScratchStorage other scratch :=
  ⟨storage.fits, fun index inside => mappedTransfer (storage.readable index inside) regions,
    fun index inside => mappedTransfer (storage.writable index inside) regions⟩

end Riscfree.RangeInsert.Nonempty
