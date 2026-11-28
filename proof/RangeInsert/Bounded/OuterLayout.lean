import RangeInsert.Bounded.EntryFresh
import RangeInsert.Bounded.HelperEntry
import RangeInsert.Theorem

namespace Riscfree.RangeInsert.Bounded.OuterLayout

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable PairAt)
open EntryPredecessor (upperBoundBase upperBoundOffset)
open EntryFresh (mapInsertBase mapInsertOffset)
open Nonempty (Span Call MapStorage ScratchStorage CacheStorage StackSpace mapHeader mapAllocation
  cacheWords scratchAllocation stackAllocation codeSpan stackDisjointOuter mappedTransfer
  WritableByte mapLengthWord stackOffset)

def helperOffset : Word := 0xfffffe20
def helperBase (base : Word) : Word := base + helperOffset

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

theorem InitialLayout.outerFrame {base returnAddress : Word} {original : Machine}
    {initial : Empty.Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high)
    (entry : original = sync base original { initial with pc := 0 })
    (link : initial.ra = returnAddress) (mode : MachineMode original returnAddress) :
    EntryEmpty.Frame base returnAddress original initial := by
  have fits := layout.stack.fits
  refine ⟨entry, link, mode, layout.code.entry, by omega, ?_,
    layout.stack.outerReadable, layout.stack.outerWritable⟩
  intro byte low high
  apply stackDisjointOuter fits
  exact (layout.apart.code _ (List.mem_cons_self ..)).2.2.2.2 byte ⟨low, high⟩

theorem InitialLayout.predecessorMap {base : Word} {original : Machine}
    {initial : Empty.Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high) :
    EntryPredecessor.Map base original initial.sp call := by
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

private theorem mapSlotContained (call : Call) (capacity : Word) {index byte : Nat}
    (inside : index < capacity.toNat) (low : call.search.slot index ≤ byte)
    (high : byte < call.search.slot index + 8) :
    (mapAllocation call capacity).Contains byte := by
  change call.data.toNat + 8 * index ≤ byte at low
  change byte < call.data.toNat + 8 * index + 8 at high
  change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
  omega

theorem MapStorage.insertBuffer {base : Word} {original : Machine} {call : Call} {capacity cache sp : Word}
    {scratch : DeleteExtra.Scratch} (map : MapStorage original call capacity)
    (apart : Separation base sp call capacity cache scratch)
    (spare : call.length.toNat < capacity.toNat) :
    RawVec.PairInsert.Buffer (SortedMap.Insert.vectorBase (mapInsertBase base)) original
      (call.freshInsert capacity).vector := by
  have allocation := map.allocationFits
  have skip := apart.code _ (show codeSpan (SortedMap.Insert.vectorBase (mapInsertBase base))
    RawVec.PairInsert.instructions.length ∈ linkedCode base by simp [linkedCode])
  refine {
    fits := ?_
    dataReadable := (map.searchKeys (key := call.start)).dataReadable
    dataWord := map.dataWord
    lengthWritable := map.lengthWritable
    lengthAwayFromCode := ?_
    live := fun index bound => map.live index bound
    readable := ?_
    writable := ?_
    separated := ?_
    awayFromCode := ?_ }
  · change call.data.toNat + 8 * (call.length.toNat + 1) ≤ 2 ^ 32
    omega
  · apply DeleteExtra.intervalApart (by decide) (by decide)
    intro byte low high code
    apply skip.1 byte code
    change call.header.toNat + 4 ≤ byte at low
    change byte < call.header.toNat + 4 + 4 at high
    change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
    omega
  · intro index _ inside
    change index < call.length.toNat at inside
    exact map.pairsReadable index (by omega)
  · intro index _ inside
    change index ≤ call.length.toNat at inside
    exact map.pairsWritable index (by omega)
  · intro index inside
    change index ≤ call.length.toNat at inside
    change call.search.slot index + 8 ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ call.search.slot index
    exact DeleteExtra.intervalApart (by decide) (by decide) fun byte low high header =>
      apart.headerMap byte header (mapSlotContained call capacity (by omega) low high)
  · intro index _ inside
    change index ≤ call.length.toNat at inside
    apply DeleteExtra.intervalApart (by decide) (by decide)
    intro byte low high code
    exact skip.2.1 byte code (mapSlotContained call capacity (by omega) low high)

private theorem stackTopNat (sp : Word) (fits : 112 ≤ sp.toNat) :
    (Empty.frameBase sp).toNat = sp.toNat - 48 := by
  have zero := Empty.frameAddress (sp := sp) (by omega) 0#32 (by decide)
  simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero

private theorem insertStackOutside (sp : Word) (fits : 112 ≤ sp.toNat) {span : Span}
    (positive : 0 < span.size) (apart : span.Disjoint (stackAllocation sp)) :
    SortedMap.Insert.outsideFrame (Empty.frameBase sp) span.start span.size := by
  have lower := stackTopNat sp fits
  have disjoint := DeleteExtra.intervalApart (first := span.start) (width := span.size)
    (other := (Empty.frameBase sp).toNat - 32) (otherWidth := 32) positive (by decide) (by
      intro byte low high near
      apply apart byte ⟨low, high⟩
      change sp.toNat - 112 ≤ byte ∧ byte < sp.toNat - 112 + 112
      rw [lower] at near
      omega)
  unfold SortedMap.Insert.outsideFrame
  rw [lower] at disjoint ⊢
  omega

private theorem insertStackSlot {sp : Word} {offset : Nat} (member : offset ∈ [12, 16, 20, 24, 28]) :
    ∃ words : Nat, 1 ≤ words ∧ words ≤ 28 ∧
      SortedMap.Insert.frameBase (Empty.frameBase sp) + BitVec.ofNat 32 offset =
        sp - BitVec.ofNat 32 (4 * words) := by
  have address : SortedMap.Insert.frameBase (Empty.frameBase sp) = sp - 80#32 := by
    change sp - 48#32 + 0xffffffe0#32 = sp - 80#32
    rw [show (0xffffffe0#32) = -32#32 by decide, ← BitVec.sub_eq_add_neg, BitVec.sub_sub]
    rfl
  rw [address]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact ⟨17, by decide, by decide, stackOffset sp 80 12 17 (by decide)⟩
  · exact ⟨16, by decide, by decide, stackOffset sp 80 16 16 (by decide)⟩
  · exact ⟨15, by decide, by decide, stackOffset sp 80 20 15 (by decide)⟩
  · exact ⟨14, by decide, by decide, stackOffset sp 80 24 14 (by decide)⟩
  · exact ⟨13, by decide, by decide, stackOffset sp 80 28 13 (by decide)⟩

theorem stackForInsert {base : Word} {original : Machine} {call : Call} {capacity cache sp : Word}
    {scratch : DeleteExtra.Scratch} (stack : StackSpace original sp)
    (apart : Separation base sp call capacity cache scratch)
    (lengthFits : call.length.toNat ≤ capacity.toNat) :
    SortedMap.Insert.Stack (mapInsertBase base) original (call.freshInsert capacity) (Empty.frameBase sp) := by
  have fits := stack.fits
  have outer := stackTopNat sp fits
  have code (address : Word) (count : Nat) (positive : 0 < 4 * count)
      (member : codeSpan address count ∈ linkedCode base) :
      SortedMap.Insert.outsideFrame (Empty.frameBase sp) address.toNat (4 * count) :=
    insertStackOutside sp fits positive (apart.code _ member).2.2.2.2
  have slot (index : Nat) (inside : index < capacity.toNat) :
      SortedMap.Insert.outsideFrame (Empty.frameBase sp) (call.search.slot index) 8 :=
    insertStackOutside sp fits (span := ⟨call.search.slot index, 8⟩) (by change 0 < 8; decide)
      fun byte near => apart.mapStack byte (mapSlotContained call capacity inside near.1 near.2)
  refine {
    fits := by rw [outer]; omega
    readable := ?_
    writable := ?_
    apartHeader := insertStackOutside sp fits (by change 0 < 12; decide) apart.headerStack
    apartEntries := ?_
    apartSpare := fun valid => slot call.length.toNat valid.2
    apartCode := code _ SortedMap.Insert.instructions.length (by decide) (by simp [linkedCode])
    apartSearch := ?_
    apartVector := code _ RawVec.PairInsert.instructions.length (by decide) (by simp [linkedCode]) }
  · intro offset member
    obtain ⟨words, low, high, address⟩ := insertStackSlot (sp := sp) member
    rw [address]
    exact stack.readable words low high
  · intro offset member
    obtain ⟨words, low, high, address⟩ := insertStackSlot (sp := sp) member
    rw [address]
    exact stack.writable words low high
  · intro index inside
    change index < call.length.toNat at inside
    exact slot index (by omega)
  · rw [lowerBoundFromInsert]
    exact code _ (SortedMap.Search.instructions .lower).length (by decide) (by simp [linkedCode])


end Riscfree.RangeInsert.Bounded.OuterLayout
