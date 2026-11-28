import RangeInsert.Bounded.OuterView
import RangeInsert.Bounded.HelperRun
import RangeInsert.Resources

namespace Riscfree.RangeInsert.Bounded.OuterHelper

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable)
open Empty (Snapshot)
open OuterView (helperView helperEntry)
open OuterLayout
open Nonempty (Call Span MapStorage ScratchStorage CacheStorage StackSpace mapHeader mapAllocation cacheWords
  scratchAllocation stackAllocation codeSpan mapLengthWord lengthInHeader stackOffset mappedTransfer)
open Riscfree.RangeInsert (stackGeometry)

set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

def helperAsOuter (call : DeleteExtra.Call) : Call :=
  ⟨call.header, call.length, call.data, call.old, call.start, call.stop⟩

structure HelperInput (base : Word) (entered : Machine) (initial : Snapshot)
    (call : DeleteExtra.Call) (capacity : Word) : Prop where
  layout : InitialLayout base entered initial (helperAsOuter call) capacity call.low call.high
  mapRef : call.mapRef = Empty.frameBase initial.sp + 4#32
  cache : call.cache = initial.a1
  keys : call.keys = Empty.frameBase initial.sp + 8#32
  mapWord : WordAt entered.mem call.mapRef.toNat call.header
  keysData : WordAt entered.mem call.keys.toNat initial.a4
  keysLength : WordAt entered.mem (call.keys.toNat + 4) 0#32
  keysCapacity : WordAt entered.mem (call.keys.toNat + 8) initial.a5
  found : call.position < call.length.toNat

theorem stackDisjointHelper {sp : Word} (fits : 112 ≤ sp.toNat) {byte : Nat}
    (outside : ¬ (stackAllocation sp).Contains byte) :
    DeleteExtra.OutsideFrame (Empty.frameBase sp) byte := by
  change ¬ (sp.toNat - 112 ≤ byte ∧ byte < sp.toNat - 112 + 112) at outside
  unfold DeleteExtra.OutsideFrame
  have outer : (Empty.frameBase sp).toNat = sp.toNat - 48 := by
    have zero := Empty.frameAddress (sp := sp) (by omega) 0#32 (by decide)
    simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero
  rw [outer]
  omega

private theorem refReadable {machine : Machine} {sp : Word} (stack : StackSpace machine sp) :
    Readable machine (Empty.frameBase sp + 4#32) :=
  (congrArg (Readable machine) (stackOffset sp 48#32 4#32 11 (by decide))).mpr
    (stack.readable 11 (by decide) (by decide))

theorem HelperInput.entry {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word}
    (input : HelperInput base entered initial call capacity) :
    HelperEntry.Entry (helperBase base) entered (Empty.frameBase initial.sp) call := by
  have map := input.layout.map
  have cache := input.layout.cache
  have stack := input.layout.stack
  have apart := input.layout.apart
  have headerFits := map.headerFits
  have lengthFits := map.lengthFits
  have fits := stack.fits
  have selected : 0 < call.length.toNat := Nat.zero_lt_of_lt input.found
  refine ⟨input.layout.code.lower, ?_, input.mapRef ▸ refReadable stack, input.mapWord, ?_,
    ⟨?_, map.headerReadable 4 (by decide), map.lengthWord⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, input.found⟩
  · intro byte first last
    apply stackDisjointHelper fits
    have codeApart := apart.code _ (show codeSpan (DeleteExtra.lowerBoundBase (helperBase base))
      (SortedMap.Search.instructions .lower).length ∈ linkedCode base by simp [linkedCode])
    exact codeApart.2.2.2.2 byte ⟨first, by rw [SortedMap.Search.instructionsLength]; exact last⟩
  · intro byte first _
    right
    rw [input.mapRef, Empty.frameAddress (by omega) 4#32 (by decide)] at first
    have outer : (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 := by
      have zero := Empty.frameAddress (sp := initial.sp) (by omega) 0#32 (by decide)
      simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero
    rw [outer]
    change initial.sp.toNat - 48 + 4 ≤ byte at first
    omega
  · change call.header.toNat + 8 ≤ 2 ^ 32
    change call.header.toNat + 12 ≤ 2 ^ 32 at headerFits
    omega
  · have original := input.layout.predecessorMap
    exact original.keys selected
  · intro byte first last
    exact stackDisjointHelper fits (apart.headerStack byte ⟨first, by
      change byte < call.header.toNat + 12
      omega⟩)
  · intro index inside byte first last
    exact stackDisjointHelper fits (apart.mapStack byte (map.entryContained inside first last))
  · rw [input.cache]
    exact cache.fits
  · rw [input.cache]
    exact cache.readable.1
  · rw [input.cache]
    exact cache.readable.2
  · rw [input.cache]
    exact cache.low
  · rw [input.cache]
    exact cache.high
  · intro byte first last
    rw [input.cache] at first last
    exact stackDisjointHelper fits (apart.cacheStack byte ⟨first, last⟩)

private theorem helperSlot {sp offset : Word} (words : Nat)
    (geometry : offset - 96#32 = -BitVec.ofNat 32 (4 * words)) :
    DeleteExtra.frameBase (Empty.frameBase sp) + offset = sp - BitVec.ofNat 32 (4 * words) := by
  change sp - 48#32 - 48#32 + offset = _
  rw [BitVec.sub_sub]
  exact stackOffset sp 96#32 offset words geometry

private theorem helperSlots {sp offset : Word} (member : offset ∈ HelperFrame.savedOffsets) :
    ∃ words : Nat, 1 ≤ words ∧ words ≤ 28 ∧
      DeleteExtra.frameBase (Empty.frameBase sp) + offset = sp - BitVec.ofNat 32 (4 * words) := by
  simp only [HelperFrame.savedOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨13, by decide, by decide, helperSlot 13 (offset := 44#32) (by decide)⟩
  · exact ⟨14, by decide, by decide, helperSlot 14 (offset := 40#32) (by decide)⟩
  · exact ⟨15, by decide, by decide, helperSlot 15 (offset := 36#32) (by decide)⟩
  · exact ⟨16, by decide, by decide, helperSlot 16 (offset := 32#32) (by decide)⟩
  · exact ⟨17, by decide, by decide, helperSlot 17 (offset := 28#32) (by decide)⟩
  · exact ⟨18, by decide, by decide, helperSlot 18 (offset := 24#32) (by decide)⟩
  · exact ⟨19, by decide, by decide, helperSlot 19 (offset := 20#32) (by decide)⟩
  · exact ⟨20, by decide, by decide, helperSlot 20 (offset := 16#32) (by decide)⟩
  · exact ⟨21, by decide, by decide, helperSlot 21 (offset := 12#32) (by decide)⟩
  · exact ⟨22, by decide, by decide, helperSlot 22 (offset := 8#32) (by decide)⟩
  · exact ⟨23, by decide, by decide, helperSlot 23 (offset := 4#32) (by decide)⟩
  · exact ⟨24, by decide, by decide, helperSlot 24 (offset := 0#32) (by decide)⟩

theorem HelperInput.helperFrame {base : Word} {background : Machine}
    {initial caller : Snapshot} {call : DeleteExtra.Call} {capacity : Word}
    (input : HelperInput base (sync base background caller) initial call capacity)
    (machine : MachineState background) {returnOffset : Word} (aligned : returnOffset.toNat % 4 = 0)
    (atHelper : caller.pc = helperOffset) (sp : caller.sp = Empty.frameBase initial.sp)
    (link : caller.ra = base + returnOffset) :
    HelperFrame.Frame (helperBase base) (base + returnOffset) (sync base background caller)
      (helperView caller 0) := by
  have entered := helperEntry (base := base) (helperBase := helperBase base) background caller (by
    rw [atHelper, BitVec.add_zero]
    rfl)
  have alignedAddress := SortedMap.Remove.alignedTargetNat input.layout.code.entry.aligned returnOffset aligned
  obtain ⟨bit0, bit1⟩ := alignedBits _ alignedAddress
  have mode : MachineMode (sync base background caller) (base + returnOffset) :=
    { machine.atSync base caller with
      returnLow := by rw [BitVec.and_comm]; exact maskEven _ bit0
      returnNext := bit1
      ra := by
        have read := syncRead (base := base) (frame := background) caller (index := 1) (by decide)
        change Sail.readReg Register.x1 (sync base background caller) =
          .ok caller.ra (sync base background caller) at read
        rw [link] at read
        exact read }
  have fits := input.layout.stack.fits
  refine ⟨entered, link, mode, input.layout.code.helper, ?_, ?_, ?_, ?_⟩
  · change 48 ≤ caller.sp.toNat
    rw [sp]
    have atBottom := Empty.frameAddress (sp := initial.sp) (by omega) 0#32 (by decide)
    rw [BitVec.add_zero] at atBottom
    change (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 + 0 at atBottom
    rw [atBottom]
    omega
  · intro byte first last
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    apply stackDisjointHelper fits
    have member : codeSpan (helperBase base) DeleteTable.instructions.length ∈ linkedCode base := by
      simp [linkedCode]
    exact (input.layout.apart.code _ member).2.2.2.2 byte ⟨first, last⟩
  · intro offset member
    change Readable (sync base background caller) (DeleteExtra.frameBase caller.sp + offset)
    rw [sp]
    obtain ⟨words, low, high, address⟩ := helperSlots (sp := initial.sp) member
    rw [address]
    exact input.layout.stack.readable words low high
  · intro offset member
    change Writable (sync base background caller) (DeleteExtra.frameBase caller.sp + offset)
    rw [sp]
    obtain ⟨words, low, high, address⟩ := helperSlots (sp := initial.sp) member
    rw [address]
    exact input.layout.stack.writable words low high

private theorem scratchWordContained (scratch : DeleteExtra.Scratch) {index byte : Nat}
    (inside : index < scratch.capacity.toNat)
    (low : scratch.slot index ≤ byte) (high : byte < scratch.slot index + 4) :
    (scratchAllocation scratch).Contains byte := by
  change scratch.data.toNat + 4 * index ≤ byte at low
  change byte < scratch.data.toNat + 4 * index + 4 at high
  change scratch.data.toNat ≤ byte ∧ byte < scratch.data.toNat + 4 * scratch.capacity.toNat
  omega

theorem HelperInput.keysNatural {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity) :
    call.keys.toNat = initial.sp.toNat - 48 + 8 := by
  have fits := input.layout.stack.fits
  rw [input.keys, Empty.frameAddress (by omega) 8#32 (by decide)]
  rfl

theorem HelperInput.keysInStack {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    {byte : Nat} (low : call.keys.toNat ≤ byte) (high : byte < call.keys.toNat + 12) :
    (stackAllocation initial.sp).Contains byte := by
  have fits := input.layout.stack.fits
  rw [input.keysNatural] at low high
  change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
  omega

private theorem scratchIntervalContained (scratch : DeleteExtra.Scratch) {accepted byte : Nat}
    (fits : accepted ≤ scratch.capacity.toNat)
    (inside : scratch.slot 0 ≤ byte ∧ byte < scratch.slot accepted) :
    (scratchAllocation scratch).Contains byte := by
  obtain ⟨low, high⟩ := inside
  change scratch.data.toNat + 4 * 0 ≤ byte at low
  change byte < scratch.data.toNat + 4 * accepted at high
  change scratch.data.toNat ≤ byte ∧ byte < scratch.data.toNat + 4 * scratch.capacity.toNat
  omega

private theorem HelperInput.scanFootprint {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    {accepted byte : Nat} (room : accepted ≤ initial.a5.toNat)
    (touched : DeleteExtra.Footprint call ⟨initial.a4, initial.a5⟩ accepted byte) :
    (cacheWords initial.a1).Contains byte ∨ (stackAllocation initial.sp).Contains byte ∨
      (scratchAllocation ⟨initial.a4, initial.a5⟩).Contains byte := by
  rcases touched with cache | keys | slots
  · rw [input.cache] at cache
    exact Or.inl cache
  · exact Or.inr (Or.inl (input.keysInStack (by omega) (by omega)))
  · exact Or.inr (Or.inr (scratchIntervalContained _ room slots))

private theorem HelperInput.codeApartScan {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    {accepted : Nat} (room : accepted ≤ initial.a5.toNat) {span : Span}
    (linked : span ∈ linkedCode base) (byte : Nat) (atCode : span.Contains byte) :
    ¬ DeleteExtra.Footprint call ⟨initial.a4, initial.a5⟩ accepted byte := by
  intro touched
  have apart := input.layout.apart.code span linked
  rcases input.scanFootprint room touched with cache | stack | scratch
  · exact apart.2.2.1 byte atCode cache
  · exact apart.2.2.2.2 byte atCode stack
  · exact apart.2.2.2.1 byte atCode scratch

private theorem HelperInput.keysAccess {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity) :
    Readable entered call.keys ∧ Readable entered (call.keys + 4#32) ∧
      Readable entered (call.keys + 8#32) ∧ Writable entered (call.keys + 4#32) := by
  have stack := input.layout.stack
  have address8 : call.keys = initial.sp - BitVec.ofNat 32 (4 * 10) :=
    input.keys.trans (stackOffset initial.sp 48#32 8#32 10 (by decide))
  have address12 : call.keys + 4#32 = initial.sp - BitVec.ofNat 32 (4 * 9) := by
    rw [input.keys, BitVec.add_assoc]
    exact stackOffset initial.sp 48#32 12#32 9 (by decide)
  have address16 : call.keys + 8#32 = initial.sp - BitVec.ofNat 32 (4 * 8) := by
    rw [input.keys, BitVec.add_assoc]
    exact stackOffset initial.sp 48#32 16#32 8 (by decide)
  exact ⟨(congrArg (Readable entered) address8).mpr (stack.readable 10 (by decide) (by decide)),
    (congrArg (Readable entered) address12).mpr (stack.readable 9 (by decide) (by decide)),
    (congrArg (Readable entered) address16).mpr (stack.readable 8 (by decide) (by decide)),
    (congrArg (Writable entered) address12).mpr (stack.writable 9 (by decide) (by decide))⟩

theorem HelperInput.scan {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    {accepted : Nat} (room : accepted ≤ initial.a5.toNat) :
    HelperLoop.Layout (helperBase base) entered call ⟨initial.a4, initial.a5⟩ accepted entered.mem := by
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have map := input.layout.map
  have cache := input.layout.cache
  have apart := input.layout.apart
  have keys := input.entry.keys
  have ⟨dataRead, lengthRead, capacityRead, lengthWrite⟩ := input.keysAccess
  refine ⟨input.layout.code.scratchInsert, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, keys.fits,
    keys.readable, ?_, keys.keyWord, ?_, ?_, input.entry.cacheFits, ?_, ?_, ?_,
    dataRead, lengthRead, capacityRead, lengthWrite, ?_, ?_, ?_, ?_, ?_, room⟩
  · intro byte low high
    exact input.codeApartScan room (span := codeSpan (helperBase base) DeleteTable.instructions.length)
      (by simp [linkedCode]) byte ⟨low, high⟩
  · intro byte low high
    exact input.codeApartScan room
      (span := codeSpan (DeleteExtra.rawVecBase (helperBase base)) RawVec.instructions.length)
      (by simp [linkedCode]) byte ⟨low, high⟩
  · intro index inside
    have valid := map.lengthFits
    change call.length.toNat ≤ capacity.toNat at valid
    change index < call.length.toNat at inside
    exact (map.pairsReadable index (by omega)).2
  · exact fun index inside => (map.live index inside).2
  · intro index inside byte low high touched
    have atMap := map.entryContained inside low high
    rcases input.scanFootprint room touched with cache | stack | scratch
    · exact apart.mapCache byte atMap cache
    · exact apart.mapStack byte atMap stack
    · exact apart.mapScratch byte atMap scratch
  · rw [input.cache]; exact cache.writable.1
  · rw [input.cache]; exact cache.writable.2
  · rw [input.keysNatural]
    have bound := initial.sp.isLt
    omega
  · change scratch.slot accepted ≤ 2 ^ 32
    have fits := input.layout.scratch.fits
    change scratch.data.toNat + 4 * scratch.capacity.toNat ≤ 2 ^ 32 at fits
    change scratch.data.toNat + 4 * accepted ≤ 2 ^ 32
    change accepted ≤ scratch.capacity.toNat at room
    omega
  · exact fun index inside => input.layout.scratch.writable index (by change index < initial.a5.toNat; omega)
  · intro index inside
    have within : index < scratch.capacity.toNat := by change index < initial.a5.toNat; omega
    exact DeleteExtra.intervalApart (by decide) (by decide) fun byte low high overlap =>
      apart.scratchStack byte (scratchWordContained scratch within low high)
        (input.keysInStack overlap.1 overlap.2)
  · rw [input.cache]
    exact DeleteExtra.intervalApart (by decide) (by decide) fun byte low high overlap =>
      apart.cacheStack byte ⟨low, high⟩ (input.keysInStack overlap.1 overlap.2)
  · intro index inside
    have within : index < scratch.capacity.toNat := by change index < initial.a5.toNat; omega
    rw [input.cache]
    exact DeleteExtra.intervalApart (by decide) (by decide) fun byte low high overlap =>
      apart.cacheScratch byte overlap (scratchWordContained scratch within low high)

private def drainStack (initial : Snapshot) : Word :=
  DeleteExtra.frameBase (Empty.frameBase initial.sp)

private theorem drainStackNat (initial : Snapshot) (fits : 112 ≤ initial.sp.toNat) :
    (drainStack initial).toNat = initial.sp.toNat - 96 :=
  (stackGeometry initial.sp fits).2.2.1

private theorem drainStackFits (initial : Snapshot) (fits : 112 ≤ initial.sp.toNat) :
    16 ≤ (drainStack initial).toNat := by rw [drainStackNat initial fits]; omega

private theorem drainStackInside (initial : Snapshot) (fits : 112 ≤ initial.sp.toNat) {byte : Nat}
    (low : (drainStack initial).toNat - 16 ≤ byte) (high : byte < (drainStack initial).toNat) :
    (stackAllocation initial.sp).Contains byte := by
  rw [drainStackNat initial fits] at low high
  change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
  omega

private theorem drainSlots {initial : Snapshot} {offset : Nat}
    (member : offset ∈ [0, 4, 8, 12]) :
    ∃ words : Nat, 1 ≤ words ∧ words ≤ 28 ∧
      SortedMap.Remove.frameBase (drainStack initial) + BitVec.ofNat 32 offset =
        initial.sp - BitVec.ofNat 32 (4 * words) := by
  have slot (words : Nat) (geometry : BitVec.ofNat 32 offset - 112#32 = -BitVec.ofNat 32 (4 * words)) :
      SortedMap.Remove.frameBase (drainStack initial) + BitVec.ofNat 32 offset =
        initial.sp - BitVec.ofNat 32 (4 * words) := by
    rw [SortedMap.Remove.frameLowered]
    change initial.sp - 48#32 - 48#32 - 16#32 + BitVec.ofNat 32 offset = _
    rw [BitVec.sub_sub, BitVec.sub_sub]
    exact stackOffset initial.sp 112#32 _ words geometry
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨28, by decide, by decide, slot 28 (by decide)⟩
  · exact ⟨27, by decide, by decide, slot 27 (by decide)⟩
  · exact ⟨26, by decide, by decide, slot 26 (by decide)⟩
  · exact ⟨25, by decide, by decide, slot 25 (by decide)⟩

private theorem outsideDrainStack (initial : Snapshot) (fits : 112 ≤ initial.sp.toNat)
    {start width : Nat} (positive : 0 < width)
    (apart : (⟨start, width⟩ : Span).Disjoint (stackAllocation initial.sp)) :
    SortedMap.Remove.outsideFrame (drainStack initial) start width := by
  have disjoint := DeleteExtra.intervalApart (first := start) (width := width)
    (other := (drainStack initial).toNat - 16) (otherWidth := 16) positive (by decide)
    (fun byte low high overlap => apart byte ⟨low, high⟩
      (drainStackInside initial fits overlap.1 (by have := drainStackFits initial fits; omega)))
  unfold SortedMap.Remove.outsideFrame
  have bound := drainStackFits initial fits
  omega

private theorem HelperInput.drainFootprint {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    {byte : Nat} (touched : DeleteExtra.DrainFootprint (drainStack initial) call.header call.search
      call.position call.length.toNat byte) :
    (stackAllocation initial.sp).Contains byte ∨ (mapHeader (helperAsOuter call)).Contains byte ∨
      (mapAllocation (helperAsOuter call) capacity).Contains byte := by
  rcases touched with nested | header | entries
  · exact Or.inl (drainStackInside initial input.layout.stack.fits nested.1 nested.2)
  · right; left
    change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
    omega
  · right; right
    have cap := input.layout.map.lengthFits
    change call.length.toNat ≤ capacity.toNat at cap
    change call.data.toNat + 8 * (call.position + 1) ≤ byte ∧
      byte < call.data.toNat + 8 * call.length.toNat at entries
    change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
    omega

private theorem helperCodeMember {base : Word} {byte : Nat}
    (atCode : HelperRun.InCode (helperBase base) byte) :
    ∃ span ∈ linkedCode base, span.Contains byte := by
  rcases atCode with own | remove | search | vector
  · exact ⟨codeSpan (helperBase base) DeleteTable.instructions.length, by simp [linkedCode], own⟩
  · exact ⟨codeSpan (DeleteExtra.removeBase (helperBase base)) SortedMap.Remove.instructions.length,
      by simp [linkedCode], remove⟩
  · rw [lowerBoundFromRemove] at search
    exact ⟨codeSpan (DeleteExtra.lowerBoundBase (helperBase base)) (SortedMap.Search.instructions .lower).length,
      by simp [linkedCode], search⟩
  · exact ⟨codeSpan (SortedMap.Remove.vectorBase (DeleteExtra.removeBase (helperBase base)))
      RawVec.PairRemove.instructions.length, by simp [linkedCode], vector⟩

private theorem apartPairHeader {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    (index : Nat) (inside : index < call.length.toNat) :
    call.search.slot index + 8 ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ call.search.slot index :=
  DeleteExtra.intervalApart (by decide) (by decide) fun byte low high header =>
    input.layout.apart.headerMap byte header (input.layout.map.entryContained inside low high)

private theorem slotApartDrainCode {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    (index : Nat) (inside : index < call.length.toNat) :
    RawVec.Insert.outsideCode 100 (SortedMap.Remove.vectorBase (DeleteExtra.removeBase (helperBase base)))
      8 (call.search.slot index) := by
  apply DeleteExtra.intervalApart (by decide) (by decide)
  intro byte low high code
  have member : codeSpan (SortedMap.Remove.vectorBase (DeleteExtra.removeBase (helperBase base)))
      RawVec.PairRemove.instructions.length ∈ linkedCode base := by simp [linkedCode]
  exact (input.layout.apart.code _ member).2.1 byte code (input.layout.map.entryContained inside low high)

theorem HelperInput.removalLayout {base : Word} {entered : Machine} {initial : Snapshot}
    {call : DeleteExtra.Call} {capacity : Word} (input : HelperInput base entered initial call capacity)
    {accepted : Nat} (live : call.position + 1 + accepted ≤ call.length.toNat)
    (room : accepted ≤ initial.a5.toNat)
    (sorted : ∀ first second, first < second → second < call.length.toNat →
      (call.old first).key.toNat < (call.old second).key.toNat) :
    HelperDrain.DrainLayout (helperBase base) entered call capacity (call.after accepted) ⟨initial.a4, initial.a5⟩
      accepted (drainStack initial) entered.mem := by
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have geo := input.layout.stack
  have map := input.layout.map
  have code := input.layout.code
  have apart := input.layout.apart
  have fits := geo.fits
  have lengthFits : call.length.toNat ≤ capacity.toNat := map.lengthFits
  have entriesFit : call.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 := (input.scan room).entriesFit
  have lower : CodeImage (SortedMap.Search.instructions .lower)
      (SortedMap.Remove.searchBase (DeleteExtra.removeBase (helperBase base))) entered := by
    rw [lowerBoundFromRemove]
    exact code.lower
  have codeOutside (address : Word) (count : Nat) (positive : 0 < 4 * count)
      (linked : codeSpan address count ∈ linkedCode base) :
      SortedMap.Remove.outsideFrame (drainStack initial) address.toNat (4 * count) :=
    outsideDrainStack initial fits positive (apart.code _ linked).2.2.2.2
  have capRead : Readable entered (call.header + 8#32) := map.headerReadable 8 (by decide)
  refine {
    removeCode := code.mapRemove
    searchCode := lower
    vectorCode := code.pairRemove
    codeKept := ?_
    stackFits := drainStackFits initial fits
    stackReadable := ?_
    stackWritable := ?_
    stackApartHeader := outsideDrainStack initial fits (by decide) apart.headerStack
    stackApartEntries := ?_
    stackApartCode := codeOutside _ SortedMap.Remove.instructions.length (by decide) (by simp [linkedCode])
    stackApartSearch := ?_
    stackApartVector := codeOutside _ RawVec.PairRemove.instructions.length (by decide) (by simp [linkedCode])
    headerFits := map.headerFits
    dataReadable := input.entry.keys.dataReadable
    lengthReadable := map.headerReadable 4 (by decide)
    capacityReadable := capRead
    lengthWritable := map.lengthWritable
    dataWord := map.dataWord
    capacityWord := map.capacityWord
    headerApartRegion := ?_
    lengthAway := ?_
    entriesFit := entriesFit
    keyReadable := input.entry.keys.readable
    pairReadable := fun index _ inside => map.pairsReadable index (by omega)
    pairWritable := fun index _ inside => map.pairsWritable index (by omega)
    separated := apartPairHeader input
    entriesAway := fun index _ inside => slotApartDrainCode input index (by omega)
    sorted := ?_
    capacityValid := lengthFits
    room := live
    keysFit := (input.scan room).slotsFit
    keyCountFits := by omega
    collectedReadable := fun index inside => input.layout.scratch.readable index (by change index < initial.a5.toNat; omega)
    collectedApart := ?_ }
  · intro byte linked
    refine ⟨rfl, fun touched => ?_⟩
    obtain ⟨span, member, atCode⟩ := helperCodeMember (base := base) linked
    have safe := apart.code span member
    rcases input.drainFootprint touched with stack | header | entries
    · exact safe.2.2.2.2 byte atCode stack
    · exact safe.1 byte atCode header
    · exact safe.2.1 byte atCode entries
  · intro offset member
    obtain ⟨words, low, high, address⟩ := drainSlots (initial := initial) member
    rw [address]
    exact geo.readable words low high
  · intro offset member
    obtain ⟨words, low, high, address⟩ := drainSlots (initial := initial) member
    rw [address]
    exact geo.writable words low high
  · intro index inside
    apply outsideDrainStack initial fits (by decide)
    intro byte inEntry
    exact apart.mapStack byte (map.entryContained inside inEntry.1 inEntry.2)
  · rw [lowerBoundFromRemove]
    exact codeOutside _ (SortedMap.Search.instructions .lower).length (by decide) (by simp [linkedCode])
  · have nonzero := input.found
    change call.header.toNat + 12 ≤ call.data.toNat ∨
      call.data.toNat + 8 * call.length.toNat ≤ call.header.toNat
    apply DeleteExtra.intervalApart (by decide) (by omega)
    intro byte low high near
    apply apart.headerMap byte ⟨low, high⟩
    change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
    omega
  · apply DeleteExtra.intervalApart (by decide) (by decide)
    intro byte low high codeByte
    have member : codeSpan (SortedMap.Remove.vectorBase (DeleteExtra.removeBase (helperBase base)))
        RawVec.PairRemove.instructions.length ∈ linkedCode base := by simp [linkedCode]
    refine (apart.code _ member).1 byte codeByte ?_
    change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
    omega
  · intro first second firstBefore inside
    rw [call.after_key, call.after_key]
    exact sorted first second firstBefore inside
  · intro index inside byte low high touched
    have size : index < scratch.capacity.toNat := by change index < initial.a5.toNat; omega
    have atScratch := scratchWordContained scratch size low high
    rcases input.drainFootprint touched with stack | header | entries
    · exact apart.scratchStack byte atScratch stack
    · exact apart.headerScratch byte header atScratch
    · exact apart.mapScratch byte entries atScratch

/-- Derive the complete deletion-helper premises from its initialized input
and the same layout used by the outer path. -/
theorem HelperInput.scanPremises {base : Word} {background : Machine}
    {initial caller : Snapshot} {call : DeleteExtra.Call} {capacity : Word}
    (input : HelperInput base (sync base background caller) initial call capacity)
    (machine : MachineState background) {returnOffset : Word} (aligned : returnOffset.toNat % 4 = 0)
    (atHelper : caller.pc = helperOffset) (sp : caller.sp = Empty.frameBase initial.sp)
    (link : caller.ra = base + returnOffset) (arguments : HelperEntry.Arguments (helperView caller 0) call)
    {accepted : Nat} (room : accepted ≤ initial.a5.toNat)
    (withinAccepted : accepted ≤ call.acceptCount) :
    HelperRun.ScanPremises (helperBase base) (base + returnOffset) (sync base background caller)
      (helperView caller 0) call ⟨initial.a4, initial.a5⟩ accepted := by
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have fits := input.layout.stack.fits
  have apart := input.layout.apart
  have outside (span : Span) (member : span ∈ linkedCode base) (byte : Nat) (atCode : span.Contains byte) :
      DeleteExtra.OutsideFrame (Empty.frameBase initial.sp) byte :=
    stackDisjointHelper fits ((apart.code _ member).2.2.2.2 byte atCode)
  have inKeysOutside (byte : Nat) (low : call.keys.toNat ≤ byte) :
      DeleteExtra.OutsideFrame (Empty.frameBase initial.sp) byte := by
    right
    rw [input.keysNatural] at low
    have address : (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 := by
      have known := Empty.frameAddress (sp := initial.sp) (by omega) 0#32 (by decide)
      simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using known
    rw [address]
    omega
  refine {
    frame := input.helperFrame machine aligned atHelper sp link
    arguments := arguments
    entry := ?_
    scan := input.scan room
    accepts := fun index within => call.accepted index (Nat.lt_of_lt_of_le within withinAccepted)
    keysData := input.keysData
    keysLength := input.keysLength
    keysCapacity := input.keysCapacity
    rawOutside := ?_
    keysOutside := ?_
    slotsOutside := ?_ }
  · change HelperEntry.Entry (helperBase base) (sync base background caller) caller.sp call
    rw [sp]
    exact input.entry
  · intro byte first last
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact outside (codeSpan (DeleteExtra.rawVecBase (helperBase base)) RawVec.instructions.length)
      (by simp [linkedCode]) byte ⟨first, last⟩
  · intro byte low _
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact inKeysOutside byte low
  · intro byte low high
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact stackDisjointHelper fits (apart.scratchStack byte (scratchIntervalContained scratch room ⟨low, high⟩))

theorem HelperInput.premises {base : Word} {background : Machine}
    {initial caller : Snapshot} {call : DeleteExtra.Call} {capacity : Word}
    (input : HelperInput base (sync base background caller) initial call capacity)
    (machine : MachineState background) {returnOffset : Word} (aligned : returnOffset.toNat % 4 = 0)
    (atHelper : caller.pc = helperOffset) (sp : caller.sp = Empty.frameBase initial.sp)
    (link : caller.ra = base + returnOffset) (arguments : HelperEntry.Arguments (helperView caller 0) call)
    (room : call.acceptCount ≤ initial.a5.toNat)
    (sorted : ∀ first second, first < second → second < call.length.toNat →
      (call.old first).key.toNat < (call.old second).key.toNat) :
    HelperRun.Premises (helperBase base) (base + returnOffset) (sync base background caller)
      (helperView caller 0) call ⟨initial.a4, initial.a5⟩ call.acceptCount capacity := by
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have map := input.layout.map
  have capacityFits : call.length.toNat ≤ capacity.toNat := map.lengthFits
  have fits := input.layout.stack.fits
  have apart := input.layout.apart
  have live : call.position + 1 + call.acceptCount ≤ call.length.toNat := by
    rcases call.stops input.found with exactEnd | ⟨beforeEnd, _⟩ <;> omega
  have endContained (byte : Nat) (atEnd : DeleteExtra.InEnd call byte) :
      (mapAllocation (helperAsOuter call) capacity).Contains byte := by
    have low : call.search.slot call.position ≤ byte := Nat.le_trans (Nat.le_add_right _ _) atEnd.1
    exact map.entryContained input.found low atEnd.2
  have outside (span : Span) (member : span ∈ linkedCode base) (byte : Nat) (atCode : span.Contains byte) :
      DeleteExtra.OutsideFrame (Empty.frameBase initial.sp) byte :=
    stackDisjointHelper fits ((apart.code _ member).2.2.2.2 byte atCode)
  have inKeysOutside (byte : Nat) (low : call.keys.toNat ≤ byte) :
      DeleteExtra.OutsideFrame (Empty.frameBase initial.sp) byte := by
    right
    rw [input.keysNatural] at low
    have address : (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 := by
      have known := Empty.frameAddress (sp := initial.sp) (by omega) 0#32 (by decide)
      simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using known
    rw [address]
    omega
  refine {
    frame := input.helperFrame machine aligned atHelper sp link
    arguments := arguments
    entry := ?_
    scan := input.scan room
    drain := ?_
    accepts := call.accepted
    stops := call.stops input.found
    keysData := input.keysData
    keysLength := input.keysLength
    keysCapacity := input.keysCapacity
    endWritable := (map.pairsWritable call.position (by have := input.found; omega)).2
    rawOutside := ?_
    codeOutside := ?_
    keysOutside := ?_
    slotsOutside := ?_
    headerOutside := ?_
    endOutside := ?_
    codeApartScan := ?_
    headerApartScan := ?_
    endApart := ?_
    keysApartDrain := ?_
    cacheApartDrain := ?_ }
  · change HelperEntry.Entry (helperBase base) (sync base background caller) caller.sp call
    rw [sp]
    exact input.entry
  · intro byte first last
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact outside (codeSpan (DeleteExtra.rawVecBase (helperBase base)) RawVec.instructions.length)
      (by simp [linkedCode]) byte ⟨first, last⟩
  · intro byte low _
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact inKeysOutside byte low
  · intro byte low high
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact stackDisjointHelper fits (apart.scratchStack byte (scratchIntervalContained scratch room ⟨low, high⟩))
  · change HelperDrain.DrainLayout _ _ _ _ _ _ _ (DeleteExtra.frameBase caller.sp) _
    rw [sp]
    exact input.removalLayout live room sorted
  · intro byte atCode
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    obtain ⟨span, member, inside⟩ := helperCodeMember (base := base) atCode
    exact outside span member byte inside
  · intro byte low high
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact stackDisjointHelper fits (apart.headerStack byte ⟨low, high⟩)
  · intro byte atEnd
    change DeleteExtra.OutsideFrame caller.sp byte
    rw [sp]
    exact stackDisjointHelper fits (apart.mapStack byte (endContained byte atEnd))
  · intro byte atCode
    obtain ⟨span, member, inside⟩ := helperCodeMember (base := base) atCode
    exact input.codeApartScan room member byte inside
  · intro byte low high touched
    have inHeader : (mapHeader (helperAsOuter call)).Contains byte := ⟨low, high⟩
    rcases input.scanFootprint room touched with cache | stack | scratchByte
    · exact apart.headerCache byte inHeader cache
    · exact apart.headerStack byte inHeader stack
    · exact apart.headerScratch byte inHeader scratchByte
  · intro byte atEnd
    have atMap := endContained byte atEnd
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro touched
      rcases input.scanFootprint room touched with cache | stack | scratchByte
      · exact apart.mapCache byte atMap cache
      · exact apart.mapStack byte atMap stack
      · exact apart.mapScratch byte atMap scratchByte
    · intro atCode
      obtain ⟨span, member, inside⟩ := helperCodeMember (base := base) atCode
      exact (apart.code _ member).2.1 byte inside atMap
    · exact fun keys => apart.mapStack byte atMap (input.keysInStack keys.1 keys.2)
    · exact fun header => apart.headerMap byte header atMap
  · intro byte low high
    change ¬ DeleteExtra.DrainFootprint (DeleteExtra.frameBase caller.sp) call.header call.search
      call.position call.length.toNat byte
    rw [sp]
    intro touched
    have stack := input.keysInStack low high
    rcases touched with nested | header | entries
    · have address := drainStackNat initial fits
      have below : byte < (drainStack initial).toNat := nested.2
      rw [address] at below
      rw [input.keysNatural] at low
      omega
    · apply apart.headerStack byte _ stack
      change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
      omega
    · apply apart.mapStack byte _ stack
      change call.data.toNat + 8 * (call.position + 1) ≤ byte ∧
        byte < call.data.toNat + 8 * call.length.toNat at entries
      change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
      omega
  · intro byte low high
    change ¬ DeleteExtra.DrainFootprint (DeleteExtra.frameBase caller.sp) call.header call.search
      call.position call.length.toNat byte
    rw [sp]
    intro touched
    rw [input.cache] at low high
    have atCache : (cacheWords initial.a1).Contains byte := ⟨low, high⟩
    rcases input.drainFootprint touched with stack | header | entries
    · exact apart.cacheStack byte atCache stack
    · exact apart.headerCache byte header atCache
    · exact apart.mapCache byte entries atCache

/-- The helper writes below the caller's saved registers, or to the
cache, scratch allocation, and map. -/
theorem HelperInput.footprintRegions {base : Word} {entered : Machine}
    {initial : Snapshot} {call : DeleteExtra.Call} {capacity : Word}
    (input : HelperInput base entered initial call capacity) {accepted byte : Nat}
    (room : accepted ≤ initial.a5.toNat)
    (touched : DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) call ⟨initial.a4, initial.a5⟩ accepted byte) :
    (initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 28) ∨
      (cacheWords initial.a1).Contains byte ∨ (scratchAllocation ⟨initial.a4, initial.a5⟩).Contains byte ∨
      (mapLengthWord (helperAsOuter call)).Contains byte ∨
        (mapAllocation (helperAsOuter call) capacity).Contains byte := by
  have fits := input.layout.stack.fits
  have geometry := stackGeometry initial.sp fits
  have outer : (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 := geometry.1
  have helper : (DeleteExtra.frameBase (Empty.frameBase initial.sp)).toNat =
      initial.sp.toNat - 96 := geometry.2.2.1
  have keys : call.keys.toNat = initial.sp.toNat - 48 + 8 := by
    rw [input.keys, Empty.frameAddress (by omega) 8#32 (by decide)]
    rfl
  have capacityFits : call.length.toNat ≤ capacity.toNat := input.layout.map.lengthFits
  rcases touched with helperStack | scan | endpoint | drain
  · left
    unfold DeleteExtra.OutsideFrame at helperStack
    rw [outer] at helperStack
    omega
  · rcases scan with cache | header | slots
    · rw [input.cache] at cache
      exact Or.inr (Or.inl cache)
    · left
      rw [keys] at header
      omega
    · right; right; left
      change initial.a4.toNat + 4 * 0 ≤ byte ∧ byte < initial.a4.toNat + 4 * accepted at slots
      change initial.a4.toNat ≤ byte ∧ byte < initial.a4.toNat + 4 * initial.a5.toNat
      omega
  · right; right; right; right
    exact input.layout.map.entryContained input.found
      (Nat.le_trans (Nat.le_add_right _ _) endpoint.1) endpoint.2
  · rcases drain with nested | header | slots
    · left
      rw [helper] at nested
      omega
    · right; right; right; left
      change call.header.toNat + 4 ≤ byte ∧ byte < call.header.toNat + 4 + 4
      omega
    · right; right; right; right
      change call.data.toNat + 8 * (call.position + 1) ≤ byte ∧
        byte < call.data.toNat + 8 * call.length.toNat at slots
      change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
      omega

theorem HelperInput.codeApartAll {base : Word} {entered : Machine}
    {initial : Snapshot} {call : DeleteExtra.Call} {capacity : Word}
    (input : HelperInput base entered initial call capacity) {accepted : Nat}
    (room : accepted ≤ initial.a5.toNat) (byte : Nat)
    (first : base.toNat ≤ byte) (last : byte < base.toNat + 4 * InsertTable.instructions.length) :
    ¬ DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) call ⟨initial.a4, initial.a5⟩ accepted byte := by
  intro touched
  have code := input.layout.apart.code _ (List.mem_cons_self ..)
  have atCode : (codeSpan base InsertTable.instructions.length).Contains byte := ⟨first, last⟩
  rcases input.footprintRegions room touched with stack | cache | scratch | header | map
  · apply code.2.2.2.2 byte atCode
    change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
    have fits := input.layout.stack.fits
    omega
  · exact code.2.2.1 byte atCode cache
  · exact code.2.2.2.1 byte atCode scratch
  · exact code.1 byte atCode (lengthInHeader header)
  · exact code.2.1 byte atCode map

theorem HelperInput.savedApartAll {base : Word} {entered : Machine}
    {initial : Snapshot} {call : DeleteExtra.Call} {capacity : Word}
    (input : HelperInput base entered initial call capacity) {accepted : Nat}
    (room : accepted ≤ initial.a5.toNat) (byte : Nat)
    (first : initial.sp.toNat - 28 ≤ byte) (last : byte < initial.sp.toNat) :
    ¬ DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) call ⟨initial.a4, initial.a5⟩ accepted byte := by
  intro touched
  have atStack : (stackAllocation initial.sp).Contains byte := by
    change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
    have fits := input.layout.stack.fits
    omega
  have apart := input.layout.apart
  rcases input.footprintRegions room touched with stack | cache | scratch | header | map
  · omega
  · exact apart.cacheStack byte cache atStack
  · exact apart.scratchStack byte scratch atStack
  · exact apart.headerStack byte (lengthInHeader header) atStack
  · exact apart.mapStack byte map atStack

end Riscfree.RangeInsert.Bounded.OuterHelper
