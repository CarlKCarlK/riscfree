import RangeInsert.Nonempty.Fresh.Prefix
import RangeInsert.Nonempty.Correspondence

/-! The sorted-map insertion must use its fresh-slot path on either fresh
range branch. Its spare slot is used before the deletion helper runs. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Pair Readable Writable)

def Call.freshInsert (call : Call) (capacity : Word) : SortedMap.Insert.Call :=
  ⟨call.header, ⟨call.start, call.stop⟩, call.length, capacity, call.data, call.old⟩

theorem Call.keysIncreasing {call : Call} (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)) :
    ∀ first second, first < second → second < call.length.toNat →
      (call.old first).key.toNat < (call.old second).key.toNat := by
  intro first second ordering inside
  have len := SortedMap.entriesOf_length call.old call.length.toNat
  have small : first < (SortedMap.entriesOf call.old call.length.toNat).length := by omega
  have large : second < (SortedMap.entriesOf call.old call.length.toNat).length := by omega
  simpa only [SortedMap.entriesOf_getElem] using
    (List.pairwise_iff_getElem.mp sorted) first second small large ordering

theorem Call.freshKeyAbsent {call : Call}
    (fresh : call.rank = 0 ∨ (0 < call.rank ∧ call.predecessor.value.toNat + 1 < call.start.toNat))
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ranges : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat) :
    ∀ index < call.length.toNat, (call.old index).key ≠ call.start := by
  intro index inside same
  have rankLe := call.rank_le
  have increasing := Call.keysIncreasing sorted
  have earlier : index < call.rank := by
    by_contra later
    have beforeEnd : call.rank < call.length.toNat := by omega
    have exit := SortedMap.scan_stops (bound := .upper) (key := call.start) (old := call.old)
      0 call.length.toNat (by simpa only [Nat.zero_add] using beforeEnd)
    have above : call.start.toNat < (call.old call.rank).key.toNat := by
      exact Nat.lt_of_not_ge (by simpa only [SortedMap.Bound.passes, decide_eq_false_iff_not] using exit)
    have less : (call.old call.rank).key.toNat ≤ (call.old index).key.toNat := by
      by_cases equal : call.rank = index
      · rw [equal]
      · exact (increasing _ _ (by omega) inside).le
    rw [same] at less
    omega
  rcases fresh with none | ⟨found, strict⟩
  · omega
  · have predInside : call.rank - 1 < call.length.toNat := by omega
    have length := ranges _ predInside
    have beforePred : (call.old index).key.toNat ≤ call.predecessor.key.toNat := by
      change (call.old index).key.toNat ≤ (call.old (call.rank - 1)).key.toNat
      by_cases equal : index = call.rank - 1
      · rw [equal]
      · exact (increasing _ _ (by omega) predInside).le
    rw [same] at beforePred
    change call.predecessor.key.toNat ≤ call.predecessor.value.toNat at length
    omega

theorem Call.freshDoesNotReplace {call : Call} (capacity : Word)
    (absent : ∀ index < call.length.toNat, (call.old index).key ≠ call.start) :
    ¬ (call.freshInsert capacity).replaces := by
  intro replacement
  exact absent _ replacement.2.1 replacement.2.2

theorem Call.freshVectorValid {call : Call} (capacity : Word) (spare : call.length.toNat < capacity.toNat) :
    (call.freshInsert capacity).vector.valid := by
  have position := (call.freshInsert capacity).position_le
  refine ⟨?_, spare⟩
  rw [SortedMap.Insert.Call.vectorIndex]
  exact position

/-- The caller's snapshot projected to the registers of sorted-map insert. -/
def insertView (caller : Empty.Snapshot) : SortedMap.Insert.Snapshot :=
  { ra := caller.ra, sp := caller.sp, t0 := caller.t0, t1 := caller.t1
    s0 := caller.s0, s1 := caller.s1, s2 := caller.s2, s3 := caller.s3
    a0 := caller.a0, a1 := caller.a1, a2 := caller.a2, a3 := caller.a3
    a4 := caller.a4, a5 := caller.a5, a6 := caller.a6, a7 := caller.a7 }

private theorem insertInside : ∀ index ∈ tracked SortedMap.Insert.Snapshot, index ∈ tracked Empty.Snapshot := by
  decide

theorem FreshCalling.insertEntry {base : Word} {frame : Machine} {initial caller : Empty.Snapshot}
    {call : Call} (reached : FreshCalling base initial call caller) :
    sync base frame caller = sync (mapInsertBase base) (sync base frame caller) { insertView caller with pc := 0 } := by
  have target : base + caller.pc = mapInsertBase base + 0#32 := by
    rw [reached.pc, BitVec.add_zero]
    rfl
  exact (syncInside (frame := frame) base (mapInsertBase base) caller caller (insertView caller)
    insertInside (fun index _ => by fin_cases index <;> rfl) target).symm

def insertReturned (pc : Word) (caller : Empty.Snapshot) (state : SortedMap.Insert.Snapshot) : Empty.Snapshot :=
  { caller with
    pc := pc, ra := state.ra, sp := state.sp, t0 := state.t0, t1 := state.t1
    s0 := state.s0, s1 := state.s1, s2 := state.s2, s3 := state.s3
    a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3
    a4 := state.a4, a5 := state.a5, a6 := state.a6, a7 := state.a7 }

theorem insertReturnedSync (base pc : Word) (frame : Machine) (caller : Empty.Snapshot)
    (state : SortedMap.Insert.Snapshot) (target : base + pc = mapInsertBase base + state.pc) :
    sync (mapInsertBase base) (sync base frame caller) state = sync base frame (insertReturned pc caller state) :=
  syncInside base (mapInsertBase base) caller (insertReturned pc caller state)
    state insertInside (fun index _ => by fin_cases index <;> rfl) target

theorem FreshPrefix.keptByte {base ret : Word} {original : Machine}
    {initial : Empty.Snapshot} {call : Call} (premises : FreshPrefix base ret original initial call)
    (byte : Nat) (outside : Empty.OutsideFrame initial.sp byte) :
    (freshStored initial (Empty.pushed original.mem initial))[byte]? = original.mem[byte]? := by
  have fit := premises.frame.frameFits
  refine (writeWordsOutside _ _ byte ?_).trans (Empty.pushedOutside _ _ fit byte outside)
  intro write member
  simp only [scratchWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  unfold Empty.OutsideFrame at outside
  rcases member with rfl | rfl | rfl
  · change byte < (Empty.frameBase initial.sp + 8#32).toNat ∨
      (Empty.frameBase initial.sp + 8#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fit 8#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 8 ∨ initial.sp.toNat - 48 + 8 + 4 ≤ byte
    omega
  · change byte < (Empty.frameBase initial.sp + 12#32).toNat ∨
      (Empty.frameBase initial.sp + 12#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fit 12#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 12 ∨ initial.sp.toNat - 48 + 12 + 4 ≤ byte
    omega
  · change byte < (Empty.frameBase initial.sp + 16#32).toNat ∨
      (Empty.frameBase initial.sp + 16#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fit 16#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 16 ∨ initial.sp.toNat - 48 + 16 + 4 ≤ byte
    omega

/-- Transfer the map and code to the fresh call's actual stack and register
state. All map words are unchanged by the setup. -/
theorem FreshPrefix.insertStorage {base ret : Word} {original : Machine}
    {initial caller : Empty.Snapshot} {call : Call} {capacity low high : Word}
    (premises : FreshPrefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high) :
    let stored := freshStored initial (Empty.pushed original.mem initial)
    let entered := sync base { original with mem := stored } caller
    CodeImages base entered ∧ MapStorage entered call capacity ∧ StackSpace entered initial.sp := by
  let stored := freshStored initial (Empty.pushed original.mem initial)
  let frame := { original with mem := stored }
  let entered := sync base frame caller
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame (base := base) (frame := frame) caller Register.pma_regions
      (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have memory : entered.mem = stored := syncMem (base := base) (frame := frame) caller
  have maps := layout.map
  have fits := layout.stack.fits
  have codes : CodeImages base frame := layout.code.withMemory stored fun span member byte inside =>
    premises.keptByte byte (stackDisjointOuter fits ((layout.apart.code span member).2.2.2.2 byte inside))
  have keepHeader {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (mapHeader call).Contains byte) :
      WordAt entered.mem address value := by
    rw [memory]
    exact word.congr fun byte low high =>
      premises.keptByte byte (stackDisjointOuter fits (layout.apart.headerStack byte (inside byte low high)))
  have headerPart (offset : Nat) (small : offset ≤ 8) (byte : Nat)
      (low : call.header.toNat + offset ≤ byte) (high : byte < call.header.toNat + offset + 4) :
      (mapHeader call).Contains byte := by
    change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
    omega
  have map : MapStorage entered call capacity := by
    refine { maps with
      headerReadable := fun offset member => mappedTransfer (maps.headerReadable offset member) regions
      lengthWritable := mappedTransfer maps.lengthWritable regions
      dataWord := keepHeader maps.dataWord (headerPart 0 (by decide))
      lengthWord := keepHeader maps.lengthWord (headerPart 4 (by decide))
      capacityWord := keepHeader maps.capacityWord (headerPart 8 (by decide))
      live := ?_
      pairsReadable := fun index inside =>
        ⟨mappedTransfer (maps.pairsReadable index inside).1 regions, mappedTransfer (maps.pairsReadable index inside).2 regions⟩
      pairsWritable := fun index inside =>
        ⟨mappedTransfer (maps.pairsWritable index inside).1 regions, mappedTransfer (maps.pairsWritable index inside).2 regions⟩ }
    intro index inside
    obtain ⟨key, value⟩ := maps.live index inside
    constructor
    · refine key.congr fun byte low high => ?_
      rw [memory]
      exact premises.keptByte byte (stackDisjointOuter fits (layout.apart.mapStack byte
        (maps.entryContained inside low (by omega))))
    · refine value.congr fun byte low high => ?_
      rw [memory]
      exact premises.keptByte byte (stackDisjointOuter fits (layout.apart.mapStack byte
        (maps.entryContained inside (by omega) (by omega))))
  exact ⟨codes.atSync caller, map, layout.stack.transfer regions⟩

private theorem mapSlotContained (call : Call) (capacity : Word) {index byte : Nat}
    (inside : index < capacity.toNat) (low : call.search.slot index ≤ byte)
    (high : byte < call.search.slot index + 8) :
    (mapAllocation call capacity).Contains byte := by
  change call.data.toNat + 8 * index ≤ byte at low
  change byte < call.data.toNat + 8 * index + 8 at high
  change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
  omega

theorem MapStorage.searchKeys {original : Machine} {call : Call} {capacity key : Word}
    (map : MapStorage original call capacity) :
    SortedMap.Search.Keys original ⟨call.header, key, call.length, call.data, call.old⟩ := by
  have length := map.lengthFits
  have fits := map.allocationFits
  have readable : Readable original (call.header + 0#32) := map.headerReadable 0#32 (by decide)
  rw [BitVec.add_zero] at readable
  refine ⟨?_, readable, map.dataWord, ?_, fun index inside => (map.live index inside).1⟩
  · change call.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32
    omega
  · intro index inside
    change index < call.length.toNat at inside
    exact (map.pairsReadable index (by omega)).1

theorem MapStorage.insertHeader {original : Machine} {call : Call} {capacity : Word}
    (map : MapStorage original call capacity) :
    RawVec.Insert.Header original (call.freshInsert capacity).vector :=
  ⟨map.headerFits, map.headerReadable 4 (by decide), map.headerReadable 8 (by decide),
    map.lengthWord, map.capacityWord⟩

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

theorem StackSpace.forInsert {base : Word} {original : Machine} {call : Call} {capacity cache sp : Word}
    {scratch : DeleteExtra.Scratch} (stack : StackSpace original sp)
    (apart : Separation base sp call capacity cache scratch)
    (spare : call.length.toNat < capacity.toNat) :
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
    apartSpare := fun _ => slot call.length.toNat spare
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

end Riscfree.RangeInsert.Nonempty
