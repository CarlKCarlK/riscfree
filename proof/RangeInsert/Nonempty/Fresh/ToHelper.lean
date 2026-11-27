import RangeInsert.Nonempty.Fresh.Insertion
import RangeInsert.Nonempty.HelperLayout
import RangeInsert.Nonempty.Extension.Stored

/-! The two fresh call sites enter the same verified sorted-map insertion.
A successful return takes the actual branch into the deletion helper. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Pair PairAt Readable Writable)
open Empty (Snapshot)

def freshPrefixMemory (original : Machine) (initial : Snapshot) : ByteMemory :=
  freshStored initial (Empty.pushed original.mem initial)

def freshToHelperCount (call : Call) (capacity : Word) : Nat :=
  insertionPrefixCount call + (call.freshInsert capacity).count + 8

structure FreshHelperCalling (base : Word) (initial : Snapshot) (call : Call) (state : Snapshot) : Prop where
  pc : state.pc = extensionHelperOffset
  sp : state.sp = Empty.frameBase initial.sp
  ra : state.ra = base + 0xf8#32
  mapRef : state.a0 = Empty.frameBase initial.sp + 4#32
  cache : state.a1 = initial.a1
  start : state.a2 = call.start
  stop : state.a3 = call.stop
  keys : state.a4 = Empty.frameBase initial.sp + 8#32
  savedCache : state.s0 = initial.a1
  savedStop : state.s1 = call.stop
  savedStart : state.s2 = call.start
  saved : state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧ state.s8 = initial.s8 ∧
    state.s9 = initial.s9 ∧ state.s10 = initial.s10

theorem freshInsertStatus {call : Call} {capacity : Word} (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces) :
    (call.freshInsert capacity).status = 0#32 := by
  let insertion := call.freshInsert capacity
  have valid : insertion.lengthValid := spare.le
  have vector := Call.freshVectorValid (call := call) capacity spare
  have lengthCheck : ¬ insertion.vector.capacity.toNat < insertion.vector.length.toNat := by
    exact Nat.not_lt.mpr spare.le
  have indexCheck : ¬ insertion.vector.length.toNat < insertion.vector.index.toNat :=
    Nat.not_lt.mpr vector.1
  have full : insertion.vector.length ≠ insertion.vector.capacity := by
    intro equal
    have sizes := congrArg BitVec.toNat equal
    change call.length.toNat = capacity.toNat at sizes
    omega
  change insertion.status = 0#32
  rw [SortedMap.Insert.Call.status, if_neg (not_not_intro valid), if_neg newKey,
    RawVec.Insert.Call.status, if_neg lengthCheck, if_neg indexCheck, if_neg full]
  rfl

private theorem insertionKeepsPrefix {initial caller : Snapshot} {original : Machine} {call : Call}
    {base : Word} {capacity : Word} {after : ByteMemory}
    (reached : FreshCalling base initial call caller)
    (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (freshPrefixMemory original initial) caller.sp (insertView caller)) after)
    (byte : Nat) (outsideInsertion : byte < caller.sp.toNat - 32 ∨ caller.sp.toNat ≤ byte)
    (outsideHeader : ¬ (mapHeader call).Contains byte)
    (outsideMap : ¬ (mapAllocation call capacity).Contains byte)
    (fit : 112 ≤ initial.sp.toNat) :
    after[byte]? = (freshPrefixMemory original initial)[byte]? := by
  have fits : 32 ≤ (insertView caller).sp.toNat := by
    change 32 ≤ caller.sp.toNat
    rw [reached.sp]
    have address := Empty.frameAddress (sp := initial.sp) (by omega) 0#32 (by decide)
    rw [BitVec.add_zero] at address
    change (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 + 0 at address
    rw [address]
    omega
  have changedMap := (result.2.2 newKey (Call.freshVectorValid capacity spare)).2.2.2.2
  have outsideLength : byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte := by
    change ¬ (call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12) at outsideHeader
    omega
  have outsideEntries :
      byte < (call.freshInsert capacity).vector.slot (call.freshInsert capacity).vector.index.toNat ∨
      (call.freshInsert capacity).vector.slot (call.length.toNat + 1) ≤ byte := by
    change ¬ (call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat) at outsideMap
    change byte < call.data.toNat + 8 * (call.freshInsert capacity).vector.index.toNat ∨
      call.data.toNat + 8 * (call.length.toNat + 1) ≤ byte
    omega
  exact (changedMap byte outsideLength outsideEntries).trans
    (SortedMap.Insert.pushedOutside (freshPrefixMemory original initial) (insertView caller) fits byte outsideInsertion)

theorem FreshPrefix.insertionKeeps {base ret : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity : Word} {after : ByteMemory}
    (premises : FreshPrefix base ret original initial call)
    (reached : FreshCalling base initial call caller)
    (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (freshPrefixMemory original initial) caller.sp (insertView caller)) after)
    (byte : Nat) (outsideStack : ¬ (stackAllocation initial.sp).Contains byte)
    (outsideHeader : ¬ (mapHeader call).Contains byte)
    (outsideMap : ¬ (mapAllocation call capacity).Contains byte)
    (fit : 112 ≤ initial.sp.toNat) :
    after[byte]? = original.mem[byte]? := by
  have outsideOuter := stackDisjointOuter fit outsideStack
  have outsideInsertion : byte < caller.sp.toNat - 32 ∨ caller.sp.toNat ≤ byte := by
    rw [reached.sp]
    have natural : (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 := by
      have zero := Empty.frameAddress (sp := initial.sp) (by omega) 0#32 (by decide)
      simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero
    rw [natural]
    change ¬ (initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112) at outsideStack
    omega
  exact (insertionKeepsPrefix reached spare newKey result byte outsideInsertion outsideHeader outsideMap fit).trans
    (premises.keptByte byte outsideOuter)

set_option maxHeartbeats 2500000 in
/-- Result of the real sorted-map call and its successful branch to the
helper. The map memory contract is relative to the insertion's prologue. -/
theorem FreshPrefix.toHelper {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : FreshPrefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ranges : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat) :
    ∃ (caller state : Snapshot) (after : ByteMemory),
      run (freshToHelperCount call capacity) original =
        some (sync base { original with mem := after } state) ∧
      FreshCalling base initial call caller ∧ FreshHelperCalling base initial call state ∧
      SortedMap.Insert.finalMemory (call.freshInsert capacity)
        (SortedMap.Insert.pushed (freshPrefixMemory original initial) caller.sp (insertView caller)) after := by
  let insertion := call.freshInsert capacity
  let memory := freshPrefixMemory original initial
  let before := { original with mem := memory }
  have nonReplace := Call.freshDoesNotReplace capacity (Call.freshKeyAbsent premises.fresh sorted ranges)
  have succeeded := freshInsertStatus spare nonReplace
  obtain ⟨caller, toInsert, facts⟩ := premises.toInsert
  let entered := sync base before caller
  have beginning : run (insertionPrefixCount call) original = some entered :=
    (congrArg (run (insertionPrefixCount call)) premises.frame.entry).trans toInsert
  obtain ⟨code, map, stack⟩ := premises.insertStorage (caller := caller) layout
  have correctStack : SortedMap.Insert.Stack (mapInsertBase base) entered insertion caller.sp := by
    rw [facts.sp]
    exact stack.forInsert layout.apart spare
  have atCall : entered = sync (mapInsertBase base) entered { insertView caller with pc := 0 } :=
    facts.insertEntry
  have callerMachine : MachineState before := premises.frame.mode.toMachineState.withMemory memory
  have offsetAlignment : (insertionReturn call).toNat % 4 = 0 := by
    unfold insertionReturn
    split <;> decide
  have alignment := SortedMap.Remove.alignedTargetNat code.entry.aligned (insertionReturn call) offsetAlignment
  obtain ⟨bit0, bit1⟩ := alignedBits _ alignment
  have insertMode : MachineMode entered (base + insertionReturn call) :=
    { callerMachine.atSync base caller with
      returnLow := by rw [BitVec.and_comm]; exact maskEven _ bit0
      returnNext := bit1
      ra := by
        have read := syncRead (base := base) (frame := before) caller (index := 1) (by decide)
        change Sail.readReg Register.x1 entered = .ok caller.ra entered at read
        rw [facts.link] at read
        exact read }
  have search : CodeImage (SortedMap.Search.instructions .lower)
      (SortedMap.Insert.searchBase (mapInsertBase base)) entered := by
    rw [lowerBoundFromInsert]
    exact code.lower
  have environment : SortedMap.Insert.Environment (mapInsertBase base)
      (base + insertionReturn call) entered :=
    ⟨insertMode, code.mapInsert, search, code.pairInsert⟩
  obtain ⟨tail, after, ran, pc, status, ra, sp, s0, s1, s2, _, result⟩ :=
    SortedMap.Insert.sortedMapInsertSailRun (mapInsertBase base) (base + insertionReturn call)
      entered insertion (insertView caller) atCall facts.header facts.start facts.stop environment
      map.insertHeader correctStack (fun _ _ => map.searchKeys)
      (fun impossible => (nonReplace impossible).elim) (fun _ _ => map.insertBuffer layout.apart spare)
  let continued := insertReturned (insertionReturn call) caller tail
  let afterMachine := { original with mem := after }
  have target : base + insertionReturn call = mapInsertBase base + tail.pc := by
    rw [pc, BitVec.add_comm (mapInsertBase base), BitVec.sub_add_cancel]
  have switch := insertReturnedSync base (insertionReturn call) afterMachine caller tail target
  have withMemory := syncWithMem base before caller after
  have insertionRan : run insertion.count entered = some (sync base afterMachine continued) := by
    rw [ran]
    change some (sync (mapInsertBase base) { sync base before caller with mem := after } tail) = _
    rw [withMemory]
    exact congrArg some switch
  have resultAtCaller : SortedMap.Insert.finalMemory insertion
      (SortedMap.Insert.pushed memory caller.sp (insertView caller)) after := by
    have unchanged : entered.mem = memory := syncMem (base := base) (frame := before) caller
    rw [unchanged] at result
    exact result
  have outerCode : CodeImage InsertTable.instructions base afterMachine :=
    layout.code.entry.withMemory after fun byte low high => by
      have safe := layout.apart.code _ (List.mem_cons_self ..)
      exact premises.insertionKeeps facts spare nonReplace resultAtCaller byte
        (safe.2.2.2.2 byte ⟨low, high⟩) (safe.1 byte ⟨low, high⟩) (safe.2.1 byte ⟨low, high⟩) layout.stack.fits
  have statusZero : continued.a0 = 0#32 := status.trans succeeded
  have returnSite : continued.pc = 0xa4#32 ∨ continued.pc = 0xd8#32 := by
    change insertionReturn call = 0xa4#32 ∨ insertionReturn call = 0xd8#32
    unfold insertionReturn
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have toHelper := freshAfterInsert premises.frame.mode.toMachineState outerCode continued returnSite statusZero
  let state := freshHelperCalling base continued
  have restoredSp : continued.sp = Empty.frameBase initial.sp := sp.trans facts.sp
  have restoredCache : continued.s0 = initial.a1 := s0.trans facts.cache
  have restoredStart : continued.s2 = call.start := s2.trans facts.savedStart
  have restoredStop : continued.s1 = call.stop := s1.trans facts.savedStop
  refine ⟨caller, state, after, ?_, facts, ?_, ?_⟩
  · rw [freshToHelperCount, runAdd, runAdd, beginning, Option.bind_some, insertionRan, Option.bind_some]
    exact toHelper
  · exact ⟨rfl, restoredSp, rfl, congrArg (· + 4#32) restoredSp, restoredCache, restoredStart, restoredStop,
      congrArg (· + 8#32) restoredSp, restoredCache, restoredStop, restoredStart, facts.saved⟩
  · exact resultAtCaller

def Call.freshHelper (call : Call) (capacity : Word) (initial : Snapshot) (low high : Word) :
    DeleteExtra.Call :=
  let sp := Empty.frameBase initial.sp
  { mapRef := sp + 4#32, header := call.header
    length := BitVec.ofNat 32 (call.length.toNat + 1), data := call.data
    old := (call.freshInsert capacity).vector.result
    cache := initial.a1, low := low, high := high, start := call.start, stop := call.stop, keys := sp + 8#32 }

theorem Call.freshHelperLength (call : Call) (capacity : Word) (initial : Snapshot) (low high : Word)
    (spare : call.length.toNat < capacity.toNat) :
    (call.freshHelper capacity initial low high).length.toNat = call.length.toNat + 1 := by
  change (BitVec.ofNat 32 (call.length.toNat + 1)).toNat = _
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := capacity.isLt; omega)

theorem Call.freshHelperSorted {call : Call} {capacity : Word} {initial : Snapshot} {low high : Word}
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces) :
    let helper := call.freshHelper capacity initial low high
    SortedMap.Sorted (SortedMap.entriesOf helper.old helper.length.toNat) := by
  let insertion := call.freshInsert capacity
  change SortedMap.Sorted (SortedMap.entriesOf insertion.vector.result
    (call.freshHelper capacity initial low high).length.toNat)
  rw [call.freshHelperLength capacity initial low high spare]
  change SortedMap.Sorted (SortedMap.entriesOf insertion.vector.result (insertion.length.toNat + 1))
  have updates := (SortedMap.Insert.sortedMapInsertUpdates insertion sorted).2 newKey
    (Call.freshVectorValid capacity spare)
  rw [updates]
  exact SortedMap.sorted_insert sorted insertion.value

theorem Call.freshHelperSelected {call : Call} {capacity : Word} {initial : Snapshot} {low high : Word}
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces) :
    (call.freshHelper capacity initial low high).position = (call.freshInsert capacity).position := by
  let insertion := call.freshInsert capacity
  let helper := call.freshHelper capacity initial low high
  have key : (helper.old insertion.position).key = call.start := by
    change (insertion.vector.result insertion.position).key = call.start
    rw [RawVec.Insert.Call.result, insertion.vectorIndex, if_neg (Nat.lt_irrefl _), if_pos rfl]
    rfl
  have length := call.freshHelperLength capacity initial low high spare
  have inside : insertion.position < helper.length.toNat := by
    change helper.length.toNat = call.length.toNat + 1 at length
    have position := insertion.position_le
    change insertion.position ≤ call.length.toNat at position
    omega
  have increasing := Call.keysIncreasing (call := helperAsOuter helper)
    (Call.freshHelperSorted (initial := initial) (low := low) (high := high) sorted spare newKey)
  change SortedMap.scan .lower call.start helper.old 0 helper.length.toNat = insertion.position
  refine DeleteExtra.scan_stopsAt call.start helper.old insertion.position ?_ ?_ 0 helper.length.toNat
    (Nat.zero_le _) (by omega)
  · intro earlier previous
    have ordered := increasing earlier insertion.position previous inside
    change (helper.old earlier).key.toNat < (helper.old insertion.position).key.toNat at ordered
    rw [key] at ordered
    exact ordered
  · rw [key]
    exact Nat.lt_irrefl _

theorem FreshHelperCalling.arguments {base : Word} {initial caller : Snapshot}
    {call : Call} {capacity low high : Word} (facts : FreshHelperCalling base initial call caller) :
    DeleteExtra.Arguments (helperView caller 0) (call.freshHelper capacity initial low high) :=
  ⟨facts.mapRef, facts.cache, facts.start, facts.stop, facts.keys⟩

private theorem freshMapReference (original : Machine) (initial : Snapshot) (fits : 48 ≤ initial.sp.toNat) :
    WordAt (freshPrefixMemory original initial) (Empty.frameBase initial.sp + 4#32).toNat initial.a0 := by
  refine (pushedMapReference initial original.mem).congr fun byte low high => ?_
  apply writeWordsOutside
  rw [Empty.frameAddress fits 4#32 (by decide)] at low high
  change initial.sp.toNat - 48 + 4 ≤ byte at low
  change byte < initial.sp.toNat - 48 + 4 + 4 at high
  intro write member
  simp only [scratchWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · left
    change byte < (Empty.frameBase initial.sp + 8#32).toNat
    rw [Empty.frameAddress fits 8#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 8
    omega
  · left
    change byte < (Empty.frameBase initial.sp + 12#32).toNat
    rw [Empty.frameAddress fits 12#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 12
    omega
  · left
    change byte < (Empty.frameBase initial.sp + 16#32).toNat
    rw [Empty.frameAddress fits 16#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 16
    omega

theorem FreshPrefix.helperStackWord {base ret : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity low high : Word} {after : ByteMemory}
    (premises : FreshPrefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (reached : FreshCalling base initial call caller)
    (spare : call.length.toNat < capacity.toNat) (noReplace : ¬ (call.freshInsert capacity).replaces)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (freshPrefixMemory original initial) caller.sp (insertView caller)) after)
    {address : Nat} {value : Word} (word : WordAt (freshPrefixMemory original initial) address value)
    (bottom : (Empty.frameBase initial.sp).toNat ≤ address)
    (top : address + 4 ≤ initial.sp.toNat) :
    WordAt after address value := by
  refine word.congr fun byte low high => ?_
  have fits := layout.stack.fits
  have atStack : (stackAllocation initial.sp).Contains byte := by
    have outer := Empty.frameAddress (sp := initial.sp) premises.frame.frameFits 0#32 (by decide)
    rw [BitVec.add_zero] at outer
    change (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 + 0 at outer
    rw [outer] at bottom
    change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
    omega
  have above : caller.sp.toNat ≤ byte := by rw [reached.sp]; omega
  exact insertionKeepsPrefix reached spare noReplace result byte (Or.inr above)
    (layout.apart.headerStack.symm byte atStack) (layout.apart.mapStack.symm byte atStack) fits

private theorem FreshPrefix.storedMap {base : Word} {original entered : Machine}
    {initial caller : Snapshot} {call : Call} {capacity low high : Word} {after : ByteMemory}
    (layout : InitialLayout base original initial call capacity low high)
    (spare : call.length.toNat < capacity.toNat) (noReplace : ¬ (call.freshInsert capacity).replaces)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (freshPrefixMemory original initial) caller.sp (insertView caller)) after)
    (regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions)
    (memory : entered.mem = after) :
    MapStorage entered (helperAsOuter (call.freshHelper capacity initial low high)) capacity := by
  let insertion := call.freshInsert capacity
  have old := layout.map
  obtain ⟨data, length, capacityWord, entries, _⟩ := result.2.2 noReplace (Call.freshVectorValid capacity spare)
  have newLength := call.freshHelperLength capacity initial low high spare
  refine {
    headerFits := old.headerFits
    allocationFits := old.allocationFits
    dataNonnull := old.dataNonnull
    lengthFits := ?_
    headerReadable := fun offset member => mappedTransfer (old.headerReadable offset member) regions
    lengthWritable := mappedTransfer old.lengthWritable regions
    dataWord := memory.symm ▸ data
    lengthWord := memory.symm ▸ length
    capacityWord := memory.symm ▸ capacityWord
    live := ?_
    pairsReadable := fun index inside => ⟨mappedTransfer (old.pairsReadable index inside).1 regions,
      mappedTransfer (old.pairsReadable index inside).2 regions⟩
    pairsWritable := fun index inside => ⟨mappedTransfer (old.pairsWritable index inside).1 regions,
      mappedTransfer (old.pairsWritable index inside).2 regions⟩ }
  · change (call.freshHelper capacity initial low high).length.toNat ≤ capacity.toNat
    rw [newLength]
    omega
  · intro index inside
    change index < (call.freshHelper capacity initial low high).length.toNat at inside
    rw [newLength] at inside
    change PairAt entered.mem (insertion.search.slot index) (insertion.vector.result index)
    rw [memory, ← insertion.slotSame]
    exact entries index inside

/-- The actual sorted-map result supplies a fresh helper call's initialized
map prefix. The helper's reference, scratch header, and cache are still
the outer caller's words. -/
theorem FreshPrefix.helperInput {base ret : Word} {original : Machine}
    {initial caller state : Snapshot} {call : Call} {capacity low high : Word} {after : ByteMemory}
    (premises : FreshPrefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (reached : FreshCalling base initial call caller)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ranges : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (freshPrefixMemory original initial) caller.sp (insertView caller)) after) :
    HelperInput base (sync base { original with mem := after } state) initial
      (call.freshHelper capacity initial low high) capacity := by
  let background := { original with mem := after }
  let entered := sync base background state
  let helperCall := call.freshHelper capacity initial low high
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have noReplace := Call.freshDoesNotReplace capacity (Call.freshKeyAbsent premises.fresh sorted ranges)
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame (base := base) (frame := background) state Register.pma_regions
      (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have bytes : entered.mem = after := syncMem (base := base) (frame := background) state
  have apart := layout.apart
  have fit := layout.stack.fits
  have frameFits := premises.frame.frameFits
  have code : CodeImages base background := layout.code.withMemory after fun span member byte inside =>
    have safe := apart.code span member
    premises.insertionKeeps reached spare noReplace result byte
      (safe.2.2.2.2 byte inside) (safe.1 byte inside) (safe.2.1 byte inside) fit
  have keepCache {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (cacheWords initial.a1).Contains byte) :
      WordAt entered.mem address value := by
    rw [bytes]
    exact word.congr fun byte low high => by
      have onCache := inside byte low high
      exact premises.insertionKeeps reached spare noReplace result byte
        (apart.cacheStack byte onCache) (apart.headerCache.symm byte onCache) (apart.mapCache.symm byte onCache) fit
  have cachePart (offset : Nat) (small : offset ≤ 4) (byte : Nat)
      (lo : initial.a1.toNat + offset ≤ byte) (hi : byte < initial.a1.toNat + offset + 4) :
      (cacheWords initial.a1).Contains byte := by
    change initial.a1.toNat ≤ byte ∧ byte < initial.a1.toNat + 8
    omega
  have cache : CacheStorage entered initial.a1 low high :=
    ⟨layout.cache.fits, ⟨mappedTransfer layout.cache.readable.1 regions, mappedTransfer layout.cache.readable.2 regions⟩,
      ⟨mappedTransfer layout.cache.writable.1 regions, mappedTransfer layout.cache.writable.2 regions⟩,
      keepCache layout.cache.low (cachePart 0 (by decide)), keepCache layout.cache.high (cachePart 4 (by decide))⟩
  have geometry : Separation base initial.sp (helperAsOuter helperCall) capacity initial.a1 scratch :=
    ⟨apart.headerMap, apart.headerCache, apart.headerScratch, apart.headerStack, apart.mapCache,
      apart.mapScratch, apart.mapStack, apart.cacheScratch, apart.cacheStack, apart.scratchStack, apart.code⟩
  have arrived : InitialLayout base entered initial (helperAsOuter helperCall) capacity low high :=
    ⟨code.atSync state, storedMap layout spare noReplace result regions bytes,
      layout.scratch.transfer regions, cache, layout.stack.transfer regions, geometry⟩
  have selected := Call.freshHelperSelected (initial := initial) (low := low) (high := high)
    sorted spare noReplace
  have helperLength := call.freshHelperLength capacity initial low high spare
  have found : helperCall.position < helperCall.length.toNat := by
    change helperCall.position = (call.freshInsert capacity).position at selected
    change helperCall.length.toNat = call.length.toNat + 1 at helperLength
    rw [selected, helperLength]
    have bound := (call.freshInsert capacity).position_le
    change (call.freshInsert capacity).position ≤ call.length.toNat at bound
    omega
  obtain ⟨scratchData, scratchLength, scratchCapacity⟩ :=
    scratchHeaderWords initial (Empty.pushed original.mem initial) frameFits
  have baseNat : (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 := by
    have zero := Empty.frameAddress (sp := initial.sp) frameFits 0#32 (by decide)
    simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero
  have mapRefNat : (Empty.frameBase initial.sp + 4#32).toNat = initial.sp.toNat - 48 + 4 :=
    Empty.frameAddress frameFits 4#32 (by decide)
  have keysNat : (Empty.frameBase initial.sp + 8#32).toNat = initial.sp.toNat - 48 + 8 :=
    Empty.frameAddress frameFits 8#32 (by decide)
  have keepSlot {address : Nat} {value : Word}
      (word : WordAt (freshPrefixMemory original initial) address value)
      (lo : initial.sp.toNat - 48 ≤ address) (hi : address + 4 ≤ initial.sp.toNat) :
      WordAt entered.mem address value := by
    rw [bytes]
    exact premises.helperStackWord layout reached spare noReplace result word (baseNat.symm ▸ lo) hi
  refine ⟨arrived, rfl, rfl, rfl, ?_, ?_, ?_, ?_, found⟩
  · have reference := freshMapReference original initial frameFits
    rw [premises.arguments.header] at reference
    exact keepSlot (address := (Empty.frameBase initial.sp + 4#32).toNat)
      reference (by rw [mapRefNat]; omega) (by rw [mapRefNat]; omega)
  · exact keepSlot (address := (Empty.frameBase initial.sp + 8#32).toNat)
      scratchData (by rw [keysNat]; omega) (by rw [keysNat]; omega)
  · exact keepSlot (address := (Empty.frameBase initial.sp + 8#32).toNat + 4)
      scratchLength (by rw [keysNat]; omega) (by rw [keysNat]; omega)
  · exact keepSlot (address := (Empty.frameBase initial.sp + 8#32).toNat + 8)
      scratchCapacity (by rw [keysNat]; omega) (by rw [keysNat]; omega)

end Riscfree.RangeInsert.Nonempty
