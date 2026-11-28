import RangeInsert.Bounded.MapFullRun
import RangeInsert.Bounded.OuterHelper
import RangeInsert.Nonempty.Fresh.ToHelper
import RangeInsert.Nonempty.Extension.Stored

/-! The bounded routine's fresh path through the sorted-map insertion.
Unlike the trapping routine, nothing outside the saved registers is written before the call:
the scratch header is initialized only after a successful insertion. A full
map returns FULL immediately; otherwise the caller writes the header and
calls the deletion helper. -/

namespace Riscfree.RangeInsert.Bounded.FreshPath

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Pair PairAt Readable Writable)
open Empty (Snapshot)
open Entry
open EntryEmpty (Frame)
open EntryPredecessor (Map)
open EntryFresh (Calling toInsert toInsertCount insertReturn mapInsertBase FullCall afterCallee insertReturnedSync)
open OuterLayout
open OuterView (helperView)
open OuterHelper (HelperInput helperAsOuter)
open Nonempty (Call Arguments Span MapStorage CacheStorage StackSpace mapHeader mapAllocation cacheWords
  stackAllocation mapLengthWord lengthInHeader stackDisjointOuter mappedTransfer insertView insertReturned
  writeWords writeWordsOutside freshStored scratchWrites scratchHeaderWords
  pushedMapReference WritableByte)

set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

/-- The fresh path's premises at entry. -/
structure Prefix (base returnAddress : Word) (original : Machine) (initial : Snapshot) (call : Call) :
    Prop where
  frame : Frame base returnAddress original initial
  arguments : Arguments initial call
  map : Map base original initial.sp call
  nonempty : call.start.toNat ≤ call.stop.toNat
  fresh : call.path = .fresh
  writable : ∀ offset ∈ ([8, 12, 16] : List Word), Writable original (Empty.frameBase initial.sp + offset)

theorem freshPrefix {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high)
    (entry : original = sync base original { initial with pc := 0 })
    (link : initial.ra = returnAddress) (mode : MachineMode original returnAddress)
    (arguments : Arguments initial call) (nonempty : call.start.toNat ≤ call.stop.toNat)
    (fresh : call.path = .fresh) :
    Prefix base returnAddress original initial call :=
  ⟨layout.outerFrame entry link mode, arguments, layout.predecessorMap, nonempty, fresh,
    layout.stack.scratchWritable⟩

private theorem frameNat (sp : Word) (fits : 48 ≤ sp.toNat) : (Empty.frameBase sp).toNat = sp.toNat - 48 := by
  have zero := Empty.frameAddress (sp := sp) fits 0#32 (by decide)
  simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero

/-- The scratch-header stores write the outer frame's words 8 through 19. -/
theorem freshStoredOutside (initial : Snapshot) (memory : ByteMemory) (fits : 48 ≤ initial.sp.toNat)
    (byte : Nat) (outside : byte < initial.sp.toNat - 48 + 8 ∨ initial.sp.toNat - 48 + 20 ≤ byte) :
    (freshStored initial memory)[byte]? = memory[byte]? := by
  refine writeWordsOutside _ _ byte ?_
  intro write member
  simp only [scratchWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change byte < (Empty.frameBase initial.sp + 8#32).toNat ∨ (Empty.frameBase initial.sp + 8#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fits 8#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 8 ∨ initial.sp.toNat - 48 + 8 + 4 ≤ byte
    omega
  · change byte < (Empty.frameBase initial.sp + 12#32).toNat ∨ (Empty.frameBase initial.sp + 12#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fits 12#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 12 ∨ initial.sp.toNat - 48 + 12 + 4 ≤ byte
    omega
  · change byte < (Empty.frameBase initial.sp + 16#32).toNat ∨ (Empty.frameBase initial.sp + 16#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fits 16#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 16 ∨ initial.sp.toNat - 48 + 16 + 4 ≤ byte
    omega

/-- Transfer the map, code, and stack to the insertion's call site. Only the
saved registers have been written. -/
theorem Prefix.insertStorage {base ret : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity low high : Word}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high) :
    let entered := sync base { original with mem := Empty.pushed original.mem initial } caller
    CodeImages base entered ∧ MapStorage entered call capacity ∧ StackSpace entered initial.sp := by
  let stored := Empty.pushed original.mem initial
  let frame : Machine := { original with mem := stored }
  let entered := sync base frame caller
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame (base := base) (frame := frame) caller Register.pma_regions
      (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have memory : entered.mem = stored := syncMem (base := base) (frame := frame) caller
  have maps := layout.map
  have fits := layout.stack.fits
  have kept (byte : Nat) (outside : Empty.OutsideFrame initial.sp byte) : stored[byte]? = original.mem[byte]? :=
    Empty.pushedOutside _ _ premises.frame.frameFits byte outside
  have codes : CodeImages base frame := layout.code.withMemory stored fun span member byte inside =>
    kept byte (stackDisjointOuter fits ((layout.apart.code span member).2.2.2.2 byte inside))
  have keepHeader {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (mapHeader call).Contains byte) :
      WordAt entered.mem address value := by
    rw [memory]
    exact word.congr fun byte low high =>
      kept byte (stackDisjointOuter fits (layout.apart.headerStack byte (inside byte low high)))
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
      exact kept byte (stackDisjointOuter fits (layout.apart.mapStack byte
        (maps.entryContained inside low (by omega))))
    · refine value.congr fun byte low high => ?_
      rw [memory]
      exact kept byte (stackDisjointOuter fits (layout.apart.mapStack byte
        (maps.entryContained inside (by omega) (by omega))))
  exact ⟨codes.atSync caller, map, layout.stack.transfer regions⟩

/-- The verified sorted-map insertion's environment at either call site. -/
theorem Prefix.environment {base ret : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity low high : Word}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (facts : Calling base initial call caller) :
    let entered := sync base { original with mem := Empty.pushed original.mem initial } caller
    SortedMap.Insert.Environment (mapInsertBase base) (base + insertReturn call) entered := by
  let memory := Empty.pushed original.mem initial
  let before : Machine := { original with mem := memory }
  let entered := sync base before caller
  obtain ⟨code, _, _⟩ := premises.insertStorage (caller := caller) layout
  have callerMachine : MachineState before := premises.frame.mode.toMachineState.withMemory memory
  have offsetAlignment : (insertReturn call).toNat % 4 = 0 := by
    unfold insertReturn
    split <;> decide
  have alignment := SortedMap.Remove.alignedTargetNat code.entry.aligned (insertReturn call) offsetAlignment
  obtain ⟨bit0, bit1⟩ := alignedBits _ alignment
  have insertMode : MachineMode entered (base + insertReturn call) :=
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
  exact ⟨insertMode, code.mapInsert, search, code.pairInsert⟩

/-- The code and the outer stack lie apart from the insertion's 32-byte frame. -/
private theorem codeOutsideCallee {base : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high)
    (facts : Calling base initial call caller) (byte : Nat)
    (outside : ¬ (stackAllocation initial.sp).Contains byte) :
    byte < caller.sp.toNat - 32 ∨ caller.sp.toNat ≤ byte := by
  have fits := layout.stack.fits
  rw [facts.sp, frameNat initial.sp (by omega)]
  change ¬ (initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112) at outside
  omega

def mapFullCount (call : Call) (capacity : Word) : Nat :=
  toInsertCount call + (call.freshInsert capacity).count + 13

set_option maxHeartbeats 4000000 in
/-- With no spare map slot, the sorted-map insertion returns FULL, and the
caller returns FULL after writing only its stack. -/
theorem Prefix.runMapFull {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (full : call.length = capacity) :
    ∃ final, Riscfree.RV32.run (mapFullCount call capacity) original = some final ∧
      final.regs.get? Register.PC = some ret ∧
      final.regs.get? Register.x10 = some (1#32) ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, ¬ (stackAllocation initial.sp).Contains byte → final.mem[byte]? = original.mem[byte]? := by
  obtain ⟨caller, ran, facts⟩ := toInsert premises.frame premises.arguments premises.map premises.nonempty
    premises.fresh
  obtain ⟨_, map, stack⟩ := premises.insertStorage (caller := caller) layout
  have fits := layout.stack.fits
  have callPremises : FullCall base ret original initial caller call capacity := {
    outer := premises.frame
    calling := facts
    fresh := premises.fresh
    full := full
    sorted := sorted
    ordered := ordered
    callee := premises.environment layout facts
    header := map.insertHeader
    stack := by rw [facts.sp]; exact stackForInsert stack layout.apart layout.map.lengthFits
    keys := fun _ => map.searchKeys
    codeOutside := fun byte low high => codeOutsideCallee layout facts byte
      ((layout.apart.code _ (List.mem_cons_self ..)).2.2.2.2 byte ⟨low, high⟩) }
  obtain ⟨returned, called, s6, s7, s8, s9, s10, kept⟩ := callPremises.run
  let last := Empty.restore initial { returned with a0 := 1, a1 := 1 } (ret - base)
  let memory := afterCallee original initial caller
  refine ⟨sync base { original with mem := memory } last, ?_, ?_, ?_, ?_, ?_⟩
  · have beginning : run (toInsertCount call) original =
        some (sync base { original with mem := Empty.pushed original.mem initial } caller) :=
      (congrArg (run (toInsertCount call)) premises.frame.entry).trans ran
    rw [show mapFullCount call capacity = toInsertCount call + ((call.freshInsert capacity).count + 13) by
      unfold mapFullCount; omega, runAdd, beginning, Option.bind_some]
    exact called
  · exact Empty.returnPc (base := base) { original with mem := memory } last rfl
  · exact readReg_succ.mp (syncRead (base := base) (frame := { original with mem := memory }) last
      (index := 10) (by decide))
  · exact Empty.restoreRegistersCalls premises.frame.entry memory
      { returned with a0 := 1, a1 := 1 } (ret - base) ⟨s6, s7, s8, s9, s10⟩
  · intro byte outside
    rw [syncMem]
    apply kept byte
    change ¬ (initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112) at outside
    omega

/-! A spare map slot: the insertion succeeds, and the caller writes the
scratch header and calls the deletion helper. -/

/-- Through the insertion, the success branch, the header stores, and the call. -/
def toHelperCount (call : Call) (capacity : Word) : Nat :=
  toInsertCount call + (call.freshInsert capacity).count + 11

structure HelperCalling (base : Word) (initial : Snapshot) (call : Call) (state : Snapshot) : Prop where
  pc : state.pc = helperOffset
  sp : state.sp = Empty.frameBase initial.sp
  ra : state.ra = base + 0xfc#32
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

theorem HelperCalling.arguments {base : Word} {initial caller : Snapshot}
    {call : Call} {capacity low high : Word} (facts : HelperCalling base initial call caller) :
    HelperEntry.Arguments (helperView caller 0) (call.freshHelper capacity initial low high) :=
  ⟨facts.mapRef, facts.cache, facts.start, facts.stop, facts.keys⟩

/-- A byte outside the outer stack, the length word, and the map keeps its
entry value through the insertion. -/
theorem Prefix.insertionKeeps {base ret : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity : Word} {after : ByteMemory}
    (premises : Prefix base ret original initial call)
    (reached : Calling base initial call caller)
    (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (Empty.pushed original.mem initial) caller.sp (insertView caller)) after)
    (byte : Nat) (outsideStack : ¬ (stackAllocation initial.sp).Contains byte)
    (outsideLength : ¬ (mapLengthWord call).Contains byte)
    (outsideMap : ¬ (mapAllocation call capacity).Contains byte)
    (fit : 112 ≤ initial.sp.toNat) :
    after[byte]? = original.mem[byte]? := by
  have spNat : caller.sp.toNat = initial.sp.toNat - 48 := by rw [reached.sp, frameNat initial.sp (by omega)]
  have fits : 32 ≤ (insertView caller).sp.toNat := by
    change 32 ≤ caller.sp.toNat
    omega
  change ¬ (initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112) at outsideStack
  have changedMap := (result.2.2 newKey (Nonempty.Call.freshVectorValid capacity spare)).2.2.2.2
  have lengthApart : byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte := by
    change ¬ (call.header.toNat + 4 ≤ byte ∧ byte < call.header.toNat + 4 + 4) at outsideLength
    omega
  have entriesApart :
      byte < (call.freshInsert capacity).vector.slot (call.freshInsert capacity).vector.index.toNat ∨
      (call.freshInsert capacity).vector.slot (call.length.toNat + 1) ≤ byte := by
    change ¬ (call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat) at outsideMap
    change byte < call.data.toNat + 8 * (call.freshInsert capacity).vector.index.toNat ∨
      call.data.toNat + 8 * (call.length.toNat + 1) ≤ byte
    omega
  refine (changedMap byte lengthApart entriesApart).trans
    ((SortedMap.Insert.pushedOutside _ (insertView caller) fits byte (by
      change byte < caller.sp.toNat - 32 ∨ caller.sp.toNat ≤ byte
      omega)).trans ?_)
  exact Empty.pushedOutside _ _ premises.frame.frameFits byte (by unfold Empty.OutsideFrame; omega)

/-- The outer frame's words at and above the insertion's caller stack pointer
survive the insertion. -/
theorem frameWordKept {base : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity : Word} {after : ByteMemory}
    (reached : Calling base initial call caller)
    (spare : call.length.toNat < capacity.toNat)
    (newKey : ¬ (call.freshInsert capacity).replaces)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (Empty.pushed original.mem initial) caller.sp (insertView caller)) after)
    (layout : StackSpace original initial.sp) (apart : (mapHeader call).Disjoint (stackAllocation initial.sp))
    (mapApart : (mapAllocation call capacity).Disjoint (stackAllocation initial.sp))
    (byte : Nat) (low : initial.sp.toNat - 48 ≤ byte) (high : byte < initial.sp.toNat) :
    after[byte]? = (Empty.pushed original.mem initial)[byte]? := by
  have fit := layout.fits
  have spNat : caller.sp.toNat = initial.sp.toNat - 48 := by rw [reached.sp, frameNat initial.sp (by omega)]
  have fits : 32 ≤ (insertView caller).sp.toNat := by
    change 32 ≤ caller.sp.toNat
    omega
  have atStack : (stackAllocation initial.sp).Contains byte := by
    change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
    omega
  have changedMap := (result.2.2 newKey (Nonempty.Call.freshVectorValid capacity spare)).2.2.2.2
  have lengthApart : byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte := by
    have outside := apart.symm byte atStack
    change ¬ (call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12) at outside
    omega
  have entriesApart :
      byte < (call.freshInsert capacity).vector.slot (call.freshInsert capacity).vector.index.toNat ∨
      (call.freshInsert capacity).vector.slot (call.length.toNat + 1) ≤ byte := by
    have outside := mapApart.symm byte atStack
    have position := (call.freshInsert capacity).position_le
    change ¬ (call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat) at outside
    change byte < call.data.toNat + 8 * (call.freshInsert capacity).vector.index.toNat ∨
      call.data.toNat + 8 * (call.length.toNat + 1) ≤ byte
    rw [SortedMap.Insert.Call.vectorIndex]
    change (call.freshInsert capacity).position ≤ call.length.toNat at position
    omega
  exact (changedMap byte lengthApart entriesApart).trans
    (SortedMap.Insert.pushedOutside _ (insertView caller) fits byte (by
      change byte < caller.sp.toNat - 32 ∨ caller.sp.toNat ≤ byte
      omega))

/-- After a successful insertion, the caller stores the scratch header and
calls the helper in eleven instructions. -/
theorem afterInsert {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage InsertTable.instructions base { original with mem := memory })
    (state : Snapshot) (atReturn : state.pc = 0xa0#32 ∨ state.pc = 0xd0#32) (success : state.a0 = 0#32)
    (data : Writable original (state.sp + 8#32)) (length : Writable original (state.sp + 12#32))
    (capacity : Writable original (state.sp + 16#32))
    (codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      ∀ write ∈ scratchWrites state, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte) :
    run 11 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := writeWords memory (scratchWrites state) }
        { state with
          pc := helperOffset, ra := base + 0xfc#32, a0 := state.sp + 4#32, a1 := state.s0,
          a2 := state.s2, a3 := state.s1, a4 := state.sp + 8#32 }) := by
  let prefixMemory (count : Nat) : ByteMemory := writeWords memory ((scratchWrites state).take count)
  have atPartial (count : Nat) : CodeImage InsertTable.instructions base { original with mem := prefixMemory count } :=
    image.withMemory (prefixMemory count) fun byte low high =>
      writeWordsOutside _ _ byte fun write member => codeApart byte low high write (List.mem_of_mem_take member)
  have entered : step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } { state with pc := 0xd4#32 }) := by
    rcases atReturn with gap | first
    · simpa only [if_pos success] using stepa0 machine image state gap
    · simpa only [if_pos success] using stepd0 machine image state first
  refine runStep entered ?_
  refine runStep (stepd4 machine image _ rfl data) ?_
  refine runStep (stepd8 machine (atPartial 1) _ rfl length) ?_
  refine runStep (stepdc machine (atPartial 2) _ rfl capacity) ?_
  refine runStep (stepe0 machine (atPartial 3) _ rfl) ?_
  refine runStep (stepe4 machine (atPartial 3) _ rfl) ?_
  refine runStep (stepe8 machine (atPartial 3) _ rfl) ?_
  refine runStep (stepec machine (atPartial 3) _ rfl) ?_
  refine runStep (stepf0 machine (atPartial 3) _ rfl) ?_
  refine runStep (stepf4 machine (atPartial 3) _ rfl) ?_
  exact runStep (stepf8 machine (atPartial 3) _ rfl rfl) rfl

set_option maxHeartbeats 4000000 in
/-- The successful insertion and the call to the deletion helper. The
memory is the insertion's result plus the scratch header. -/
theorem Prefix.toHelper {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat) :
    ∃ (caller state : Snapshot) (after : ByteMemory),
      run (toHelperCount call capacity) original =
        some (sync base { original with mem := freshStored initial after } state) ∧
      Calling base initial call caller ∧ HelperCalling base initial call state ∧
      SortedMap.Insert.finalMemory (call.freshInsert capacity)
        (SortedMap.Insert.pushed (Empty.pushed original.mem initial) caller.sp (insertView caller)) after := by
  let insertion := call.freshInsert capacity
  let memory := Empty.pushed original.mem initial
  let before : Machine := { original with mem := memory }
  have nonReplace := Nonempty.Call.freshDoesNotReplace capacity
    (Nonempty.Call.freshKeyAbsent (Call.freshHasGap premises.fresh) sorted ordered)
  have succeeded := Nonempty.freshInsertStatus spare nonReplace
  obtain ⟨caller, toCall, facts⟩ := toInsert premises.frame premises.arguments premises.map premises.nonempty
    premises.fresh
  let entered := sync base before caller
  have beginning : run (toInsertCount call) original = some entered :=
    (congrArg (run (toInsertCount call)) premises.frame.entry).trans toCall
  obtain ⟨code, map, stack⟩ := premises.insertStorage (caller := caller) layout
  have correctStack : SortedMap.Insert.Stack (mapInsertBase base) entered insertion caller.sp := by
    rw [facts.sp]
    exact stackForInsert stack layout.apart layout.map.lengthFits
  have atCall : entered = sync (mapInsertBase base) entered { insertView caller with pc := 0 } :=
    facts.insertEntry
  obtain ⟨tail, after, ran, pc, status, ra, sp, s0, s1, s2, s3, result⟩ :=
    SortedMap.Insert.sortedMapInsertSailRun (mapInsertBase base) (base + insertReturn call)
      entered insertion (insertView caller) atCall facts.header facts.start facts.stop
      (premises.environment layout facts) map.insertHeader correctStack (fun _ _ => map.searchKeys)
      (fun impossible => (nonReplace impossible).elim) (fun _ _ => OuterLayout.MapStorage.insertBuffer map layout.apart spare)
  let continued := insertReturned (insertReturn call) caller tail
  let afterMachine : Machine := { original with mem := after }
  have target : base + insertReturn call = mapInsertBase base + tail.pc := by
    rw [pc, BitVec.add_comm (mapInsertBase base), BitVec.sub_add_cancel]
  have switch := insertReturnedSync base (insertReturn call) afterMachine caller tail target
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
  have fits := layout.stack.fits
  have frameFits := premises.frame.frameFits
  have outerCode : CodeImage InsertTable.instructions base afterMachine :=
    layout.code.entry.withMemory after fun byte low high => by
      have safe := layout.apart.code _ (List.mem_cons_self ..)
      exact premises.insertionKeeps facts spare nonReplace resultAtCaller byte
        (safe.2.2.2.2 byte ⟨low, high⟩) (fun length => safe.1 byte ⟨low, high⟩ (lengthInHeader length))
        (safe.2.1 byte ⟨low, high⟩) fits
  have statusZero : continued.a0 = 0#32 := status.trans succeeded
  have returnSite : continued.pc = 0xa0#32 ∨ continued.pc = 0xd0#32 := by
    change insertReturn call = 0xa0#32 ∨ insertReturn call = 0xd0#32
    unfold insertReturn
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have restoredSp : continued.sp = Empty.frameBase initial.sp := sp.trans facts.sp
  have restoredCache : continued.s0 = initial.a1 := s0.trans facts.cached
  have restoredStart : continued.s2 = call.start := s2.trans facts.savedStart
  have restoredStop : continued.s1 = call.stop := s1.trans facts.savedStop
  have restoredCapacity : continued.s3 = initial.a5 := s3.trans facts.scratchCapacity
  have restoredData : continued.s4 = initial.a4 := facts.scratchData
  have writes : scratchWrites continued = scratchWrites { initial with
      sp := Empty.frameBase initial.sp, s4 := initial.a4, s3 := initial.a5 } := by
    simp only [scratchWrites, restoredSp, restoredData, restoredCapacity]
  have toHelper := afterInsert premises.frame.mode.toMachineState outerCode continued returnSite statusZero
    (by rw [restoredSp]; exact premises.writable 8 (by decide))
    (by rw [restoredSp]; exact premises.writable 12 (by decide))
    (by rw [restoredSp]; exact premises.writable 16 (by decide))
    (by
      intro byte low high write member
      rw [writes] at member
      have outside := premises.frame.codeOutside byte low high
      unfold Empty.OutsideFrame at outside
      simp only [scratchWrites, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change byte < (Empty.frameBase initial.sp + 8#32).toNat ∨ (Empty.frameBase initial.sp + 8#32).toNat + 4 ≤ byte
        rw [Empty.frameAddress frameFits 8#32 (by decide)]
        change byte < initial.sp.toNat - 48 + 8 ∨ initial.sp.toNat - 48 + 8 + 4 ≤ byte
        omega
      · change byte < (Empty.frameBase initial.sp + 12#32).toNat ∨ (Empty.frameBase initial.sp + 12#32).toNat + 4 ≤ byte
        rw [Empty.frameAddress frameFits 12#32 (by decide)]
        change byte < initial.sp.toNat - 48 + 12 ∨ initial.sp.toNat - 48 + 12 + 4 ≤ byte
        omega
      · change byte < (Empty.frameBase initial.sp + 16#32).toNat ∨ (Empty.frameBase initial.sp + 16#32).toNat + 4 ≤ byte
        rw [Empty.frameAddress frameFits 16#32 (by decide)]
        change byte < initial.sp.toNat - 48 + 16 ∨ initial.sp.toNat - 48 + 16 + 4 ≤ byte
        omega)
  rw [writes] at toHelper
  let calling : Snapshot :=
    { continued with
      pc := helperOffset, ra := base + 0xfc#32, a0 := continued.sp + 4#32, a1 := continued.s0,
      a2 := continued.s2, a3 := continued.s1, a4 := continued.sp + 8#32 }
  refine ⟨caller, calling, after, ?_, facts, ?_, resultAtCaller⟩
  · rw [toHelperCount, runAdd, runAdd, beginning, Option.bind_some, insertionRan, Option.bind_some]
    exact toHelper
  · exact ⟨rfl, restoredSp, rfl, congrArg (· + 4#32) restoredSp, restoredCache, restoredStart, restoredStop,
      congrArg (· + 8#32) restoredSp, restoredCache, restoredStop, restoredStart, facts.untouched⟩

end Riscfree.RangeInsert.Bounded.FreshPath
