import RangeInsert.Bounded.FreshInsert
import RangeInsert.Bounded.ExtensionRun
import RangeInsert.Nonempty.Fresh.Finish

/-! The bounded fresh path from the helper call to the caller's return.
The helper's input layout comes from the insertion result plus the scratch
header. An OK helper status adds the input's width to the cache and returns
OK; a FULL status takes the common OOM return. -/

namespace Riscfree.RangeInsert.Bounded.FreshPath

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Pair PairAt Readable Writable)
open Empty (Snapshot)
open Entry
open EntryEmpty (Frame)
open EntryFresh (Calling)
open EntryExtension (outsideOfHelperFootprint)
open OuterLayout
open OuterView (helperView helperReturned helperReturnedSync)
open OuterHelper (HelperInput helperAsOuter)
open Nonempty (Call Arguments Span MapStorage CacheStorage StackSpace mapHeader mapAllocation cacheWords
  stackAllocation mapLengthWord lengthInHeader stackDisjointOuter mappedTransfer insertView
  freshStored scratchHeaderWords pushedMapReference WritableByte freshLow freshHigh freshCacheMemory
  freshCacheOutside freshCacheWords cacheHighAddress)

set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

private theorem frameNat (sp : Word) (fits : 48 ≤ sp.toNat) : (Empty.frameBase sp).toNat = sp.toNat - 48 := by
  have zero := Empty.frameAddress (sp := sp) fits 0#32 (by decide)
  simpa only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] using zero

/-- Outside the outer stack, the scratch-header stores do not change memory. -/
theorem storedOutsideStack (initial : Snapshot) (memory : ByteMemory) (fits : 112 ≤ initial.sp.toNat)
    (byte : Nat) (outside : ¬ (stackAllocation initial.sp).Contains byte) :
    (freshStored initial memory)[byte]? = memory[byte]? := by
  apply freshStoredOutside initial memory (by omega) byte
  change ¬ (initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112) at outside
  omega

/-- The insertion result plus the scratch header supplies the fresh helper's
input layout. -/
theorem Prefix.helperInput {base ret : Word} {original : Machine}
    {initial caller state : Snapshot} {call : Call} {capacity low high : Word} {after : ByteMemory}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (reached : Calling base initial call caller)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (Empty.pushed original.mem initial) caller.sp (insertView caller)) after) :
    HelperInput base (sync base { original with mem := freshStored initial after } state) initial
      (call.freshHelper capacity initial low high) capacity := by
  let stored := freshStored initial after
  let background : Machine := { original with mem := stored }
  let entered := sync base background state
  let helperCall := call.freshHelper capacity initial low high
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have noReplace := Nonempty.Call.freshDoesNotReplace capacity
    (Nonempty.Call.freshKeyAbsent (Call.freshHasGap premises.fresh) sorted ordered)
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame (base := base) (frame := background) state Register.pma_regions
      (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have bytes : entered.mem = stored := syncMem (base := base) (frame := background) state
  have apart := layout.apart
  have fit := layout.stack.fits
  have frameFits := premises.frame.frameFits
  have storedKept (byte : Nat) (outside : ¬ (stackAllocation initial.sp).Contains byte) :
      stored[byte]? = after[byte]? := storedOutsideStack initial after fit byte outside
  have keeps (byte : Nat) (outsideStack : ¬ (stackAllocation initial.sp).Contains byte)
      (outsideLength : ¬ (mapLengthWord call).Contains byte)
      (outsideMap : ¬ (mapAllocation call capacity).Contains byte) : stored[byte]? = original.mem[byte]? :=
    (storedKept byte outsideStack).trans
      (premises.insertionKeeps reached spare noReplace result byte outsideStack outsideLength outsideMap fit)
  have code : CodeImages base background := layout.code.withMemory stored fun span member byte inside =>
    have safe := apart.code span member
    keeps byte (safe.2.2.2.2 byte inside) (fun length => safe.1 byte inside (lengthInHeader length))
      (safe.2.1 byte inside)
  have keepCache {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (cacheWords initial.a1).Contains byte) :
      WordAt entered.mem address value := by
    rw [bytes]
    exact word.congr fun byte low high => by
      have onCache := inside byte low high
      exact keeps byte (apart.cacheStack byte onCache)
        (fun length => apart.headerCache.symm byte onCache (lengthInHeader length)) (apart.mapCache.symm byte onCache)
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
  -- The insertion's map words survive the scratch-header stores.
  have old := layout.map
  obtain ⟨data, length, capacityWord, entries, _⟩ := result.2.2 noReplace
    (Nonempty.Call.freshVectorValid capacity spare)
  have newLength := call.freshHelperLength capacity initial low high spare
  have headerKept {address : Nat} {value : Word} (word : WordAt after address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (mapHeader call).Contains byte) :
      WordAt entered.mem address value := by
    rw [bytes]
    exact word.congr fun byte lo hi => storedKept byte (apart.headerStack byte (inside byte lo hi))
  have headerPart (offset : Nat) (small : offset ≤ 8) (byte : Nat)
      (lo : call.header.toNat + offset ≤ byte) (hi : byte < call.header.toNat + offset + 4) :
      (mapHeader call).Contains byte := by
    change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
    omega
  have map : MapStorage entered (helperAsOuter helperCall) capacity := by
    refine {
      headerFits := old.headerFits
      allocationFits := old.allocationFits
      dataNonnull := old.dataNonnull
      lengthFits := ?_
      headerReadable := fun offset member => mappedTransfer (old.headerReadable offset member) regions
      lengthWritable := mappedTransfer old.lengthWritable regions
      dataWord := headerKept data (headerPart 0 (by decide))
      lengthWord := headerKept length (headerPart 4 (by decide))
      capacityWord := headerKept capacityWord (headerPart 8 (by decide))
      live := ?_
      pairsReadable := fun index inside => ⟨mappedTransfer (old.pairsReadable index inside).1 regions,
        mappedTransfer (old.pairsReadable index inside).2 regions⟩
      pairsWritable := fun index inside => ⟨mappedTransfer (old.pairsWritable index inside).1 regions,
        mappedTransfer (old.pairsWritable index inside).2 regions⟩ }
    · change helperCall.length.toNat ≤ capacity.toNat
      rw [newLength]
      omega
    · intro index inside
      change index < helperCall.length.toNat at inside
      rw [newLength] at inside
      have pair := entries index inside
      have slotSame := (call.freshInsert capacity).slotSame index
      have allocated (byte : Nat) (lo : (call.freshInsert capacity).vector.slot index ≤ byte)
          (hi : byte < (call.freshInsert capacity).vector.slot index + 8) :
          (mapAllocation call capacity).Contains byte := by
        change call.data.toNat + 8 * index ≤ byte at lo
        change byte < call.data.toNat + 8 * index + 8 at hi
        change call.data.toNat ≤ byte ∧ byte < call.data.toNat + 8 * capacity.toNat
        omega
      change PairAt entered.mem ((call.freshInsert capacity).search.slot index)
        ((call.freshInsert capacity).vector.result index)
      rw [← slotSame, bytes]
      exact ⟨pair.1.congr fun byte lo hi => storedKept byte (apart.mapStack byte (allocated byte lo (by omega))),
        pair.2.congr fun byte lo hi =>
          storedKept byte (apart.mapStack byte (allocated byte (by omega) (by omega)))⟩
  have arrived : InitialLayout base entered initial (helperAsOuter helperCall) capacity low high :=
    ⟨code.atSync state, map, layout.scratch.transfer regions, cache, layout.stack.transfer regions, geometry⟩
  have selected := Nonempty.Call.freshHelperSelected (initial := initial) (low := low) (high := high)
    sorted spare noReplace
  have found : helperCall.position < helperCall.length.toNat := by
    change helperCall.position = (call.freshInsert capacity).position at selected
    change helperCall.length.toNat = call.length.toNat + 1 at newLength
    rw [selected, newLength]
    have bound := (call.freshInsert capacity).position_le
    change (call.freshInsert capacity).position ≤ call.length.toNat at bound
    omega
  obtain ⟨scratchData, scratchLength, scratchCapacity⟩ := scratchHeaderWords initial after frameFits
  have mapRefNat : (Empty.frameBase initial.sp + 4#32).toNat = initial.sp.toNat - 48 + 4 :=
    Empty.frameAddress frameFits 4#32 (by decide)
  have reference : WordAt entered.mem (Empty.frameBase initial.sp + 4#32).toNat call.header := by
    have pushedWord := pushedMapReference initial original.mem
    rw [premises.arguments.header] at pushedWord
    rw [bytes]
    refine pushedWord.congr fun byte lo hi => ?_
    rw [mapRefNat] at lo hi
    refine (freshStoredOutside initial after frameFits byte (Or.inl (by omega))).trans ?_
    exact frameWordKept reached spare noReplace result layout.stack apart.headerStack apart.mapStack byte
      (by omega) (by omega)
  refine ⟨arrived, rfl, rfl, rfl, reference, ?_, ?_, ?_, found⟩
  · rw [bytes]; exact scratchData
  · rw [bytes]; exact scratchLength
  · rw [bytes]; exact scratchCapacity

/-- The cache registers after the fresh width is added. -/
def cacheState (state : Snapshot) (low high : Word) : Snapshot :=
  let distance := state.s1 - state.s2
  { state with
    pc := 0x124#32, a1 := freshLow low distance, a2 := freshHigh low high distance
    a3 := Step.lessWord (freshLow low distance) 1#32 }

set_option maxHeartbeats 4000000 in
/-- From the helper's return site with an OK status, the caller adds the
input's width to the cache, writes both words, and returns. -/
theorem finish {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) {memory : ByteMemory}
    (image : CodeImage InsertTable.instructions base { original with mem := memory })
    (state : Snapshot) (atReturn : state.pc = 0xfc#32) (ok : state.a0 = 0#32)
    (lowered : state.sp = Empty.frameBase initial.sp)
    {low high : Word} (cache : CacheStorage { original with mem := memory } state.s0 low high)
    (codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      ¬ (cacheWords state.s0).Contains byte)
    (saved : ∀ (offset : Word) (value : Word),
      offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word) →
      WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value →
      WordAt (freshCacheMemory memory state.s0 (freshLow low (state.s1 - state.s2))
        (freshHigh low high (state.s1 - state.s2))) (Empty.frameBase initial.sp + offset).toNat value) :
    let distance := state.s1 - state.s2
    let stored := freshCacheMemory memory state.s0 (freshLow low distance) (freshHigh low high distance)
    run 22 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := stored }
        (Empty.restore initial { cacheState state low high with pc := 0x1a4 } (returnAddress - base))) := by
  intro distance stored
  let calculated := cacheState state low high
  have machine := frame.mode.toMachineState
  have test := stepfc machine image state atReturn
  rw [if_pos ok] at test
  have highNat := cacheHighAddress cache.fits
  have arithmetic : run 10 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } calculated) := by
    refine runStep test ?_
    refine runStep (step100 machine image _ rfl low (mappedTransfer cache.readable.1 rfl) cache.low) ?_
    refine runStep (step104 machine image _ rfl high (mappedTransfer cache.readable.2 rfl)
      (by rw [highNat]; exact cache.high)) ?_
    refine runStep (step108 machine image _ rfl) ?_
    refine runStep (step10c machine image _ rfl) ?_
    refine runStep (step110 machine image _ rfl) ?_
    refine runStep (step114 machine image _ rfl) ?_
    refine runStep (step118 machine image _ rfl) ?_
    refine runStep (step11c machine image _ rfl) ?_
    exact runStep (step120 machine image _ rfl) rfl
  have lowApart (byte : Nat) (low : base.toNat ≤ byte)
      (high : byte < base.toNat + 4 * InsertTable.instructions.length) :
      byte < state.s0.toNat ∨ state.s0.toNat + 4 ≤ byte := by
    have apart := codeApart byte low high
    change ¬ (state.s0.toNat ≤ byte ∧ byte < state.s0.toNat + 8) at apart
    omega
  have middleImage := image.withMemory (storeWord memory state.s0.toNat calculated.a1)
    (fun byte low high => storeWordOutside _ _ _ _ (lowApart byte low high))
  have finalImage : CodeImage InsertTable.instructions base { original with mem := stored } :=
    image.withMemory stored fun byte low high => freshCacheOutside memory state.s0
      calculated.a1 calculated.a2 byte cache.fits (codeApart byte low high)
  have stores : run 3 (sync base { original with mem := memory } calculated) =
      some (sync base { original with mem := stored } { calculated with pc := 0x1a4 }) := by
    refine runStep (step124 machine image _ rfl (mappedTransfer cache.writable.1 rfl)) ?_
    refine runStep (step128 machine middleImage _ rfl (mappedTransfer cache.writable.2 rfl)) ?_
    exact runStep (step12c machine finalImage _ rfl) rfl
  have epilogue := frame.epilogueFrom (machine.withMemory stored) finalImage
    (fun offset member => mappedTransfer (frame.readable offset member) rfl)
    saved { calculated with pc := 0x1a4 } rfl lowered
  rw [show 22 = 10 + 3 + 9 by decide, runAdd, runAdd, arithmetic, Option.bind_some, stores, Option.bind_some]
  exact epilogue

/-- From the helper's return site with a FULL status, the common OOM return. -/
theorem returnFull {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (codeKept : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      memory[byte]? = original.mem[byte]?)
    (savedKept : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      memory[byte]? = (Empty.pushed original.mem initial)[byte]?)
    (state : Snapshot) (pc : state.pc = 0xfc#32) (full : state.a0 ≠ 0#32)
    (sp : state.sp = Empty.frameBase initial.sp) :
    run 11 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        (Empty.restore initial { state with pc := 0x1a4, a0 := 1 } (returnAddress - base))) := by
  have machine := frame.mode.toMachineState.withMemory memory
  have image : CodeImage InsertTable.instructions base { original with mem := memory } :=
    frame.code.withMemory memory codeKept
  have saved (offset value : Word) (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word))
      (contents : WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value) :
      WordAt memory (Empty.frameBase initial.sp + offset).toNat value := by
    have bound : 20 ≤ offset.toNat ∧ offset.toNat ≤ 44 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine contents.congr fun byte first last => ?_
    rw [Empty.frameAddress frame.frameFits offset bound.2] at first last
    have fits := frame.frameFits
    exact savedKept byte (by omega) (by omega)
  have test := stepfc machine image state pc
  rw [if_neg full] at test
  refine runStep test ?_
  refine runStep (step1a0 machine image _ rfl) ?_
  exact frame.epilogueFrom machine image (fun offset member => mappedTransfer (frame.readable offset member) rfl)
    saved _ rfl sp

private theorem returnTarget (base : Word) (first last : Helper.Snapshot) :
    base + 0xfc#32 = helperBase base +
      (HelperFrame.restore first last (base + 0xfc#32 - helperBase base)).pc := by
  change base + 0xfc#32 = helperBase base + (base + 0xfc#32 - helperBase base)
  rw [BitVec.add_comm (helperBase base), BitVec.sub_add_cancel]

/-- The memory and register facts at the helper's call site, shared by both
outcomes. -/
private theorem Prefix.called {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat) :
    ∃ (caller atCall : Snapshot) (after : ByteMemory),
      run (toHelperCount call capacity) original =
        some (sync base { original with mem := freshStored initial after } atCall) ∧
      Calling base initial call caller ∧ HelperCalling base initial call atCall ∧
      SortedMap.Insert.finalMemory (call.freshInsert capacity)
        (SortedMap.Insert.pushed (Empty.pushed original.mem initial) caller.sp (insertView caller)) after ∧
      HelperInput base (sync base { original with mem := freshStored initial after } atCall) initial
        (call.freshHelper capacity initial low high) capacity := by
  obtain ⟨caller, atCall, after, ran, reached, regs, result⟩ := premises.toHelper layout spare sorted ordered
  exact ⟨caller, atCall, after, ran, reached, regs, result,
    premises.helperInput layout reached spare sorted ordered result⟩

/-- At the helper's entry, the code, the saved registers, and every byte
outside the writable regions still hold their values as computed from the
insertion result. -/
private theorem Prefix.storedFacts {base ret : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity low high : Word} {after : ByteMemory}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (reached : Calling base initial call caller)
    (spare : call.length.toNat < capacity.toNat) (noReplace : ¬ (call.freshInsert capacity).replaces)
    (result : SortedMap.Insert.finalMemory (call.freshInsert capacity)
      (SortedMap.Insert.pushed (Empty.pushed original.mem initial) caller.sp (insertView caller)) after) :
    (∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      (freshStored initial after)[byte]? = original.mem[byte]?) ∧
    (∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      (freshStored initial after)[byte]? = (Empty.pushed original.mem initial)[byte]?) ∧
    (∀ byte, ¬ (stackAllocation initial.sp).Contains byte → ¬ (mapLengthWord call).Contains byte →
      ¬ (mapAllocation call capacity).Contains byte → (freshStored initial after)[byte]? = original.mem[byte]?) := by
  have fit := layout.stack.fits
  have keeps (byte : Nat) (outsideStack : ¬ (stackAllocation initial.sp).Contains byte)
      (outsideLength : ¬ (mapLengthWord call).Contains byte)
      (outsideMap : ¬ (mapAllocation call capacity).Contains byte) :
      (freshStored initial after)[byte]? = original.mem[byte]? :=
    (storedOutsideStack initial after fit byte outsideStack).trans
      (premises.insertionKeeps reached spare noReplace result byte outsideStack outsideLength outsideMap fit)
  refine ⟨fun byte first last => ?_, fun byte first last => ?_, keeps⟩
  · have safe := layout.apart.code _ (List.mem_cons_self ..)
    exact keeps byte (safe.2.2.2.2 byte ⟨first, last⟩)
      (fun length => safe.1 byte ⟨first, last⟩ (lengthInHeader length)) (safe.2.1 byte ⟨first, last⟩)
  · refine (freshStoredOutside initial after premises.frame.frameFits byte (Or.inr (by omega))).trans ?_
    exact frameWordKept reached spare noReplace result layout.stack layout.apart.headerStack
      layout.apart.mapStack byte (by omega) last

/-- The fresh path's live map and cache after an OK return. -/
structure Result (initial : Snapshot) (call : Call) (helperCall : DeleteExtra.Call) (final : ByteMemory) :
    Prop where
  length : WordAt final (call.header.toNat + 4)
    (BitVec.ofNat 32 (helperCall.length.toNat - helperCall.acceptCount))
  entries : ∀ index < helperCall.length.toNat - helperCall.acceptCount,
    PairAt final (helperCall.search.slot index)
      (DeleteExtra.drained (helperCall.after helperCall.acceptCount) helperCall.position helperCall.acceptCount index)
  cacheLow : WordAt final initial.a1.toNat
    (freshLow (helperCall.finalLow helperCall.acceptCount) (call.stop - call.start))
  cacheHigh : WordAt final (initial.a1.toNat + 4)
    (freshHigh (helperCall.finalLow helperCall.acceptCount) (helperCall.finalHigh helperCall.acceptCount)
      (call.stop - call.start))

def successCount (call : Call) (capacity : Word) (helperCall : DeleteExtra.Call) : Nat :=
  toHelperCount call capacity + HelperRun.successCount helperCall capacity helperCall.acceptCount + 22

set_option maxHeartbeats 6000000 in
/-- With a spare map slot and enough scratch, the fresh path returns OK
with the canonical result in memory. -/
theorem Prefix.runSuccess {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (room : (call.freshHelper capacity initial low high).acceptCount ≤ initial.a5.toNat) :
    let helperCall := call.freshHelper capacity initial low high
    ∃ final, Riscfree.RV32.run (successCount call capacity helperCall) original = some final ∧
      final.regs.get? Register.PC = some ret ∧
      final.regs.get? Register.x10 = some (0#32) ∧
      Result initial call helperCall final.mem ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
  intro helperCall
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have noReplace := Nonempty.Call.freshDoesNotReplace capacity
    (Nonempty.Call.freshKeyAbsent (Call.freshHasGap premises.fresh) sorted ordered)
  obtain ⟨caller, atCall, after, toCall, reached, regs, insertEffects, input⟩ :=
    premises.called layout spare sorted ordered
  let stored := freshStored initial after
  let background : Machine := { original with mem := stored }
  let entered := sync base background atCall
  obtain ⟨storedCode, storedSaved, storedKeeps⟩ := premises.storedFacts layout reached spare noReplace insertEffects
  have candidateSorted := Nonempty.Call.freshHelperSorted (initial := initial) (low := low) (high := high)
    sorted spare noReplace
  have increasing := Nonempty.Call.keysIncreasing (call := helperAsOuter helperCall) candidateSorted
  have mode : MachineState background := premises.frame.mode.toMachineState.withMemory stored
  have helperPremises := input.premises mode (by decide : (0xfc#32).toNat % 4 = 0)
    regs.pc regs.sp regs.ra regs.arguments room increasing
  obtain ⟨tail, helperMemory, ran, resultAtCall⟩ := helperPremises.run
  let helperFinal := HelperFrame.restore (helperView atCall 0) { tail with a0 := 0 }
    (base + 0xfc#32 - helperBase base)
  have callBytes : entered.mem = stored := syncMem (base := base) (frame := background) atCall
  have effects : DeleteExtra.ResultMemory (Empty.frameBase initial.sp) helperCall scratch
      helperCall.acceptCount stored helperMemory := by
    have sp : (helperView atCall 0).sp = Empty.frameBase initial.sp := regs.sp
    rw [← sp, ← callBytes]
    exact resultAtCall
  let helperBackground : Machine := { original with mem := helperMemory }
  let state := helperReturned 0xfc#32 atCall helperFinal
  have next : Riscfree.RV32.run (HelperRun.successCount helperCall capacity helperCall.acceptCount) entered =
      some (sync base helperBackground state) := by
    rw [ran]
    change some (sync (helperBase base) { sync base background atCall with mem := helperMemory } helperFinal) = _
    rw [syncWithMem base background atCall helperMemory]
    exact congrArg some (helperReturnedSync base (helperBase base) 0xfc#32 helperBackground atCall helperFinal
      (returnTarget base _ _))
  have afterCode : CodeImage InsertTable.instructions base helperBackground :=
    premises.frame.code.withMemory helperMemory fun byte first last =>
      (effects.others byte (input.codeApartAll room byte first last)).trans (storedCode byte first last)
  have cacheAddress : state.s0 = initial.a1 := regs.savedCache
  have start : state.s2 = call.start := regs.savedStart
  have stop : state.s1 = call.stop := regs.savedStop
  let lowWord := helperCall.finalLow helperCall.acceptCount
  let highWord := helperCall.finalHigh helperCall.acceptCount
  have cache : CacheStorage helperBackground state.s0 lowWord highWord := by
    rw [cacheAddress]
    exact ⟨layout.cache.fits,
      ⟨mappedTransfer layout.cache.readable.1 rfl, mappedTransfer layout.cache.readable.2 rfl⟩,
      ⟨mappedTransfer layout.cache.writable.1 rfl, mappedTransfer layout.cache.writable.2 rfl⟩,
      effects.cacheLow, effects.cacheHigh⟩
  have cacheCode : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      ¬ (cacheWords state.s0).Contains byte := by
    rw [cacheAddress]
    intro byte low high
    exact (layout.apart.code _ (List.mem_cons_self ..)).2.2.1 byte ⟨low, high⟩
  let distance := call.stop - call.start
  let returnedLow := freshLow lowWord distance
  let returnedHigh := freshHigh lowWord highWord distance
  let finalMemory := freshCacheMemory helperMemory initial.a1 returnedLow returnedHigh
  have finalOutside (byte : Nat) (apart : ¬ (cacheWords initial.a1).Contains byte) :
      finalMemory[byte]? = helperMemory[byte]? :=
    freshCacheOutside helperMemory initial.a1 returnedLow returnedHigh byte layout.cache.fits apart
  have saved (offset : Word) (value : Word)
      (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word))
      (word : WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value) :
      WordAt (freshCacheMemory helperMemory state.s0 (freshLow lowWord (state.s1 - state.s2))
        (freshHigh lowWord highWord (state.s1 - state.s2))) (Empty.frameBase initial.sp + offset).toNat value := by
    rw [cacheAddress, start, stop]
    have bound : 20 ≤ offset.toNat ∧ offset.toNat ≤ 44 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have address := Empty.frameAddress premises.frame.frameFits offset bound.2
    have fit := layout.stack.fits
    refine word.congr fun byte first last => ?_
    rw [address] at first last
    refine (finalOutside byte ?_).trans ((effects.others byte
      (input.savedApartAll room byte (by omega) (by omega))).trans (storedSaved byte (by omega) (by omega)))
    apply layout.apart.cacheStack.symm byte
    change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
    omega
  have finished := finish premises.frame afterCode state rfl rfl regs.sp cache cacheCode saved
  let finalSnapshot := Empty.restore initial { cacheState state lowWord highWord with pc := 0x1a4 } (ret - base)
  let final := sync base { original with mem := finalMemory } finalSnapshot
  have lastRun : Riscfree.RV32.run 22 (sync base helperBackground state) = some final := by
    dsimp only at finished
    rw [cacheAddress, start, stop] at finished
    exact finished
  have finalBytes : final.mem = finalMemory := syncMem (base := base) (frame := { original with mem := finalMemory }) finalSnapshot
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [successCount, runAdd, runAdd, toCall, Option.bind_some, next, Option.bind_some]
    exact lastRun
  · exact Empty.returnPc (base := base) { original with mem := finalMemory } finalSnapshot rfl
  · exact readReg_succ.mp (syncRead (base := base) (frame := { original with mem := finalMemory }) finalSnapshot
      (index := 10) (by decide))
  · have ⟨cacheLow, cacheHigh⟩ := freshCacheWords helperMemory initial.a1 returnedLow returnedHigh layout.cache.fits
    refine ⟨?_, ?_, finalBytes.symm ▸ cacheLow, finalBytes.symm ▸ cacheHigh⟩
    · refine effects.lengthWord.congr fun byte low high => ?_
      rw [finalBytes]
      apply finalOutside byte
      apply layout.apart.headerCache byte
      change call.header.toNat + 4 ≤ byte at low
      change byte < call.header.toNat + 4 + 4 at high
      change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
      omega
    · intro index inside
      have pair := effects.entries index inside
      have live : index < helperCall.length.toNat := by omega
      have kept (byte : Nat) (low : helperCall.search.slot index ≤ byte)
          (high : byte < helperCall.search.slot index + 8) :
          final.mem[byte]? = helperMemory[byte]? := by
        rw [finalBytes]
        exact finalOutside byte (layout.apart.mapCache byte (input.layout.map.entryContained live low high))
      exact ⟨pair.1.congr fun byte low high => kept byte low (by omega),
        pair.2.congr fun byte low high => kept byte (by omega) (by omega)⟩
  · exact Empty.restoreRegistersCalls premises.frame.entry finalMemory
      { cacheState state lowWord highWord with pc := 0x1a4 } (ret - base) regs.saved
  · intro byte outside
    simp only [WritableByte, not_or] at outside
    obtain ⟨outsideStack, outsideCache, outsideScratch, outsideLength, outsideMap⟩ := outside
    have helperApart : ¬ DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) helperCall scratch
        helperCall.acceptCount byte := by
      intro wrote
      rcases input.footprintRegions room wrote with stack | cache | scratch | header | map
      · apply outsideStack
        have fits := layout.stack.fits
        change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
        omega
      · exact outsideCache cache
      · exact outsideScratch scratch
      · exact outsideLength header
      · exact outsideMap map
    rw [finalBytes]
    exact (finalOutside byte outsideCache).trans ((effects.others byte helperApart).trans
      (storedKeeps byte outsideStack outsideLength outsideMap))

/-- After a FULL return the allocation can be disposed of: the header's data
pointer and capacity are unchanged, and the stored length is within the
capacity. Every byte outside the writable regions keeps its value. -/
structure Disposable (initial : Snapshot) (call : Call) (capacity : Word) (original final : Machine) :
    Prop where
  dataWord : WordAt final.mem call.header.toNat call.data
  capacityWord : WordAt final.mem (call.header.toNat + 8) capacity
  lengthWord : ∃ length : Word, WordAt final.mem (call.header.toNat + 4) length ∧ length.toNat ≤ capacity.toNat
  kept : ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]?

def fullCount (call : Call) (capacity : Word) (helperCall : DeleteExtra.Call) (scratchCapacity : Nat) : Nat :=
  toHelperCount call capacity + HelperRun.fullCount helperCall scratchCapacity + 11

set_option maxHeartbeats 6000000 in
/-- With a spare map slot but too little scratch, the helper returns FULL
and so does the caller. The map holds the inserted range and its original
entries, and the allocation can be disposed of. -/
theorem Prefix.runFull {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : Prefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (short : initial.a5.toNat < (call.freshHelper capacity initial low high).acceptCount) :
    let helperCall := call.freshHelper capacity initial low high
    ∃ final, Riscfree.RV32.run (fullCount call capacity helperCall initial.a5.toNat) original = some final ∧
      final.regs.get? Register.PC = some ret ∧
      final.regs.get? Register.x10 = some (1#32) ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      Disposable initial call capacity original final := by
  intro helperCall
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have noReplace := Nonempty.Call.freshDoesNotReplace capacity
    (Nonempty.Call.freshKeyAbsent (Call.freshHasGap premises.fresh) sorted ordered)
  obtain ⟨caller, atCall, after, toCall, reached, regs, insertEffects, input⟩ :=
    premises.called layout spare sorted ordered
  let stored := freshStored initial after
  let background : Machine := { original with mem := stored }
  let entered := sync base background atCall
  obtain ⟨storedCode, storedSaved, storedKeeps⟩ := premises.storedFacts layout reached spare noReplace insertEffects
  have mode : MachineState background := premises.frame.mode.toMachineState.withMemory stored
  have scanPremises := input.scanPremises mode (by decide : (0xfc#32).toNat % 4 = 0)
    regs.pc regs.sp regs.ra regs.arguments (accepted := initial.a5.toNat) (Nat.le_refl _) (Nat.le_of_lt short)
  obtain ⟨tail, helperMemory, ran, unchanged⟩ := scanPremises.runFull short
  let helperFinal := HelperFrame.restore (helperView atCall 0)
    { tail with a0 := 1, a1 := 1, a2 := tail.s9 } (base + 0xfc#32 - helperBase base)
  have callBytes : entered.mem = stored := syncMem (base := base) (frame := background) atCall
  have sp : (helperView atCall 0).sp = Empty.frameBase initial.sp := regs.sp
  have keptByHelper (byte : Nat)
      (outside : ¬ DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) helperCall scratch
        initial.a5.toNat byte) : helperMemory[byte]? = stored[byte]? := by
    obtain ⟨frameOutside, scanOutside⟩ := outsideOfHelperFootprint outside
    rw [← callBytes]
    exact unchanged byte (sp ▸ frameOutside) scanOutside
  let helperBackground : Machine := { original with mem := helperMemory }
  let state := helperReturned 0xfc#32 atCall helperFinal
  have next : Riscfree.RV32.run (HelperRun.fullCount helperCall initial.a5.toNat) entered =
      some (sync base helperBackground state) := by
    rw [ran]
    change some (sync (helperBase base) { sync base background atCall with mem := helperMemory } helperFinal) = _
    rw [syncWithMem base background atCall helperMemory]
    exact congrArg some (helperReturnedSync base (helperBase base) 0xfc#32 helperBackground atCall helperFinal
      (returnTarget base _ _))
  have codeKept (byte : Nat) (first : base.toNat ≤ byte)
      (last : byte < base.toNat + 4 * InsertTable.instructions.length) :
      helperMemory[byte]? = original.mem[byte]? :=
    (keptByHelper byte (input.codeApartAll (Nat.le_refl _) byte first last)).trans (storedCode byte first last)
  have savedKept (byte : Nat) (first : initial.sp.toNat - 28 ≤ byte) (last : byte < initial.sp.toNat) :
      helperMemory[byte]? = (Empty.pushed original.mem initial)[byte]? :=
    (keptByHelper byte (input.savedApartAll (Nat.le_refl _) byte first last)).trans (storedSaved byte first last)
  have full : state.a0 ≠ 0#32 := by
    change (1 : Word) ≠ 0#32
    decide
  have returned := returnFull premises.frame helperMemory codeKept savedKept state rfl full regs.sp
  let finalSnapshot := Empty.restore initial { state with pc := 0x1a4, a0 := 1 } (ret - base)
  let final := sync base helperBackground finalSnapshot
  have finalBytes : final.mem = helperMemory := syncMem (base := base) (frame := helperBackground) finalSnapshot
  -- The helper's scan leaves the map header as the insertion wrote it.
  have fits := layout.stack.fits
  have apart := layout.apart
  have headerByHelper (byte : Nat) (inHeader : (mapHeader call).Contains byte) :
      helperMemory[byte]? = after[byte]? := by
    have frameOutside : HelperFrame.OutsideFrame (Empty.frameBase initial.sp) byte :=
      OuterHelper.stackDisjointHelper fits (apart.headerStack byte inHeader)
    have scanOutside : ¬ DeleteExtra.Footprint helperCall scratch initial.a5.toNat byte := by
      intro touched
      rcases touched with cacheByte | keys | slots
      · exact apart.headerCache byte inHeader cacheByte
      · obtain ⟨low, high⟩ := keys
        exact apart.headerStack byte inHeader
          (input.keysInStack (call := helperCall) (Nat.le_trans (Nat.le_add_right _ 4) low) (by omega))
      · apply apart.headerScratch byte inHeader
        change initial.a4.toNat + 4 * 0 ≤ byte ∧ byte < initial.a4.toNat + 4 * initial.a5.toNat at slots
        change initial.a4.toNat ≤ byte ∧ byte < initial.a4.toNat + 4 * initial.a5.toNat
        omega
    have viaStored := unchanged byte (sp ▸ frameOutside) scanOutside
    rw [callBytes] at viaStored
    exact viaStored.trans (storedOutsideStack initial after fits byte (apart.headerStack byte inHeader))
  have headerWord {address : Nat} {value : Word} (word : WordAt after address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (mapHeader call).Contains byte) :
      WordAt final.mem address value := by
    rw [finalBytes]
    exact word.congr fun byte low high => headerByHelper byte (inside byte low high)
  have headerPart (offset : Nat) (small : offset ≤ 8) (byte : Nat)
      (low : call.header.toNat + offset ≤ byte) (high : byte < call.header.toNat + offset + 4) :
      (mapHeader call).Contains byte := by
    change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
    omega
  obtain ⟨data, length, capacityWord, _, _⟩ := insertEffects.2.2 noReplace
    (Nonempty.Call.freshVectorValid capacity spare)
  refine ⟨final, ?_, ?_, ?_, ?_, ⟨headerWord data (headerPart 0 (by decide)),
    headerWord capacityWord (headerPart 8 (by decide)),
    ⟨_, headerWord length (headerPart 4 (by decide)), ?_⟩, ?_⟩⟩
  · rw [fullCount, runAdd, runAdd, toCall, Option.bind_some, next, Option.bind_some]
    exact returned
  · exact Empty.returnPc (base := base) helperBackground finalSnapshot rfl
  · exact readReg_succ.mp (syncRead (base := base) (frame := helperBackground) finalSnapshot
      (index := 10) (by decide))
  · exact Empty.restoreRegistersCalls premises.frame.entry helperMemory
      { state with pc := 0x1a4, a0 := 1 } (ret - base) regs.saved
  · have newLength := call.freshHelperLength capacity initial low high spare
    change (BitVec.ofNat 32 (call.length.toNat + 1)).toNat ≤ capacity.toNat
    change (BitVec.ofNat 32 (call.length.toNat + 1)).toNat = call.length.toNat + 1 at newLength
    rw [newLength]
    omega
  · intro byte outside
    simp only [WritableByte, not_or] at outside
    obtain ⟨outsideStack, outsideCache, outsideScratch, outsideLength, outsideMap⟩ := outside
    have helperApart : ¬ DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) helperCall scratch
        initial.a5.toNat byte := by
      intro wrote
      rcases input.footprintRegions (Nat.le_refl _) wrote with stack | cache | scratch | header | map
      · apply outsideStack
        change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
        omega
      · exact outsideCache cache
      · exact outsideScratch scratch
      · exact outsideLength header
      · exact outsideMap map
    rw [finalBytes]
    exact (keptByHelper byte helperApart).trans (storedKeeps byte outsideStack outsideLength outsideMap)

end Riscfree.RangeInsert.Bounded.FreshPath
