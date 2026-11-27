import RangeInsert.Nonempty.Extension.Execution
import RangeInsert.Nonempty.Extension.Stored
import RangeInsert.Nonempty.HelperLayout
import RangeInsert.Resources

/-! The extension prefix's stores supply the helper's input layout. The
verified helper and outer epilogue then complete the linked machine run. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable)
open Empty (Snapshot)

def extensionMemory (original : Machine) (initial : Snapshot) (call : Call) (low high : Word) : ByteMemory :=
  extensionStored initial call low high (Empty.pushed original.mem initial)

private theorem ExtensionPrefix.addresses {base ret : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {low high : Word} (premises : ExtensionPrefix base ret original initial call low high) :
    let index := call.rank - 1
    (initial.a1 + 4#32).toNat = initial.a1.toNat + 4 ∧
    (call.search.wordSlot index + 4#32).toNat = call.search.slot index + 4 := by
  have inside : call.rank - 1 < call.length.toNat := by
    have := premises.found
    have := call.rank_le
    omega
  have keys := premises.map.keys (Nat.zero_lt_of_lt inside)
  constructor
  · rw [BitVec.toNat_add]
    change (initial.a1.toNat + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by have := premises.cacheFits; omega)
  · rw [BitVec.toNat_add, SortedMap.Search.slotNat keys inside]
    have fits := keys.fits
    change call.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at fits
    change (call.data.toNat + 8 * (call.rank - 1) + 4) % 2 ^ 32 =
      call.data.toNat + 8 * (call.rank - 1) + 4
    exact Nat.mod_eq_of_lt (by omega)

private theorem ExtensionPrefix.keptByte {base ret : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {low high : Word} (premises : ExtensionPrefix base ret original initial call low high)
    (byte : Nat) (cache : ¬ (cacheWords initial.a1).Contains byte)
    (endpoint : ¬ (⟨call.search.slot (call.rank - 1) + 4, 4⟩ : Span).Contains byte)
    (stack : Empty.OutsideFrame initial.sp byte) :
    (extensionMemory original initial call low high)[byte]? = original.mem[byte]? := by
  change ¬ (initial.a1.toNat ≤ byte ∧ byte < initial.a1.toNat + 8) at cache
  change ¬ (call.search.slot (call.rank - 1) + 4 ≤ byte ∧
    byte < call.search.slot (call.rank - 1) + 4 + 4) at endpoint
  have noStack := stack
  unfold Empty.OutsideFrame at noStack
  have fits := premises.frame.frameFits
  exact (premises.writesAway byte (by omega) (by omega) (by omega)).trans
    (Empty.pushedOutside _ _ fits byte stack)

private theorem ExtensionPrefix.keptWord {base ret : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {low high value : Word} (premises : ExtensionPrefix base ret original initial call low high)
    {address : Nat} (word : WordAt original.mem address value)
    (outside : ∀ byte, address ≤ byte → byte < address + 4 →
      (¬ (cacheWords initial.a1).Contains byte) ∧
      (¬ (⟨call.search.slot (call.rank - 1) + 4, 4⟩ : Span).Contains byte) ∧
      Empty.OutsideFrame initial.sp byte) :
    WordAt (extensionMemory original initial call low high) address value :=
  word.congr fun byte low high =>
    have ⟨apartCache, apartEndpoint, apartStack⟩ := outside byte low high
    premises.keptByte byte apartCache apartEndpoint apartStack

private theorem apartFollowingStack {sp address : Word}
    (fits : 48 ≤ sp.toNat) (outside : ∀ byte, address.toNat ≤ byte → byte < address.toNat + 4 →
      Empty.OutsideFrame sp byte) (offset : Word) (offsetFits : offset.toNat ≤ 44) :
    ∀ byte, address.toNat ≤ byte → byte < address.toNat + 4 →
      byte < (Empty.frameBase sp + offset).toNat ∨ (Empty.frameBase sp + offset).toNat + 4 ≤ byte := by
  intro byte low high
  have apart := outside byte low high
  unfold Empty.OutsideFrame at apart
  rw [Empty.frameAddress fits offset offsetFits]
  omega

theorem ExtensionPrefix.storedData {base ret : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word} (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high) :
    let after := extensionMemory original initial call low high
    WordAt after initial.a1.toNat (extendLow call low) ∧
      WordAt after (initial.a1.toNat + 4) (extendHigh call low high) ∧
      WordAt after (call.search.slot (call.rank - 1) + 4) call.stop := by
  let sp := Empty.frameBase initial.sp
  let endpoint := call.search.wordSlot (call.rank - 1) + 4#32
  let scratchHeader : List (Word × Word) :=
    [(sp + 8#32, initial.a4), (sp + 12#32, 0#32), (sp + 16#32, initial.a5)]
  let cacheLow : Word × Word := (initial.a1, extendLow call low)
  let cacheHigh : Word × Word := (initial.a1 + 4#32, extendHigh call low high)
  let endWrite : Word × Word := (endpoint, call.stop)
  let before := Empty.pushed original.mem initial
  have ⟨highAddress, endAddress⟩ := premises.addresses
  have fits := premises.frame.frameFits
  have found := premises.found
  have rank := call.rank_le
  have indexInside : call.rank - 1 < call.length.toNat := by omega
  have layoutEnd (byte : Nat) (low : endpoint.toNat ≤ byte) (high : byte < endpoint.toNat + 4) :
      (mapAllocation call capacity).Contains byte := by
    change (call.search.wordSlot (call.rank - 1) + 4#32).toNat ≤ byte at low
    change byte < (call.search.wordSlot (call.rank - 1) + 4#32).toNat + 4 at high
    rw [endAddress] at low high
    exact layout.map.entryContained indexInside (by omega) (by omega)
  have stackAfter {address : Word} (outside : ∀ byte, address.toNat ≤ byte → byte < address.toNat + 4 →
        Empty.OutsideFrame initial.sp byte)
      (write : Word × Word) (member : write ∈ scratchHeader)
      (byte : Nat) (low : address.toNat ≤ byte) (high : byte < address.toNat + 4) :
      byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte := by
    simp only [scratchHeader, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact apartFollowingStack fits outside 8 (by decide) byte low high
    · exact apartFollowingStack fits outside 12 (by decide) byte low high
    · exact apartFollowingStack fits outside 16 (by decide) byte low high
  have cacheAfter (address : Word)
      (atCache : ∀ byte, address.toNat ≤ byte → byte < address.toNat + 4 → (cacheWords initial.a1).Contains byte)
      (write : Word × Word) (member : write ∈ endWrite :: scratchHeader)
      (byte : Nat) (low : address.toNat ≤ byte) (high : byte < address.toNat + 4) :
      byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte := by
    rcases List.mem_cons.mp member with same | rest
    · subst write
      change byte < endpoint.toNat ∨ endpoint.toNat + 4 ≤ byte
      by_contra overlaps
      push_neg at overlaps
      exact layout.apart.mapCache byte (layoutEnd byte overlaps.1 overlaps.2) (atCache byte low high)
    · exact stackAfter (fun byte low high =>
        stackDisjointOuter layout.stack.fits (layout.apart.cacheStack byte (atCache byte low high)))
        write rest byte low high
  have lowWithin (byte : Nat) (low : initial.a1.toNat ≤ byte) (high : byte < initial.a1.toNat + 4) :
      (cacheWords initial.a1).Contains byte := by
    change initial.a1.toNat ≤ byte ∧ byte < initial.a1.toNat + 8
    omega
  have highWithin (byte : Nat) (low : (initial.a1 + 4#32).toNat ≤ byte)
      (high : byte < (initial.a1 + 4#32).toNat + 4) : (cacheWords initial.a1).Contains byte := by
    rw [highAddress] at low high
    change initial.a1.toNat ≤ byte ∧ byte < initial.a1.toNat + 8
    omega
  have lowValue := writeWordsAt before [] (cacheHigh :: endWrite :: scratchHeader)
    initial.a1 (extendLow call low) (by
      intro write member byte low high
      rcases List.mem_cons.mp member with same | rest
      · subst write
        change byte < (initial.a1 + 4#32).toNat ∨ (initial.a1 + 4#32).toNat + 4 ≤ byte
        rw [highAddress]
        omega
      · exact cacheAfter initial.a1 lowWithin write rest byte low high)
  have highValue := writeWordsAt before [cacheLow] (endWrite :: scratchHeader)
    (initial.a1 + 4#32) (extendHigh call low high) (cacheAfter (initial.a1 + 4#32) highWithin)
  have endValue := writeWordsAt before [cacheLow, cacheHigh] scratchHeader endpoint call.stop
    (stackAfter fun byte lo hi =>
      stackDisjointOuter layout.stack.fits (layout.apart.mapStack byte (layoutEnd byte lo hi)))
  rw [highAddress] at highValue
  change endpoint.toNat = call.search.slot (call.rank - 1) + 4 at endAddress
  rw [endAddress] at endValue
  exact ⟨lowValue, highValue, endValue⟩

private theorem ExtensionPrefix.endContained {base ret : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {capacity low high : Word} (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    {byte : Nat} (inside : (⟨call.search.slot (call.rank - 1) + 4, 4⟩ : Span).Contains byte) :
    (mapAllocation call capacity).Contains byte := by
  have found := premises.found
  have rank := call.rank_le
  change call.search.slot (call.rank - 1) + 4 ≤ byte ∧
    byte < call.search.slot (call.rank - 1) + 4 + 4 at inside
  exact layout.map.entryContained (index := call.rank - 1) (by omega) (by omega) (by omega)

private theorem ExtensionPrefix.storedMap {base ret : Word} {original entered : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    (memory : entered.mem = extensionMemory original initial call low high)
    (regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions) :
    MapStorage entered (helperAsOuter (call.extensionHelper initial low high)) capacity := by
  have map := layout.map
  have apart := layout.apart
  have keepHeader {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (mapHeader call).Contains byte) :
      WordAt entered.mem address value := by
    rw [memory]
    exact premises.keptWord word fun byte low high => by
      have atHeader := inside byte low high
      exact ⟨apart.headerCache byte atHeader,
        fun near => apart.headerMap byte atHeader (premises.endContained layout near),
        stackDisjointOuter layout.stack.fits (apart.headerStack byte atHeader)⟩
  have keepEntry {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (inside : ∀ byte, address ≤ byte → byte < address + 4 → (mapAllocation call capacity).Contains byte)
      (away : ∀ byte, address ≤ byte → byte < address + 4 →
        ¬ (⟨call.search.slot (call.rank - 1) + 4, 4⟩ : Span).Contains byte) :
      WordAt entered.mem address value := by
    rw [memory]
    exact premises.keptWord word fun byte low high => by
      have atMap := inside byte low high
      exact ⟨apart.mapCache byte atMap, away byte low high,
        stackDisjointOuter layout.stack.fits (apart.mapStack byte atMap)⟩
  have headerRange (byte : Nat) (low : call.header.toNat ≤ byte) (high : byte < call.header.toNat + 12) :
      (mapHeader call).Contains byte := ⟨low, high⟩
  refine {
    headerFits := map.headerFits
    allocationFits := map.allocationFits
    dataNonnull := map.dataNonnull
    lengthFits := map.lengthFits
    headerReadable := fun offset member => mappedTransfer (map.headerReadable offset member) regions
    lengthWritable := mappedTransfer map.lengthWritable regions
    dataWord := keepHeader map.dataWord (fun byte low high => by
      change call.header.toNat + 0 ≤ byte at low
      change byte < call.header.toNat + 0 + 4 at high
      exact headerRange byte (by omega) (by omega))
    lengthWord := keepHeader map.lengthWord (fun byte low high => by
      change call.header.toNat + 4 ≤ byte at low
      change byte < call.header.toNat + 4 + 4 at high
      exact headerRange byte (by omega) (by omega))
    capacityWord := keepHeader map.capacityWord (fun byte low high => by
      change call.header.toNat + 8 ≤ byte at low
      change byte < call.header.toNat + 8 + 4 at high
      exact headerRange byte (by omega) (by omega))
    live := ?_
    pairsReadable := fun index inside =>
      ⟨mappedTransfer (map.pairsReadable index inside).1 regions, mappedTransfer (map.pairsReadable index inside).2 regions⟩
    pairsWritable := fun index inside =>
      ⟨mappedTransfer (map.pairsWritable index inside).1 regions, mappedTransfer (map.pairsWritable index inside).2 regions⟩ }
  intro index inside
  change index < call.length.toNat at inside
  have old := map.live index inside
  constructor
  · change WordAt entered.mem (call.search.slot index) (call.extendedEntries index).key
    rw [call.extendedKey]
    refine keepEntry old.1 (fun byte low high => map.entryContained inside low (by omega)) ?_
    intro byte first last near
    change call.data.toNat + 8 * index ≤ byte at first
    change byte < call.data.toNat + 8 * index + 4 at last
    change call.data.toNat + 8 * (call.rank - 1) + 4 ≤ byte ∧
      byte < call.data.toNat + 8 * (call.rank - 1) + 4 + 4 at near
    omega
  · change WordAt entered.mem (call.search.slot index + 4) (call.extendedEntries index).value
    by_cases selected : index = call.rank - 1
    · subst index
      rw [memory]
      simpa only [Call.extendedEntries, if_pos rfl] using (premises.storedData layout).2.2
    · simp only [Call.extendedEntries, if_neg selected]
      refine keepEntry old.2 (fun byte low high => map.entryContained inside (by omega) (by omega)) ?_
      intro byte first last near
      change call.data.toNat + 8 * index + 4 ≤ byte at first
      change byte < call.data.toNat + 8 * index + 4 + 4 at last
      change call.data.toNat + 8 * (call.rank - 1) + 4 ≤ byte ∧
        byte < call.data.toNat + 8 * (call.rank - 1) + 4 + 4 at near
      omega

theorem ExtensionPrefix.helperInput {base ret : Word} {original : Machine}
    {initial caller : Snapshot} {call : Call} {capacity low high : Word}
    (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)) :
    HelperInput base (sync base { original with mem := extensionMemory original initial call low high } caller)
      initial (call.extensionHelper initial low high) capacity := by
  let stored := extensionMemory original initial call low high
  let background := { original with mem := stored }
  let entered := sync base background caller
  let helperCall := call.extensionHelper initial low high
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame (base := base) (frame := background) caller Register.pma_regions
      (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have memory : entered.mem = stored := syncMem (base := base) (frame := background) caller
  have fits := layout.stack.fits
  have codeBefore : CodeImages base background := layout.code.withMemory stored (by
    intro span member byte inside
    have safe := layout.apart.code span member
    exact premises.keptByte byte (safe.2.2.1 byte inside)
      (fun near => safe.2.1 byte inside (premises.endContained layout near))
      (stackDisjointOuter fits (safe.2.2.2.2 byte inside)))
  have ⟨cacheLow, cacheHigh, _⟩ := premises.storedData layout
  have cache : CacheStorage entered initial.a1 helperCall.low helperCall.high := by
    refine ⟨layout.cache.fits, ⟨mappedTransfer layout.cache.readable.1 regions,
      mappedTransfer layout.cache.readable.2 regions⟩,
      ⟨mappedTransfer layout.cache.writable.1 regions, mappedTransfer layout.cache.writable.2 regions⟩, ?_, ?_⟩
    · rw [memory]
      exact cacheLow
    · rw [memory]
      exact cacheHigh
  have apart := layout.apart
  have geometry : Separation base initial.sp (helperAsOuter helperCall) capacity initial.a1 ⟨initial.a4, initial.a5⟩ :=
    ⟨apart.headerMap, apart.headerCache, apart.headerScratch, apart.headerStack, apart.mapCache,
      apart.mapScratch, apart.mapStack, apart.cacheScratch, apart.cacheStack, apart.scratchStack, apart.code⟩
  have arrived : InitialLayout base entered initial (helperAsOuter helperCall) capacity helperCall.low helperCall.high :=
    ⟨codeBefore.atSync caller, premises.storedMap layout memory regions, layout.scratch.transfer regions,
      cache, layout.stack.transfer regions, geometry⟩
  have found : helperCall.position < helperCall.length.toNat := by
    rw [show helperCall.position = call.rank - 1 from Call.extensionPosition sorted premises.found initial low high]
    change call.rank - 1 < call.length.toNat
    have := premises.found
    have := call.rank_le
    omega
  have ⟨scratchData, scratchLength, scratchCapacity⟩ :=
    extensionScratchWords initial call low high (Empty.pushed original.mem initial) premises.frame.frameFits
  refine ⟨arrived, rfl, rfl, rfl, ?_, ?_, ?_, ?_, found⟩
  · rw [memory]
    have word := pushedMapReference initial original.mem
    rw [premises.arguments.header] at word
    refine word.congr fun byte low high => ?_
    rw [Empty.frameAddress premises.frame.frameFits 4#32 (by decide)] at low high
    change initial.sp.toNat - 48 + 4 ≤ byte at low
    change byte < initial.sp.toNat - 48 + 4 + 4 at high
    have onStack : (stackAllocation initial.sp).Contains byte := by
      change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
      omega
    have cacheApart := layout.apart.cacheStack.symm byte onStack
    have endApart (near : (⟨call.search.slot (call.rank - 1) + 4, 4⟩ : Span).Contains byte) : False :=
      layout.apart.mapStack byte (premises.endContained layout near) onStack
    change ¬ (initial.a1.toNat ≤ byte ∧ byte < initial.a1.toNat + 8) at cacheApart
    have endpoint : ¬ (call.search.slot (call.rank - 1) + 4 ≤ byte ∧ byte < call.search.slot (call.rank - 1) + 8) :=
      fun near => endApart (by
        change call.search.slot (call.rank - 1) + 4 ≤ byte ∧
          byte < call.search.slot (call.rank - 1) + 4 + 4
        omega)
    exact premises.writesAway byte (by omega) (by omega) (by omega)
  · rw [memory]; exact scratchData
  · rw [memory]; exact scratchLength
  · rw [memory]; exact scratchCapacity

private theorem extensionReturnTarget (base : Word) (first last : DeleteExtra.Snapshot) :
    base + 0x1a8#32 = (base + extensionHelperOffset) +
      (DeleteExtra.restore first last (base + 0x1a8#32 - (base + extensionHelperOffset))).pc := by
  let helper := base + extensionHelperOffset
  let ret := base + 0x1a8#32
  change ret = helper + (ret - helper)
  rw [BitVec.add_comm helper, BitVec.sub_add_cancel]

private theorem extensionKeysIncreasing {call : Call}
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)) {initial : Snapshot}
    {low high : Word} :
    ∀ first second, first < second → second < call.length.toNat →
      ((call.extensionHelper initial low high).old first).key.toNat <
        ((call.extensionHelper initial low high).old second).key.toNat := by
  intro first second before inside
  change (call.extendedEntries first).key.toNat < (call.extendedEntries second).key.toNat
  rw [call.extendedKey, call.extendedKey]
  have length := SortedMap.entriesOf_length call.old call.length.toNat
  have left : first < (SortedMap.entriesOf call.old call.length.toNat).length := by omega
  have right : second < (SortedMap.entriesOf call.old call.length.toNat).length := by omega
  simpa only [SortedMap.entriesOf_getElem] using
    (List.pairwise_iff_getElem.mp sorted) first second left right before

set_option maxHeartbeats 2500000 in
/-- The linked predecessor-extension path returns at the ABI return address
with the memory computed by the helper at its actual call site. -/
theorem ExtensionPrefix.run {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (room : (call.extensionHelper initial low high).acceptCount ≤ initial.a5.toNat) :
    let helperCall := call.extensionHelper initial low high
    ∃ final, Riscfree.RV32.run
        (68 + call.search.count .upper + helperCall.helperCount capacity helperCall.acceptCount) original = some final ∧
      final.regs.get? Register.PC = some ret ∧
      DeleteExtra.ResultMemory (Empty.frameBase initial.sp) helperCall ⟨initial.a4, initial.a5⟩
        helperCall.acceptCount (extensionMemory original initial call low high) final.mem ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
  let helperCall := call.extensionHelper initial low high
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  let memory := extensionMemory original initial call low high
  let background := { original with mem := memory }
  obtain ⟨caller, toCall, regs⟩ := premises.toHelper
  let entered := sync base background caller
  have headMemory : entered.mem = memory := syncMem (base := base) (frame := background) caller
  have input : HelperInput base entered initial helperCall capacity := premises.helperInput layout sorted
  have mode : MachineState background := premises.frame.mode.toMachineState.withMemory memory
  have arguments : DeleteExtra.Arguments (helperView caller 0) helperCall :=
    regs.helperArguments rfl rfl rfl rfl rfl
  have helperPremises := input.premises mode (by decide : (0x1a8#32).toNat % 4 = 0)
    regs.pc regs.sp regs.ra arguments room (extensionKeysIncreasing sorted)
  have prefixRun : Riscfree.RV32.run (58 + call.search.count .upper) original = some entered :=
    (congrArg (Riscfree.RV32.run (58 + call.search.count .upper)) premises.frame.entry).trans toCall
  have ranHelper : ∃ (state : DeleteExtra.Snapshot) (after : ByteMemory),
      Riscfree.RV32.run (helperCall.helperCount capacity helperCall.acceptCount) entered =
        some (sync (helperBase base) { entered with mem := after }
          (DeleteExtra.restore (helperView caller 0) state (base + 0x1a8#32 - helperBase base))) ∧
      DeleteExtra.ResultMemory caller.sp helperCall scratch helperCall.acceptCount entered.mem after :=
    helperPremises.run
  obtain ⟨tail, after, ran, resultAtCall⟩ := ranHelper
  let helperFinal := DeleteExtra.restore (helperView caller 0) tail (base + 0x1a8#32 - helperBase base)
  have effects : DeleteExtra.ResultMemory caller.sp helperCall scratch helperCall.acceptCount background.mem after := by
    rw [headMemory] at resultAtCall
    exact resultAtCall
  have codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      ¬ DeleteExtra.HelperFootprint caller.sp helperCall scratch helperCall.acceptCount byte := by
    rw [regs.sp]
    exact input.codeApartAll room
  have savedApart : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      ¬ DeleteExtra.HelperFootprint caller.sp helperCall scratch helperCall.acceptCount byte := by
    rw [regs.sp]
    exact input.savedApartAll room
  have total := completeExtensionRun premises.frame background mode rfl caller (helperFinal := helperFinal)
    prefixRun ran effects (extensionReturnTarget base (helperView caller 0) tail) regs.sp
    codeApart premises.writesAwayFromCode savedApart premises.writesAwayFromSaved
  let last := Empty.restore initial (helperReturned 0x1a8#32 caller helperFinal) (ret - base)
  let final := sync base { background with mem := after } last
  have finalMemory : final.mem = after := syncMem (base := base) (frame := { background with mem := after }) last
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · have count : 68 + call.search.count .upper + helperCall.helperCount capacity helperCall.acceptCount =
        58 + call.search.count .upper + helperCall.helperCount capacity helperCall.acceptCount + 10 := by omega
    rw [count]
    exact total
  · exact Empty.returnPc (base := base) { background with mem := after } last rfl
  · rw [finalMemory, ← regs.sp]
    exact effects
  · exact Empty.restoreRegistersCalls premises.frame.entry after
      (helperReturned 0x1a8#32 caller helperFinal) (ret - base) regs.saved
  · intro byte outside
    simp only [WritableByte, not_or] at outside
    obtain ⟨stack, cache, scratchApart, header, map⟩ := outside
    have noHelper : ¬ DeleteExtra.HelperFootprint caller.sp helperCall scratch helperCall.acceptCount byte := by
      rw [regs.sp]
      intro wrote
      rcases input.footprintRegions room wrote with helperStack | helperCache | helperScratch | helperHeader | helperMap
      · apply stack
        have fits := layout.stack.fits
        change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
        omega
      · exact cache helperCache
      · exact scratchApart helperScratch
      · exact header helperHeader
      · exact map helperMap
    rw [finalMemory]
    exact (effects.others byte noHelper).trans (premises.keptByte byte cache
      (fun endpoint => map (premises.endContained layout endpoint))
      (stackDisjointOuter layout.stack.fits stack))

end Riscfree.RangeInsert.Nonempty
