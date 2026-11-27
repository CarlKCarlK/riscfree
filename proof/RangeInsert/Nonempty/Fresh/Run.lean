import RangeInsert.Nonempty.Fresh.ToHelper
import RangeInsert.Nonempty.Fresh.Finish
import RangeInsert.Empty

/-! Complete the linked fresh-insertion path through sorted insertion,
the shared deletion helper, and the final cache update. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word PairAt)
open Empty (Snapshot)

private theorem FreshPrefix.savedAtPrefix {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} (premises : FreshPrefix base ret original initial call)
    (byte : Nat) (atSaved : initial.sp.toNat - 28 ≤ byte) :
    (freshPrefixMemory original initial)[byte]? = (Empty.pushed original.mem initial)[byte]? := by
  apply writeWordsOutside
  have fits := premises.frame.frameFits
  intro write member
  simp only [scratchWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · right
    change (Empty.frameBase initial.sp + 8#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fits 8#32 (by decide)]
    change initial.sp.toNat - 48 + 8 + 4 ≤ byte
    omega
  · right
    change (Empty.frameBase initial.sp + 12#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fits 12#32 (by decide)]
    change initial.sp.toNat - 48 + 12 + 4 ≤ byte
    omega
  · right
    change (Empty.frameBase initial.sp + 16#32).toNat + 4 ≤ byte
    rw [Empty.frameAddress fits 16#32 (by decide)]
    change initial.sp.toNat - 48 + 16 + 4 ≤ byte
    omega

private theorem freshReturnTarget (base : Word) (first last : DeleteExtra.Snapshot) :
    base + 0xf8#32 = (base + extensionHelperOffset) +
      (DeleteExtra.restore first last (base + 0xf8#32 - (base + extensionHelperOffset))).pc := by
  let helper := base + extensionHelperOffset
  let ret := base + 0xf8#32
  change ret = helper + (ret - helper)
  rw [BitVec.add_comm helper, BitVec.sub_add_cancel]

structure FreshResult (initial : Snapshot) (call : Call) (helperCall : DeleteExtra.Call) (final : ByteMemory) : Prop where
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

set_option maxHeartbeats 2800000 in
theorem FreshPrefix.run {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : FreshPrefix base ret original initial call)
    (layout : InitialLayout base original initial call capacity low high)
    (spare : call.length.toNat < capacity.toNat)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (ranges : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat)
    (room : (call.freshHelper capacity initial low high).acceptCount ≤ initial.a5.toNat) :
    let helperCall := call.freshHelper capacity initial low high
    ∃ final, Riscfree.RV32.run
        (freshToHelperCount call capacity + helperCall.helperCount capacity helperCall.acceptCount + 20) original =
          some final ∧
      final.regs.get? Register.PC = some ret ∧ FreshResult initial call helperCall final.mem ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
  let helperCall := call.freshHelper capacity initial low high
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  have noReplace := Call.freshDoesNotReplace capacity (Call.freshKeyAbsent premises.fresh sorted ranges)
  obtain ⟨caller, atCall, insertedMemory, toCall, beforeInsert, regs, insertEffects⟩ :=
    premises.toHelper layout spare sorted ranges
  let background := { original with mem := insertedMemory }
  let entered := sync base background atCall
  have input : HelperInput base entered initial helperCall capacity :=
    premises.helperInput layout beforeInsert spare sorted ranges insertEffects
  have candidateSorted := Call.freshHelperSorted (initial := initial) (low := low) (high := high)
    sorted spare noReplace
  have increasing := Call.keysIncreasing (call := helperAsOuter helperCall) candidateSorted
  have mode : MachineState background := premises.frame.mode.toMachineState.withMemory insertedMemory
  have args : DeleteExtra.Arguments (helperView atCall 0) helperCall := regs.arguments
  have helperPremises := input.premises mode (by decide : (0xf8#32).toNat % 4 = 0)
    regs.pc regs.sp regs.ra args room increasing
  have helperRan : ∃ (state : DeleteExtra.Snapshot) (memory : ByteMemory),
      Riscfree.RV32.run (helperCall.helperCount capacity helperCall.acceptCount) entered =
        some (sync (helperBase base) { entered with mem := memory }
          (DeleteExtra.restore (helperView atCall 0) state (base + 0xf8#32 - helperBase base))) ∧
      DeleteExtra.ResultMemory atCall.sp helperCall scratch helperCall.acceptCount entered.mem memory :=
    helperPremises.run
  obtain ⟨tail, helperMemory, ran, resultAtCall⟩ := helperRan
  let helperFinal := DeleteExtra.restore (helperView atCall 0) tail (base + 0xf8#32 - helperBase base)
  have callBytes : entered.mem = insertedMemory := syncMem (base := base) (frame := background) atCall
  have effects : DeleteExtra.ResultMemory atCall.sp helperCall scratch helperCall.acceptCount insertedMemory helperMemory := by
    rw [callBytes] at resultAtCall
    exact resultAtCall
  let helperBackground := { original with mem := helperMemory }
  let state := helperReturned 0xf8#32 atCall helperFinal
  have resumed := helperReturnedSync base (helperBase base) 0xf8#32 helperBackground atCall helperFinal
    (freshReturnTarget base (helperView atCall 0) tail)
  have next : Riscfree.RV32.run (helperCall.helperCount capacity helperCall.acceptCount) entered =
      some (sync base helperBackground state) := by
    rw [ran]
    change some (sync (helperBase base) { sync base background atCall with mem := helperMemory } helperFinal) = _
    rw [syncWithMem base background atCall helperMemory]
    exact congrArg some resumed
  have codeSafe : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      ¬ DeleteExtra.HelperFootprint atCall.sp helperCall scratch helperCall.acceptCount byte := by
    rw [regs.sp]
    exact input.codeApartAll room
  have savedSafe : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      ¬ DeleteExtra.HelperFootprint atCall.sp helperCall scratch helperCall.acceptCount byte := by
    rw [regs.sp]
    exact input.savedApartAll room
  have afterCode : CodeImage InsertTable.instructions base helperBackground :=
    layout.code.entry.withMemory helperMemory fun byte first last => by
      have apart := layout.apart.code _ (List.mem_cons_self ..)
      exact (effects.others byte (codeSafe byte first last)).trans
        (premises.insertionKeeps beforeInsert spare noReplace insertEffects byte
          (apart.2.2.2.2 byte ⟨first, last⟩) (fun length => apart.1 byte ⟨first, last⟩ (lengthInHeader length))
          (apart.2.1 byte ⟨first, last⟩) layout.stack.fits)
  have saved (offset : Word) (value : Word)
      (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word))
      (word : WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value) :
      WordAt helperMemory (Empty.frameBase initial.sp + offset).toNat value := by
    have bound : 20 ≤ offset.toNat ∧ offset.toNat ≤ 44 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have address := Empty.frameAddress premises.frame.frameFits offset bound.2
    have fit := premises.frame.frameFits
    have before : WordAt (freshPrefixMemory original initial) (Empty.frameBase initial.sp + offset).toNat value :=
      word.congr fun byte first last => by
        rw [address] at first
        exact premises.savedAtPrefix byte (by omega)
    have after := premises.helperStackWord layout beforeInsert spare noReplace insertEffects before
      (by rw [address]; have bottom := Empty.frameAddress fit 0#32 (by decide)
          rw [BitVec.add_zero] at bottom
          change (Empty.frameBase initial.sp).toNat = initial.sp.toNat - 48 + 0 at bottom
          rw [bottom]; omega)
      (by rw [address]; omega)
    refine after.congr fun byte first last => ?_
    rw [address] at first last
    exact effects.others byte (savedSafe byte (by omega) (by omega))
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
  have cacheSaved : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      ¬ (cacheWords state.s0).Contains byte := by
    rw [cacheAddress]
    intro byte low high
    apply layout.apart.cacheStack.symm byte
    have fits := layout.stack.fits
    change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
    omega
  have finished := finishFresh premises.frame afterCode state rfl regs.sp cache cacheCode cacheSaved saved
  let distance := call.stop - call.start
  let returnedLow := freshLow lowWord distance
  let returnedHigh := freshHigh lowWord highWord distance
  let stored := freshCacheMemory helperMemory initial.a1 returnedLow returnedHigh
  let finalSnapshot := Empty.restore initial (freshCacheState state lowWord highWord) (ret - base)
  let final := sync base { original with mem := stored } finalSnapshot
  have lastRun : Riscfree.RV32.run 20 (sync base helperBackground state) = some final := by
    dsimp only at finished
    rw [cacheAddress, start, stop] at finished
    exact finished
  have finalBytes : final.mem = stored := syncMem (base := base) (frame := { original with mem := stored }) finalSnapshot
  have finalOutside (byte : Nat) (apart : ¬ (cacheWords initial.a1).Contains byte) :
      final.mem[byte]? = helperMemory[byte]? := by
    rw [finalBytes]
    exact freshCacheOutside helperMemory initial.a1 returnedLow returnedHigh byte layout.cache.fits apart
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runAdd, runAdd, toCall, Option.bind_some, next, Option.bind_some]
    exact lastRun
  · exact Empty.returnPc (base := base) { original with mem := stored } finalSnapshot rfl
  · have ⟨cacheLow, cacheHigh⟩ := freshCacheWords helperMemory initial.a1 returnedLow returnedHigh layout.cache.fits
    refine ⟨?_, ?_, finalBytes.symm ▸ cacheLow, finalBytes.symm ▸ cacheHigh⟩
    · refine effects.lengthWord.congr fun byte low high => ?_
      apply finalOutside byte
      apply layout.apart.headerCache byte
      change helperCall.header.toNat + 4 ≤ byte at low
      change byte < helperCall.header.toNat + 4 + 4 at high
      change call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12
      change call.header.toNat + 4 ≤ byte at low
      change byte < call.header.toNat + 4 + 4 at high
      omega
    · intro index inside
      change index < helperCall.length.toNat - helperCall.acceptCount at inside
      have pair := effects.entries index inside
      have live : index < helperCall.length.toNat := by omega
      have kept (byte : Nat) (low : helperCall.search.slot index ≤ byte)
          (high : byte < helperCall.search.slot index + 8) :
          final.mem[byte]? = helperMemory[byte]? :=
        finalOutside byte (layout.apart.mapCache byte (input.layout.map.entryContained live low high))
      exact ⟨pair.1.congr fun byte low high => kept byte low (by omega),
        pair.2.congr fun byte low high => kept byte (by omega) (by omega)⟩
  · exact Empty.restoreRegistersCalls premises.frame.entry stored
      (freshCacheState state lowWord highWord) (ret - base) regs.saved
  · intro byte outside
    simp only [WritableByte, not_or] at outside
    obtain ⟨outsideStack, outsideCache, outsideScratch, outsideLength, outsideMap⟩ := outside
    have helperApart : ¬ DeleteExtra.HelperFootprint atCall.sp helperCall scratch helperCall.acceptCount byte := by
      rw [regs.sp]
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
    exact (finalOutside byte outsideCache).trans ((effects.others byte helperApart).trans
      (premises.insertionKeeps beforeInsert spare noReplace insertEffects byte outsideStack outsideLength
        outsideMap layout.stack.fits))

end Riscfree.RangeInsert.Nonempty
