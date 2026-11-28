import RangeInsert.Bounded.HelperLoop

namespace Riscfree.RangeInsert.Bounded.HelperFullScan

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable)
open Helper
open HelperFrame
open HelperLoop (Layout Registers)
open HelperScan (stored throughAppend)
open DeleteExtra (Call Scratch Memory Footprint cacheStored rawVecBase scratchAppendFull)

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

def failureCount (call : Call) (index : Nat) : Nat :=
  (if (call.successor index).value.toNat < (call.progress index).endNew.toNat then 25 else 26) + 7

/-- The loop is about to process the first eligible successor that does
not fit. The append leaves its header and storage intact. The cache has
already been updated for that successor. -/
theorem fullIteration {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {scratch : Scratch} {t : Nat} {start before : ByteMemory}
    (frame : Frame base returnAddress original initial)
    (layout : Layout base original call scratch t start)
    (full : t = scratch.capacity.toNat) (short : t < call.acceptCount)
    (state : Snapshot) (regs : Registers initial call t state)
    (mem : Memory call scratch start t before) :
    ∃ (returned : Snapshot) (after : ByteMemory),
      run (failureCount call t) (sync base { original with mem := before } state) =
        some (sync base { original with mem := after } returned) ∧
      returned.pc = 0x108#32 ∧ returned.sp = state.sp ∧ returned.a0 = 1#32 ∧
      ∀ byte, ¬ Footprint call scratch t byte → after[byte]? = start[byte]? := by
  obtain ⟨inside, within⟩ := call.accepted t short
  let index := call.position + 1 + t
  let next := call.successor t
  have entriesFit := layout.entriesFit
  have slotBound : call.search.slot index + 8 ≤ 2 ^ 32 := by
    unfold SortedMap.Search.Call.slot at entriesFit ⊢
    change call.search.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at entriesFit
    have scaled : 8 * index + 8 ≤ 8 * call.length.toNat := by omega
    omega
  have cursorNat : (call.search.wordSlot index).toNat = call.search.slot index := by
    unfold SortedMap.Search.Call.wordSlot
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have cursorEnd : (call.search.wordSlot index + 0x4#32).toNat = call.search.slot index + 4 := by
    rw [BitVec.toNat_add, cursorNat]
    change (call.search.slot index + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by omega)
  have different : state.a0 ≠ state.s7 := by
    rw [regs.cursor, regs.last]
    intro same
    have toNat := congrArg BitVec.toNat same
    rw [cursorNat] at toNat
    unfold SortedMap.Search.Call.wordSlot at toNat
    rw [BitVec.toNat_ofNat] at toNat
    unfold SortedMap.Search.Call.slot at toNat entriesFit slotBound
    change call.search.data.toNat + 8 * index =
      (call.search.data.toNat + 8 * call.length.toNat) % 2 ^ 32 at toNat
    change call.search.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at entriesFit
    by_cases full : call.search.data.toNat + 8 * call.length.toNat = 2 ^ 32
    · rw [full, Nat.mod_self] at toNat
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at toNat
      omega
  have imageOf (other : ByteMemory) (agree : ∀ byte, base.toNat ≤ byte →
      byte < base.toNat + 4 * DeleteTable.instructions.length → other[byte]? = before[byte]?) :
      CodeImage DeleteTable.instructions base { original with mem := other } :=
    frame.code.withMemory other fun byte low high =>
      (agree byte low high).trans ((mem.others byte fun footprint =>
        layout.helperApart byte low high (footprint.mono (by omega))).trans
          (layout.helperStart byte low high))
  have rawImageOf (other : ByteMemory) (agree : ∀ byte, (rawVecBase base).toNat ≤ byte →
      byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length →
      other[byte]? = before[byte]?) :
      CodeImage RawVec.instructions (rawVecBase base) { original with mem := other } :=
    layout.rawCode.withMemory other fun byte low high =>
      (agree byte low high).trans ((mem.others byte fun footprint =>
        layout.rawApart byte low high (footprint.mono (by omega))).trans
          (layout.rawStart byte low high))
  have capacitySmall := scratch.capacity.isLt
  have tNat : (BitVec.ofNat 32 t).toNat = t := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := layout.capacity; omega)
  let vector : RawVec.Call :=
    { header := call.keys, index := BitVec.ofNat 32 t, value := next.key,
      length := BitVec.ofNat 32 t, capacity := scratch.capacity, data := scratch.data,
      old := fun j => (call.successor j).key }
  have cacheFits := layout.cacheFits
  have keysFits := layout.keysFits
  have cacheHighNat : (call.cache + 0x4#32).toNat = call.cache.toNat + 4 := by
    rw [BitVec.toNat_add]
    change (call.cache.toNat + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by omega)
  have keysLengthNat : (call.keys + 0x4#32).toNat = call.keys.toNat + 4 := by
    rw [BitVec.toNat_add]
    change (call.keys.toNat + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by omega)
  -- The two cache stores change only the cache.
  have storedOutside (byte : Nat)
      (outside : byte < call.cache.toNat ∨ call.cache.toNat + 8 ≤ byte) :
      (stored before state next.key next.value)[byte]? = before[byte]? := by
    unfold stored cacheStored
    rw [regs.cache, storeWordOutside _ _ _ _ (by rw [cacheHighNat]; omega),
      storeWordOutside _ _ _ _ (by omega)]
  have storedWord {address : Nat} {value : Word} (word : WordAt before address value)
      (apart : address + 4 ≤ call.cache.toNat ∨ call.cache.toNat + 8 ≤ address) :
      WordAt (stored before state next.key next.value) address value :=
    word.congr fun byte low high => storedOutside byte (by omega)
  have headerApart := layout.cacheApartHeader
  have lengthApart : call.keys.toNat + 4 + 4 ≤ call.cache.toNat ∨
      call.cache.toNat + 8 ≤ call.keys.toNat + 4 := by omega
  have capacityApart : call.keys.toNat + 8 + 4 ≤ call.cache.toNat ∨
      call.cache.toNat + 8 ≤ call.keys.toNat + 8 := by omega
  have header : RawVec.Header { original with mem := stored before state next.key next.value }
      vector := by
    refine ⟨keysFits, Nonempty.mappedTransfer layout.keysLengthReadable rfl,
      Nonempty.mappedTransfer layout.keysCapacityReadable rfl, ?_, ?_⟩
    · exact storedWord mem.keysLength lengthApart
    · exact storedWord mem.keysCapacity capacityApart
  have keyWord : WordAt before state.a0.toNat next.key := by
    rw [regs.cursor, cursorNat]
    exact (layout.keyWord index inside).congr fun byte low high =>
      mem.others byte fun footprint => layout.entriesApart index inside byte low (by omega)
        (footprint.mono (by omega))
  have endWord : WordAt before (state.a0 + 0x4#32).toNat next.value := by
    rw [regs.cursor, cursorEnd]
    exact (layout.valueWord index inside).congr fun byte low high =>
      mem.others byte fun footprint => layout.entriesApart index inside byte (by omega) (by omega)
        (footprint.mono (by omega))
  have lengthWord : WordAt before (state.s1 + 0x4#32).toNat (BitVec.ofNat 32 t) := by
    rw [regs.keys, keysLengthNat]; exact mem.keysLength
  have cacheOutsideCode : ∀ byte, (state.s2.toNat ≤ byte ∧ byte < state.s2.toNat + 4) ∨
      ((state.s2 + 0x4#32).toNat ≤ byte ∧ byte < (state.s2 + 0x4#32).toNat + 4) →
      (byte < base.toNat ∨ base.toNat + 4 * DeleteTable.instructions.length ≤ byte) ∧
      (byte < (rawVecBase base).toNat ∨
        (rawVecBase base).toNat + 4 * RawVec.instructions.length ≤ byte) := by
    intro byte inCache
    rw [regs.cache, cacheHighNat] at inCache
    have footprint : Footprint call scratch t byte := Or.inl (by omega)
    constructor
    · by_contra inCode
      simp only [not_or, Nat.not_lt] at inCode
      exact layout.helperApart byte inCode.1 (by omega) footprint
    · by_contra inCode
      simp only [not_or, Nat.not_lt] at inCode
      exact layout.rawApart byte inCode.1 (by omega) footprint
  have sameCapacity : vector.length = vector.capacity := by
    apply BitVec.eq_of_toNat_eq
    exact tNat.trans full
  obtain ⟨status, count, invalid⟩ := scratchAppendFull (append := vector) rfl sameCapacity
  obtain ⟨returned, after, ran, facts, rejected, _⟩ :=
    throughAppend frame before imageOf rawImageOf state regs.pc next.key next.value different
      (by rw [regs.cursor]; exact layout.keyReadable index inside) keyWord
      (by rw [regs.cursor]; exact layout.valueReadable index inside) endWord
      (by rw [regs.limit]; exact Nat.not_lt.mpr within) (by rw [regs.keys]; exact layout.keysLengthReadable)
      (BitVec.ofNat 32 t) lengthWord (by rw [regs.cache]; exact layout.cacheLowWritable)
      (by rw [regs.cache]; exact layout.cacheHighWritable) cacheOutsideCode vector
      regs.keys.symm rfl rfl header (fun valid => (invalid valid).elim)
  refine ⟨returned, after, ?_, facts.pc, facts.sp, facts.status.trans status, ?_⟩
  · rw [regs.endNew, count] at ran
    exact ran
  · intro byte outside
    rw [rejected invalid]
    exact (storedOutside byte (by
      by_contra overlap
      push_neg at overlap
      exact outside (Or.inl overlap))).trans (mem.others byte outside)

end Riscfree.RangeInsert.Bounded.HelperFullScan
