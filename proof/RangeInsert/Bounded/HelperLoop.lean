import RangeInsert.Bounded.HelperScan
import RangeInsert.DeleteExtra.Count

namespace Riscfree.RangeInsert.Bounded.HelperLoop

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable)
open Helper
open HelperFrame
open HelperEntry (Head)
open HelperScan (stored nextEnd)
open DeleteExtra (Call Scratch Memory Footprint cacheStored rawVecBase
  lowAfter highAfter intervalApart appendStatus appendCount)

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def iterationCount (call : Call) (t : Nat) : Nat :=
  if (call.successor t).value.toNat < (call.progress t).endNew.toNat then 43 else 44

def scanCount (call : Call) : Nat → Nat
  | 0 => 0
  | t + 1 => scanCount call t + iterationCount call t

/-- The loop-head registers after `t` accepted successors. -/
structure Registers (initial : Snapshot) (call : Call) (t : Nat) (state : Snapshot) : Prop where
  pc : state.pc = 0xa0#32
  sp : state.sp = frameBase initial.sp
  header : state.s0 = call.header
  keys : state.s1 = call.keys
  cache : state.s2 = call.cache
  stop : state.s3 = call.stop
  entry : state.s4 = call.search.wordSlot call.position
  limit : state.s6 = call.limit
  last : state.s7 = call.search.wordSlot call.length.toNat
  cursor : state.a0 = call.search.wordSlot (call.position + 1 + t)
  endNew : state.s5 = (call.progress t).endNew
  low : state.a2 = (call.progress t).low
  high : state.s8 = (call.progress t).high

theorem Registers.ofHead {initial : Snapshot} {call : Call} {state : Snapshot}
    (head : Head initial call state) : Registers initial call 0 state :=
  ⟨head.pc, head.sp, head.header, head.keys, head.cache, head.stop, head.entry, head.limit,
    head.last, head.cursor, head.endNew, head.low, head.high⟩

theorem iteration {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (imageOf : ∀ other : ByteMemory, (∀ byte, base.toNat ≤ byte →
      byte < base.toNat + 4 * DeleteTable.instructions.length → other[byte]? = memory[byte]?) →
      CodeImage DeleteTable.instructions base { original with mem := other })
    (rawImageOf : ∀ other : ByteMemory, (∀ byte, (rawVecBase base).toNat ≤ byte →
      byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length →
      other[byte]? = memory[byte]?) →
      CodeImage RawVec.instructions (rawVecBase base) { original with mem := other })
    (head : Snapshot) (atHead : head.pc = 0xa0#32)
    (key endWord : Word) (different : head.a0 ≠ head.s7)
    (keyReadable : Readable original head.a0) (keyWord : WordAt memory head.a0.toNat key)
    (endReadable : Readable original (head.a0 + 0x4#32))
    (endWordAt : WordAt memory (head.a0 + 0x4#32).toNat endWord)
    (accepted : ¬ head.s6.toNat < key.toNat)
    (lengthReadable : Readable original (head.s1 + 0x4#32))
    (pushed : Word) (lengthWord : WordAt memory (head.s1 + 0x4#32).toNat pushed)
    (cacheLowWritable : Writable original head.s2)
    (cacheHighWritable : Writable original (head.s2 + 0x4#32))
    (cacheOutsideCode : ∀ byte, (head.s2.toNat ≤ byte ∧ byte < head.s2.toNat + 4) ∨
      ((head.s2 + 0x4#32).toNat ≤ byte ∧ byte < (head.s2 + 0x4#32).toNat + 4) →
      (byte < base.toNat ∨ base.toNat + 4 * DeleteTable.instructions.length ≤ byte) ∧
      (byte < (rawVecBase base).toNat ∨
        (rawVecBase base).toNat + 4 * RawVec.instructions.length ≤ byte))
    (vector : RawVec.Call) (vectorHeader : vector.header = head.s1)
    (vectorIndex : vector.index = pushed) (vectorLength : vector.length = pushed)
    (vectorValue : vector.value = key) (valid : vector.valid)
    (header : RawVec.Header { original with mem := stored memory head key endWord } vector)
    (buffer : RawVec.Buffer (rawVecBase base) { original with mem := stored memory head key endWord } vector)
    (vectorOutsideCode : ∀ other : ByteMemory, vector.unchanged (stored memory head key endWord) other →
      ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * DeleteTable.instructions.length →
        other[byte]? = memory[byte]?) :
    ∃ (state : Snapshot) (after : ByteMemory),
      run (if endWord.toNat < head.s5.toNat then 43 else 44)
          (sync base { original with mem := memory } head) =
        some (sync base { original with mem := after } state) ∧
      state.pc = 0xa0#32 ∧ state.sp = head.sp ∧ state.s0 = head.s0 ∧ state.s1 = head.s1 ∧
      state.s2 = head.s2 ∧ state.s3 = head.s3 ∧ state.s4 = head.s4 ∧ state.s6 = head.s6 ∧
      state.s7 = head.s7 ∧
      state.s5 = (if endWord.toNat < head.s5.toNat then head.s5 else endWord) ∧
      state.a2 = lowAfter head.a2 key endWord ∧
      state.s8 = highAfter head.a2 head.s8 key endWord ∧
      state.a0 = head.a0 + 0x8#32 ∧
      WordAt after vector.header.toNat vector.data ∧
      WordAt after (vector.header.toNat + 4) (BitVec.ofNat 32 (vector.length.toNat + 1)) ∧
      WordAt after (vector.header.toNat + 8) vector.capacity ∧
      (∀ index, index < vector.length.toNat + 1 →
        WordAt after (vector.slot index) (vector.result index)) ∧
      vector.unchanged (stored memory head key endWord) after := by
  obtain ⟨returned, after, ran, facts, _, effects⟩ :=
    HelperScan.throughAppend frame memory imageOf rawImageOf head atHead key endWord different
      keyReadable keyWord endReadable endWordAt accepted lengthReadable pushed lengthWord
      cacheLowWritable cacheHighWritable cacheOutsideCode vector vectorHeader vectorIndex
      vectorValue header (fun _ => buffer)
  let machine := frame.mode.toMachineState
  obtain ⟨data, length, capacity, slots, keeps⟩ := effects valid
  have append : vector.index = vector.length := vectorIndex.trans vectorLength.symm
  have zero := facts.status.trans (appendStatus vector valid append)
  have count := appendCount vector valid append
  have image := imageOf after (vectorOutsideCode after keeps)
  let final : Snapshot := { returned with pc := 0xa0, a0 := returned.s10, a1 := returned.a0, a2 := returned.s9 }
  have resumed : run 4 (sync base { original with mem := after } returned) =
      some (sync base { original with mem := after } final) := by
    refine runStep (step108 machine image returned facts.pc) ?_
    refine runStep (step10c machine image _ rfl) ?_
    refine runStep (step110 machine image _ rfl) ?_
    have branch := step114 machine image
      { returned with pc := 0x114, a1 := returned.a0, a2 := returned.s9, a0 := returned.s10 } rfl
    have tested : (if returned.a0 = 0#32 then 0xa0#32 else 0x118#32) = 0xa0#32 := if_pos zero
    rw [tested] at branch
    exact runStep branch rfl
  refine ⟨final, after, ?_, rfl, facts.sp, facts.s0, facts.s1, facts.s2, facts.s3, facts.s4,
    facts.s6, facts.s7, facts.s5, facts.s9, facts.s8, facts.s10, data, length, capacity, slots, keeps⟩
  have costs : (if endWord.toNat < head.s5.toNat then 43 else 44) =
      ((if endWord.toNat < head.s5.toNat then 25 else 26) + vector.count) + 4 := by
    rw [count]
    split <;> decide
  rw [costs, runAdd, ran, Option.bind_some]
  exact resumed

/-- What the scan reads and writes, besides the frame. -/
structure Layout (base : Word) (original : Machine) (call : Call) (scratch : Scratch)
    (accepted : Nat) (start : ByteMemory) : Prop where
  rawCode : CodeImage RawVec.instructions (rawVecBase base) original
  helperStart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * DeleteTable.instructions.length →
    start[byte]? = original.mem[byte]?
  rawStart : ∀ byte, (rawVecBase base).toNat ≤ byte →
    byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length →
    start[byte]? = original.mem[byte]?
  helperApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * DeleteTable.instructions.length →
    ¬ Footprint call scratch accepted byte
  rawApart : ∀ byte, (rawVecBase base).toNat ≤ byte →
    byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length →
    ¬ Footprint call scratch accepted byte
  -- The candidate entries.
  entriesFit : call.search.slot call.length.toNat ≤ 2 ^ 32
  keyReadable : ∀ index < call.length.toNat, Readable original (call.search.wordSlot index)
  valueReadable : ∀ index < call.length.toNat,
    Readable original (call.search.wordSlot index + 0x4#32)
  keyWord : ∀ index < call.length.toNat, WordAt start (call.search.slot index) (call.old index).key
  valueWord : ∀ index < call.length.toNat,
    WordAt start (call.search.slot index + 4) (call.old index).value
  entriesApart : ∀ index < call.length.toNat, ∀ byte, call.search.slot index ≤ byte →
    byte < call.search.slot index + 8 → ¬ Footprint call scratch accepted byte
  -- The cache.
  cacheFits : call.cache.toNat + 8 ≤ 2 ^ 32
  cacheLowWritable : Writable original call.cache
  cacheHighWritable : Writable original (call.cache + 0x4#32)
  -- The deletion buffer.
  keysFits : call.keys.toNat + 12 ≤ 2 ^ 32
  keysDataReadable : Readable original call.keys
  keysLengthReadable : Readable original (call.keys + 0x4#32)
  keysCapacityReadable : Readable original (call.keys + 0x8#32)
  keysLengthWritable : Writable original (call.keys + 0x4#32)
  slotsFit : scratch.slot accepted ≤ 2 ^ 32
  slotWritable : ∀ index < accepted, Writable original (scratch.wordSlot index)
  slotsApartHeader : ∀ index < accepted, scratch.slot index + 4 ≤ call.keys.toNat ∨
    call.keys.toNat + 12 ≤ scratch.slot index
  cacheApartHeader : call.cache.toNat + 8 ≤ call.keys.toNat ∨ call.keys.toNat + 12 ≤ call.cache.toNat
  cacheApartSlots : ∀ index < accepted,
    scratch.slot index + 4 ≤ call.cache.toNat ∨ call.cache.toNat + 8 ≤ scratch.slot index
  capacity : accepted ≤ scratch.capacity.toNat

/-- A scan layout stated for one memory holds for another that agrees on both
code images and the candidate entries. -/
theorem Layout.transfer {base : Word} {original : Machine} {call : Call} {scratch : Scratch}
    {accepted : Nat} {start other : ByteMemory}
    (layout : Layout base original call scratch accepted start)
    (helper : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * DeleteTable.instructions.length →
      other[byte]? = start[byte]?)
    (raw : ∀ byte, (rawVecBase base).toNat ≤ byte →
      byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length → other[byte]? = start[byte]?)
    (entries : ∀ index < call.length.toNat, ∀ byte, call.search.slot index ≤ byte →
      byte < call.search.slot index + 8 → other[byte]? = start[byte]?) :
    Layout base original call scratch accepted other :=
  { layout with
    helperStart := fun byte low high => (helper byte low high).trans (layout.helperStart byte low high)
    rawStart := fun byte low high => (raw byte low high).trans (layout.rawStart byte low high)
    keyWord := fun index bound => (layout.keyWord index bound).congr fun byte low high =>
      entries index bound byte low (by omega)
    valueWord := fun index bound => (layout.valueWord index bound).congr fun byte low high =>
      entries index bound byte (by omega) (by omega) }

theorem scan {base returnAddress : Word} {original : Machine} {initial : Snapshot} {call : Call}
    {scratch : Scratch} {accepted : Nat} {start : ByteMemory}
    (frame : Frame base returnAddress original initial)
    (layout : Layout base original call scratch accepted start)
    (acceptedAll : ∀ t < accepted, call.position + 1 + t < call.length.toNat ∧
      (call.successor t).key.toNat ≤ call.limit.toNat)
    (head : Snapshot) (registers : Registers initial call 0 head)
    (memory : Memory call scratch start 0 start) :
    ∀ t ≤ accepted, ∃ (state : Snapshot) (after : ByteMemory),
      run (scanCount call t) (sync base { original with mem := start } head) =
        some (sync base { original with mem := after } state) ∧
      Registers initial call t state ∧ Memory call scratch start t after := by
  have machine := frame.mode.toMachineState
  intro t
  induction t with
  | zero => exact fun _ => ⟨head, start, rfl, registers, memory⟩
  | succ t previous =>
    intro below
    obtain ⟨state, before, ran, regs, mem⟩ := previous (by omega)
    obtain ⟨inside, within⟩ := acceptedAll t (by omega)
    let index := call.position + 1 + t
    let next := call.successor t
    have rawLength : RawVec.instructions.length = 30 := rfl
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
    have valid : vector.valid := by
      refine ⟨Nat.le_refl _, ?_⟩
      change (BitVec.ofNat 32 t).toNat < scratch.capacity.toNat
      rw [tNat]; have := layout.capacity; omega
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
    have dataApart : call.keys.toNat + 4 ≤ call.cache.toNat ∨ call.cache.toNat + 8 ≤ call.keys.toNat := by
      omega
    have lengthApart : call.keys.toNat + 4 + 4 ≤ call.cache.toNat ∨
        call.cache.toNat + 8 ≤ call.keys.toNat + 4 := by omega
    have capacityApart : call.keys.toNat + 8 + 4 ≤ call.cache.toNat ∨
        call.cache.toNat + 8 ≤ call.keys.toNat + 8 := by omega
    have slotApart := layout.cacheApartSlots
    have header : RawVec.Header { original with mem := stored before state next.key next.value }
        vector := by
      refine ⟨keysFits, Nonempty.mappedTransfer layout.keysLengthReadable rfl,
        Nonempty.mappedTransfer layout.keysCapacityReadable rfl, ?_, ?_⟩
      · exact storedWord mem.keysLength lengthApart
      · exact storedWord mem.keysCapacity capacityApart
    have slotOf (j : Nat) : vector.slot j = scratch.slot j := rfl
    have buffer : RawVec.Buffer (rawVecBase base)
        { original with mem := stored before state next.key next.value } vector := by
      refine ⟨?_, Nonempty.mappedTransfer layout.keysDataReadable rfl, ?_,
        Nonempty.mappedTransfer layout.keysLengthWritable rfl, ?_, fun j bound => ?_,
        fun j low high => ?_, fun j low high => ?_, fun j bound => ?_, fun j low high => ?_⟩
      · change scratch.data.toNat + 4 * ((BitVec.ofNat 32 t).toNat + 1) ≤ 2 ^ 32
        have fits := layout.slotsFit
        unfold Scratch.slot at fits
        rw [tNat]; omega
      · exact storedWord mem.keysData dataApart
      · change call.keys.toNat + 4 + 4 ≤ (rawVecBase base).toNat ∨
          (rawVecBase base).toNat + 120 ≤ call.keys.toNat + 4
        exact intervalApart (by decide) (by decide) fun byte low high inRaw =>
          layout.rawApart byte inRaw.1 (by rw [rawLength]; exact inRaw.2)
            (Or.inr (Or.inl ⟨low, high⟩))
      · change j < (BitVec.ofNat 32 t).toNat at bound
        rw [tNat] at bound
        have word := mem.pushed j bound
        exact storedWord word (slotApart j (by omega))
      · change (BitVec.ofNat 32 t).toNat ≤ j at low
        change j < (BitVec.ofNat 32 t).toNat at high
        omega
      · change (BitVec.ofNat 32 t).toNat ≤ j at low
        change j ≤ (BitVec.ofNat 32 t).toNat at high
        rw [tNat] at low high
        have same : j = t := by omega
        subst same
        exact Nonempty.mappedTransfer (layout.slotWritable j (by omega)) rfl
      · change j ≤ (BitVec.ofNat 32 t).toNat at bound
        rw [tNat] at bound
        change scratch.slot j + 4 ≤ call.keys.toNat ∨ call.keys.toNat + 12 ≤ scratch.slot j
        exact layout.slotsApartHeader j (by omega)
      · change (BitVec.ofNat 32 t).toNat ≤ j at low
        change j ≤ (BitVec.ofNat 32 t).toNat at high
        rw [tNat] at low high
        change scratch.slot j + 4 ≤ (rawVecBase base).toNat ∨
          (rawVecBase base).toNat + 120 ≤ scratch.slot j
        exact intervalApart (by decide) (by decide) fun byte lowByte highByte inRaw =>
          layout.rawApart byte inRaw.1 (by rw [rawLength]; exact inRaw.2)
            (Or.inr (Or.inr ⟨by unfold Scratch.slot at lowByte ⊢; omega,
              by unfold Scratch.slot at highByte ⊢; omega⟩))
    have nextIndex : next = call.old index := rfl
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
      have footprint : Footprint call scratch accepted byte := Or.inl (by omega)
      constructor
      · by_contra inCode
        simp only [not_or, Nat.not_lt] at inCode
        exact layout.helperApart byte inCode.1 (by omega) footprint
      · by_contra inCode
        simp only [not_or, Nat.not_lt] at inCode
        exact layout.rawApart byte inCode.1 (by omega) footprint
    have vectorOutsideCode : ∀ other : ByteMemory,
        vector.unchanged (stored before state next.key next.value) other →
        ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * DeleteTable.instructions.length →
          other[byte]? = before[byte]? := by
      intro other unchanged byte low high
      have outside := layout.helperApart byte low high
      unfold Footprint Scratch.slot at outside
      rw [unchanged byte (by change byte < call.keys.toNat + 4 ∨ call.keys.toNat + 8 ≤ byte; omega)
        (by change byte < scratch.data.toNat + 4 * (BitVec.ofNat 32 t).toNat ∨
            scratch.data.toNat + 4 * ((BitVec.ofNat 32 t).toNat + 1) ≤ byte
            rw [tNat]; omega)]
      exact storedOutside byte (by omega)
    obtain ⟨final, after, ranNext, pc, sp, s0, s1, s2, s3, s4, s6, s7, s5, low, high, cursor,
        dataAfter, lengthAfter, capacityAfter, slotsAfter, unchangedAfter⟩ :=
      iteration frame before imageOf rawImageOf state regs.pc next.key next.value different
        (by rw [regs.cursor]; exact layout.keyReadable index inside) keyWord
        (by rw [regs.cursor]; exact layout.valueReadable index inside) endWord
        (by rw [regs.limit]; exact Nat.not_lt.mpr within) (by rw [regs.keys]; exact layout.keysLengthReadable)
        (BitVec.ofNat 32 t) lengthWord (by rw [regs.cache]; exact layout.cacheLowWritable)
        (by rw [regs.cache]; exact layout.cacheHighWritable) cacheOutsideCode vector
        regs.keys.symm rfl rfl rfl valid header buffer vectorOutsideCode
    refine ⟨final, after, ?_, ?_, ?_⟩
    · rw [scanCount, runAdd, ran, Option.bind_some]
      unfold iterationCount
      rw [regs.endNew] at ranNext
      exact ranNext
    · refine ⟨pc, sp.trans regs.sp, s0.trans regs.header, s1.trans regs.keys, s2.trans regs.cache,
        s3.trans regs.stop, s4.trans regs.entry, s6.trans regs.limit, s7.trans regs.last, ?_, ?_, ?_,
        ?_⟩
      · rw [cursor, regs.cursor]
        exact call.search.slotNext index
      · rw [s5, regs.endNew]; rfl
      · rw [low, regs.low]; rfl
      · rw [high, regs.low, regs.high]; rfl
    · have unchangedAt (byte : Nat) (header : byte < call.keys.toNat + 4 ∨ call.keys.toNat + 8 ≤ byte)
          (slot : byte < scratch.slot t ∨ scratch.slot (t + 1) ≤ byte) :
          after[byte]? = (stored before state next.key next.value)[byte]? :=
        unchangedAfter byte header (by
          change byte < scratch.data.toNat + 4 * (BitVec.ofNat 32 t).toNat ∨
            scratch.data.toNat + 4 * ((BitVec.ofNat 32 t).toNat + 1) ≤ byte
          rw [tNat]; unfold Scratch.slot at slot; exact slot)
      have cacheKept (byte : Nat) (low : call.cache.toNat ≤ byte) (high : byte < call.cache.toNat + 8) :
          after[byte]? = (stored before state next.key next.value)[byte]? :=
        unchangedAt byte (by omega) (by have := slotApart t (by omega); unfold Scratch.slot at this ⊢; omega)
      refine ⟨?_, ?_, dataAfter, ?_, capacityAfter, ?_, ?_⟩
      · have inStored : WordAt (stored before state next.key next.value) call.cache.toNat
            (lowAfter (call.progress t).low next.key next.value) := by
          unfold stored cacheStored
          rw [regs.cache, regs.low]
          exact (wordAtStore _ _ _).storeOther (by rw [cacheHighNat]; omega)
        exact inStored.congr fun byte low high => cacheKept byte low (by omega)
      · have inStored : WordAt (stored before state next.key next.value) (call.cache.toNat + 4)
            (highAfter (call.progress t).low (call.progress t).high next.key next.value) := by
          unfold stored cacheStored
          rw [regs.cache, regs.low, regs.high, ← cacheHighNat]
          exact wordAtStore _ _ _
        exact inStored.congr fun byte low high => cacheKept byte (by omega) (by omega)
      · have length := lengthAfter
        change WordAt after (call.keys.toNat + 4) (BitVec.ofNat 32 ((BitVec.ofNat 32 t).toNat + 1))
          at length
        rw [tNat] at length
        exact length
      · intro j bound
        have slot := slotsAfter j (by change j < (BitVec.ofNat 32 t).toNat + 1; rw [tNat]; exact bound)
        change WordAt after (scratch.slot j)
          (if j < (BitVec.ofNat 32 t).toNat then (call.successor j).key
            else if j = (BitVec.ofNat 32 t).toNat then next.key else (call.successor (j - 1)).key)
          at slot
        rw [tNat] at slot
        by_cases below : j < t
        · rw [if_pos below] at slot; exact slot
        · have same : j = t := by omega
          rw [if_neg below, if_pos same] at slot
          subst same; exact slot
      · intro byte outside
        have notCurrent : ¬ Footprint call scratch t byte := fun footprint =>
          outside (footprint.mono (by omega))
        unfold Footprint Scratch.slot at outside
        rw [unchangedAt byte (by omega) (by unfold Scratch.slot; omega), storedOutside byte (by omega)]
        exact mem.others byte notCurrent

end Riscfree.RangeInsert.Bounded.HelperLoop
