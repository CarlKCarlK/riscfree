import RangeInsert.Bounded.HelperDrain
import RangeInsert.Bounded.HelperFullScan
import RangeInsert.DeleteExtra.Helper

namespace Riscfree.RangeInsert.Bounded.HelperRun

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec hiding Call Snapshot
open Helper
open HelperFrame
open HelperEntry (Arguments Entry entryCount toLoop)
open HelperLoop (Layout Registers scan scanCount)
open HelperFullScan (failureCount fullIteration)
open HelperFinish (extended exitAtEnd exitAtGap keepEnd extendEnd)
open HelperDrain
open DeleteExtra (Call Scratch Footprint Memory rawVecBase removeBase distance extendedLow extendedHigh
  ResultMemory HelperFootprint InEnd drained intervalApart)
open Nonempty (mappedTransfer)

set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

def InCode (base : Word) (byte : Nat) : Prop :=
  (base.toNat ≤ byte ∧ byte < base.toNat + 4 * DeleteTable.instructions.length) ∨
    ((removeBase base).toNat ≤ byte ∧ byte < (removeBase base).toNat + 144) ∨
    ((SortedMap.Remove.searchBase (removeBase base)).toNat ≤ byte ∧
      byte < (SortedMap.Remove.searchBase (removeBase base)).toNat + 52) ∨
    ((SortedMap.Remove.vectorBase (removeBase base)).toNat ≤ byte ∧
      byte < (SortedMap.Remove.vectorBase (removeBase base)).toNat + 100)

-- The selected range's end word.
/-- Shared premises of the helper scan, including a possibly short prefix. -/
structure ScanPremises (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) (scratch : Scratch) (accepted : Nat) : Prop where
  frame : Frame base returnAddress original initial
  arguments : Arguments initial call
  entry : Entry base original initial.sp call
  scan : Layout base original call scratch accepted original.mem
  accepts : ∀ t < accepted, call.position + 1 + t < call.length.toNat ∧
    (call.successor t).key.toNat ≤ call.limit.toNat
  keysData : WordAt original.mem call.keys.toNat scratch.data
  keysLength : WordAt original.mem (call.keys.toNat + 4) (BitVec.ofNat 32 0)
  keysCapacity : WordAt original.mem (call.keys.toNat + 8) scratch.capacity
  rawOutside : ∀ byte, (rawVecBase base).toNat ≤ byte →
    byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length → OutsideFrame initial.sp byte
  keysOutside : ∀ byte, call.keys.toNat ≤ byte → byte < call.keys.toNat + 12 →
    OutsideFrame initial.sp byte
  slotsOutside : ∀ byte, scratch.slot 0 ≤ byte → byte < scratch.slot accepted →
    OutsideFrame initial.sp byte

/-- Additional layout and stopping conditions for a completed scan. -/
structure Premises (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) (scratch : Scratch) (accepted : Nat) (capacity : Word) : Prop
    extends ScanPremises base returnAddress original initial call scratch accepted where
  drain : DrainLayout base original call capacity (call.after accepted) scratch accepted
    (frameBase initial.sp) original.mem
  stops : call.position + 1 + accepted = call.length.toNat ∨
    (call.position + 1 + accepted < call.length.toNat ∧
      call.limit.toNat < (call.successor accepted).key.toNat)
  endWritable : Writable original (call.search.wordSlot call.position + 0x4#32)
  codeOutside : ∀ byte, InCode base byte → OutsideFrame initial.sp byte
  headerOutside : ∀ byte, call.header.toNat ≤ byte → byte < call.header.toNat + 12 →
    OutsideFrame initial.sp byte
  endOutside : ∀ byte, InEnd call byte → OutsideFrame initial.sp byte
  codeApartScan : ∀ byte, InCode base byte → ¬ Footprint call scratch accepted byte
  headerApartScan : ∀ byte, call.header.toNat ≤ byte → byte < call.header.toNat + 12 →
    ¬ Footprint call scratch accepted byte
  endApart : ∀ byte, InEnd call byte →
    ¬ Footprint call scratch accepted byte ∧ ¬ InCode base byte ∧
      ¬ (call.keys.toNat ≤ byte ∧ byte < call.keys.toNat + 12) ∧
      ¬ (call.header.toNat ≤ byte ∧ byte < call.header.toNat + 12)
  keysApartDrain : ∀ byte, call.keys.toNat ≤ byte → byte < call.keys.toNat + 12 →
    ¬ DrainFootprint (frameBase initial.sp) call.header call.search call.position
      call.length.toNat byte
  cacheApartDrain : ∀ byte, call.cache.toNat ≤ byte → byte < call.cache.toNat + 8 →
    ¬ DrainFootprint (frameBase initial.sp) call.header call.search call.position
      call.length.toNat byte

/-- Through the scan: entry, then `accepted` iterations. Memory outside the
helper's frame differs from the entry memory only in the scan's footprint. -/
theorem ScanPremises.throughScan {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {scratch : Scratch} {accepted : Nat}
    (premises : ScanPremises base returnAddress original initial call scratch accepted) :
    ∃ (start : ByteMemory) (state : Snapshot) (memory : ByteMemory),
      run (entryCount call + scanCount call accepted) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } state) ∧
      (∀ byte, OutsideFrame initial.sp byte → start[byte]? = original.mem[byte]?) ∧
      Saved start initial ∧ Registers initial call accepted state ∧
      Memory call scratch start accepted memory := by
  have frame := premises.frame
  obtain ⟨start, head, toHead, agrees, saved, atHead⟩ := toLoop frame premises.arguments premises.entry
  have entry := premises.entry
  have layout := premises.scan.transfer
    (fun byte low high => agrees byte (frame.codeOutside byte low high))
    (fun byte low high => agrees byte (premises.rawOutside byte low high))
    (fun index bound byte low high => agrees byte (entry.entriesOutside index bound byte low high))
  have kept {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (outside : ∀ byte, address ≤ byte → byte < address + 4 → OutsideFrame initial.sp byte) :
      WordAt start address value :=
    word.congr fun byte low high => agrees byte (outside byte low high)
  have memory : Memory call scratch start 0 start :=
    ⟨kept entry.cacheLow fun byte low high => entry.cacheOutside byte low (by omega),
      kept entry.cacheHigh fun byte low high => entry.cacheOutside byte (by omega) (by omega),
      kept premises.keysData fun byte low high => premises.keysOutside byte low (by omega),
      kept premises.keysLength fun byte low high => premises.keysOutside byte (by omega) (by omega),
      kept premises.keysCapacity fun byte low high => premises.keysOutside byte (by omega) (by omega),
      fun _ bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl⟩
  obtain ⟨state, after, scanned, registers, memoryAfter⟩ :=
    HelperLoop.scan frame layout premises.accepts head (Registers.ofHead atHead) memory accepted
      (Nat.le_refl _)
  refine ⟨start, state, after, ?_, agrees, saved, registers, memoryAfter⟩
  rw [runAdd, toHead, Option.bind_some]
  exact scanned

/-- The memory at `+0x154`, after the scan and the extension. -/
structure Extended (call : Call) (scratch : Scratch) (accepted : Nat) (start : ByteMemory)
    (memory : ByteMemory) : Prop where
  cacheLow : WordAt memory call.cache.toNat (call.finalLow accepted)
  cacheHigh : WordAt memory (call.cache.toNat + 4) (call.finalHigh accepted)
  keysData : WordAt memory call.keys.toNat scratch.data
  keysLength : WordAt memory (call.keys.toNat + 4) (BitVec.ofNat 32 accepted)
  pushed : ∀ index < accepted, WordAt memory (scratch.slot index) (call.successor index).key
  endWord : WordAt memory (call.search.slot call.position + 4) (call.after accepted call.position).value
  others : ∀ byte, ¬ Footprint call scratch accepted byte → ¬ InEnd call byte →
    memory[byte]? = start[byte]?

def exitCount (call : Call) (accepted : Nat) : Nat :=
  if call.position + 1 + accepted = call.length.toNat then 1 else 3

def extendCount (call : Call) (accepted : Nat) : Nat :=
  if call.extended accepted then 14 else 1

theorem Premises.throughExtension {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {scratch : Scratch} {accepted : Nat} {capacity : Word}
    (premises : Premises base returnAddress original initial call scratch accepted capacity) :
    ∃ (start : ByteMemory) (state : Snapshot) (memory : ByteMemory),
      run (entryCount call + scanCount call accepted + exitCount call accepted +
          extendCount call accepted) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } state) ∧
      (∀ byte, OutsideFrame initial.sp byte → start[byte]? = original.mem[byte]?) ∧
      Saved start initial ∧ state.pc = 0x190#32 ∧ state.sp = frameBase initial.sp ∧
      state.s0 = call.header ∧ state.s1 = call.keys ∧
      Extended call scratch accepted start memory := by
  have frame := premises.frame
  have machine := frame.mode.toMachineState
  obtain ⟨start, state, memory, scanned, agrees, saved, regs, mem⟩ := premises.toScanPremises.throughScan
  have layout := premises.scan
  have entry := premises.entry
  -- The helper's code is unchanged in the scanned memory.
  have codeKept (other : ByteMemory) (same : ∀ byte, base.toNat ≤ byte →
      byte < base.toNat + 4 * DeleteTable.instructions.length → other[byte]? = memory[byte]?) :
      CodeImage DeleteTable.instructions base { original with mem := other } :=
    frame.code.withMemory other fun byte low high =>
      (same byte low high).trans ((mem.others byte (layout.helperApart byte low high)).trans
        (agrees byte (frame.codeOutside byte low high)))
  have image := codeKept memory fun _ _ _ => rfl
  have limitReached : ∃ exit : Snapshot,
      run (exitCount call accepted) (sync base { original with mem := memory } state) =
        some (sync base { original with mem := memory } exit) ∧
      exit.pc = 0x158#32 ∧ exit.sp = state.sp ∧ exit.s0 = state.s0 ∧ exit.s1 = state.s1 ∧
      exit.s2 = state.s2 ∧ exit.s3 = state.s3 ∧ exit.s4 = state.s4 ∧ exit.s5 = state.s5 := by
    rcases premises.stops with atEnd | ⟨inside, gap⟩
    · rw [exitCount, if_pos atEnd]
      exact ⟨_, exitAtEnd machine image state regs atEnd, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · have cursorNat := SortedMap.Search.slotNat entry.keys inside
      have different : state.a0 ≠ state.s7 := by
        rw [regs.cursor, regs.last]
        intro same
        have addresses := congrArg BitVec.toNat same
        rw [cursorNat] at addresses
        change call.search.slot (call.position + 1 + accepted) =
          call.search.slot call.length.toNat % 2 ^ 32 at addresses
        have fits := layout.entriesFit
        unfold SortedMap.Search.Call.slot at addresses fits
        by_cases full : call.search.data.toNat + 8 * call.length.toNat = 2 ^ 32
        · rw [full, Nat.mod_self] at addresses
          omega
        · rw [Nat.mod_eq_of_lt (by omega)] at addresses
          omega
      have readable : Readable original state.a0 := by
        rw [regs.cursor]; exact layout.keyReadable _ inside
      have key : WordAt memory state.a0.toNat (call.successor accepted).key := by
        rw [regs.cursor, cursorNat]
        exact (layout.keyWord _ inside).congr fun byte low high =>
          (mem.others byte (layout.entriesApart _ inside byte low (by omega))).trans
            (agrees byte (entry.entriesOutside _ inside byte low (by omega)))
      rw [exitCount, if_neg (by omega)]
      exact ⟨_, exitAtGap machine image state regs different _ readable key gap,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨exit, ranExit, pc, sp, header, keys, cache, stop, selected, maximum⟩ := limitReached
  have beforeExtension : run (entryCount call + scanCount call accepted + exitCount call accepted)
      (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } exit) := by
    rw [runAdd, scanned, Option.bind_some, ranExit]
  have exitSp := sp.trans regs.sp
  have exitHeader := header.trans regs.header
  have exitKeys := keys.trans regs.keys
  have exitCache := cache.trans regs.cache
  have exitStop := stop.trans regs.stop
  have exitEntry := selected.trans regs.entry
  have exitMax := maximum.trans regs.endNew
  by_cases grows : call.extended accepted
  · have beyond : ¬ exit.s5.toNat ≤ exit.s3.toNat := by
      rw [exitMax, exitStop]
      exact Nat.not_le.mpr grows
    have cacheHighNat : (exit.s2 + 0x4#32).toNat = call.cache.toNat + 4 := by
      rw [exitCache, BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by have := layout.cacheFits; change call.cache.toNat + 4 < 2 ^ 32; omega)
    have endNat : (exit.s4 + 0x4#32).toNat = call.search.slot call.position + 4 := by
      rw [exitEntry, BitVec.toNat_add, SortedMap.Search.slotNat entry.keys entry.found]
      have fits := layout.entriesFit
      have inside := entry.found
      change (call.search.slot call.position + 4) % 2 ^ 32 = _
      unfold SortedMap.Search.Call.slot at fits ⊢
      exact Nat.mod_eq_of_lt (by omega)
    have cacheCode (byte : Nat) (low : base.toNat ≤ byte)
        (high : byte < base.toNat + 4 * DeleteTable.instructions.length) :
        byte < call.cache.toNat ∨ call.cache.toNat + 8 ≤ byte := by
      have apart := layout.helperApart byte low high
      unfold Footprint at apart
      omega
    have endCode (byte : Nat) (low : base.toNat ≤ byte)
        (high : byte < base.toNat + 4 * DeleteTable.instructions.length) :
        byte < call.search.slot call.position + 4 ∨ call.search.slot call.position + 8 ≤ byte := by
      by_contra no
      push_neg at no
      exact (premises.endApart byte no).2.1 (Or.inl ⟨low, high⟩)
    have ran := extendEnd machine codeKept exit pc beyond
      (call.progress accepted).low (call.progress accepted).high
      (exitCache ▸ entry.cacheLowReadable) (exitCache ▸ mem.cacheLow)
      (exitCache ▸ entry.cacheHighReadable) (cacheHighNat ▸ mem.cacheHigh)
      (exitCache ▸ layout.cacheLowWritable) (exitCache ▸ layout.cacheHighWritable)
      (exitEntry ▸ premises.endWritable) (by
        intro byte low high
        rw [cacheHighNat, endNat, exitCache]
        have apart := cacheCode byte low high
        exact ⟨by omega, by omega, by have := endCode byte low high; omega⟩)
    let next : Snapshot :=
      { exit with
        pc := 0x190#32, a0 := extendedLow (call.progress accepted).low exit.s3 exit.s5,
        a1 := extendedHigh (call.progress accepted).low (call.progress accepted).high exit.s3 exit.s5,
        a2 := Step.lessWord (extendedLow (call.progress accepted).low exit.s3 exit.s5) 0x1#32 }
    refine ⟨start, next, extended memory exit (call.progress accepted).low
      (call.progress accepted).high, ?_, agrees, saved, rfl, exitSp, exitHeader, exitKeys, ?_⟩
    · rw [runAdd, beforeExtension, Option.bind_some, extendCount, if_pos grows]
      exact ran
    · dsimp only [extended]
      rw [cacheHighNat, endNat, exitCache, exitStop, exitMax]
      have endCache := intervalApart (first := call.search.slot call.position + 4) (width := 4)
        (other := call.cache.toNat) (otherWidth := 8) (by decide) (by decide) (by
          intro byte low high inside
          exact (premises.endApart byte ⟨low, by omega⟩).1 (Or.inl inside))
      have kept {address : Nat} {value : Word} (word : WordAt memory address value)
          (cacheApart : address + 4 ≤ call.cache.toNat ∨ call.cache.toNat + 8 ≤ address)
          (endApart : address + 4 ≤ call.search.slot call.position + 4 ∨
            call.search.slot call.position + 8 ≤ address) :
          WordAt (storeWord (storeWord (storeWord memory call.cache.toNat
              (extendedLow (call.progress accepted).low call.stop (call.progress accepted).endNew))
              (call.cache.toNat + 4) (extendedHigh (call.progress accepted).low
                (call.progress accepted).high call.stop (call.progress accepted).endNew))
              (call.search.slot call.position + 4) (call.progress accepted).endNew) address value :=
        ((word.storeOther (by omega)).storeOther (by omega)).storeOther (by omega)
      have headerApart := intervalApart (first := call.search.slot call.position + 4) (width := 4)
        (other := call.keys.toNat) (otherWidth := 12) (by decide) (by decide) (by
          intro byte low high inside
          exact (premises.endApart byte ⟨low, by omega⟩).2.2.1 inside)
      have cacheApart := layout.cacheApartHeader
      refine ⟨?_, ?_, kept mem.keysData (by omega) (by omega),
        kept mem.keysLength (by omega) (by omega), ?_, ?_, ?_⟩
      · simp only [Call.finalLow, if_pos grows]
        exact ((wordAtStore _ _ _).storeOther (by omega)).storeOther (by omega)
      · simp only [Call.finalHigh, if_pos grows]
        exact (wordAtStore _ _ _).storeOther (by omega)
      · intro index bound
        have low : scratch.slot 0 ≤ scratch.slot index := by unfold Scratch.slot; omega
        have high : scratch.slot index + 4 ≤ scratch.slot accepted := by unfold Scratch.slot; omega
        have cacheSlots := layout.cacheApartSlots index bound
        have endSlots := intervalApart (first := call.search.slot call.position + 4) (width := 4)
          (other := scratch.slot index) (otherWidth := 4) (by decide) (by decide) (by
            intro byte left right inside
            exact (premises.endApart byte ⟨left, by omega⟩).1
              (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        exact kept (mem.pushed index bound) (by omega) (by omega)
      · simp only [Call.after, true_and, if_pos grows]
        exact wordAtStore _ _ _
      · intro byte outside endOutside
        have cacheOutside : byte < call.cache.toNat ∨ call.cache.toNat + 8 ≤ byte := by
          unfold Footprint at outside
          omega
        unfold InEnd at endOutside
        rw [storeWordOutside _ _ _ _ (by omega), storeWordOutside _ _ _ _ (by omega),
          storeWordOutside _ _ _ _ (by omega)]
        exact mem.others byte outside
  · have within : exit.s5.toNat ≤ exit.s3.toNat := by
      rw [exitMax, exitStop]
      exact Nat.le_of_not_gt grows
    refine ⟨start, { exit with pc := 0x190#32 }, memory, ?_, agrees, saved,
      rfl, exitSp, exitHeader, exitKeys, ?_⟩
    · rw [runAdd, beforeExtension, Option.bind_some, extendCount, if_neg grows]
      exact keepEnd machine image exit pc within
    · refine ⟨?_, ?_, mem.keysData, mem.keysLength, mem.pushed,
        ?_, fun byte outside _ => mem.others byte outside⟩
      · simpa only [Call.finalLow, if_neg grows] using mem.cacheLow
      · simpa only [Call.finalHigh, if_neg grows] using mem.cacheHigh
      · simp only [Call.after, and_false, grows, if_false]
        refine (layout.valueWord _ entry.found).congr fun byte low high => ?_
        have startKept := agrees byte (entry.entriesOutside _ entry.found byte (by omega) (by omega))
        exact (mem.others byte (layout.entriesApart _ entry.found byte (by omega) (by omega))).trans startKept

def removalCount (call : Call) (capacity : Word) (accepted : Nat) : Nat :=
  if accepted = 0 then 2 else 4 + drainCount call capacity (call.after accepted) accepted

private theorem Premises.entriesAfterExtension {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {scratch : Scratch} {accepted : Nat} {capacity : Word}
    (premises : Premises base returnAddress original initial call scratch accepted capacity)
    {start memory : ByteMemory}
    (agrees : ∀ byte, OutsideFrame initial.sp byte → start[byte]? = original.mem[byte]?)
    (extended : Extended call scratch accepted start memory) :
    ∀ index < call.length.toNat, PairAt memory (call.search.slot index) (call.after accepted index) := by
  intro index inside
  have unchanged (byte : Nat) (low : call.search.slot index ≤ byte)
      (high : byte < call.search.slot index + 8) (apart : ¬ InEnd call byte) :
      memory[byte]? = original.mem[byte]? :=
    (extended.others byte (premises.scan.entriesApart index inside byte low high) apart).trans
      (agrees byte (premises.entry.entriesOutside index inside byte low high))
  have keyApart (byte : Nat) (low : call.search.slot index ≤ byte)
      (high : byte < call.search.slot index + 4) : ¬ InEnd call byte := by
    unfold InEnd SortedMap.Search.Call.slot at *
    omega
  constructor
  · rw [call.after_key]
    exact (premises.scan.keyWord index inside).congr fun byte low high =>
      unchanged byte low (by omega) (keyApart byte low high)
  · by_cases selected : index = call.position
    · subst index
      exact extended.endWord
    · simp only [Call.after, selected, false_and, if_false]
      refine (premises.scan.valueWord index inside).congr fun byte low high => ?_
      apply unchanged byte (by omega) (by omega)
      unfold InEnd SortedMap.Search.Call.slot at *
      omega

/-- From entry to the restored helper's epilogue entry, with the final map,
cache, and scratch prefix known. -/
theorem Premises.throughRemoval {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {scratch : Scratch} {accepted : Nat} {capacity : Word}
    (premises : Premises base returnAddress original initial call scratch accepted capacity) :
    ∃ (start middle : ByteMemory) (state : Snapshot) (memory : ByteMemory),
      run (entryCount call + scanCount call accepted + exitCount call accepted +
          extendCount call accepted + removalCount call capacity accepted)
          (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } state) ∧
      (∀ byte, OutsideFrame initial.sp byte → start[byte]? = original.mem[byte]?) ∧
      Saved start initial ∧ Extended call scratch accepted start middle ∧
      state.pc = 0x1c0#32 ∧ state.sp = frameBase initial.sp ∧
      DrainMemory call (call.after accepted) (frameBase initial.sp) middle accepted memory := by
  obtain ⟨start, state, middle, ran, agrees, saved, pc, sp, header, keys, extension⟩ :=
    premises.throughExtension
  have codeKept (byte : Nat) (inside : InCode base byte) :
      middle[byte]? = original.mem[byte]? :=
    (extension.others byte (premises.codeApartScan byte inside)
      (fun endByte => (premises.endApart byte endByte).2.1 inside)).trans
      (agrees byte (premises.codeOutside byte inside))
  have headerKept (byte : Nat) (low : call.header.toNat ≤ byte)
      (high : byte < call.header.toNat + 12) : middle[byte]? = original.mem[byte]? :=
    (extension.others byte (premises.headerApartScan byte low high)
      (fun endByte => (premises.endApart byte endByte).2.2.2 ⟨low, high⟩)).trans
      (agrees byte (premises.headerOutside byte low high))
  have layout := premises.drain.transfer codeKept (fun byte low high _ => headerKept byte low high)
  have helperKept : CodeAgreesFor (4 * DeleteTable.instructions.length) base original.mem middle :=
    fun byte low high => codeKept byte (Or.inl ⟨low, high⟩)
  have image : CodeImage DeleteTable.instructions base { original with mem := middle } :=
    premises.frame.code.withMemory middle helperKept
  have keysLengthNat : (state.s1 + 0x4#32).toNat = call.keys.toNat + 4 := by
    rw [keys, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by
      have := premises.scan.keysFits
      change call.keys.toNat + 4 < 2 ^ 32
      omega)
  have lengthWord : WordAt middle (state.s1 + 0x4#32).toNat (BitVec.ofNat 32 accepted) := by
    rw [keysLengthNat]
    exact extension.keysLength
  obtain ⟨noneEntry, someEntry⟩ := drainEntry (scratch := scratch)
    premises.frame.mode.toMachineState image state pc
    (keys ▸ premises.scan.keysLengthReadable) lengthWord (keys ▸ premises.scan.keysDataReadable)
    (keys ▸ extension.keysData) layout.keyCountFits
  have drainStart : DrainMemory call (call.after accepted) (frameBase initial.sp) middle 0 middle := by
    constructor
    · simp only [Nat.sub_zero, Insert.ofWordNat]
      apply premises.entry.header.lengthWord.congr
      intro byte low high
      change call.header.toNat + 4 ≤ byte at low
      change byte < call.header.toNat + 4 + 4 at high
      exact headerKept byte (by omega) (by omega)
    · intro index inside
      simp only [Nat.sub_zero] at inside
      have word := premises.entriesAfterExtension agrees extension index inside
      simpa [drained] using word
    · exact fun _ _ => rfl
  by_cases none : accepted = 0
  · refine ⟨start, middle, { state with pc := 0x1c0#32, s2 := BitVec.ofNat 32 accepted },
      middle, ?_, agrees, saved, extension, rfl, sp, ?_⟩
    · rw [runAdd, ran, Option.bind_some, removalCount, if_pos none]
      exact noneEntry none
    · simpa only [none] using drainStart
  · let head : Snapshot :=
      { state with
        pc := 0x1a0#32, s1 := scratch.wordSlot 0,
        s2 := BitVec.ofNat 32 (4 * (accepted - 0)) }
    have regs : DrainRegisters call scratch accepted (frameBase initial.sp) 0 head :=
      ⟨by change 0x1a0#32 = _; rw [if_neg (Ne.symm none)], sp, header, rfl, rfl⟩
    have collected (index : Nat) (inside : index < accepted) :
        WordAt middle (scratch.slot index) ((call.after accepted) (call.position + 1 + index)).key := by
      rw [call.after_key]
      exact extension.pushed index inside
    obtain ⟨final, after, drainedRun, registers, result⟩ :=
      HelperDrain.drain premises.frame layout collected head regs drainStart accepted (Nat.le_refl _)
    refine ⟨start, middle, final, after, ?_, agrees, saved, extension, ?_, registers.sp, result⟩
    · rw [runAdd, ran, Option.bind_some, removalCount, if_neg none, runAdd,
        someEntry (Nat.pos_of_ne_zero none), Option.bind_some]
      exact drainedRun
    · simpa only [if_pos rfl] using registers.pc

private theorem Premises.savedOutsideDrain {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {scratch : Scratch} {accepted : Nat} {capacity : Word}
    (premises : Premises base returnAddress original initial call scratch accepted capacity)
    (byte : Nat) (inside : ¬ OutsideFrame initial.sp byte) :
    ¬ DrainFootprint (frameBase initial.sp) call.header call.search call.position
      call.length.toNat byte := by
  intro footprint
  rcases footprint with nested | header | slots
  · have baseNat : (frameBase initial.sp).toNat = initial.sp.toNat - 48 := by
      have address := frameAddress premises.frame.frameFits 0#32 (by decide)
      simpa only [BitVec.add_zero, show (0#32).toNat = 0 by decide, Nat.add_zero] using address
    exact inside (Or.inl (by rw [baseNat] at nested; exact nested.2))
  · exact inside (premises.headerOutside byte (by omega) (by omega))
  · let index := (byte - call.search.data.toNat) / 8
    unfold SortedMap.Search.Call.slot at slots
    have bound : index < call.length.toNat := by
      dsimp [index]
      omega
    apply inside (premises.entry.entriesOutside index bound byte ?_ ?_)
    all_goals
      unfold SortedMap.Search.Call.slot index
      omega

private theorem savedTransfer {initial : Snapshot} {start other : ByteMemory}
    (saved : Saved start initial) (fits : 48 ≤ initial.sp.toNat)
    (kept : ∀ byte, ¬ OutsideFrame initial.sp byte → other[byte]? = start[byte]?) :
    Saved other initial := by
  have word {offset value : Word} (small : offset.toNat ≤ 44)
      (contents : WordAt start (frameBase initial.sp + offset).toNat value) :
      WordAt other (frameBase initial.sp + offset).toNat value := by
    apply contents.congr
    intro byte low high
    rw [frameAddress fits offset small] at low high
    apply kept byte
    unfold OutsideFrame
    omega
  have bottom : WordAt other (frameBase initial.sp).toNat initial.s10 := by
    have bottomWord : WordAt start (frameBase initial.sp + 0#32).toNat initial.s10 := by
      rw [BitVec.add_zero]; exact saved.s10
    simpa only [BitVec.add_zero] using word (offset := 0#32) (by decide) bottomWord
  exact ⟨word (by decide) saved.ra, word (by decide) saved.s0, word (by decide) saved.s1,
    word (by decide) saved.s2, word (by decide) saved.s3, word (by decide) saved.s4,
    word (by decide) saved.s5, word (by decide) saved.s6, word (by decide) saved.s7,
    word (by decide) saved.s8, word (by decide) saved.s9, bottom⟩

def successCount (call : Call) (capacity : Word) (accepted : Nat) : Nat :=
  entryCount call + scanCount call accepted + exitCount call accepted +
    extendCount call accepted + removalCount call capacity accepted + 16

/-- Run the linked helper to its aligned return address. Its epilogue restores
the saved registers and stack pointer. The map contains the original prefix,
the selected range with its final end, and the unabsorbed suffix. -/
theorem Premises.run {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {scratch : Scratch} {accepted : Nat} {capacity : Word}
    (premises : Premises base returnAddress original initial call scratch accepted capacity) :
    ∃ (state : Snapshot) (memory : ByteMemory),
      Riscfree.RV32.run (successCount call capacity accepted) original =
        some (sync base { original with mem := memory } (restore initial { state with a0 := 0 } (returnAddress - base))) ∧
      ResultMemory initial.sp call scratch accepted original.mem memory := by
  obtain ⟨start, middle, state, memory, ran, agrees, saved, extension, pc, sp, result⟩ :=
    premises.throughRemoval
  have kept (byte : Nat) (inside : ¬ OutsideFrame initial.sp byte) :
      memory[byte]? = start[byte]? := by
    have scanOutside : ¬ Footprint call scratch accepted byte := by
      intro footprint
      rcases footprint with cache | keys | slots
      · exact inside (premises.entry.cacheOutside byte cache.1 cache.2)
      · exact inside (premises.keysOutside byte (by omega) (by omega))
      · exact inside (premises.slotsOutside byte slots.1 slots.2)
    exact (result.others byte (premises.savedOutsideDrain byte inside)).trans
      (extension.others byte scanOutside (fun atEnd => inside (premises.endOutside byte atEnd)))
  have finalSaved := savedTransfer saved premises.frame.frameFits kept
  have codeKept (byte : Nat) (inside : InCode base byte) :
      memory[byte]? = original.mem[byte]? :=
    (result.others byte (premises.drain.codeKept byte inside).2).trans
      ((extension.others byte (premises.codeApartScan byte inside)
        (fun endByte => (premises.endApart byte endByte).2.1 inside)).trans
        (agrees byte (premises.codeOutside byte inside)))
  have helperKept : CodeAgreesFor (4 * DeleteTable.instructions.length) base original.mem memory :=
    fun byte low high => codeKept byte (Or.inl ⟨low, high⟩)
  have image : CodeImage DeleteTable.instructions base { original with mem := memory } :=
    premises.frame.code.withMemory memory helperKept
  refine ⟨state, memory, ?_, result.lengthWord, result.entries, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have epilogue := premises.frame.epilogue memory image finalSaved
      { state with pc := 0x120, a0 := 0 } rfl sp
    have tail : Riscfree.RV32.run 16 (sync base { original with mem := memory } state) =
        some (sync base { original with mem := memory }
          (restore initial { state with a0 := 0 } (returnAddress - base))) := by
      refine runStep (step1c0 premises.frame.mode.toMachineState image state pc) ?_
      refine runStep (step1c4 premises.frame.mode.toMachineState image _ rfl) ?_
      exact epilogue
    rw [← premises.frame.entry] at ran
    rw [successCount, runAdd, ran, Option.bind_some]
    exact tail
  · exact extension.cacheLow.congr fun byte low high =>
      result.others byte (premises.cacheApartDrain byte low (by omega))
  · exact extension.cacheHigh.congr fun byte low high =>
      result.others byte (premises.cacheApartDrain byte (by omega) (by omega))
  · exact extension.keysData.congr fun byte low high =>
      result.others byte (premises.keysApartDrain byte low (by omega))
  · exact extension.keysLength.congr fun byte low high =>
      result.others byte (premises.keysApartDrain byte (by omega) (by omega))
  · intro index bound
    exact (extension.pushed index bound).congr fun byte low high =>
      result.others byte (premises.drain.collectedApart index bound byte low high)
  · intro byte outside
    simp only [HelperFootprint, not_or, not_not] at outside
    exact (result.others byte outside.2.2.2).trans
      ((extension.others byte outside.2.1 outside.2.2.1).trans (agrees byte outside.1))

def fullCount (call : Call) (capacity : Nat) : Nat :=
  entryCount call + scanCount call capacity + failureCount call capacity + 20

/-- On a short scratch buffer, process precisely its capacity's worth of
successful keys. The next eligible key returns FULL before removal. -/
theorem ScanPremises.runFull {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {scratch : Scratch}
    (premises : ScanPremises base returnAddress original initial call scratch scratch.capacity.toNat)
    (short : scratch.capacity.toNat < call.acceptCount) :
    ∃ (state : Snapshot) (memory : ByteMemory),
      Riscfree.RV32.run (fullCount call scratch.capacity.toNat) original =
        some (sync base { original with mem := memory }
          (restore initial { state with a0 := 1, a1 := 1, a2 := state.s9 } (returnAddress - base))) ∧
      ∀ byte, OutsideFrame initial.sp byte → ¬ Footprint call scratch scratch.capacity.toNat byte →
        memory[byte]? = original.mem[byte]? := by
  obtain ⟨start, head, before, ran, agrees, saved, registers, memory⟩ := premises.throughScan
  obtain ⟨state, after, appended, pc, sp, status, kept⟩ :=
    fullIteration premises.frame (premises.scan.transfer
      (fun byte low high => agrees byte (premises.frame.codeOutside byte low high))
      (fun byte low high => agrees byte (premises.rawOutside byte low high))
      (fun index valid byte low high => agrees byte (premises.entry.entriesOutside index valid byte low high)))
      rfl short head registers memory
  have finalSaved := savedTransfer saved premises.frame.frameFits (fun byte inside =>
    kept byte fun footprint => by
      rcases footprint with cache | key | slot
      · exact inside (premises.entry.cacheOutside byte cache.1 cache.2)
      · exact inside (premises.keysOutside byte (by omega) (by omega))
      · exact inside (premises.slotsOutside byte slot.1 slot.2))
  have image := premises.frame.code.withMemory after (fun byte low high =>
    (kept byte (premises.scan.helperApart byte low high)).trans
      (agrees byte (premises.frame.codeOutside byte low high)))
  have returned := premises.frame.returnFull after image finalSaved state pc
    (sp.trans registers.sp) status
  refine ⟨state, after, ?_, fun byte outside unchanged => (kept byte unchanged).trans (agrees byte outside)⟩
  rw [← premises.frame.entry] at ran
  rw [fullCount, runAdd, runAdd, ran, Option.bind_some, appended, Option.bind_some]
  exact returned

end Riscfree.RangeInsert.Bounded.HelperRun
