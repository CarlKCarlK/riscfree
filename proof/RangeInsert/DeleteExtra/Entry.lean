import RangeInsert.DeleteExtra.Frame
import SortedMap.Search.Correct
import RangeInsert.Nonempty.Predecessor

/-! From the `delete_extra` helper's entry to its scan loop head at `+0xf0`:
the prologue, the argument moves, the call to `sorted_map_lower_bound`
(composed from `SortedMap.Search.sortedMapSearchSailRun`), the test that the
suffix is nonempty, and the iterator setup. -/

namespace Riscfree.RangeInsert.DeleteExtra

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open DeleteTable (instructions)
open Nonempty (mappedTransfer)

set_option maxHeartbeats 2000000

-- `sorted_map_lower_bound` lies 0xf8 bytes before the helper.
def lowerBoundOffset : Word := 0xffffff08
def lowerBoundBase (base : Word) : Word := base + lowerBoundOffset

/-- The helper's view of the map, the cached length, and the deletion keys. -/
structure Call where
  -- The address of the word that holds the map header pointer.
  mapRef : Word
  header : Word
  length : Word
  data : Word
  old : Nat → Pair
  -- The address of the u64 cached length, and its two words.
  cache : Word
  low : Word
  high : Word
  start : Word
  stop : Word
  -- The deletion-key RawVec header.
  keys : Word

namespace Call

def search (call : Call) : SortedMap.Search.Call :=
  ⟨call.header, call.start, call.length, call.data, call.old⟩

-- The index of the first entry whose key is at least `start`.
def position (call : Call) : Nat := call.search.result .lower

-- The scan accepts a successor whose key is at most this limit. It is
-- `stop + 1`, or `stop` when `stop + 1` wraps.
def limit (call : Call) : Word :=
  if (call.stop + 1#32).toNat < call.stop.toNat then call.stop else call.stop + 1#32

def entryCount (call : Call) : Nat :=
  (if (call.stop + 1#32).toNat < call.stop.toNat then 40 else 41) + call.search.count .lower

theorem position_le (call : Call) : call.position ≤ call.length.toNat :=
  call.search.result_le .lower

end Call

/-- Register arguments: the map reference, the cache, `start`, `stop`, and
the deletion keys. -/
structure Arguments (initial : Snapshot) (call : Call) : Prop where
  mapRef : initial.a0 = call.mapRef
  cache : initial.a1 = call.cache
  start : initial.a2 = call.start
  stop : initial.a3 = call.stop
  keys : initial.a4 = call.keys

/-- What the entry segment reads, all outside the helper's frame. The suffix
from `start` must be nonempty: the routine traps otherwise. -/
structure Entry (base : Word) (original : Machine) (sp : Word) (call : Call) : Prop where
  searchCode : CodeImage (SortedMap.Search.instructions .lower) (lowerBoundBase base) original
  searchOutside : ∀ byte, (lowerBoundBase base).toNat ≤ byte →
    byte < (lowerBoundBase base).toNat + 52 → OutsideFrame sp byte
  mapRefReadable : Readable original call.mapRef
  mapRefWord : WordAt original.mem call.mapRef.toNat call.header
  mapRefOutside : ∀ byte, call.mapRef.toNat ≤ byte → byte < call.mapRef.toNat + 4 →
    OutsideFrame sp byte
  header : SortedMap.Search.Header original call.search
  keys : SortedMap.Search.Keys original call.search
  headerOutside : ∀ byte, call.header.toNat ≤ byte → byte < call.header.toNat + 8 →
    OutsideFrame sp byte
  entriesOutside : ∀ index < call.length.toNat, ∀ byte, call.search.slot index ≤ byte →
    byte < call.search.slot index + 8 → OutsideFrame sp byte
  cacheFits : call.cache.toNat + 8 ≤ 2 ^ 32
  cacheLowReadable : Readable original call.cache
  cacheHighReadable : Readable original (call.cache + 4#32)
  cacheLow : WordAt original.mem call.cache.toNat call.low
  cacheHigh : WordAt original.mem (call.cache.toNat + 4) call.high
  cacheOutside : ∀ byte, call.cache.toNat ≤ byte → byte < call.cache.toNat + 8 →
    OutsideFrame sp byte
  found : call.position < call.length.toNat

-- The snapshot when `sorted_map_lower_bound` is entered.
def calling (base : Word) (initial : Snapshot) (header : Word) : Snapshot :=
  { initial with
    pc := lowerBoundOffset, sp := frameBase initial.sp, ra := base + 0x54#32,
    s0 := header, s1 := initial.a4, s2 := initial.a1, s3 := initial.a3,
    a0 := header, a1 := initial.a2 }

def searchEntry (state : Snapshot) : SortedMap.Search.Snapshot :=
  { a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4 }

def afterSearch (state : Snapshot) (endState : SortedMap.Search.Snapshot) : Snapshot :=
  { state with
    pc := 0x54#32, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2, a3 := endState.a3,
    a4 := endState.a4 }

theorem searchInside : ∀ index ∈ tracked SortedMap.Search.Snapshot, index ∈ tracked Snapshot := by
  decide

/-- The registers at the scan loop head before the first iteration. -/
structure Head (initial : Snapshot) (call : Call) (state : Snapshot) : Prop where
  pc : state.pc = 0xf0#32
  sp : state.sp = frameBase initial.sp
  header : state.s0 = call.header
  keys : state.s1 = call.keys
  cache : state.s2 = call.cache
  stop : state.s3 = call.stop
  entry : state.s4 = call.search.wordSlot call.position
  endNew : state.s5 = call.stop
  limit : state.s6 = call.limit
  last : state.s7 = call.search.wordSlot call.length.toNat
  high : state.s8 = call.high
  low : state.a1 = call.low
  cursor : state.a3 = call.search.wordSlot (call.position + 1)

-- `sltiu`, `addi -1`, and `and` keep the entry pointer when the position is
-- not the length.
theorem keepWhenDifferent {left right value : Word} (different : left ≠ right) :
    (Step.lessWord (left ^^^ right) 0x1#32 + 0xffffffff#32) &&& value = value := by
  have nonzero : left ^^^ right ≠ 0#32 := by
    intro zero
    apply different
    have back := congrArg (· ^^^ right) zero
    simpa [BitVec.xor_assoc] using back
  have positive : ¬ (left ^^^ right).toNat < (0x1#32).toNat := by
    intro small
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    change (left ^^^ right).toNat < 1 at small
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  unfold Step.lessWord
  rw [if_neg positive, show (0#1).setWidth 32 + 0xffffffff#32 = BitVec.allOnes 32 by decide,
    BitVec.allOnes_and]

/-- From entry to the loop head: `entryCount` instructions. Only the frame
changes in memory. -/
theorem Frame.toLoop {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (frame : Frame base returnAddress original initial)
    (arguments : Arguments initial call) (entry : Entry base original initial.sp call) :
    ∃ (memory : ByteMemory) (state : Snapshot),
      run call.entryCount (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } state) ∧
      (∀ byte, OutsideFrame initial.sp byte → memory[byte]? = original.mem[byte]?) ∧
      Saved memory initial ∧ Head initial call state := by
  obtain ⟨memory, begun, agrees, saved⟩ := frame.prologue
  have machine := frame.mode.toMachineState
  have image := frame.imageAt memory agrees
  have fits := frame.frameFits
  -- A word outside the frame reads the same after the prologue.
  have kept {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (outside : ∀ byte, address ≤ byte → byte < address + 4 → OutsideFrame initial.sp byte) :
      WordAt memory address value :=
    word.congr fun byte low high => agrees byte (outside byte low high)
  have lengthSmall := call.length.isLt
  have positionBound := entry.found
  have positive : 0 < call.length.toNat := by omega
  have keys := entry.keys
  -- To the call.
  have toCall : run 21 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } (calling base initial call.header)) := by
    rw [show 21 = 13 + 8 from rfl, runAdd, begun, Option.bind_some]
    refine runStep (step34 machine image _ rfl) ?_
    refine runStep (step38 machine image _ rfl) ?_
    refine runStep (step3c machine image _ rfl call.header (by
      change Readable original initial.a0
      rw [arguments.mapRef]; exact entry.mapRefReadable) (by
      change WordAt memory initial.a0.toNat call.header
      rw [arguments.mapRef]; exact kept entry.mapRefWord entry.mapRefOutside)) ?_
    refine runStep (step40 machine image _ rfl) ?_
    refine runStep (step44 machine image _ rfl) ?_
    refine runStep (step48 machine image _ rfl) ?_
    refine runStep (step4c machine image _ rfl) ?_
    exact runStep (step50 machine image _ rfl rfl) rfl
  -- The verified search.
  let called := calling base initial call.header
  let entered := sync base { original with mem := memory } called
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame called _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have enteredMem : entered.mem = memory := syncMem called
  have routineEntered :
      entered = sync (lowerBoundBase base) entered { searchEntry called with pc := 0 } := by
    have inside := syncInside (frame := { original with mem := memory }) base (lowerBoundBase base)
      called called (searchEntry called) searchInside (fun index _ => by fin_cases index <;> rfl)
      (BitVec.add_zero _).symm
    exact inside.symm
  have returnAligned : (base + 0x54#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat frame.code.aligned _ (by decide)
  obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
  have mode : MachineMode entered (base + 0x54#32) :=
    { (machine.withMemory memory).atSync base called with
      returnLow := by rw [BitVec.and_comm]; exact maskEven _ returnBit0
      returnNext := returnBit1
      ra := syncRead called (index := 1) (by decide) }
  have searchImage :
      CodeImage (SortedMap.Search.instructions .lower) (lowerBoundBase base) entered :=
    (entry.searchCode.withMemory memory fun byte low high => by
      rw [SortedMap.Search.instructionsLength] at high
      exact agrees byte (entry.searchOutside byte low (by omega))).atSync base called
  have headerWord : WordAt memory (call.header.toNat + 4) call.length :=
    kept entry.header.lengthWord fun byte low high =>
      entry.headerOutside byte (by change call.header.toNat + 4 ≤ byte at low; omega)
        (by change byte < call.header.toNat + 4 + 4 at high; omega)
  have dataWord : WordAt memory call.header.toNat call.data :=
    kept keys.dataWord fun byte low high =>
      entry.headerOutside byte low (by change byte < call.header.toNat + 4 at high; omega)
  have searchHeader : SortedMap.Search.Header entered call.search :=
    ⟨entry.header.fits, mappedTransfer entry.header.lengthReadable regions,
      by rw [enteredMem]; exact headerWord⟩
  have searchKeys (_ : 0 < call.search.length.toNat) : SortedMap.Search.Keys entered call.search :=
    ⟨keys.fits, mappedTransfer keys.dataReadable regions, by rw [enteredMem]; exact dataWord,
      fun index bound => mappedTransfer (keys.readable index bound) regions,
      fun index bound => by
        rw [enteredMem]
        exact kept (keys.keyWord index bound) fun byte low high =>
          entry.entriesOutside index bound byte low (by omega)⟩
  obtain ⟨endState, ran, endPc, result, -⟩ := SortedMap.Search.sortedMapSearchSailRun .lower
    (lowerBoundBase base) (base + 0x54#32) entered call.search (searchEntry called) routineEntered
    rfl (by change initial.a2 = call.start; exact arguments.start)
    (SortedMap.Search.Environment.ofMachine mode searchImage) searchHeader searchKeys
  have back : run (call.search.count .lower) entered =
      some (sync base { original with mem := memory } (afterSearch called endState)) := by
    rw [ran]
    have inside := syncInside (frame := { original with mem := memory }) base (lowerBoundBase base)
      called (afterSearch called endState) endState searchInside
      (fun index _ => by fin_cases index <;> rfl) (by
        change base + 0x54#32 = lowerBoundBase base + endState.pc
        rw [endPc, BitVec.add_comm (lowerBoundBase base), BitVec.sub_add_cancel])
    exact congrArg some inside
  have toBack : run (21 + call.search.count .lower) (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } (afterSearch called endState)) := by
    rw [runAdd, toCall, Option.bind_some]
    exact back
  -- Facts about the search result and the map's words.
  have positionNat : (BitVec.ofNat 32 call.position).toNat = call.position := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have different : endState.a0 ≠ call.length := by
    rw [result]
    intro same
    have toNat := congrArg BitVec.toNat same
    change (BitVec.ofNat 32 call.position).toNat = _ at toNat
    rw [positionNat] at toNat
    omega
  have entrySlot : call.data + endState.a0 <<< (3 : Nat) = call.search.wordSlot call.position := by
    rw [result, BitVec.add_comm]
    have shifted := call.search.slotShift (BitVec.ofNat 32 call.position)
    rw [positionNat] at shifted
    exact shifted
  have lastSlot : call.data + call.length <<< (3 : Nat) = call.search.wordSlot call.length.toNat := by
    rw [BitVec.add_comm]
    exact call.search.slotShift call.length
  have cursorSlot : call.search.wordSlot call.position + 0x8#32 =
      call.search.wordSlot (call.position + 1) := call.search.slotNext _
  have cacheHighAddress : (call.cache + 0x4#32).toNat = call.cache.toNat + 4 := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by have := entry.cacheFits; change call.cache.toNat + 4 < 2 ^ 32; omega)
  have lowWord : WordAt memory call.cache.toNat call.low :=
    kept entry.cacheLow fun byte low high => entry.cacheOutside byte low (by omega)
  have highWord : WordAt memory (call.cache.toNat + 4) call.high :=
    kept entry.cacheHigh fun byte low high => entry.cacheOutside byte (by omega) (by omega)
  -- From `+0x54` to the overflow test at `+0x80`.
  have toTest : run 12 (sync base { original with mem := memory } (afterSearch called endState)) =
      some (sync base { original with mem := memory }
        { afterSearch called endState with
          pc := if (initial.a3 + 0x1#32).toNat < initial.a3.toNat then 0x88#32 else 0x84#32,
          a1 := initial.a3 + 0x1#32, s7 := call.data,
          a3 := call.data + endState.a0 <<< (3 : Nat),
          a2 := call.length <<< (3 : Nat),
          a0 := Step.lessWord (endState.a0 ^^^ call.length) 0x1#32 + 0xffffffff#32,
          s6 := initial.a3 }) := by
    refine runStep (step54 machine image _ rfl call.length (by
      change Readable original (call.header + 0x4#32); exact entry.header.lengthReadable) (by
      change WordAt memory (call.search.header + 0x4#32).toNat call.length
      rw [SortedMap.Search.headerOffset entry.header]; exact headerWord)) ?_
    refine runStep (step58 machine image _ rfl) ?_
    dsimp only [afterSearch, calling]
    rw [if_neg different]
    refine runStep (step5c machine image _ rfl call.data (by
      change Readable original call.header; exact keys.dataReadable) (by
      change WordAt memory call.header.toNat call.data; exact dataWord)) ?_
    refine runStep (step60 machine image _ rfl) ?_
    refine runStep (step64 machine image _ rfl) ?_
    refine runStep (step68 machine image _ rfl) ?_
    refine runStep (step6c machine image _ rfl) ?_
    refine runStep (step70 machine image _ rfl) ?_
    refine runStep (step74 machine image _ rfl) ?_
    refine runStep (step78 machine image _ rfl) ?_
    refine runStep (step7c machine image _ rfl) ?_
    exact runStep (step80 machine image _ rfl) rfl
  -- From `+0x88`: load the cache words and finish the iterator.
  have finish (state : Snapshot) (atLoad : state.pc = 0x88#32) (cacheRegister : state.s2 = call.cache) :
      run 7 (sync base { original with mem := memory } state) =
        some (sync base { original with mem := memory }
          { state with
            pc := 0xf0#32, a1 := call.low, s8 := call.high, s7 := state.s7 + state.a2,
            s4 := state.a0 &&& state.a3, a3 := state.a3 + 0x8#32, s5 := state.s3 }) := by
    refine runStep (step88 machine image _ atLoad call.low (by
      rw [cacheRegister]; exact entry.cacheLowReadable) (by
      rw [cacheRegister]; exact lowWord)) ?_
    refine runStep (step8c machine image _ rfl call.high (by
      change Readable original (state.s2 + 0x4#32)
      rw [cacheRegister]; exact entry.cacheHighReadable) (by
      change WordAt memory (state.s2 + 0x4#32).toNat call.high
      rw [cacheRegister, cacheHighAddress]; exact highWord)) ?_
    refine runStep (step90 machine image _ rfl) ?_
    refine runStep (step94 machine image _ rfl) ?_
    refine runStep (step98 machine image _ rfl) ?_
    refine runStep (step9c machine image _ rfl) ?_
    exact runStep (stepa0 machine image _ rfl) rfl
  have stopArgument := arguments.stop
  by_cases overflow : (call.stop + 1#32).toNat < call.stop.toNat
  · have total : call.entryCount = (21 + call.search.count .lower) + (12 + 7) := by
      unfold Call.entryCount
      rw [if_pos overflow]
      omega
    have taken : (initial.a3 + 0x1#32).toNat < initial.a3.toNat := by
      rw [stopArgument]; exact overflow
    refine ⟨memory, ?_⟩
    constructor
    refine ⟨?_, agrees, saved, ?_⟩
    · rw [total, runAdd, toBack, Option.bind_some, runAdd, toTest, Option.bind_some, if_pos taken]
      exact finish _ rfl (by exact arguments.cache)
    · refine ⟨rfl, rfl, rfl, arguments.keys, arguments.cache, arguments.stop, ?_, arguments.stop,
        ?_, ?_, rfl, rfl, ?_⟩
      · change (Step.lessWord (endState.a0 ^^^ call.length) 0x1#32 + 0xffffffff#32) &&&
          (call.data + endState.a0 <<< (3 : Nat)) = _
        rw [keepWhenDifferent different, entrySlot]
      · change initial.a3 = call.limit
        rw [stopArgument]; unfold Call.limit; rw [if_pos overflow]
      · change call.data + call.length <<< (3 : Nat) = _
        exact lastSlot
      · change call.data + endState.a0 <<< (3 : Nat) + 0x8#32 = _
        rw [entrySlot, cursorSlot]
  · have total : call.entryCount = (21 + call.search.count .lower) + (12 + (1 + 7)) := by
      unfold Call.entryCount
      rw [if_neg overflow]
      omega
    have notTaken : ¬ (initial.a3 + 0x1#32).toNat < initial.a3.toNat := by
      rw [stopArgument]; exact overflow
    refine ⟨memory, ?_⟩
    constructor
    refine ⟨?_, agrees, saved, ?_⟩
    · rw [total, runAdd, toBack, Option.bind_some, runAdd, toTest, Option.bind_some, if_neg notTaken]
      refine runStep (step84 machine image _ rfl) ?_
      exact finish _ rfl (by exact arguments.cache)
    · refine ⟨rfl, rfl, rfl, arguments.keys, arguments.cache, arguments.stop, ?_, arguments.stop,
        ?_, ?_, rfl, rfl, ?_⟩
      · change (Step.lessWord (endState.a0 ^^^ call.length) 0x1#32 + 0xffffffff#32) &&&
          (call.data + endState.a0 <<< (3 : Nat)) = _
        rw [keepWhenDifferent different, entrySlot]
      · change initial.a3 + 0x1#32 = call.limit
        rw [stopArgument]; unfold Call.limit; rw [if_neg overflow]
      · change call.data + call.length <<< (3 : Nat) = _
        exact lastSlot
      · change call.data + endState.a0 <<< (3 : Nat) + 0x8#32 = _
        rw [entrySlot, cursorSlot]

end Riscfree.RangeInsert.DeleteExtra
