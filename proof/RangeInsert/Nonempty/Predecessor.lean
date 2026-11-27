import RangeInsert.Nonempty.Steps
import SortedMap.Search.Correct

/-! The prefix shared by every nonempty range insertion: the prologue, the
fall-through of the empty-input test, the argument moves, and the call to
`sorted_map_upper_bound`. The call is composed from
`SortedMap.Search.sortedMapSearchSailRun`; its instructions are not
re-proved here. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Empty (Snapshot Frame frameBase OutsideFrame pushed pushedOutside)

set_option maxHeartbeats 2000000

def upperBoundBase (base : Word) : Word := base + upperBoundOffset

/-- The map and the inclusive input range `start..=stop`, as the routine
receives them. -/
structure Call where
  header : Word
  length : Word
  data : Word
  old : Nat → Pair
  start : Word
  stop : Word

namespace Call

def search (call : Call) : SortedMap.Search.Call :=
  ⟨call.header, call.start, call.length, call.data, call.old⟩

-- The number of entries whose key is at most `start`.
def rank (call : Call) : Nat := call.search.result .upper

-- The last entry whose key is at most `start`, when `rank` is positive.
def predecessor (call : Call) : Pair := call.old (call.rank - 1)

theorem rank_le (call : Call) : call.rank ≤ call.length.toNat := call.search.result_le .upper

end Call

/-- Register arguments: the map header, the input start, and the input end. -/
structure Arguments (initial : Snapshot) (call : Call) : Prop where
  header : initial.a0 = call.header
  start : initial.a2 = call.start
  stop : initial.a3 = call.stop

/-- The map and upper-bound search premises shared by the nonempty paths.
The search code, the header, and the live entries lie outside the entry's
stack frame. Every live entry's end word is readable. -/
structure Map (base : Word) (original : Machine) (sp : Word) (call : Call) : Prop where
  searchCode : CodeImage (SortedMap.Search.instructions .upper) (upperBoundBase base) original
  searchOutside : ∀ byte, (upperBoundBase base).toNat ≤ byte →
    byte < (upperBoundBase base).toNat + 52 → OutsideFrame sp byte
  header : SortedMap.Search.Header original call.search
  keys : 0 < call.length.toNat → SortedMap.Search.Keys original call.search
  headerOutside : ∀ byte, call.header.toNat ≤ byte → byte < call.header.toNat + 8 →
    OutsideFrame sp byte
  entriesOutside : ∀ index < call.length.toNat, ∀ byte, call.search.slot index ≤ byte →
    byte < call.search.slot index + 8 → OutsideFrame sp byte
  valueReadable : ∀ index < call.length.toNat,
    Readable original (call.search.wordSlot index + 4#32)
  valueWord : ∀ index < call.length.toNat,
    WordAt original.mem (call.search.slot index + 4) (call.old index).value
  dataNonnull : 0 < call.data.toNat

theorem mappedTransfer {frame other : Machine} {address : Word}
    {permission : PMA_Region → Prop} (mapped : Mapped frame address permission)
    (regions : other.regs.get? Register.pma_regions = frame.regs.get? Register.pma_regions) :
    Mapped other address permission := by
  obtain ⟨aligned, found, region, regionsRead, matched, allowed⟩ := mapped
  have stored : frame.regs.get? Register.pma_regions = some found := readReg_succ.mp regionsRead
  exact ⟨aligned, found, region, readReg_succ.mpr (regions.trans stored), matched, allowed⟩

theorem pushedWord {memory : ByteMemory} {address : Nat} {value : Word} (initial : Snapshot)
    (fits : 48 ≤ initial.sp.toNat) (word : WordAt memory address value)
    (apart : ∀ byte, address ≤ byte → byte < address + 4 → OutsideFrame initial.sp byte) :
    WordAt (pushed memory initial) address value :=
  word.congr fun byte low high => pushedOutside memory initial fits byte (apart byte low high)

-- The snapshot when `sorted_map_upper_bound` is entered.
def calling (base : Word) (initial : Snapshot) : Snapshot :=
  { initial with
    pc := upperBoundOffset, sp := frameBase initial.sp, ra := base + 0x4c#32,
    s0 := initial.a1, s1 := initial.a3, s2 := initial.a2, s3 := initial.a5,
    s4 := initial.a4, s5 := initial.a0, a1 := initial.a2 }

-- The search's snapshot, from the caller's argument registers.
def searchEntry (state : Snapshot) : SortedMap.Search.Snapshot :=
  { a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4 }

-- Back in the entry point at `+0x4c` with the search's registers.
def afterSearch (state : Snapshot) (endState : SortedMap.Search.Snapshot) : Snapshot :=
  { state with
    pc := 0x4c#32, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2, a3 := endState.a3,
    a4 := endState.a4 }

theorem searchInside : ∀ index ∈ tracked SortedMap.Search.Snapshot, index ∈ tracked Snapshot := by
  decide

/-- From entry, 19 instructions reach the call, and the verified search
returns to `+0x4c` with the upper-bound rank in `a0`. Memory outside the
frame is unchanged. -/
theorem toPredecessor {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (frame : Frame base returnAddress original initial)
    (arguments : Arguments initial call) (map : Map base original initial.sp call)
    (nonempty : call.start.toNat ≤ call.stop.toNat) :
    ∃ endState : SortedMap.Search.Snapshot,
      run (19 + call.search.count .upper) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := pushed original.mem initial }
          (afterSearch (calling base initial) endState)) ∧
      endState.a0 = BitVec.ofNat 32 call.rank := by
  let memory := pushed original.mem initial
  have machine := frame.mode.toMachineState
  have image := frame.pushedImage
  have fits := frame.frameFits
  have toCall : run 19 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } (calling base initial)) := by
    rw [show 19 = 9 + 10 from rfl, runAdd, frame.prologue, Option.bind_some]
    refine runStep (branchNonempty machine image _ rfl (by
      change initial.a2.toNat ≤ initial.a3.toNat
      rw [arguments.start, arguments.stop]
      exact nonempty)) ?_
    refine runStep (step28 machine image _ rfl) ?_
    refine runStep (step2c machine image _ rfl) ?_
    refine runStep (step30 machine image _ rfl) ?_
    refine runStep (step34 machine image _ rfl) ?_
    refine runStep (step38 machine image _ rfl) ?_
    refine runStep (step3c machine image _ rfl) ?_
    refine runStep (step40 machine image _ rfl) ?_
    refine runStep (step44 machine image _ rfl) ?_
    exact runStep (step48 machine image _ rfl rfl) rfl
  let called := calling base initial
  let entered := sync base { original with mem := memory } called
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame called _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have enteredMem : entered.mem = memory := syncMem called
  have routineEntered :
      entered = sync (upperBoundBase base) entered { searchEntry called with pc := 0 } :=
    (syncInside base (upperBoundBase base) called called (searchEntry called) searchInside
      (fun index _ => by fin_cases index <;> rfl) (BitVec.add_zero _).symm).symm
  have returnAligned : (base + 0x4c#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat frame.code.aligned _ (by decide)
  obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
  have mode : MachineMode entered (base + 0x4c#32) :=
    { (machine.withMemory memory).atSync base called with
      returnLow := by rw [BitVec.and_comm]; exact maskEven _ returnBit0
      returnNext := returnBit1
      ra := syncRead called (index := 1) (by decide) }
  have searchImage :
      CodeImage (SortedMap.Search.instructions .upper) (upperBoundBase base) entered :=
    (map.searchCode.withMemory memory fun byte low high => by
      rw [SortedMap.Search.instructionsLength] at high
      exact pushedOutside original.mem initial fits byte
        (map.searchOutside byte low (by omega))).atSync base called
  have searchHeader : SortedMap.Search.Header entered call.search := by
    refine ⟨map.header.fits, mappedTransfer map.header.lengthReadable regions, ?_⟩
    rw [enteredMem]
    exact pushedWord initial fits map.header.lengthWord fun byte low high =>
      map.headerOutside byte (by change call.header.toNat + 4 ≤ byte at low; omega)
        (by change byte < call.header.toNat + 4 + 4 at high; omega)
  have searchKeys (positive : 0 < call.search.length.toNat) :
      SortedMap.Search.Keys entered call.search := by
    have given := map.keys positive
    refine ⟨given.fits, mappedTransfer given.dataReadable regions, ?_,
      fun index bound => mappedTransfer (given.readable index bound) regions, fun index bound => ?_⟩
    · rw [enteredMem]
      exact pushedWord initial fits given.dataWord fun byte low high =>
        map.headerOutside byte low (by change byte < call.header.toNat + 4 at high; omega)
    · rw [enteredMem]
      exact pushedWord initial fits (given.keyWord index bound) fun byte low high =>
        map.entriesOutside index bound byte low (by omega)
  obtain ⟨endState, ran, endPc, result, -⟩ := SortedMap.Search.sortedMapSearchSailRun .upper
    (upperBoundBase base) (base + 0x4c#32) entered call.search (searchEntry called) routineEntered
    (by change initial.a0 = call.header; exact arguments.header)
    (by change initial.a2 = call.start; exact arguments.start)
    (SortedMap.Search.Environment.ofMachine mode searchImage) searchHeader searchKeys
  refine ⟨endState, ?_, result⟩
  have back : run (call.search.count .upper) entered =
      some (sync base { original with mem := memory } (afterSearch called endState)) := by
    rw [ran]
    refine congrArg some (syncInside base (upperBoundBase base) called _ endState searchInside
      (fun index _ => by fin_cases index <;> rfl) ?_)
    change base + 0x4c#32 = upperBoundBase base + endState.pc
    rw [endPc, BitVec.add_comm (upperBoundBase base), BitVec.sub_add_cancel]
  rw [runAdd, toCall, Option.bind_some]
  exact back

/-- Register facts at the strict-gap branch after a positive-rank lookup. -/
structure Inspected (initial : Snapshot) (call : Call) (state : Snapshot) : Prop where
  pc : state.pc = 0x84#32
  sp : state.sp = frameBase initial.sp
  header : state.a0 = call.header
  cached : state.s0 = initial.a1
  mapHeader : state.s5 = initial.a0
  stop : state.s1 = call.stop
  start : state.s2 = call.start
  scratchCapacity : state.s3 = initial.a5
  scratchData : state.s4 = initial.a4
  predecessorEnd : state.a2 = call.predecessor.value
  predecessorKeyAddress : state.a1 = call.search.wordSlot (call.rank - 1)
  predecessorEndAddress : state.a3 = call.search.wordSlot (call.rank - 1) + 4#32
  gap : state.a4 = (Step.lessWord call.predecessor.value 0xffffffff#32 &&&
    Step.lessWord (call.predecessor.value + 1#32) call.start)
  -- The registers only the callees write still hold their entry values.
  untouched : state.t0 = initial.t0 ∧ state.t1 = initial.t1 ∧ state.a6 = initial.a6 ∧
    state.a7 = initial.a7 ∧ state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧
    state.s8 = initial.s8 ∧ state.s9 = initial.s9 ∧ state.s10 = initial.s10

/-- Inspect the predecessor with a positive upper-bound rank. All writes to
this point are in the entry frame. -/
theorem inspectPredecessor {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (frame : Frame base returnAddress original initial) (arguments : Arguments initial call)
    (map : Map base original initial.sp call) (nonempty : call.start.toNat ≤ call.stop.toNat)
    (found : 0 < call.rank) :
    ∃ state : Snapshot,
      run (33 + call.search.count .upper) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := pushed original.mem initial } state) ∧
      Inspected initial call state := by
  obtain ⟨endState, toSearch, rankWord⟩ :=
    toPredecessor frame arguments map nonempty
  have machine := frame.mode.toMachineState
  have image := frame.pushedImage
  have fits := frame.frameFits
  have rankBound := call.rank_le
  have lengthSmall := call.length.isLt
  have keys := map.keys (by omega)
  obtain ⟨index, indexNext⟩ : ∃ index, index + 1 = call.rank := ⟨call.rank - 1, by omega⟩
  have inside : index < call.length.toNat := by omega
  have predecessorAt : call.predecessor = call.old index := by
    unfold Call.predecessor
    rw [← indexNext, Nat.add_sub_cancel]
  have rankNat : (BitVec.ofNat 32 call.rank).toNat = call.rank := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have rankNonzero : BitVec.ofNat 32 call.rank ≠ 0#32 := by
    intro zero
    have toNat := congrArg BitVec.toNat zero
    rw [rankNat] at toNat
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at toNat
    omega
  have slotNext : call.search.wordSlot index + 8#32 = call.search.wordSlot call.rank := by
    rw [call.search.slotNext index, indexNext]
  have dataAddress :
      call.data + BitVec.ofNat 32 call.rank <<< (3 : Nat) = call.search.wordSlot call.rank := by
    rw [BitVec.add_comm]
    have shifted := call.search.slotShift (BitVec.ofNat 32 call.rank)
    rw [rankNat] at shifted
    exact shifted
  have keyAddress : call.search.wordSlot call.rank + 0xfffffff8#32 = call.search.wordSlot index := by
    rw [← slotNext, BitVec.add_assoc, show 8#32 + 0xfffffff8#32 = 0#32 from rfl, BitVec.add_zero]
  have valueAddress :
      call.search.wordSlot call.rank + 0xfffffffc#32 = call.search.wordSlot index + 4#32 := by
    rw [← slotNext, BitVec.add_assoc, show 8#32 + 0xfffffffc#32 = 4#32 from rfl]
  have slotFits : call.search.slot index + 8 ≤ 2 ^ 32 := by
    have total := keys.fits
    unfold SortedMap.Search.Call.slot at total ⊢
    change call.search.data.toNat + 8 * index + 8 ≤ 2 ^ 32
    change call.search.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at total
    have scaled : 8 * index + 8 ≤ 8 * call.length.toNat := by omega
    omega
  have keyNat : (call.search.wordSlot index).toNat = call.search.slot index :=
    SortedMap.Search.slotNat keys inside
  have valueNat : (call.search.wordSlot index + 4#32).toNat = call.search.slot index + 4 := by
    rw [BitVec.toNat_add, keyNat]
    exact Nat.mod_eq_of_lt (by change call.search.slot index + 4 < 2 ^ 32; omega)
  have keyNonnull : call.search.wordSlot index ≠ 0#32 := by
    intro zero
    have toNat := congrArg BitVec.toNat zero
    rw [keyNat] at toNat
    have positive := map.dataNonnull
    unfold SortedMap.Search.Call.slot at toNat
    change call.data.toNat + 8 * index = 0 at toNat
    omega
  let offset := call.data + endState.a0 <<< (3 : Nat)
  let state : Snapshot :=
    { afterSearch (calling base initial) endState with
      pc := 0x84, a0 := initial.a0, a1 := offset + 0xfffffff8#32,
      a2 := call.predecessor.value, a3 := offset + 0xfffffffc#32,
      a4 := Step.lessWord call.predecessor.value 0xffffffff#32 &&&
        Step.lessWord (call.predecessor.value + 1#32) initial.a2,
      a5 := Step.lessWord call.predecessor.value 0xffffffff#32 }
  refine ⟨state, ?_, ?_⟩
  · rw [show 33 + call.search.count .upper = (19 + call.search.count .upper) + 14 by omega,
      runAdd, toSearch, Option.bind_some]
    refine runStep (branchFound machine image _ rfl (by
      change endState.a0 ≠ 0#32
      rw [rankWord]
      exact rankNonzero)) ?_
    refine runStep (step50 machine image _ rfl) ?_
    refine runStep (step54 machine image _ rfl) ?_
    refine runStep (step58 machine image _ rfl call.data (by
      change Readable original initial.a0
      rw [arguments.header]
      exact keys.dataReadable) (by
      change WordAt (pushed original.mem initial) initial.a0.toNat call.data
      rw [arguments.header]
      exact pushedWord initial fits keys.dataWord fun byte low high =>
        map.headerOutside byte low (by omega))) ?_
    refine runStep (step5c machine image _ rfl) ?_
    refine runStep (step60 machine image _ rfl) ?_
    refine runStep (step64 machine image _ rfl) ?_
    refine runStep (step68 machine image _ rfl) ?_
    refine runStep (branchKeyPointer machine image _ rfl (by
      change call.data + endState.a0 <<< (3 : Nat) + 0xfffffff8#32 ≠ 0#32
      rw [rankWord, dataAddress, keyAddress]
      exact keyNonnull)) ?_
    refine runStep (step70 machine image _ rfl call.predecessor.value (by
      change Readable original (call.data + endState.a0 <<< (3 : Nat) + 0xfffffffc#32)
      rw [rankWord, dataAddress, valueAddress]
      exact map.valueReadable index inside) (by
      change WordAt (pushed original.mem initial)
        (call.data + endState.a0 <<< (3 : Nat) + 0xfffffffc#32).toNat call.predecessor.value
      rw [rankWord, dataAddress, valueAddress, valueNat, predecessorAt]
      exact pushedWord initial fits (map.valueWord index inside) fun byte low high =>
        map.entriesOutside index inside byte (by omega) (by omega))) ?_
    refine runStep (step74 machine image _ rfl) ?_
    refine runStep (step78 machine image _ rfl) ?_
    refine runStep (step7c machine image _ rfl) ?_
    refine runStep (step80 machine image _ rfl) ?_
    rfl
  · refine ⟨rfl, rfl, arguments.header, rfl, rfl, arguments.stop, arguments.start, rfl, rfl, rfl, ?_, ?_, ?_,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · change offset + 0xfffffff8#32 = call.search.wordSlot (call.rank - 1)
      dsimp only [offset]
      rw [rankWord, dataAddress, keyAddress, ← indexNext, Nat.add_sub_cancel]
    · change offset + 0xfffffffc#32 = call.search.wordSlot (call.rank - 1) + 4#32
      dsimp only [offset]
      rw [rankWord, dataAddress, valueAddress, ← indexNext, Nat.add_sub_cancel]
    · change Step.lessWord call.predecessor.value 0xffffffff#32 &&&
        Step.lessWord (call.predecessor.value + 1#32) initial.a2 = _
      rw [arguments.start]

end Riscfree.RangeInsert.Nonempty
