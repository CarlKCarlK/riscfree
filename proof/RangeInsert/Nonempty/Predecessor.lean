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

end Riscfree.RangeInsert.Nonempty
