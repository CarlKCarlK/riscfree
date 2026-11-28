import RangeInsert.Bounded.HelperEntry
import RangeInsert.CapacityStatus

namespace Riscfree.RangeInsert.Bounded.HelperScan

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable rawVecU32InsertSailRun)
open HelperFrame
open Helper
open DeleteExtra (rawVecOffset rawVecBase lowAfter highAfter keepWhenDifferent stepOne
  cacheStored headerTransfer bufferTransfer appendStatus appendCount)

set_option maxHeartbeats 3200000

def rawVecEntry (state : Snapshot) : RawVec.Snapshot :=
  { a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4,
    a5 := state.a5, a6 := state.a6, a7 := state.a7 }

def afterRawVec (state : Snapshot) (endState : RawVec.Snapshot) : Snapshot :=
  { state with
    pc := 0x108#32, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2, a3 := endState.a3,
    a4 := endState.a4, a5 := endState.a5, a6 := endState.a6, a7 := endState.a7 }

theorem rawVecInside : ∀ index ∈ tracked RawVec.Snapshot, index ∈ tracked Snapshot := by
  decide

def stored (memory : ByteMemory) (head : Snapshot) (key endWord : Word) : ByteMemory :=
  cacheStored memory head.s2 (lowAfter head.a2 key endWord) (highAfter head.a2 head.s8 key endWord)

def nextEnd (head : Snapshot) (endWord : Word) : Word :=
  if endWord.toNat < head.s5.toNat then head.s5 else endWord

structure Returned (head : Snapshot) (key endWord : Word) (vector : RawVec.Call)
    (state : Snapshot) : Prop where
  pc : state.pc = 0x108#32
  sp : state.sp = head.sp
  s0 : state.s0 = head.s0
  s1 : state.s1 = head.s1
  s2 : state.s2 = head.s2
  s3 : state.s3 = head.s3
  s4 : state.s4 = head.s4
  s5 : state.s5 = nextEnd head endWord
  s6 : state.s6 = head.s6
  s7 : state.s7 = head.s7
  s8 : state.s8 = highAfter head.a2 head.s8 key endWord
  s9 : state.s9 = lowAfter head.a2 key endWord
  s10 : state.s10 = head.a0 + 0x8#32
  status : state.a0 = vector.status

theorem throughAppend {base returnAddress : Word} {original : Machine} {initial : Snapshot}
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
    (vectorIndex : vector.index = pushed)
    (vectorValue : vector.value = key)
    (header : RawVec.Header { original with mem := stored memory head key endWord } vector)
    (buffer : vector.valid → RawVec.Buffer (rawVecBase base) { original with mem := stored memory head key endWord } vector)
    : ∃ (state : Snapshot) (after : ByteMemory),
      run ((if endWord.toNat < head.s5.toNat then 25 else 26) + vector.count)
          (sync base { original with mem := memory } head) =
        some (sync base { original with mem := after } state) ∧
      Returned head key endWord vector state ∧
      (¬ vector.valid → after = stored memory head key endWord) ∧
      (vector.valid →
        WordAt after vector.header.toNat vector.data ∧
        WordAt after (vector.header.toNat + 4) (BitVec.ofNat 32 (vector.length.toNat + 1)) ∧
        WordAt after (vector.header.toNat + 8) vector.capacity ∧
        (∀ index < vector.length.toNat + 1,
          WordAt after (vector.slot index) (vector.result index)) ∧
        vector.unchanged (stored memory head key endWord) after) := by
  have machine := frame.mode.toMachineState
  have image := imageOf memory fun _ _ _ => rfl
  have keep := keepWhenDifferent (value := head.a0) different
  -- To the running-maximum decision at `+0xc0`.
  have toDecide : run 9 (sync base { original with mem := memory } head) =
      some (sync base { original with mem := memory }
        { head with
          pc := if endWord.toNat < head.s5.toNat then 0xc8#32 else 0xc4#32,
          a1 := key, a3 := head.a0 ^^^ head.s7, a4 := endWord }) := by
    refine runStep (stepa0 machine image _ atHead) ?_
    rw [if_neg different]
    refine runStep (stepa4 machine image _ rfl key keyReadable keyWord) ?_
    refine runStep (stepa8 machine image _ rfl) ?_
    rw [if_neg accepted]
    refine runStep (stepac machine image _ rfl) ?_
    refine runStep (stepb0 machine image _ rfl) ?_
    refine runStep (stepb4 machine image _ rfl) ?_
    refine runStep (stepb8 machine image _ rfl) ?_
    refine runStep (stepbc machine image _ rfl endWord (by
      change Readable original
        (((Step.lessWord (head.a0 ^^^ head.s7) 0x1#32 + 0xffffffff#32) &&& head.a0) + 0x4#32)
      rw [keep]; exact endReadable) (by
      change WordAt memory
        (((Step.lessWord (head.a0 ^^^ head.s7) 0x1#32 + 0xffffffff#32) &&& head.a0) + 0x4#32).toNat
        endWord
      rw [keep]; exact endWordAt)) ?_
    exact runStep (stepc0 machine image _ rfl) rfl
  -- A code byte is not a cache byte.
  have codeApart (byte : Nat) (low : base.toNat ≤ byte)
      (high : byte < base.toNat + 4 * DeleteTable.instructions.length) :
      (byte < head.s2.toNat ∨ head.s2.toNat + 4 ≤ byte) ∧
        (byte < (head.s2 + 0x4#32).toNat ∨ (head.s2 + 0x4#32).toNat + 4 ≤ byte) := by
    constructor
    · by_cases inside : head.s2.toNat ≤ byte ∧ byte < head.s2.toNat + 4
      · have := (cacheOutsideCode byte (Or.inl inside)).1; omega
      · omega
    · by_cases inside : (head.s2 + 0x4#32).toNat ≤ byte ∧ byte < (head.s2 + 0x4#32).toNat + 4
      · have := (cacheOutsideCode byte (Or.inr inside)).1; omega
      · omega
  have rawApart (byte : Nat) (low : (rawVecBase base).toNat ≤ byte)
      (high : byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length) :
      (byte < head.s2.toNat ∨ head.s2.toNat + 4 ≤ byte) ∧
        (byte < (head.s2 + 0x4#32).toNat ∨ (head.s2 + 0x4#32).toNat + 4 ≤ byte) := by
    constructor
    · by_cases inside : head.s2.toNat ≤ byte ∧ byte < head.s2.toNat + 4
      · have := (cacheOutsideCode byte (Or.inl inside)).2; omega
      · omega
    · by_cases inside : (head.s2 + 0x4#32).toNat ≤ byte ∧ byte < (head.s2 + 0x4#32).toNat + 4
      · have := (cacheOutsideCode byte (Or.inr inside)).2; omega
      · omega
  let lowStored := storeWord memory head.s2.toNat (lowAfter head.a2 key endWord)
  have image1 := imageOf lowStored fun byte low high =>
    storeWordOutside _ _ _ _ (codeApart byte low high).1
  have image2 := imageOf (stored memory head key endWord) fun byte low high => by
    unfold stored cacheStored
    rw [storeWordOutside _ _ _ _ (codeApart byte low high).2,
      storeWordOutside _ _ _ _ (codeApart byte low high).1]
  -- From `+0xc8` to the call.
  have toCall (newEnd : Word) : ∃ entered : Snapshot,
      run 16 (sync base { original with mem := memory }
        { head with
          pc := 0xc8#32, a1 := key, a3 := head.a0 ^^^ head.s7, a4 := endWord,
          s5 := newEnd }) =
        some (sync base { original with mem := stored memory head key endWord } entered) ∧
      entered.pc = rawVecOffset ∧ entered.ra = base + 0x108#32 ∧ entered.a0 = head.s1 ∧
      entered.a1 = pushed ∧ entered.a2 = key ∧ entered.sp = head.sp ∧ entered.s0 = head.s0 ∧
      entered.s1 = head.s1 ∧ entered.s2 = head.s2 ∧ entered.s3 = head.s3 ∧ entered.s4 = head.s4 ∧
      entered.s5 = newEnd ∧ entered.s6 = head.s6 ∧ entered.s7 = head.s7 ∧
      entered.s8 = highAfter head.a2 head.s8 key endWord ∧
      entered.s9 = lowAfter head.a2 key endWord ∧ entered.s10 = head.a0 + 0x8#32 :=
    ⟨_, by
      refine runStep (stepc8 machine image _ rfl) ?_
      refine runStep (stepcc machine image _ rfl) ?_
      refine runStep (stepd0 machine image _ rfl) ?_
      refine runStep (stepd4 machine image _ rfl) ?_
      refine runStep (stepd8 machine image _ rfl) ?_
      refine runStep (stepdc machine image _ rfl key keyReadable keyWord) ?_
      refine runStep (stepe0 machine image _ rfl pushed lengthReadable lengthWord) ?_
      refine runStep (stepe4 machine image _ rfl) ?_
      refine runStep (stepe8 machine image _ rfl) ?_
      refine runStep (stepec machine image _ rfl) ?_
      refine runStep (stepf0 machine image _ rfl) ?_
      refine runStep (stepf4 machine image _ rfl cacheLowWritable) ?_
      refine runStep (stepf8 machine image1 _ rfl cacheHighWritable) ?_
      refine runStep (stepfc machine image2 _ rfl) ?_
      refine runStep (step100 machine image2 _ rfl) ?_
      exact runStep (step104 machine image2 _ rfl rfl) rfl,
      by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl,
      by rfl, by rfl, by rfl, by rfl, by rfl, by
        change head.a0 + Step.lessWord 0#32 (head.a0 ^^^ head.s7) <<< (3 : Nat) = head.a0 + 0x8#32
        rw [stepOne different]⟩
  have finishFrom : ∃ (state : Snapshot) (after : ByteMemory),
      run (16 + vector.count) (sync base { original with mem := memory }
        { head with
          pc := 0xc8#32, a1 := key, a3 := head.a0 ^^^ head.s7, a4 := endWord,
          s5 := nextEnd head endWord }) =
        some (sync base { original with mem := after } state) ∧
      Returned head key endWord vector state ∧
      (¬ vector.valid → after = stored memory head key endWord) ∧
      (vector.valid →
        WordAt after vector.header.toNat vector.data ∧
        WordAt after (vector.header.toNat + 4) (BitVec.ofNat 32 (vector.length.toNat + 1)) ∧
        WordAt after (vector.header.toNat + 8) vector.capacity ∧
        (∀ index < vector.length.toNat + 1,
          WordAt after (vector.slot index) (vector.result index)) ∧
        vector.unchanged (stored memory head key endWord) after) := by
    obtain ⟨called, ranCall, calledPc, calledRa, calledA0, calledA1, calledA2, calledSp, calledS0,
      calledS1, calledS2, calledS3, calledS4, calledS5, calledS6, calledS7, calledS8, calledS9,
      calledS10⟩ := toCall (nextEnd head endWord)
    let entered := sync base { original with mem := stored memory head key endWord } called
    have regions : entered.regs.get? Register.pma_regions =
        ({ original with mem := stored memory head key endWord } : Machine).regs.get?
          Register.pma_regions :=
      syncFrame called _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
    have enteredMem : entered.mem = stored memory head key endWord := syncMem called
    have routineEntered :
        entered = sync (rawVecBase base) entered { rawVecEntry called with pc := 0 } := by
      have inside := syncInside (frame := { original with mem := stored memory head key endWord })
        base (rawVecBase base) called called (rawVecEntry called) rawVecInside
        (fun index _ => by fin_cases index <;> rfl) (by
          change base + called.pc = rawVecBase base + 0#32
          rw [calledPc, BitVec.add_zero]; rfl)
      exact inside.symm
    have returnAligned : (base + 0x108#32).toNat % 4 = 0 :=
      SortedMap.Remove.alignedTargetNat frame.code.aligned _ (by decide)
    obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
    have mode : MachineMode entered (base + 0x108#32) :=
      { (machine.withMemory (stored memory head key endWord)).atSync base called with
        returnLow := by rw [BitVec.and_comm]; exact maskEven _ returnBit0
        returnNext := returnBit1
        ra := by
          have read := syncRead (base := base)
            (frame := { original with mem := stored memory head key endWord }) called
            (index := 1) (by decide)
          rw [show RegisterView.value called 1 = base + 0x108#32 from calledRa] at read
          exact read }
    have rawImage : CodeImage RawVec.instructions (rawVecBase base) entered :=
      (rawImageOf (stored memory head key endWord) fun byte low high => by
        unfold stored cacheStored
        rw [storeWordOutside _ _ _ _ (rawApart byte low high).2,
          storeWordOutside _ _ _ _ (rawApart byte low high).1]).atSync base called
    obtain ⟨endState, after, ran, endPc, status, rejected, accepted⟩ :=
      rawVecU32InsertSailRun (rawVecBase base) (base + 0x108#32) entered vector (rawVecEntry called)
        routineEntered (by change called.a0 = _; rw [calledA0, vectorHeader])
        (by change called.a1 = _; rw [calledA1, vectorIndex])
        (by change called.a2 = _; rw [calledA2, vectorValue])
        (RawVec.Environment.ofMachine mode rawImage) (headerTransfer header regions enteredMem)
        (fun valid => bufferTransfer (buffer valid) regions enteredMem)
    have back : run vector.count entered =
        some (sync base { original with mem := after } (afterRawVec called endState)) := by
      rw [ran]
      have withMem := syncWithMem base { original with mem := stored memory head key endWord }
        called after
      have inside := syncInside (frame := { original with mem := after }) base (rawVecBase base)
        called (afterRawVec called endState) endState rawVecInside
        (fun index _ => by fin_cases index <;> rfl) (by
          change base + 0x108#32 = rawVecBase base + endState.pc
          rw [endPc, BitVec.add_comm (rawVecBase base), BitVec.sub_add_cancel])
      change some (sync (rawVecBase base) { sync base { original with mem := stored memory head key endWord }
        called with mem := after } endState) = _
      rw [withMem]
      exact congrArg some inside
    refine ⟨afterRawVec called endState, after, ?_, ?_, ?_, ?_⟩
    · rw [runAdd, ranCall, Option.bind_some]
      exact back
    · exact ⟨rfl, calledSp, calledS0, calledS1, calledS2, calledS3, calledS4, calledS5,
        calledS6, calledS7, calledS8, calledS9, calledS10, status⟩
    · intro invalid
      exact (rejected invalid).trans enteredMem
    · intro valid
      obtain ⟨data, length, capacity, slots, keeps⟩ := accepted valid
      rw [enteredMem] at keeps
      exact ⟨data, length, capacity, slots, keeps⟩
  by_cases taken : endWord.toNat < head.s5.toNat
  · rw [if_pos taken, show 25 + vector.count = 9 + (16 + vector.count) by omega,
      runAdd, toDecide, Option.bind_some, if_pos taken]
    simpa only [nextEnd, if_pos taken] using finishFrom
  · rw [if_neg taken, show 26 + vector.count = 9 + (1 + (16 + vector.count)) by omega,
      runAdd, toDecide, Option.bind_some, if_neg taken]
    -- The branch's record is explicit to avoid reducing it during unification.
    have update := stepc4 machine image
      { head with pc := 0xc4, a1 := key, a3 := head.a0 ^^^ head.s7, a4 := endWord } rfl
    rcases finishFrom with ⟨state, after, ran, values, invalid, valid⟩
    refine ⟨state, after, ?_, values, invalid, valid⟩
    rw [Nat.add_comm 1]
    refine runStep update ?_
    simpa only [nextEnd, if_neg taken] using ran

end Riscfree.RangeInsert.Bounded.HelperScan
