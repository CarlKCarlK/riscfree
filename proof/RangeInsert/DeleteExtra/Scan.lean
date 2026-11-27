import RangeInsert.DeleteExtra.Entry
import RawVec

/-! One accepted iteration of the `delete_extra` scan loop: from the loop head
at `+0xf0`, the routine loads a successor that starts within the limit,
updates the running maximum end, subtracts the successor's inclusive length
from the two-word cache, and appends the successor's key with the verified
`raw_vec_u32_insert`, composed from `rawVecU32InsertSailRun`. -/

namespace Riscfree.RangeInsert.DeleteExtra

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

set_option maxHeartbeats 4000000

-- `raw_vec_u32_insert` lies 0x2e0 bytes before the helper.
def rawVecOffset : Word := 0xfffffd20
def rawVecBase (base : Word) : Word := base + rawVecOffset

-- The cache words after subtracting the inclusive length of `key..=endWord`,
-- in the instruction order of `+0xa4`–`+0xcc`.
def lowAfter (low key endWord : Word) : Word := low + ((endWord - key) ^^^ 0xffffffff#32)

def highAfter (low high key endWord : Word) : Word :=
  high + Step.lessWord (lowAfter low key endWord) low + 0xffffffff#32

def rawVecEntry (state : Snapshot) : RawVec.Snapshot :=
  { a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4,
    a5 := state.a5, a6 := state.a6, a7 := state.a7 }

def afterRawVec (state : Snapshot) (endState : RawVec.Snapshot) : Snapshot :=
  { state with
    pc := 0xe4#32, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2, a3 := endState.a3,
    a4 := endState.a4, a5 := endState.a5, a6 := endState.a6, a7 := endState.a7 }

theorem rawVecInside : ∀ index ∈ tracked RawVec.Snapshot, index ∈ tracked Snapshot := by
  decide

-- An append returns status 0.
theorem appendStatus (call : RawVec.Call) (valid : call.valid) (append : call.index = call.length) :
    call.status = 0 := by
  have bounds := valid.2
  unfold Insert.Call.status
  rw [if_neg (by omega), if_neg (by rw [append]; omega), if_neg (by
    intro same; rw [same] at bounds; omega)]

theorem appendCount (call : RawVec.Call) (valid : call.valid) (append : call.index = call.length) :
    call.count = 14 := by
  have bounds := valid.2
  unfold RawVec.Call.count
  rw [if_neg (by omega), if_neg (by rw [append]; omega), if_neg (by
    intro same; rw [same] at bounds; omega), if_pos append]

theorem headerTransfer {frame other : Machine} {call : RawVec.Call} (header : RawVec.Header frame call)
    (regions : other.regs.get? Register.pma_regions = frame.regs.get? Register.pma_regions)
    (memory : other.mem = frame.mem) : RawVec.Header other call :=
  ⟨header.fits, Nonempty.mappedTransfer header.lengthReadable regions,
    Nonempty.mappedTransfer header.capacityReadable regions, memory ▸ header.lengthWord,
    memory ▸ header.capacityWord⟩

theorem bufferTransfer {base : Word} {frame other : Machine} {call : RawVec.Call}
    (buffer : RawVec.Buffer base frame call)
    (regions : other.regs.get? Register.pma_regions = frame.regs.get? Register.pma_regions)
    (memory : other.mem = frame.mem) : RawVec.Buffer base other call :=
  ⟨buffer.fits, Nonempty.mappedTransfer buffer.dataReadable regions, memory ▸ buffer.dataWord,
    Nonempty.mappedTransfer buffer.lengthWritable regions, buffer.lengthAwayFromCode,
    fun index bound => memory ▸ buffer.live index bound,
    fun index low high => Nonempty.mappedTransfer (buffer.readable index low high) regions,
    fun index low high => Nonempty.mappedTransfer (buffer.writable index low high) regions,
    buffer.separated, buffer.awayFromCode⟩

-- `sltu a0, zero, a2` is 1 for the nonzero `cursor ^^^ last`.
theorem stepOne {left right : Word} (different : left ≠ right) :
    Step.lessWord 0#32 (left ^^^ right) <<< (3 : Nat) = 0x8#32 := by
  have nonzero : left ^^^ right ≠ 0#32 := by
    intro zero
    apply different
    have back := congrArg (· ^^^ right) zero
    simpa [BitVec.xor_assoc] using back
  have positive : (0#32).toNat < (left ^^^ right).toNat := by
    rcases Nat.eq_zero_or_pos (left ^^^ right).toNat with zero | pos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using zero)) nonzero
    · simpa using pos
  unfold Step.lessWord
  rw [if_pos positive]
  decide

/-- One accepted iteration from the loop head, before the key is appended:
the memory after the two cache stores. -/
def cacheStored (memory : ByteMemory) (cache low high : Word) : ByteMemory :=
  storeWord (storeWord memory cache.toNat low) (cache + 0x4#32).toNat high

-- The memory when the key is appended.
def stored (memory : ByteMemory) (head : Snapshot) (key endWord : Word) : ByteMemory :=
  cacheStored memory head.s2 (lowAfter head.a1 key endWord) (highAfter head.a1 head.s8 key endWord)

theorem iteration {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (imageOf : ∀ other : ByteMemory, (∀ byte, base.toNat ≤ byte →
      byte < base.toNat + 4 * DeleteTable.instructions.length → other[byte]? = memory[byte]?) →
      CodeImage DeleteTable.instructions base { original with mem := other })
    (rawImageOf : ∀ other : ByteMemory, (∀ byte, (rawVecBase base).toNat ≤ byte →
      byte < (rawVecBase base).toNat + 4 * RawVec.instructions.length →
      other[byte]? = memory[byte]?) →
      CodeImage RawVec.instructions (rawVecBase base) { original with mem := other })
    (head : Snapshot) (atHead : head.pc = 0xf0#32)
    (key endWord : Word) (different : head.a3 ≠ head.s7)
    (keyReadable : Readable original head.a3) (keyWord : WordAt memory head.a3.toNat key)
    (endReadable : Readable original (head.a3 + 0x4#32))
    (endWordAt : WordAt memory (head.a3 + 0x4#32).toNat endWord)
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
      run (if endWord.toNat < head.s5.toNat then 42 else 44)
          (sync base { original with mem := memory } head) =
        some (sync base { original with mem := after } state) ∧
      state.pc = 0xf0#32 ∧ state.sp = head.sp ∧ state.s0 = head.s0 ∧ state.s1 = head.s1 ∧
      state.s2 = head.s2 ∧ state.s3 = head.s3 ∧ state.s4 = head.s4 ∧ state.s6 = head.s6 ∧
      state.s7 = head.s7 ∧
      state.s5 = (if endWord.toNat < head.s5.toNat then head.s5 else endWord) ∧
      state.a1 = lowAfter head.a1 key endWord ∧
      state.s8 = highAfter head.a1 head.s8 key endWord ∧
      state.a3 = head.a3 + 0x8#32 ∧
      WordAt after vector.header.toNat vector.data ∧
      WordAt after (vector.header.toNat + 4) (BitVec.ofNat 32 (vector.length.toNat + 1)) ∧
      WordAt after (vector.header.toNat + 8) vector.capacity ∧
      (∀ index, index < vector.length.toNat + 1 →
        WordAt after (vector.slot index) (vector.result index)) ∧
      vector.unchanged (stored memory head key endWord) after := by
  have machine := frame.mode.toMachineState
  have image := imageOf memory fun _ _ _ => rfl
  have keep := keepWhenDifferent (value := head.a3) different
  -- To the running-maximum decision at `+0x110`.
  have toDecide : run 9 (sync base { original with mem := memory } head) =
      some (sync base { original with mem := memory }
        { head with
          pc := if endWord.toNat < head.s5.toNat then 0xa4#32 else 0x114#32,
          a0 := key, a2 := head.a3 ^^^ head.s7, a4 := endWord }) := by
    refine runStep (stepf0 machine image _ atHead) ?_
    rw [if_neg different]
    refine runStep (stepf4 machine image _ rfl key keyReadable keyWord) ?_
    refine runStep (stepf8 machine image _ rfl) ?_
    rw [if_neg accepted]
    refine runStep (stepfc machine image _ rfl) ?_
    refine runStep (step100 machine image _ rfl) ?_
    refine runStep (step104 machine image _ rfl) ?_
    refine runStep (step108 machine image _ rfl) ?_
    refine runStep (step10c machine image _ rfl endWord (by
      change Readable original
        (((Step.lessWord (head.a3 ^^^ head.s7) 0x1#32 + 0xffffffff#32) &&& head.a3) + 0x4#32)
      rw [keep]; exact endReadable) (by
      change WordAt memory
        (((Step.lessWord (head.a3 ^^^ head.s7) 0x1#32 + 0xffffffff#32) &&& head.a3) + 0x4#32).toNat
        endWord
      rw [keep]; exact endWordAt)) ?_
    exact runStep (step110 machine image _ rfl) rfl
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
  let lowStored := storeWord memory head.s2.toNat (lowAfter head.a1 key endWord)
  have image1 := imageOf lowStored fun byte low high =>
    storeWordOutside _ _ _ _ (codeApart byte low high).1
  have image2 := imageOf (stored memory head key endWord) fun byte low high => by
    unfold stored cacheStored
    rw [storeWordOutside _ _ _ _ (codeApart byte low high).2,
      storeWordOutside _ _ _ _ (codeApart byte low high).1]
  -- From `+0xa4` to the call.
  have toCall (newEnd : Word) : ∃ entered : Snapshot,
      run 16 (sync base { original with mem := memory }
        { head with
          pc := 0xa4#32, a0 := key, a2 := head.a3 ^^^ head.s7, a4 := endWord,
          s5 := newEnd }) =
        some (sync base { original with mem := stored memory head key endWord } entered) ∧
      entered.pc = rawVecOffset ∧ entered.ra = base + 0xe4#32 ∧ entered.a0 = head.s1 ∧
      entered.a1 = pushed ∧ entered.a2 = key ∧ entered.sp = head.sp ∧ entered.s0 = head.s0 ∧
      entered.s1 = head.s1 ∧ entered.s2 = head.s2 ∧ entered.s3 = head.s3 ∧ entered.s4 = head.s4 ∧
      entered.s5 = newEnd ∧ entered.s6 = head.s6 ∧ entered.s7 = head.s7 ∧
      entered.s8 = highAfter head.a1 head.s8 key endWord ∧
      entered.s9 = lowAfter head.a1 key endWord ∧ entered.s10 = head.a3 + 0x8#32 :=
    ⟨_, by
      refine runStep (stepa4 machine image _ rfl) ?_
      refine runStep (stepa8 machine image _ rfl) ?_
      refine runStep (stepac machine image _ rfl) ?_
      refine runStep (stepb0 machine image _ rfl) ?_
      refine runStep (stepb4 machine image _ rfl) ?_
      refine runStep (stepb8 machine image _ rfl key keyReadable keyWord) ?_
      refine runStep (stepbc machine image _ rfl pushed lengthReadable lengthWord) ?_
      refine runStep (stepc0 machine image _ rfl) ?_
      refine runStep (stepc4 machine image _ rfl) ?_
      refine runStep (stepc8 machine image _ rfl) ?_
      refine runStep (stepcc machine image _ rfl) ?_
      refine runStep (stepd0 machine image _ rfl cacheLowWritable) ?_
      refine runStep (stepd4 machine image1 _ rfl cacheHighWritable) ?_
      refine runStep (stepd8 machine image2 _ rfl) ?_
      refine runStep (stepdc machine image2 _ rfl) ?_
      exact runStep (stepe0 machine image2 _ rfl rfl) rfl,
      by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl,
      by rfl, by rfl, by rfl, by rfl, by rfl, by
        change head.a3 + Step.lessWord 0#32 (head.a3 ^^^ head.s7) <<< (3 : Nat) = head.a3 + 0x8#32
        rw [stepOne different]⟩
  have append : vector.index = vector.length := vectorIndex.trans vectorLength.symm
  -- The call, the append, and the status test.
  have finishFrom (newEnd : Word) : ∃ (state : Snapshot) (after : ByteMemory),
      run 33 (sync base { original with mem := memory }
        { head with
          pc := 0xa4#32, a0 := key, a2 := head.a3 ^^^ head.s7, a4 := endWord,
          s5 := newEnd }) =
        some (sync base { original with mem := after } state) ∧
      state.pc = 0xf0#32 ∧ state.sp = head.sp ∧ state.s0 = head.s0 ∧ state.s1 = head.s1 ∧
      state.s2 = head.s2 ∧ state.s3 = head.s3 ∧ state.s4 = head.s4 ∧ state.s6 = head.s6 ∧
      state.s7 = head.s7 ∧ state.s5 = newEnd ∧
      state.a1 = lowAfter head.a1 key endWord ∧
      state.s8 = highAfter head.a1 head.s8 key endWord ∧
      state.a3 = head.a3 + 0x8#32 ∧
      WordAt after vector.header.toNat vector.data ∧
      WordAt after (vector.header.toNat + 4) (BitVec.ofNat 32 (vector.length.toNat + 1)) ∧
      WordAt after (vector.header.toNat + 8) vector.capacity ∧
      (∀ index, index < vector.length.toNat + 1 →
        WordAt after (vector.slot index) (vector.result index)) ∧
      vector.unchanged (stored memory head key endWord) after := by
    obtain ⟨called, ranCall, calledPc, calledRa, calledA0, calledA1, calledA2, calledSp, calledS0,
      calledS1, calledS2, calledS3, calledS4, calledS5, calledS6, calledS7, calledS8, calledS9,
      calledS10⟩ := toCall newEnd
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
    have returnAligned : (base + 0xe4#32).toNat % 4 = 0 :=
      SortedMap.Remove.alignedTargetNat frame.code.aligned _ (by decide)
    obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
    have mode : MachineMode entered (base + 0xe4#32) :=
      { (machine.withMemory (stored memory head key endWord)).atSync base called with
        returnLow := by rw [BitVec.and_comm]; exact maskEven _ returnBit0
        returnNext := returnBit1
        ra := by
          have read := syncRead (base := base)
            (frame := { original with mem := stored memory head key endWord }) called
            (index := 1) (by decide)
          rw [show RegisterView.value called 1 = base + 0xe4#32 from calledRa] at read
          exact read }
    have rawImage : CodeImage RawVec.instructions (rawVecBase base) entered :=
      (rawImageOf (stored memory head key endWord) fun byte low high => by
        unfold stored cacheStored
        rw [storeWordOutside _ _ _ _ (rawApart byte low high).2,
          storeWordOutside _ _ _ _ (rawApart byte low high).1]).atSync base called
    obtain ⟨endState, after, ran, endPc, status, -, accepted⟩ :=
      rawVecU32InsertSailRun (rawVecBase base) (base + 0xe4#32) entered vector (rawVecEntry called)
        routineEntered (by change called.a0 = _; rw [calledA0, vectorHeader])
        (by change called.a1 = _; rw [calledA1, vectorIndex])
        (by change called.a2 = _; rw [calledA2, vectorValue])
        (RawVec.Environment.ofMachine mode rawImage) (headerTransfer header regions enteredMem)
        (fun _ => bufferTransfer buffer regions enteredMem)
    obtain ⟨dataAfter, lengthAfter, capacityAfter, slotsAfter, unchangedAfter⟩ := accepted valid
    rw [enteredMem] at unchangedAfter
    have count := appendCount vector valid append
    have statusZero : endState.a0 = 0#32 := status.trans (appendStatus vector valid append)
    have back : run vector.count entered =
        some (sync base { original with mem := after } (afterRawVec called endState)) := by
      rw [ran]
      have withMem := syncWithMem base { original with mem := stored memory head key endWord }
        called after
      have inside := syncInside (frame := { original with mem := after }) base (rawVecBase base)
        called (afterRawVec called endState) endState rawVecInside
        (fun index _ => by fin_cases index <;> rfl) (by
          change base + 0xe4#32 = rawVecBase base + endState.pc
          rw [endPc, BitVec.add_comm (rawVecBase base), BitVec.sub_add_cancel])
      change some (sync (rawVecBase base) { sync base { original with mem := stored memory head key endWord }
        called with mem := after } endState) = _
      rw [withMem]
      exact congrArg some inside
    have image3 := imageOf after (vectorOutsideCode after unchangedAfter)
    obtain ⟨final, tail, finalPc, finalSp, finalS0, finalS1, finalS2, finalS3, finalS4, finalS5,
      finalS6, finalS7, finalS8, finalA1, finalA3⟩ : ∃ final : Snapshot,
        run 3 (sync base { original with mem := after } (afterRawVec called endState)) =
          some (sync base { original with mem := after } final) ∧
        final.pc = 0xf0#32 ∧ final.sp = called.sp ∧ final.s0 = called.s0 ∧
        final.s1 = called.s1 ∧ final.s2 = called.s2 ∧ final.s3 = called.s3 ∧
        final.s4 = called.s4 ∧ final.s5 = called.s5 ∧ final.s6 = called.s6 ∧
        final.s7 = called.s7 ∧ final.s8 = called.s8 ∧ final.a1 = called.s9 ∧
        final.a3 = called.s10 :=
      ⟨_, by
        refine runStep (stepe4 machine image3 _ rfl) ?_
        refine runStep (stepe8 machine image3 _ rfl) ?_
        exact runStep (stepec machine image3 _ rfl) rfl, by
        change (if endState.a0 = 0#32 then (0xf0#32 : Word) else 0x1c4#32) = 0xf0#32
        rw [if_pos statusZero], by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl,
        by rfl, by rfl, by rfl, by rfl⟩
    refine ⟨final, after, ?_, finalPc, finalSp.trans calledSp, finalS0.trans calledS0,
      finalS1.trans calledS1, finalS2.trans calledS2, finalS3.trans calledS3,
      finalS4.trans calledS4, finalS6.trans calledS6, finalS7.trans calledS7,
      finalS5.trans calledS5, finalA1.trans calledS9, finalS8.trans calledS8,
      finalA3.trans calledS10, dataAfter, lengthAfter, capacityAfter, slotsAfter, unchangedAfter⟩
    rw [show 33 = 16 + (vector.count + 3) by rw [count], runAdd, ranCall, Option.bind_some, runAdd,
      back, Option.bind_some]
    exact tail
  by_cases taken : endWord.toNat < head.s5.toNat
  · obtain ⟨state, after, ran, facts⟩ := finishFrom head.s5
    refine ⟨state, after, ?_, ?_⟩
    · rw [if_pos taken, show 42 = 9 + 33 from rfl, runAdd, toDecide, Option.bind_some, if_pos taken]
      exact ran
    · rw [if_pos taken]
      exact facts
  · obtain ⟨state, after, ran, facts⟩ := finishFrom endWord
    refine ⟨state, after, ?_, ?_⟩
    · rw [if_neg taken, show 44 = 9 + (2 + 33) from rfl, runAdd, toDecide, Option.bind_some,
        if_neg taken]
      refine runStep (step114 machine image _ rfl) ?_
      refine runStep (step118 machine image _ rfl) ?_
      exact ran
    · rw [if_neg taken]
      exact facts

end Riscfree.RangeInsert.DeleteExtra
