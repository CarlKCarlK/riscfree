import RangeInsert.DeleteExtra.Finish
import SortedMap.Remove

/-! One iteration of the `delete_extra` removal loop at `+0x164`: load the next
collected key, remove it with the verified `sorted_map_remove` (composed from
`sortedMapRemoveSailRun`), require the `OK` status, and advance the key
cursor. -/

namespace Riscfree.RangeInsert.DeleteExtra

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open Nonempty (mappedTransfer)

set_option maxHeartbeats 4000000

-- `sorted_map_remove` lies 0xc4 bytes before the helper.
def removeOffset : Word := 0xffffff3c
def removeBase (base : Word) : Word := base + removeOffset

def removeEntry (state : Snapshot) : SortedMap.Remove.Snapshot :=
  { ra := state.ra, sp := state.sp, t1 := state.t1, s0 := state.s0, s1 := state.s1, a0 := state.a0,
    a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4, a5 := state.a5, s2 := state.s2 }

def afterRemove (state : Snapshot) (endState : SortedMap.Remove.Snapshot) : Snapshot :=
  { state with
    pc := 0x174#32, ra := endState.ra, sp := endState.sp, t1 := endState.t1, s0 := endState.s0,
    s1 := endState.s1, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2, a3 := endState.a3,
    a4 := endState.a4, a5 := endState.a5, s2 := endState.s2 }

theorem removeInside : ∀ index ∈ tracked SortedMap.Remove.Snapshot, index ∈ tracked Snapshot := by
  decide

section Transfer

variable {frame other : Machine}
  (regions : other.regs.get? Register.pma_regions = frame.regs.get? Register.pma_regions)
  (memory : other.mem = frame.mem)
include regions memory

theorem removeHeaderTransfer {call : PairRemove.Call} (header : PairRemove.Header frame call) :
    PairRemove.Header other call :=
  ⟨header.fits, mappedTransfer header.lengthReadable regions,
    mappedTransfer header.capacityReadable regions, memory ▸ header.lengthWord,
    memory ▸ header.capacityWord⟩

theorem removeBufferTransfer {base : Word} {call : PairRemove.Call}
    (buffer : PairRemove.Buffer base frame call) : PairRemove.Buffer base other call :=
  ⟨buffer.fits, mappedTransfer buffer.dataReadable regions, memory ▸ buffer.dataWord,
    mappedTransfer buffer.lengthWritable regions, buffer.lengthAwayFromCode,
    fun index bound => memory ▸ buffer.live index bound,
    fun index low high => ⟨mappedTransfer (buffer.readable index low high).1 regions,
      mappedTransfer (buffer.readable index low high).2 regions⟩,
    fun index low high => ⟨mappedTransfer (buffer.writable index low high).1 regions,
      mappedTransfer (buffer.writable index low high).2 regions⟩,
    buffer.separated, buffer.awayFromCode⟩

theorem keysTransfer {call : SortedMap.Search.Call} (keys : SortedMap.Search.Keys frame call) :
    SortedMap.Search.Keys other call :=
  ⟨keys.fits, mappedTransfer keys.dataReadable regions, memory ▸ keys.dataWord,
    fun index bound => mappedTransfer (keys.readable index bound) regions,
    fun index bound => memory ▸ keys.keyWord index bound⟩

omit memory in
theorem stackTransfer {base sp : Word} {call : SortedMap.Remove.Call}
    (stack : SortedMap.Remove.Stack base frame call sp) : SortedMap.Remove.Stack base other call sp :=
  ⟨stack.fits, fun offset member => mappedTransfer (stack.readable offset member) regions,
    fun offset member => mappedTransfer (stack.writable offset member) regions,
    stack.apartHeader, stack.apartEntries, stack.apartCode, stack.apartSearch, stack.apartVector⟩

end Transfer

set_option maxRecDepth 20000 in
/-- One removal: 8 instructions of the helper and the verified removal. Only
the 16-byte frame below `sp`, the map's length word, and the shifted slots can
change. -/
theorem removal {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (imageOf : ∀ other : ByteMemory, (∀ byte, base.toNat ≤ byte →
      byte < base.toNat + 4 * DeleteTable.instructions.length → other[byte]? = memory[byte]?) →
      CodeImage DeleteTable.instructions base { original with mem := other })
    (removeCode : CodeImage SortedMap.Remove.instructions (removeBase base)
      { original with mem := memory })
    (searchCode : CodeImage (SortedMap.Search.instructions .lower)
      (SortedMap.Remove.searchBase (removeBase base)) { original with mem := memory })
    (vectorCode : CodeImage PairRemove.instructions
      (SortedMap.Remove.vectorBase (removeBase base)) { original with mem := memory })
    (state : Snapshot) (atLoop : state.pc = 0x164#32) (key : Word)
    (keyReadable : Readable original state.s1) (keyWord : WordAt memory state.s1.toNat key)
    (call : SortedMap.Remove.Call) (callHeader : call.header = state.s0) (callKey : call.key = key)
    (removes : call.removes)
    (header : PairRemove.Header { original with mem := memory } call.vector)
    (stack : SortedMap.Remove.Stack (removeBase base) { original with mem := memory } call state.sp)
    (keys : SortedMap.Search.Keys { original with mem := memory } call.search)
    (buffer : PairRemove.Buffer (SortedMap.Remove.vectorBase (removeBase base))
      { original with mem := memory } call.vector)
    (codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * DeleteTable.instructions.length →
      (byte < state.sp.toNat - 16 ∨ state.sp.toNat ≤ byte) ∧
      (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) ∧
      (byte < call.vector.slot call.vector.index.toNat ∨
        call.vector.slot (call.length.toNat - 1) ≤ byte)) :
    ∃ (final : Snapshot) (after : ByteMemory),
      run (8 + call.count) (sync base { original with mem := memory } state) =
        some (sync base { original with mem := after } final) ∧
      final.pc = (if state.s2 + 0xfffffffc#32 = 0#32 then 0x184#32 else 0x164#32) ∧
      final.sp = state.sp ∧ final.s0 = state.s0 ∧ final.s1 = state.s1 + 0x4#32 ∧
      final.s2 = state.s2 + 0xfffffffc#32 ∧ final.s3 = state.s3 ∧ final.s4 = state.s4 ∧
      final.s5 = state.s5 ∧ final.s6 = state.s6 ∧ final.s7 = state.s7 ∧ final.s8 = state.s8 ∧
      final.s9 = state.s9 ∧ final.s10 = state.s10 ∧
      WordAt after call.header.toNat call.data ∧
      WordAt after (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - 1)) ∧
      WordAt after (call.header.toNat + 8) call.capacity ∧
      (∀ index, index < call.length.toNat - 1 →
        PairAt after (call.vector.slot index) (call.vector.result index)) ∧
      (∀ byte, (byte < state.sp.toNat - 16 ∨ state.sp.toNat ≤ byte) →
        (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) →
        (byte < call.vector.slot call.vector.index.toNat ∨
          call.vector.slot (call.length.toNat - 1) ≤ byte) →
        after[byte]? = memory[byte]?) := by
  have machine := frame.mode.toMachineState
  have image := imageOf memory fun _ _ _ => rfl
  let called : Snapshot :=
    { state with pc := removeOffset, a1 := key, a0 := state.s0, ra := base + 0x174#32 }
  have toCall : run 4 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } called) := by
    refine runStep (step164 machine image _ atLoop key keyReadable keyWord) ?_
    refine runStep (step168 machine image _ rfl) ?_
    refine runStep (step16c machine image _ rfl) ?_
    exact runStep (step170 machine image _ rfl rfl) rfl
  let entered := sync base { original with mem := memory } called
  have regions : entered.regs.get? Register.pma_regions =
      ({ original with mem := memory } : Machine).regs.get? Register.pma_regions :=
    syncFrame called _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have enteredMem : entered.mem = memory := syncMem called
  have routineEntered :
      entered = sync (removeBase base) entered { removeEntry called with pc := 0 } := by
    have inside := syncInside (frame := { original with mem := memory }) base (removeBase base)
      called called (removeEntry called) removeInside (fun index _ => by fin_cases index <;> rfl)
      (BitVec.add_zero _).symm
    exact inside.symm
  have returnAligned : (base + 0x174#32).toNat % 4 = 0 :=
    SortedMap.Remove.alignedTargetNat frame.code.aligned _ (by decide)
  obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
  have mode : MachineMode entered (base + 0x174#32) :=
    { (machine.withMemory memory).atSync base called with
      returnLow := by rw [BitVec.and_comm]; exact maskEven _ returnBit0
      returnNext := returnBit1
      ra := syncRead called (index := 1) (by decide) }
  have environment : SortedMap.Remove.Environment (removeBase base) (base + 0x174#32) entered :=
    ⟨mode, removeCode.atSync base called, searchCode.atSync base called,
      vectorCode.atSync base called⟩
  have fits := stack.fits
  obtain ⟨endState, after, ran, endPc, status, endRa, endSp, endS0, endS1, endS2, -, accepted⟩ :=
    SortedMap.Remove.sortedMapRemoveSailRun (removeBase base) (base + 0x174#32) entered call
      (removeEntry called) routineEntered (by change state.s0 = _; exact callHeader.symm)
      (by change key = _; exact callKey.symm) environment
      (removeHeaderTransfer regions enteredMem header) (stackTransfer regions stack)
      (fun _ _ => keysTransfer regions enteredMem keys)
      (fun _ => removeBufferTransfer regions enteredMem buffer)
  obtain ⟨dataAfter, lengthAfter, capacityAfter, entriesAfter, unchangedAfter⟩ := accepted removes
  rw [enteredMem] at unchangedAfter
  have statusZero : endState.a0 = 0#32 := by
    rw [status]; simp [SortedMap.Remove.Call.status, removes, removes.1]
  have back : run call.count entered =
      some (sync base { original with mem := after } (afterRemove called endState)) := by
    rw [ran]
    have withMem := syncWithMem base { original with mem := memory } called after
    have inside := syncInside (frame := { original with mem := after }) base (removeBase base)
      called (afterRemove called endState) endState removeInside
      (fun index _ => by fin_cases index <;> rfl) (by
        change base + 0x174#32 = removeBase base + endState.pc
        rw [endPc, BitVec.add_comm (removeBase base), BitVec.sub_add_cancel])
    change some (sync (removeBase base) { sync base { original with mem := memory } called with
      mem := after } endState) = _
    rw [withMem]
    exact congrArg some inside
  have kept (byte : Nat) (outsideFrame : byte < state.sp.toNat - 16 ∨ state.sp.toNat ≤ byte)
      (outsideLength : byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte)
      (outsideSlots : byte < call.vector.slot call.vector.index.toNat ∨
        call.vector.slot (call.length.toNat - 1) ≤ byte) :
      after[byte]? = memory[byte]? := by
    rw [unchangedAfter byte outsideLength outsideSlots]
    exact SortedMap.Remove.pushedOutside memory (removeEntry called) fits byte outsideFrame
  have imageAfter := imageOf after fun byte low high =>
    kept byte (codeApart byte low high).1 (codeApart byte low high).2.1 (codeApart byte low high).2.2
  have ok : (afterRemove called endState).a0 = 0#32 := statusZero
  let final : Snapshot :=
    { afterRemove called endState with
      pc := if endState.s2 + 0xfffffffc#32 = 0#32 then 0x184#32 else 0x164#32,
      s1 := endState.s1 + 0x4#32, s2 := endState.s2 + 0xfffffffc#32 }
  have tail : run 4 (sync base { original with mem := after } (afterRemove called endState)) =
      some (sync base { original with mem := after } final) := by
    refine runStep (step174 machine imageAfter _ rfl) ?_
    rw [if_pos ok]
    refine runStep (step178 machine imageAfter _ rfl) ?_
    refine runStep (step17c machine imageAfter _ rfl) ?_
    exact runStep (step180 machine imageAfter _ rfl) rfl
  have finalSp : final.sp = endState.sp := rfl
  have finalS0 : final.s0 = endState.s0 := rfl
  have finalPc : final.pc = (if endState.s2 + 0xfffffffc#32 = 0#32 then 0x184#32 else 0x164#32) := by
    dsimp only [final]
  have finalS1 : final.s1 = endState.s1 + 0x4#32 := rfl
  have finalS2 : final.s2 = endState.s2 + 0xfffffffc#32 := rfl
  have finalS3 : final.s3 = state.s3 := rfl
  have finalS4 : final.s4 = state.s4 := rfl
  have finalS5 : final.s5 = state.s5 := rfl
  have finalS6 : final.s6 = state.s6 := rfl
  have finalS7 : final.s7 = state.s7 := rfl
  have finalS8 : final.s8 = state.s8 := rfl
  have finalS9 : final.s9 = state.s9 := rfl
  have finalS10 : final.s10 = state.s10 := rfl
  refine ⟨final, after, ?_, ?_, finalSp.trans endSp, finalS0.trans endS0, ?_, ?_, finalS3,
    finalS4, finalS5, finalS6, finalS7, finalS8, finalS9, finalS10, dataAfter, lengthAfter,
    capacityAfter, entriesAfter, kept⟩
  · rw [show 8 + call.count = 4 + (call.count + 4) by omega, runAdd, toCall, Option.bind_some,
      runAdd, back, Option.bind_some]
    exact tail
  · rw [finalPc, endS2]; rfl
  · rw [finalS1, endS1]; rfl
  · rw [finalS2, endS2]; rfl

end Riscfree.RangeInsert.DeleteExtra
