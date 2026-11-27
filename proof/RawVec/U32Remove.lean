import Riscfree.Elf
import RawVec.U32Remove.Instructions
import RawVec.Remove

/-!
# `raw_vec_u32_remove` is correct against Sail

The specification, footprint, and copy-loop invariant come from
`RawVec/Remove.lean`. This module supplies only what the linked code fixes:
the step count, the register assignment, and the composition of the step
lemmas in `RawVec/U32Remove/Instructions.lean`.
-/

namespace Riscfree.RawVec.U32Remove

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

abbrev Call := Remove.Call Word

-- Invalid length, invalid index, removal of the last element, and removal
-- before `m = length - 1 - index > 0` elements, which runs the loop `m` times.
def Call.count (call : Call) : Nat :=
  if call.capacity.toNat < call.length.toNat then 5
  else if call.length.toNat ≤ call.index.toNat then 6
  else if call.index.toNat + 1 = call.length.toNat then 9
  else 15 + 4 * (call.length.toNat - 1 - call.index.toNat)

abbrev Header (original : Machine) (call : Call) : Prop := Remove.Header original call

abbrev Buffer (base : Word) (original : Machine) (call : Call) : Prop :=
  Remove.Buffer 92 base original call

open Remove (headerOffset slotNat slotReached Progress initialProgress finalMemory finalWords)
open Insert (storeKeepsCode)

section Run

variable {base returnAddress : Word} {original : Machine} {call : Call}

private abbrev synced (base : Word) (original : Machine) (memory : ByteMemory)
    (state : Snapshot) : Machine := sync base {original with mem := memory} state

private def ready (call : Call) (state : Snapshot) : Snapshot :=
  { state with
    pc := if call.index.toNat + 1 = call.length.toNat then 72 else 32
    a2 := call.newLength
    a3 := call.length }

private theorem newLengthNat (call : Call) (positive : 0 < call.length.toNat) :
    call.newLength.toNat = call.length.toNat - 1 := by
  have := call.length.isLt
  simp only [Remove.Call.newLength, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

private theorem dispatch (environment : Environment base returnAddress original)
    (header : Header original call) (state : Snapshot) (atEntry : state.pc = 0)
    (argument : state.a0 = call.header) (index : state.a1 = call.index) :
    let final := if call.valid then ready call state else
      { state with
        pc := returnAddress - base
        a0 := call.status
        a2 := call.capacity
        a3 := call.length }
    run (if call.valid then 6 else call.count) (synced base original original.mem state) =
      some (synced base original original.mem final) := by
  dsimp only
  let platform := environment.platform original.mem (fun _ _ _ => rfl)
  have lengthRead : Readable original (state.a0 + 4) := argument ▸ header.lengthReadable
  have capacityRead : Readable original (state.a0 + 8) := argument ▸ header.capacityReadable
  have lengthWord : WordAt original.mem (state.a0 + 4).toNat call.length := by
    have address : (state.a0 + 4).toNat = call.header.toNat + 4 := by
      rw [argument]
      exact headerOffset header 4 (by decide)
    rw [address]
    exact header.lengthWord
  have capacityWord : WordAt original.mem (state.a0 + 8).toNat call.capacity := by
    have address : (state.a0 + 8).toNat = call.header.toNat + 8 := by
      rw [argument]
      exact headerOffset header 8 (by decide)
    rw [address]
    exact header.capacityWord
  have first := step00 platform state atEntry call.length lengthRead lengthWord
  have second := step04 platform { state with pc := 4, a3 := call.length } rfl
    call.capacity capacityRead capacityWord
  by_cases badLength : call.capacity.toNat < call.length.toNat
  · have notValid : ¬ call.valid := fun valid => (Nat.not_lt_of_ge valid.2) badLength
    simp only [notValid, if_false, Call.count, Remove.Call.status, if_pos badLength]
    refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
    have branch : ¬ call.length.toNat ≤ call.capacity.toNat := by omega
    simp only [branch, if_false]
    exact runStep (step0c platform _ rfl) (runStep (step10 platform _ rfl) rfl)
  · have lengthValid : call.length.toNat ≤ call.capacity.toNat := by omega
    by_cases badIndex : call.length.toNat ≤ call.index.toNat
    · have notValid : ¬ call.valid := fun valid => Nat.not_lt_of_ge badIndex valid.1
      simp only [notValid, if_false, Call.count, Remove.Call.status, if_neg badLength,
        if_pos badIndex]
      refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
      simp only [if_pos lengthValid]
      refine runStep (step14 platform _ rfl) ?_
      simp only [index, if_pos badIndex]
      exact runStep (step54 platform _ rfl) (runStep (step58 platform _ rfl) rfl)
    · have valid : call.valid := ⟨by omega, lengthValid⟩
      simp only [if_pos valid, ready]
      refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
      simp only [if_pos lengthValid]
      refine runStep (step14 platform _ rfl) ?_
      simp only [index, if_neg badIndex]
      refine runStep (step18 platform _ rfl) (runStep (step1c platform _ rfl) ?_)
      have last : call.newLength.toNat ≤ call.index.toNat ↔
          call.index.toNat + 1 = call.length.toNat := by
        rw [newLengthNat call (by omega)]
        omega
      simp only [call.decrement (by omega), last, run]
      rfl

-- The registers the loop and the final store rely on.
private def arguments (call : Call) (state : Snapshot) : Prop :=
  state.a0 = call.header ∧ state.a2 = call.newLength ∧ state.a3 = call.wordSlot call.length.toNat

private theorem setupLoop (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (state : Snapshot) (atSetup : state.pc = 32)
    (header : state.a0 = call.header) (index : state.a1 = call.index)
    (newLength : state.a2 = call.newLength) (length : state.a3 = call.length) :
    ∃ seed, run 6 (synced base original original.mem state) =
      some (synced base original original.mem seed) ∧
      seed.pc = 56 ∧ arguments call seed ∧ seed.a1 = call.wordSlot (call.index.toNat + 1) := by
  let platform := environment.platform original.mem (fun _ _ _ => rfl)
  have read : Readable original state.a0 := header ▸ buffer.dataReadable
  have contents : WordAt original.mem state.a0.toNat call.data := header ▸ buffer.dataWord
  refine ⟨_, runStep (step20 platform state atSetup call.data read contents)
    (runStep (step24 platform _ rfl) (runStep (step28 platform _ rfl)
      (runStep (step2c platform _ rfl) (runStep (step30 platform _ rfl)
        (runStep (step34 platform _ rfl) rfl))))), rfl, ⟨header, newLength, ?_⟩, ?_⟩
  · change call.data + state.a3 <<< (2 : Nat) = _
    rw [length, BitVec.add_comm]
    exact call.slotShift 2 rfl call.length
  · change state.a1 <<< (2 : Nat) + call.data + 4#32 = _
    rw [index, call.slotShift 2 rfl call.index]
    exact call.slotNext call.index.toNat

private def afterCopy (call : Call) (state : Snapshot) (current : Nat) : Snapshot :=
  { state with
    pc := if current + 2 = call.length.toNat then 72 else 56
    a1 := call.wordSlot (current + 2)
    a4 := call.old (current + 1) }

private theorem oneCopy (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (state : Snapshot) {memory : ByteMemory} (current : Nat)
    (progress : Progress 92 base original call current memory)
    (atLoop : state.pc = 56) (inputs : arguments call state)
    (pointer : state.a1 = call.wordSlot (current + 1))
    (afterIndex : call.index.toNat ≤ current) (bound : current + 1 < call.length.toNat) :
    run 4 (synced base original memory state) =
      some (synced base original (storeWord memory (call.slot current) (call.old (current + 1)))
        (afterCopy call state current)) := by
  let platform := environment.platform memory progress.code
  let nextPlatform := environment.platform (storeWord memory (call.slot current) (call.old (current + 1)))
    (storeKeepsCode progress.code (buffer.awayFromCode current afterIndex bound) _)
  have read : Readable original state.a1 := by
    rw [pointer]
    exact buffer.readable (current + 1) (by omega) bound
  have contents : WordAt memory state.a1.toNat (call.old (current + 1)) := by
    rw [pointer, slotNat buffer bound]
    exact progress.source buffer (by omega) bound
  have target : state.a1 + 0xfffffffc#32 = call.wordSlot current := by
    rw [pointer]
    exact call.slotPrev current _ (by decide)
  have write : Writable original (state.a1 + 0xfffffffc#32) := by
    rw [target]
    exact buffer.writable current afterIndex bound
  have address : (state.a1 + 0xfffffffc#32).toNat = call.slot current := by
    rw [target, slotNat buffer (by omega)]
  refine runStep (step38 platform state atLoop _ read contents) ?_
  have stored := step3c platform { state with pc := 60, a4 := call.old (current + 1) } rfl write
  rw [address] at stored
  refine runStep stored (runStep (step40 nextPlatform _ rfl) (runStep (step44 nextPlatform _ rfl) ?_))
  have advanced : call.wordSlot (current + 1) + 4#32 = call.wordSlot (current + 2) :=
    call.slotNext (current + 1)
  have reached := slotReached buffer (index := current + 2) (by omega) (by omega)
  simp only [run, afterCopy, pointer, advanced, inputs.2.2, reached]
  rfl

private def Looping (base : Word) (original : Machine) (call : Call) (current : Nat)
    (position : ByteMemory × Snapshot) : Prop :=
  Progress 92 base original call current position.1 ∧ call.index.toNat ≤ current ∧
    position.2.pc = (if current + 1 = call.length.toNat then 72 else 56) ∧
    arguments call position.2 ∧ position.2.a1 = call.wordSlot (current + 1)

private theorem copyLoop (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (remaining current : Nat) (state : Snapshot)
    (memory : ByteMemory) (sum : current + 1 + remaining = call.length.toNat)
    (looping : Looping base original call current (memory, state)) :
    ∃ final out, run (4 * remaining) (synced base original memory state) =
      some (synced base original out final) ∧
      final.pc = 72 ∧ arguments call final ∧
      Progress 92 base original call (call.length.toNat - 1) out := by
  -- The countdown runs from `remaining` iterations down to none.
  let Invariant (remaining : Nat) (position : ByteMemory × Snapshot) : Prop :=
    ∃ current, current + 1 + remaining = call.length.toNat ∧ Looping base original call current position
  obtain ⟨⟨out, final⟩, ran, last, sum, progress, -, pc, args, -⟩ := runCountdown
    (fun position => synced base original position.1 position.2) Invariant 0 4
    (fun remaining position holds => by
      obtain ⟨memory, state⟩ := position
      obtain ⟨current, sum, progress, afterIndex, pc, inputs, pointer⟩ := holds
      have looping : state.pc = 56 := by rw [pc, if_neg (by omega)]
      refine ⟨(_, afterCopy call state current),
        oneCopy environment buffer state current progress looping inputs pointer afterIndex (by omega),
        current + 1, by omega, progress.copy buffer afterIndex (by omega), by omega, ?_, inputs, rfl⟩
      by_cases done : current + 2 = call.length.toNat
      · simp [afterCopy, done]
      · simp [afterCopy, done])
    remaining (memory, state) ⟨current, by omega, looping⟩
  have whole : last = call.length.toNat - 1 := by omega
  subst whole
  exact ⟨final, out, ran, by rw [pc, if_pos (by omega)], args, progress⟩

private def returned (base returnAddress : Word) (state : Snapshot) : Snapshot :=
  { state with pc := returnAddress - base, a0 := 0 }

private theorem finish (environment : Environment base returnAddress original)
    (header : Header original call) (buffer : Buffer base original call)
    (state : Snapshot) (memory : ByteMemory)
    (progress : Progress 92 base original call (call.length.toNat - 1) memory)
    (atFinish : state.pc = 72) (argument : state.a0 = call.header)
    (newLength : state.a2 = call.newLength) :
    run 3 (synced base original memory state) =
      some (synced base original (finalMemory call memory) (returned base returnAddress state)) := by
  -- Substitute the argument registers into the snapshot, so the stored value
  -- is literally the call's value (see `PairInsert.finish`).
  obtain ⟨pc, a0, a1, a2, a3, a4⟩ := state
  dsimp only at atFinish argument newLength
  subst atFinish argument newLength
  let platform := environment.platform memory progress.code
  let completed := environment.platform (finalMemory call memory)
    (storeKeepsCode progress.code buffer.lengthAwayFromCode _)
  have updated := step48 platform
    { pc := 72, a0 := call.header, a1 := a1, a2 := call.newLength, a3 := a3, a4 := a4 }
    rfl buffer.lengthWritable
  dsimp only at updated
  rw [headerOffset header 4 (by decide)] at updated
  exact runStep updated (runStep (step4c completed _ rfl) (runStep (step50 completed _ rfl) rfl))

private theorem success (environment : Environment base returnAddress original)
    (header : Header original call) (buffer : Buffer base original call)
    (initial : Snapshot) (argument : initial.a0 = call.header) (index : initial.a1 = call.index)
    (valid : call.valid) :
    ∃ state memory,
      run (call.count - 6) (synced base original original.mem (ready call initial)) =
        some (synced base original (finalMemory call memory) (returned base returnAddress state)) ∧
      Progress 92 base original call (call.length.toNat - 1) memory := by
  obtain ⟨indexBound, lengthBound⟩ := valid
  have lengthValid : ¬ call.capacity.toNat < call.length.toNat := by omega
  have indexValid : ¬ call.length.toNat ≤ call.index.toNat := by omega
  by_cases last : call.index.toNat + 1 = call.length.toNat
  · have progress : Progress 92 base original call (call.length.toNat - 1) original.mem := by
      rw [show call.length.toNat - 1 = call.index.toNat by omega]
      exact initialProgress header buffer
    refine ⟨ready call initial, original.mem, ?_, progress⟩
    simp only [Call.count, lengthValid, indexValid, last, if_false, if_true]
    exact finish environment header buffer _ original.mem progress
      (by simp [ready, last]) argument rfl
  · let remaining := call.length.toNat - 1 - call.index.toNat
    obtain ⟨seed, setup, atLoop, inputs, pointer⟩ :=
      setupLoop environment buffer (ready call initial) (by simp [ready, last]) argument index rfl rfl
    obtain ⟨state, memory, copied, exited, args, progress⟩ :=
      copyLoop environment buffer remaining call.index.toNat seed original.mem (by omega)
        ⟨initialProgress header buffer, Nat.le_refl _, by rw [atLoop, if_neg last], inputs, pointer⟩
    have done := finish environment header buffer state memory progress exited args.1 args.2.1
    refine ⟨state, memory, ?_, progress⟩
    simp only [Call.count, lengthValid, indexValid, last, if_false]
    rw [show 15 + 4 * (call.length.toNat - 1 - call.index.toNat) - 6 = 6 + (4 * remaining + 3) by omega,
      runAdd, setup, Option.bind_some, runAdd, copied, Option.bind_some, done]

private theorem a0Read (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x10 = some state.a0 :=
  readReg_succ.mp (syncRead state (index := 10) (by decide))

-- The same run, ending in a synchronized state: the snapshot's PC, the
-- status in `a0`, and a memory.
theorem rawVecU32RemoveSailRun (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (environment : Environment base returnAddress original)
    (header : Header original call)
    (buffer : call.valid → Buffer base original call) :
    ∃ (endState : Snapshot) (memory : ByteMemory),
      run call.count original = some (sync base { original with mem := memory } endState) ∧
      endState.pc = returnAddress - base ∧ endState.a0 = call.status ∧
      (¬ call.valid → memory = original.mem) ∧
      (call.valid →
        WordAt memory call.header.toNat call.data ∧
        WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - 1)) ∧
        WordAt memory (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat - 1 →
          WordAt memory (call.slot index) (call.result index)) ∧
        call.unchanged original.mem memory) := by
  let start := { initial with pc := 0#32 }
  have begins : original = synced base original original.mem start := entry
  have checks := dispatch environment header start rfl headerArgument indexArgument
  by_cases valid : call.valid
  · have goodLength : ¬ call.capacity.toNat < call.length.toNat := by have := valid.2; omega
    have goodIndex : ¬ call.length.toNat ≤ call.index.toNat := by have := valid.1; omega
    have enough : 6 ≤ call.count := by
      simp only [Call.count, goodLength, goodIndex, if_false]
      split <;> omega
    obtain ⟨state, memory, ran, progress⟩ :=
      success environment header (buffer valid) start headerArgument indexArgument valid
    refine ⟨returned base returnAddress state, finalMemory call memory, ?_, rfl, ?_, ?_,
      fun _ => finalWords (buffer valid) memory progress valid⟩
    · have checkedRun := checks
      simp only [if_pos valid] at checkedRun
      refine (congrArg (run call.count) begins).trans ?_
      rw [show call.count = 6 + (call.count - 6) by omega, runAdd, checkedRun,
        Option.bind_some, ran]
    · simp [returned, Remove.Call.status, goodLength, goodIndex]
    · intro rejected
      exact (rejected valid).elim
  · simp only [if_neg valid] at checks
    refine ⟨_, original.mem, (congrArg (run call.count) begins).trans checks, rfl, rfl,
      fun _ => rfl, fun accepted => (valid accepted).elim⟩

-- The pointwise output specifies the entire new logical sequence. Bytes
-- outside the length word and the written slots, including the vacated last
-- slot, keep their original values. A rejected call changes no memory.
theorem rawVecU32RemoveSailCorrect (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (environment : Environment base returnAddress original)
    (header : Header original call)
    (buffer : call.valid → Buffer base original call) :
    ∃ final, run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = original.mem) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat - 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged original.mem final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14],
        final.regs.get? register = original.regs.get? register) := by
  obtain ⟨endState, memory, ran, pc, result, rejected, accepted⟩ :=
    rawVecU32RemoveSailRun base returnAddress original call initial entry headerArgument
      indexArgument environment header buffer
  refine ⟨_, ran, pcReadReturned _ _ _ _ pc, (a0Read _ _ _).trans (congrArg some result),
    ?_, ?_, ?_⟩
  · simpa only [syncMem] using rejected
  · simpa only [syncMem] using accepted
  · intro register outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨pc, next, a0, a1, a2, a3, a4⟩ := outside
    refine syncFrame endState register pc next ?_
    intro index member
    change index ∈ ([10, 11, 12, 13, 14] : List (Fin 32)) at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    exacts [Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4]

-- The same guarantee with the code mapping derived rather than assumed. The
-- hart runs in machine mode, and the routine's 92 bytes lie in memory that
-- Sail's PMA check lets it fetch. Because every write the routine makes misses
-- the code (`Buffer.awayFromCode`), the fetches stay valid for the whole run.
theorem rawVecU32RemoveSailCorrectInMachineMode (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (mode : MachineMode original returnAddress)
    (image : CodeImage instructions base original)
    (header : Header original call)
    (buffer : call.valid → Buffer base original call) :
    ∃ final, run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = original.mem) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat - 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged original.mem final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14],
        final.regs.get? register = original.regs.get? register) :=
  rawVecU32RemoveSailCorrect base returnAddress original call initial entry headerArgument
    indexArgument (Environment.ofMachine mode image) header buffer

end Run

def verifyElf (path : String) : IO Unit :=
  Riscfree.verifyElf path "raw_vec_u32_remove" (instructions.map Prod.fst)

end Riscfree.RawVec.U32Remove
