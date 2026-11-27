import RawVec.PairInsert.Instructions
import RawVec.Insert

/-!
# `raw_vec_pair_insert` is correct against Sail

The same theorem as `rawVecU32InsertSailCorrect`, for `RawVec<Pair>`. The
specification, footprint, and copy-loop invariant come from
`RawVec/Insert.lean`. This module supplies only what the linked code fixes:
the step count, the register assignment, and the composition of the step
lemmas in `RawVec/PairInsert/Instructions.lean`.
-/

namespace Riscfree.RawVec.PairInsert

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

abbrev Call := Insert.Call Pair

def Call.count (call : Call) : Nat :=
  if call.capacity.toNat < call.length.toNat then 5
  else if call.length.toNat < call.index.toNat then 6
  else if call.length = call.capacity then 7
  else if call.index = call.length then 15
  else 19 + 8 * (call.length.toNat - call.index.toNat)

abbrev Header (original : Machine) (call : Call) : Prop := Insert.Header original call

abbrev Buffer (base : Word) (original : Machine) (call : Call) : Prop :=
  Insert.Buffer 132 base original call

open Insert (headerOffset slotNat slotAdd slotPrev slotOffset counterPrev storeKeepsCode
  elementKeepsCode Progress initialProgress insertedMemory finalMemory finalWords ofWordNat)

section Run

variable {base returnAddress : Word} {original : Machine} {call : Call}

private abbrev synced (base : Word) (original : Machine) (memory : ByteMemory)
    (state : Snapshot) : Machine := sync base {original with mem := memory} state

private def ready (call : Call) (state : Snapshot) : Snapshot :=
  { state with
    pc := if call.index = call.length then 96 else 48
    a4 := call.length
    a5 := call.capacity }

private theorem dispatch (environment : Environment base returnAddress original)
    (header : Header original call) (state : Snapshot) (atEntry : state.pc = 0)
    (argument : state.a0 = call.header) (index : state.a1 = call.index) :
    let final := if call.valid then ready call state else
      { state with
        pc := returnAddress - base
        a0 := call.status
        a4 := call.length
        a5 := call.capacity }
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
  have second := step04 platform { state with pc := 4, a4 := call.length } rfl
    call.capacity capacityRead capacityWord
  by_cases badLength : call.capacity.toNat < call.length.toNat
  · have notValid : ¬ call.valid := fun valid =>
      (Nat.not_lt_of_ge (Nat.le_of_lt valid.2)) badLength
    simp only [notValid, if_false, Call.count, Insert.Call.status, if_pos badLength]
    refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
    have branch : ¬ call.length.toNat ≤ call.capacity.toNat := by omega
    simp only [branch, if_false]
    exact runStep (step0c platform _ rfl) (runStep (step10 platform _ rfl) rfl)
  · have lengthValid : call.length.toNat ≤ call.capacity.toNat := by omega
    by_cases badIndex : call.length.toNat < call.index.toNat
    · have notValid : ¬ call.valid := fun valid => Nat.not_lt_of_ge valid.1 badIndex
      simp only [notValid, if_false, Call.count, Insert.Call.status, if_neg badLength, if_pos badIndex]
      refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
      simp only [if_pos lengthValid]
      refine runStep (step14 platform _ rfl) ?_
      have branch : ¬ call.index.toNat ≤ call.length.toNat := by omega
      simp only [index, branch, if_false]
      exact runStep (step18 platform _ rfl) (runStep (step1c platform _ rfl) rfl)
    · have indexValid : call.index.toNat ≤ call.length.toNat := by omega
      by_cases full : call.length = call.capacity
      · have notValid : ¬ call.valid := by intro valid; simpa [full] using valid.2
        simp only [notValid, if_false, Call.count, Insert.Call.status, if_neg badLength,
          if_neg badIndex, if_pos full]
        refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
        simp only [if_pos lengthValid]
        refine runStep (step14 platform _ rfl) ?_
        simp only [index, if_pos indexValid]
        refine runStep (step20 platform _ rfl) ?_
        simp only [if_pos full]
        exact runStep (step24 platform _ rfl) (runStep (step28 platform _ rfl) rfl)
      · have lt : call.length.toNat < call.capacity.toNat := by
          refine Nat.lt_of_le_of_ne lengthValid ?_
          intro same
          exact full (BitVec.eq_of_toNat_eq same)
        have valid : call.valid := ⟨indexValid, lt⟩
        simp only [if_pos valid, ready]
        refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
        simp only [if_pos lengthValid]
        refine runStep (step14 platform _ rfl) ?_
        simp only [index, if_pos indexValid]
        refine runStep (step20 platform _ rfl) ?_
        simp only [if_neg full]
        refine runStep (step2c platform _ rfl) ?_
        have eqIff : call.length.toNat ≤ call.index.toNat ↔ call.index = call.length := by
          constructor
          · intro le
            exact BitVec.eq_of_toNat_eq (by omega)
          · intro same
            simp [same]
        simp only [eqIff, run]
        rfl

private def arguments (call : Call) (state : Snapshot) : Prop :=
  state.a0 = call.header ∧ state.a1 = call.index ∧ state.a2 = call.value.key ∧
    state.a3 = call.value.value ∧ state.a4 = call.length

private theorem setupLoop (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (state : Snapshot) (atSetup : state.pc = 48)
    (inputs : arguments call state) :
    run 4 (synced base original original.mem state) =
      some (synced base original original.mem
        { state with pc := 64, a5 := call.wordSlot call.length.toNat, a6 := call.length }) := by
  let platform := environment.platform original.mem (fun _ _ _ => rfl)
  obtain ⟨header, _, _, _, length⟩ := inputs
  have read : Readable original state.a0 := header ▸ buffer.dataReadable
  have contents : WordAt original.mem state.a0.toNat call.data := header ▸ buffer.dataWord
  refine runStep (step30 platform state atSetup call.data read contents)
    (runStep (step34 platform _ rfl) (runStep (step38 platform _ rfl)
      (runStep (step3c platform _ rfl) ?_)))
  have effective : call.data + (call.length <<< (3 : Nat)) = call.wordSlot call.length.toNat := by
    simpa only [ofWordNat] using slotAdd buffer 3 rfl (index := call.length.toNat) (Nat.le_refl _)
  simp only [run, effective, length]
  rfl

-- The second word of the slot below the pointer.
private theorem secondWordPrev (call : Call) (index : Nat) :
    call.wordSlot (index + 1) + 0xfffffffc#32 = call.wordSlot index + 4#32 := by
  rw [← slotPrev call index 0xfffffff8#32 (by decide), BitVec.add_assoc]
  rfl

private def afterCopy (call : Call) (state : Snapshot) (index : Nat) : Snapshot :=
  { state with
    pc := if call.index.toNat < index then 64 else 96
    t0 := (call.old index).value
    t1 := call.wordSlot index
    a5 := call.wordSlot index
    a6 := BitVec.ofNat 32 index
    a7 := (call.old index).key }

private theorem oneCopy (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (state : Snapshot) {memory : ByteMemory} (index : Nat)
    (progress : Progress 132 base original call (index + 1) memory)
    (atLoop : state.pc = 64) (inputs : arguments call state)
    (pointer : state.a5 = call.wordSlot (index + 1))
    (counter : state.a6 = BitVec.ofNat 32 (index + 1))
    (above : call.index.toNat ≤ index) (live : index < call.length.toNat) :
    run 8 (synced base original memory state) =
      some (synced base original (storePair memory (call.slot (index + 1)) (call.old index))
        (afterCopy call state index)) := by
  let platform := environment.platform memory progress.code
  let target := call.slot (index + 1)
  let half := storeWord memory target (call.old index).key
  let updated := storePair memory target (call.old index)
  have away := buffer.awayFromCode (index + 1) (by omega) (by omega)
  let halfPlatform := environment.platform half (storeKeepsCode progress.code (away.narrow (by decide)) _)
  let nextPlatform := environment.platform updated (elementKeepsCode progress.code away _)
  have source : state.a5 + 0xfffffff8#32 = call.wordSlot index := by
    rw [pointer, slotPrev call index _ (by decide)]
  have sourceSecond : state.a5 + 0xfffffffc#32 = call.wordSlot index + 4#32 := by
    rw [pointer, secondWordPrev]
  have readable : Readable original (call.wordSlot index) ∧
      Readable original (call.wordSlot index + 4) := buffer.readable index above live
  have firstRead : Readable original (state.a5 + 0xfffffff8#32) := by rw [source]; exact readable.1
  have secondRead : Readable original (state.a5 + 0xfffffffc#32) := by
    rw [sourceSecond]; exact readable.2
  have pair := progress.source buffer (by omega) live
  have firstContents : WordAt memory (state.a5 + 0xfffffff8#32).toNat (call.old index).key := by
    rw [source, slotNat buffer (by omega)]
    exact pair.1
  have secondContents : WordAt memory (state.a5 + 0xfffffffc#32).toNat (call.old index).value := by
    rw [sourceSecond, slotOffset buffer (by omega) (by decide)]
    exact pair.2
  have writable : Writable original (call.wordSlot (index + 1)) ∧
      Writable original (call.wordSlot (index + 1) + 4) :=
    buffer.writable (index + 1) (by omega) (by omega)
  have firstWrite : Writable original state.a5 := by rw [pointer]; exact writable.1
  have secondWrite : Writable original (state.a5 + 4#32) := by rw [pointer]; exact writable.2
  have address : state.a5.toNat = target := by
    rw [pointer, slotNat buffer (by omega)]
  have secondAddress : (state.a5 + 4#32).toNat = target + 4 := by
    rw [pointer, slotOffset buffer (by omega) (by decide)]
  refine runStep (step40 platform state atLoop (call.old index).key firstRead
    firstContents) (runStep (step44 platform _ rfl (call.old index).value
      secondRead secondContents)
    (runStep (step48 platform _ rfl) (runStep (step4c platform _ rfl) ?_)))
  have firstStore := step50 platform
    { state with
      pc := 80
      a7 := (call.old index).key
      t0 := (call.old index).value
      a6 := state.a6 + 0xffffffff#32
      t1 := state.a5 + 0xfffffff8#32 } rfl firstWrite
  rw [address] at firstStore
  have secondStore := step54 halfPlatform
    { state with
      pc := 84
      a7 := (call.old index).key
      t0 := (call.old index).value
      a6 := state.a6 + 0xffffffff#32
      t1 := state.a5 + 0xfffffff8#32 } rfl secondWrite
  rw [secondAddress] at secondStore
  refine runStep firstStore (runStep secondStore
    (runStep (step58 nextPlatform _ rfl) (runStep (step5c nextPlatform _ rfl) ?_)))
  have fits : index < 2 ^ 32 := by have := call.length.isLt; omega
  simp only [run, afterCopy, source, counter, counterPrev, inputs.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits]
  rfl

private def Looping (base : Word) (original : Machine) (call : Call) (current : Nat)
    (position : ByteMemory × Snapshot) : Prop :=
  Progress 132 base original call current position.1 ∧ current ≤ call.length.toNat ∧
    position.2.pc = (if current = call.index.toNat then 96 else 64) ∧ arguments call position.2 ∧
    position.2.a5 = call.wordSlot current ∧ position.2.a6 = BitVec.ofNat 32 current

private theorem copyLoop (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (remaining : Nat) (state : Snapshot) (memory : ByteMemory)
    (looping : Looping base original call (call.index.toNat + remaining) (memory, state)) :
    ∃ final out, run (8 * remaining) (synced base original memory state) =
      some (synced base original out final) ∧
      final.pc = 96 ∧ arguments call final ∧ Progress 132 base original call call.index.toNat out := by
  obtain ⟨⟨out, final⟩, ran, progress, -, pc, args, -⟩ := runCountdown
    (fun position => synced base original position.1 position.2) (Looping base original call)
    call.index.toNat 8 (fun remaining position holds => by
      obtain ⟨memory, state⟩ := position
      obtain ⟨progress, bound, pc, inputs, pointer, counter⟩ := holds
      let index := call.index.toNat + remaining
      have looping : state.pc = 64 := by rw [pc, if_neg (by omega)]
      refine ⟨(_, afterCopy call state index),
        oneCopy environment buffer state index progress looping inputs pointer counter
          (by omega) (by omega),
        progress.copy buffer (by omega) (by omega), by omega, ?_, inputs, rfl, rfl⟩
      by_cases empty : remaining = 0
      · simp [afterCopy, index, empty]
      · have less : call.index.toNat < index := by omega
        simp [afterCopy, less, empty])
    remaining (memory, state) looping
  exact ⟨final, out, ran, by simpa using pc, args, progress⟩

private def returned (base returnAddress : Word) (call : Call) (state : Snapshot) : Snapshot :=
  { state with
    pc := returnAddress - base
    a0 := 0
    a1 := call.wordSlot call.index.toNat
    a4 := call.length + 1
    a6 := call.data }

private theorem finish (environment : Environment base returnAddress original)
    (header : Header original call) (buffer : Buffer base original call)
    (state : Snapshot) (memory : ByteMemory) (progress : Progress 132 base original call call.index.toNat memory)
    (atFinish : state.pc = 96) (inputs : arguments call state)
    (indexBound : call.index.toNat ≤ call.length.toNat) :
    run 9 (synced base original memory state) =
      some (synced base original (finalMemory call memory) (returned base returnAddress call state)) := by
  -- Substitute the argument registers into the snapshot, so every later
  -- snapshot field and stored value is literally the call's value. Rewriting
  -- one step's statement instead makes its snapshot differ from the goal's.
  obtain ⟨pc, t0, t1, a0, a1, a2, a3, a4, a5, a6, a7⟩ := state
  obtain ⟨argument, index, key, value, length⟩ := inputs
  dsimp only at atFinish argument index key value length
  subst atFinish argument index key value length
  have away := buffer.awayFromCode _ (Nat.le_refl _) indexBound
  let platform := environment.platform memory progress.code
  let half := storeWord memory (call.slot call.index.toNat) call.value.key
  let halfPlatform := environment.platform half
    (storeKeepsCode progress.code (away.narrow (by decide)) _)
  let inserted := environment.platform (insertedMemory call memory)
    (elementKeepsCode progress.code away _)
  let completed := environment.platform (finalMemory call memory)
    (storeKeepsCode (elementKeepsCode progress.code away call.value) buffer.lengthAwayFromCode _)
  refine runStep (step60 platform _ rfl call.data buffer.dataReadable progress.data)
    (runStep (step64 platform _ rfl) (runStep (step68 platform _ rfl)
      (runStep (step6c platform _ rfl) ?_)))
  have effective : call.data + (call.index <<< (3 : Nat)) = call.wordSlot call.index.toNat := by
    simpa only [ofWordNat] using slotAdd buffer 3 rfl indexBound
  dsimp only
  rw [effective]
  have writable : Writable original (call.wordSlot call.index.toNat) ∧
      Writable original (call.wordSlot call.index.toNat + 4) :=
    buffer.writable _ (Nat.le_refl _) indexBound
  have firstStore := step70 platform
    { pc := 112, t0 := t0, t1 := t1, a0 := call.header, a1 := call.wordSlot call.index.toNat,
      a2 := call.value.key, a3 := call.value.value, a4 := call.length + 1, a5 := a5,
      a6 := call.data, a7 := a7 }
    rfl writable.1
  dsimp only at firstStore
  rw [slotNat buffer indexBound] at firstStore
  refine runStep firstStore ?_
  have secondStore := step74 halfPlatform
    { pc := 116, t0 := t0, t1 := t1, a0 := call.header, a1 := call.wordSlot call.index.toNat,
      a2 := call.value.key, a3 := call.value.value, a4 := call.length + 1, a5 := a5,
      a6 := call.data, a7 := a7 }
    rfl writable.2
  dsimp only at secondStore
  rw [slotOffset buffer indexBound (by decide)] at secondStore
  refine runStep secondStore ?_
  have updated := step78 inserted
    { pc := 120, t0 := t0, t1 := t1, a0 := call.header, a1 := call.wordSlot call.index.toNat,
      a2 := call.value.key, a3 := call.value.value, a4 := call.length + 1, a5 := a5,
      a6 := call.data, a7 := a7 }
    rfl buffer.lengthWritable
  dsimp only at updated
  rw [headerOffset header 4 (by decide)] at updated
  exact runStep updated (runStep (step7c completed _ rfl) (runStep (step80 completed _ rfl) rfl))

private theorem success (environment : Environment base returnAddress original)
    (header : Header original call) (buffer : Buffer base original call)
    (initial : Snapshot) (inputs : arguments call (ready call initial))
    (valid : call.valid) :
    ∃ state memory,
      run (call.count - 6) (synced base original original.mem (ready call initial)) =
        some (synced base original (finalMemory call memory) (returned base returnAddress call state)) ∧
      Progress 132 base original call call.index.toNat memory := by
  let start := ready call initial
  obtain ⟨indexBound, spare⟩ := valid
  have lengthValid : ¬ call.capacity.toNat < call.length.toNat := by omega
  have indexValid : ¬ call.length.toNat < call.index.toNat := by omega
  have space : call.length ≠ call.capacity := by
    intro same
    rw [same] at spare
    exact (Nat.lt_irrefl _) spare
  by_cases append : call.index = call.length
  · have progress : Progress 132 base original call call.index.toNat original.mem := by
      rw [append]
      exact initialProgress header buffer
    exact ⟨start, original.mem, by
      simp only [Call.count, lengthValid, space, if_false, append, lt_irrefl, if_true]
      exact finish environment header buffer start original.mem progress
        (by simp [start, ready, append]) inputs indexBound, progress⟩
  · let remaining := call.length.toNat - call.index.toNat
    have remainingEq : call.index.toNat + remaining = call.length.toNat := by dsimp [remaining]; omega
    have nonzero : remaining ≠ 0 := by
      intro zero
      apply append
      exact BitVec.eq_of_toNat_eq (by omega)
    let seed := { start with pc := 64#32, a5 := call.wordSlot call.length.toNat, a6 := call.length }
    have setup : run 4 (synced base original original.mem start) =
        some (synced base original original.mem seed) :=
      setupLoop environment buffer start (by simp [start, ready, append]) inputs
    have initialCopy : Progress 132 base original call (call.index.toNat + remaining) original.mem := by
      rw [remainingEq]
      exact initialProgress header buffer
    obtain ⟨state, memory, copied, exited, args, progress⟩ :=
      copyLoop environment buffer remaining seed original.mem
        ⟨initialCopy, by omega, by simp [seed, nonzero], inputs, by simp [seed, remainingEq],
          by simp [seed, remainingEq]⟩
    have done := finish environment header buffer state memory progress exited args indexBound
    refine ⟨state, memory, ?_, progress⟩
    simp only [Call.count, lengthValid, indexValid, space, append, if_false]
    rw [show 19 + 8 * remaining - 6 = 4 + (8 * remaining + 9) by omega,
      runAdd, setup, Option.bind_some, runAdd, copied, Option.bind_some, done]

private theorem a0Read (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x10 = some state.a0 :=
  readReg_succ.mp (syncRead state (index := 10) (by decide))

-- The same run, ending in a synchronized state: the snapshot's PC, the
-- status in `a0`, and a memory.
theorem rawVecPairInsertSailRun (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (keyArgument : initial.a2 = call.value.key)
    (valueArgument : initial.a3 = call.value.value)
    (environment : Environment base returnAddress original)
    (header : Header original call)
    (buffer : call.valid → Buffer base original call) :
    ∃ (endState : Snapshot) (memory : ByteMemory),
      run call.count original = some (sync base { original with mem := memory } endState) ∧
      endState.pc = returnAddress - base ∧ endState.a0 = call.status ∧
      (¬ call.valid → memory = original.mem) ∧
      (call.valid →
        WordAt memory call.header.toNat call.data ∧
        WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt memory (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          PairAt memory (call.slot index) (call.result index)) ∧
        call.unchanged original.mem memory) := by
  let start := { initial with pc := 0#32 }
  have begins : original = synced base original original.mem start := entry
  have checks := dispatch environment header start rfl headerArgument indexArgument
  by_cases valid : call.valid
  · have goodLength : ¬ call.capacity.toNat < call.length.toNat := by have := valid.2; omega
    have goodIndex : ¬ call.length.toNat < call.index.toNat := by have := valid.1; omega
    have spare : call.length ≠ call.capacity := by
      intro same
      have lt := valid.2
      rw [same] at lt
      exact (Nat.lt_irrefl _) lt
    have enough : 6 ≤ call.count := by
      simp only [Call.count, goodLength, goodIndex, spare, if_false]
      split <;> omega
    have args : arguments call (ready call start) :=
      ⟨headerArgument, indexArgument, keyArgument, valueArgument, rfl⟩
    obtain ⟨state, memory, ran, progress⟩ := success environment header (buffer valid) start args valid
    refine ⟨returned base returnAddress call state, finalMemory call memory, ?_, rfl, ?_, ?_, ?_⟩
    · have checkedRun := checks
      simp only [if_pos valid] at checkedRun
      refine (congrArg (run call.count) begins).trans ?_
      rw [show call.count = 6 + (call.count - 6) by omega, runAdd, checkedRun,
        Option.bind_some, ran]
    · simp [returned, Insert.Call.status, goodLength, goodIndex, spare]
    · intro rejected
      exact (rejected valid).elim
    · intro _
      have words := finalWords (buffer valid) memory progress valid.1
      have newLength : BitVec.ofNat 32 (call.length.toNat + 1) = call.length + 1 := by
        rw [BitVec.ofNat_add, ofWordNat]
        rfl
      rw [newLength]
      exact ⟨words.1, words.2.1, words.2.2.1,
        fun index bound => words.2.2.2.1 index (by omega), words.2.2.2.2⟩
  · simp only [if_neg valid] at checks
    refine ⟨_, original.mem, (congrArg (run call.count) begins).trans checks, rfl, rfl,
      fun _ => rfl, fun accepted => (valid accepted).elim⟩

-- The pointwise output specifies the entire logical sequence of pairs. Bytes
-- outside the one length word and the written suffix, including spare slots
-- after the new length, retain their original values.
theorem rawVecPairInsertSailCorrect (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (keyArgument : initial.a2 = call.value.key)
    (valueArgument : initial.a3 = call.value.value)
    (environment : Environment base returnAddress original)
    (header : Header original call)
    (buffer : call.valid → Buffer base original call) :
    ∃ final, run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = original.mem) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          PairAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged original.mem final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
          .x17],
        final.regs.get? register = original.regs.get? register) := by
  obtain ⟨endState, memory, ran, pc, result, rejected, accepted⟩ :=
    rawVecPairInsertSailRun base returnAddress original call initial entry headerArgument
      indexArgument keyArgument valueArgument environment header buffer
  refine ⟨_, ran, pcReadReturned _ _ _ _ pc, (a0Read _ _ _).trans (congrArg some result),
    ?_, ?_, ?_⟩
  · simpa only [syncMem] using rejected
  · simpa only [syncMem] using accepted
  · intro register outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨pc, next, t0, t1, a0, a1, a2, a3, a4, a5, a6, a7⟩ := outside
    refine syncFrame endState register pc next ?_
    intro index member
    change index ∈ ([5, 6, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 32)) at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Ne.symm t0, Ne.symm t1, Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4,
      Ne.symm a5, Ne.symm a6, Ne.symm a7]

-- The same guarantee with the code mapping derived rather than assumed. The
-- hart runs in machine mode, and the routine's 132 bytes lie in memory that
-- Sail's PMA check lets it fetch. Because every write the routine makes misses
-- the code (`Buffer.awayFromCode`), the fetches stay valid for the whole run.
theorem rawVecPairInsertSailCorrectInMachineMode (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (keyArgument : initial.a2 = call.value.key)
    (valueArgument : initial.a3 = call.value.value)
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
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          PairAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged original.mem final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
          .x17],
        final.regs.get? register = original.regs.get? register) :=
  rawVecPairInsertSailCorrect base returnAddress original call initial entry headerArgument
    indexArgument keyArgument valueArgument (Environment.ofMachine mode image) header buffer

end Run

end Riscfree.RawVec.PairInsert
