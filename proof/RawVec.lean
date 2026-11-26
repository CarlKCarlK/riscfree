import Riscfree.Elf
import RawVec.Instructions

namespace Riscfree.RawVec

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

structure Call where
  header : Word
  index : Word
  value : Word
  length : Word
  capacity : Word
  data : Word
  old : Nat → Word

namespace Call

def slot (call : Call) (index : Nat) : Nat := call.data.toNat + 4 * index

def wordSlot (call : Call) (index : Nat) : Word := BitVec.ofNat 32 (call.slot index)

def valid (call : Call) : Prop :=
  call.index.toNat ≤ call.length.toNat ∧ call.length.toNat < call.capacity.toNat

instance (call : Call) : Decidable call.valid :=
  inferInstanceAs (Decidable (call.index.toNat ≤ call.length.toNat ∧
    call.length.toNat < call.capacity.toNat))

def status (call : Call) : Word :=
  if call.capacity.toNat < call.length.toNat then 3
  else if call.length.toNat < call.index.toNat then 2
  else if call.length = call.capacity then 1
  else 0

def count (call : Call) : Nat :=
  if call.capacity.toNat < call.length.toNat then 5
  else if call.length.toNat < call.index.toNat then 6
  else if call.length = call.capacity then 7
  else if call.index = call.length then 14
  else 18 + 6 * (call.length.toNat - call.index.toNat)

def result (call : Call) (index : Nat) : Word :=
  if index < call.index.toNat then call.old index
  else if index = call.index.toNat then call.value
  else call.old (index - 1)

def outsideHeader (call : Call) (address : Nat) : Prop :=
  address + 4 ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ address

def outsideCode (base : Word) (address : Nat) : Prop :=
  address + 4 ≤ base.toNat ∨ base.toNat + 120 ≤ address

def unchanged (call : Call) (before after : ByteMemory) : Prop :=
  ∀ byte, (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) →
    (byte < call.slot call.index.toNat ∨ call.slot (call.length.toNat + 1) ≤ byte) →
    after[byte]? = before[byte]?

end Call

-- Rejected calls need only the two readable header words used in the checks.
-- A successful call needs access to the live prefix and a single spare slot.
-- Permissions for the rest of the capacity are irrelevant to this routine.
structure Header (original : Machine) (call : Call) : Prop where
  fits : call.header.toNat + 12 ≤ 2 ^ 32
  lengthReadable : Readable original (call.header + 4)
  capacityReadable : Readable original (call.header + 8)
  lengthWord : WordAt original.mem (call.header.toNat + 4) call.length
  capacityWord : WordAt original.mem (call.header.toNat + 8) call.capacity

structure Buffer (base : Word) (original : Machine) (call : Call) : Prop where
  fits : call.slot (call.length.toNat + 1) ≤ 2 ^ 32
  dataReadable : Readable original call.header
  dataWord : WordAt original.mem call.header.toNat call.data
  lengthWritable : Writable original (call.header + 4)
  lengthAwayFromCode : Call.outsideCode base (call.header.toNat + 4)
  live : ∀ index, index < call.length.toNat →
    WordAt original.mem (call.slot index) (call.old index)
  readable : ∀ index, call.index.toNat ≤ index → index < call.length.toNat →
    Readable original (call.wordSlot index)
  writable : ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
    Writable original (call.wordSlot index)
  separated : ∀ index, index ≤ call.length.toNat →
    call.outsideHeader (call.slot index)
  awayFromCode : ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
    Call.outsideCode base (call.slot index)

section Arithmetic

variable {base : Word} {original : Machine} {call : Call}

private theorem ofWordNat (word : Word) : BitVec.ofNat 32 word.toNat = word := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem headerOffset (header : Header original call) (offset : Nat) (bound : offset ≤ 8) :
    (call.header + BitVec.ofNat 32 offset).toNat = call.header.toNat + offset := by
  have fits := header.fits
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

private theorem slotBound (buffer : Buffer base original call) {index : Nat}
    (bound : index ≤ call.length.toNat) : call.slot index < 2 ^ 32 := by
  have fits := buffer.fits
  unfold Call.slot at *
  omega

private theorem slotNat (buffer : Buffer base original call) {index : Nat}
    (bound : index ≤ call.length.toNat) : (call.wordSlot index).toNat = call.slot index := by
  change call.slot index % 2 ^ 32 = call.slot index
  exact Nat.mod_eq_of_lt (slotBound buffer bound)

private theorem slotAdd (buffer : Buffer base original call) {index : Nat}
    (bound : index ≤ call.length.toNat) :
    call.data + (BitVec.ofNat 32 index <<< (2 : Nat)) = call.wordSlot index := by
  have indexFits : index < 2 ^ 32 := by have := call.length.isLt; omega
  have addressFits := slotBound buffer bound
  have offsetFits : index * 2 ^ 2 < 2 ^ 32 := by unfold Call.slot at addressFits; omega
  apply BitVec.eq_of_toNat_eq
  rw [slotNat buffer bound, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt indexFits, Nat.shiftLeft_eq, Nat.mod_eq_of_lt offsetFits,
    Nat.mod_eq_of_lt (by unfold Call.slot at addressFits; omega)]
  unfold Call.slot
  omega

private theorem slotPrev (call : Call) (index : Nat) :
    call.wordSlot (index + 1) + 0xfffffffc#32 = call.wordSlot index := by
  have increment : call.slot (index + 1) = call.slot index + 4 := by simp [Call.slot]; omega
  rw [Call.wordSlot, Call.wordSlot, increment, BitVec.ofNat_add, BitVec.add_assoc]
  exact BitVec.add_zero _

private theorem counterPrev (index : Nat) :
    BitVec.ofNat 32 (index + 1) + 0xffffffff#32 = BitVec.ofNat 32 index := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  exact BitVec.add_zero _

private theorem storeKeepsCode {memory : ByteMemory}
    (agrees : CodeAgrees base original.mem memory) {address : Nat}
    (apart : Call.outsideCode base address) (value : Word) :
    CodeAgrees base original.mem (storeWord memory address value) := by
  intro byte low high
  rw [storeWordOutside _ _ _ _ (by unfold Call.outsideCode at apart; omega)]
  exact agrees byte low high

end Arithmetic

section Run

variable {base returnAddress : Word} {original : Machine} {call : Call}

private abbrev synced (base : Word) (original : Machine) (memory : ByteMemory)
    (state : Snapshot) : Machine := sync base {original with mem := memory} state

private def ready (call : Call) (state : Snapshot) : Snapshot :=
  { state with
    pc := if call.index = call.length then 88 else 48
    a3 := call.length
    a4 := call.capacity }

private theorem dispatch (environment : Environment base returnAddress original)
    (header : Header original call) (state : Snapshot) (atEntry : state.pc = 0)
    (argument : state.a0 = call.header) (index : state.a1 = call.index) :
    let final := if call.valid then ready call state else
      { state with
        pc := returnAddress - base
        a0 := call.status
        a3 := call.length
        a4 := call.capacity }
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
  · have notValid : ¬ call.valid := fun valid =>
      (Nat.not_lt_of_ge (Nat.le_of_lt valid.2)) badLength
    simp only [notValid, if_false, Call.count, Call.status, if_pos badLength]
    refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
    have branch : ¬ call.length.toNat ≤ call.capacity.toNat := by omega
    simp only [branch, if_false]
    exact runStep (step0c platform _ rfl) (runStep (step10 platform _ rfl) rfl)
  · have lengthValid : call.length.toNat ≤ call.capacity.toNat := by omega
    by_cases badIndex : call.length.toNat < call.index.toNat
    · have notValid : ¬ call.valid := fun valid => Nat.not_lt_of_ge valid.1 badIndex
      simp only [notValid, if_false, Call.count, Call.status, if_neg badLength, if_pos badIndex]
      refine runStep first (runStep second (runStep (step08 platform _ rfl) ?_))
      simp only [if_pos lengthValid]
      refine runStep (step14 platform _ rfl) ?_
      have branch : ¬ call.index.toNat ≤ call.length.toNat := by omega
      simp only [index, branch, if_false]
      exact runStep (step18 platform _ rfl) (runStep (step1c platform _ rfl) rfl)
    · have indexValid : call.index.toNat ≤ call.length.toNat := by omega
      by_cases full : call.length = call.capacity
      · have notValid : ¬ call.valid := by intro valid; simpa [full] using valid.2
        simp only [notValid, if_false, Call.count, Call.status, if_neg badLength, if_neg badIndex,
          if_pos full]
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
  state.a0 = call.header ∧ state.a1 = call.index ∧ state.a2 = call.value ∧ state.a3 = call.length

private structure Progress (base : Word) (original : Machine) (call : Call)
    (current : Nat) (memory : ByteMemory) : Prop where
  code : CodeAgrees base original.mem memory
  data : WordAt memory call.header.toNat call.data
  capacity : WordAt memory (call.header.toNat + 8) call.capacity
  shifted : ∀ index, current < index → index ≤ call.length.toNat →
    WordAt memory (call.slot index) (call.old (index - 1))
  outside : ∀ byte, byte < call.slot (current + 1) ∨ call.slot (call.length.toNat + 1) ≤ byte →
    memory[byte]? = original.mem[byte]?

private theorem initialProgress (header : Header original call) (buffer : Buffer base original call) :
    Progress base original call call.length.toNat original.mem :=
  ⟨fun _ _ _ => rfl, buffer.dataWord, header.capacityWord,
    fun _ greater less => (Nat.not_lt_of_ge less greater).elim, fun _ _ => rfl⟩

private theorem Progress.source {memory : ByteMemory} {current index : Nat}
    (progress : Progress base original call current memory)
    (buffer : Buffer base original call) (before : index ≤ current)
    (live : index < call.length.toNat) :
    WordAt memory (call.slot index) (call.old index) := by
  intro byte
  rw [progress.outside _ (Or.inl (by unfold Call.slot; have := byte.isLt; omega))]
  exact buffer.live index live byte

private theorem Progress.copy {memory : ByteMemory} {index : Nat}
    (progress : Progress base original call (index + 1) memory)
    (buffer : Buffer base original call)
    (afterIndex : call.index.toNat ≤ index) (live : index < call.length.toNat) :
    Progress base original call index (storeWord memory (call.slot (index + 1)) (call.old index)) := by
  constructor
  · exact storeKeepsCode progress.code (buffer.awayFromCode _ (by omega) (by omega)) _
  · apply progress.data.storeOther
    have apart := buffer.separated (index + 1) (by omega)
    unfold Call.outsideHeader at apart
    omega
  · apply progress.capacity.storeOther
    have apart := buffer.separated (index + 1) (by omega)
    unfold Call.outsideHeader at apart
    omega
  · intro observed afterCurrent inBounds
    by_cases same : observed = index + 1
    · subst observed
      simpa only [Nat.add_sub_cancel] using wordAtStore memory (call.slot (index + 1)) (call.old index)
    · apply (progress.shifted observed (by omega) inBounds).storeOther
      unfold Call.slot
      omega
  · intro byte outside
    have apart : byte < call.slot (index + 1) ∨ call.slot (index + 1) + 4 ≤ byte := by
      unfold Call.slot at *
      omega
    rw [storeWordOutside _ _ _ _ apart]
    apply progress.outside
    unfold Call.slot at *
    omega

private theorem setupLoop (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (state : Snapshot) (atSetup : state.pc = 48)
    (inputs : arguments call state) :
    run 4 (synced base original original.mem state) =
      some (synced base original original.mem
        { state with pc := 64, a4 := call.wordSlot call.length.toNat, a5 := call.length }) := by
  let platform := environment.platform original.mem (fun _ _ _ => rfl)
  obtain ⟨header, _, _, length⟩ := inputs
  have read : Readable original state.a0 := header ▸ buffer.dataReadable
  have contents : WordAt original.mem state.a0.toNat call.data := header ▸ buffer.dataWord
  refine runStep (step30 platform state atSetup call.data read contents)
    (runStep (step34 platform _ rfl) (runStep (step38 platform _ rfl)
      (runStep (step3c platform _ rfl) ?_)))
  have effective : call.data + (call.length <<< (2 : Nat)) = call.wordSlot call.length.toNat := by
    simpa only [ofWordNat] using slotAdd buffer (index := call.length.toNat) (Nat.le_refl _)
  simp only [run, effective, length]
  rfl

private def afterCopy (call : Call) (state : Snapshot) (index : Nat) : Snapshot :=
  { state with
    pc := if call.index.toNat < index then 64 else 88
    a4 := call.wordSlot index
    a5 := BitVec.ofNat 32 index
    a6 := call.old index
    a7 := call.wordSlot index }

private theorem oneCopy (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (state : Snapshot) {memory : ByteMemory} (index : Nat)
    (progress : Progress base original call (index + 1) memory)
    (atLoop : state.pc = 64) (inputs : arguments call state)
    (pointer : state.a4 = call.wordSlot (index + 1))
    (counter : state.a5 = BitVec.ofNat 32 (index + 1))
    (above : call.index.toNat ≤ index) (live : index < call.length.toNat) :
    run 6 (synced base original memory state) =
      some (synced base original (storeWord memory (call.slot (index + 1)) (call.old index))
        (afterCopy call state index)) := by
  let platform := environment.platform memory progress.code
  let updated := storeWord memory (call.slot (index + 1)) (call.old index)
  have copied := progress.copy buffer above live
  let nextPlatform := environment.platform updated copied.code
  have source : state.a4 + 0xfffffffc#32 = call.wordSlot index := by
    rw [pointer, slotPrev]
  have read : Readable original (state.a4 + 0xfffffffc#32) :=
    source ▸ buffer.readable index above live
  have contents : WordAt memory (state.a4 + 0xfffffffc#32).toNat (call.old index) := by
    rw [source, slotNat buffer (by omega)]
    exact progress.source buffer (by omega) live
  have write : Writable original state.a4 := pointer ▸ buffer.writable (index + 1) (by omega) (by omega)
  have address : state.a4.toNat = call.slot (index + 1) := by
    rw [pointer, slotNat buffer (by omega)]
  have first := step40 platform state atLoop (call.old index) read contents
  refine runStep first (runStep (step44 platform _ rfl) (runStep (step48 platform _ rfl) ?_))
  have stored := step4c platform
    { state with
      pc := 76
      a6 := call.old index
      a5 := state.a5 + 0xffffffff#32
      a7 := state.a4 + 0xfffffffc#32 } rfl write
  rw [address] at stored
  refine runStep stored (runStep (step50 nextPlatform _ rfl) (runStep (step54 nextPlatform _ rfl) ?_))
  have fits : index < 2 ^ 32 := by have := call.length.isLt; omega
  simp only [run, afterCopy, source, counter, counterPrev, inputs.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits]
  rfl

private theorem copyLoop (environment : Environment base returnAddress original)
    (buffer : Buffer base original call) (remaining : Nat) (state : Snapshot) (memory : ByteMemory)
    (bound : call.index.toNat + remaining ≤ call.length.toNat)
    (progress : Progress base original call (call.index.toNat + remaining) memory)
    (pc : state.pc = if remaining = 0 then 88 else 64)
    (inputs : arguments call state)
    (pointer : state.a4 = call.wordSlot (call.index.toNat + remaining))
    (counter : state.a5 = BitVec.ofNat 32 (call.index.toNat + remaining)) :
    ∃ final out, run (6 * remaining) (synced base original memory state) =
      some (synced base original out final) ∧
      final.pc = 88 ∧ arguments call final ∧ Progress base original call call.index.toNat out := by
  induction remaining generalizing state memory with
  | zero =>
    exact ⟨state, memory, rfl, pc, inputs, progress⟩
  | succ remaining previous =>
    let index := call.index.toNat + remaining
    have copied := progress.copy buffer (index := index) (by dsimp [index]; omega)
      (by dsimp [index]; omega)
    have stepped := oneCopy environment buffer state index progress (by simpa using pc)
      inputs pointer counter (by dsimp [index]; omega) (by dsimp [index]; omega)
    have nextPc : (afterCopy call state index).pc = if remaining = 0 then 88 else 64 := by
      by_cases empty : remaining = 0
      · simp [afterCopy, index, empty]
      · have less : call.index.toNat < index := by dsimp [index]; omega
        simp [afterCopy, less, empty]
    obtain ⟨final, out, rest, exit, args, contents⟩ :=
      previous _ _ (by omega) copied nextPc inputs rfl rfl
    refine ⟨final, out, ?_, exit, args, contents⟩
    rw [show 6 * (remaining + 1) = 6 + 6 * remaining by omega, runAdd, stepped,
      Option.bind_some, rest]

private def insertedMemory (call : Call) (memory : ByteMemory) : ByteMemory :=
  storeWord memory (call.slot call.index.toNat) call.value

private def finalMemory (call : Call) (memory : ByteMemory) : ByteMemory :=
  storeWord (insertedMemory call memory) (call.header.toNat + 4) (call.length + 1)

private def returned (base returnAddress : Word) (call : Call) (state : Snapshot) : Snapshot :=
  { state with
    pc := returnAddress - base
    a0 := 0
    a1 := call.wordSlot call.index.toNat
    a3 := call.length + 1
    a5 := call.data }

set_option maxHeartbeats 1500000 in
private theorem finish (environment : Environment base returnAddress original)
    (header : Header original call) (buffer : Buffer base original call)
    (state : Snapshot) (memory : ByteMemory) (progress : Progress base original call call.index.toNat memory)
    (atFinish : state.pc = 88) (inputs : arguments call state)
    (indexBound : call.index.toNat ≤ call.length.toNat) :
    run 8 (synced base original memory state) =
      some (synced base original (finalMemory call memory) (returned base returnAddress call state)) := by
  let platform := environment.platform memory progress.code
  let inserted := environment.platform (insertedMemory call memory)
    (storeKeepsCode progress.code (buffer.awayFromCode _ (Nat.le_refl _) indexBound) _)
  let completed := environment.platform (finalMemory call memory)
    (storeKeepsCode (storeKeepsCode progress.code
      (buffer.awayFromCode _ (Nat.le_refl _) indexBound) call.value) buffer.lengthAwayFromCode _)
  obtain ⟨argument, index, value, length⟩ := inputs
  have read : Readable original state.a0 := argument ▸ buffer.dataReadable
  have contents : WordAt memory state.a0.toNat call.data := argument ▸ progress.data
  refine runStep (step58 platform state atFinish call.data read contents)
    (runStep (step5c platform _ rfl) (runStep (step60 platform _ rfl)
      (runStep (step64 platform _ rfl) ?_)))
  have effective : call.data + (state.a1 <<< (2 : Nat)) = call.wordSlot call.index.toNat := by
    rw [index]
    simpa only [ofWordNat] using slotAdd buffer indexBound
  rw [effective, length]
  have stored := step68 platform
    { state with
      pc := 104
      a1 := call.wordSlot call.index.toNat
      a3 := call.length + 1
      a5 := call.data } rfl (buffer.writable _ (Nat.le_refl _) indexBound)
  rw [slotNat buffer indexBound, value] at stored
  refine runStep stored ?_
  have lengthWrite : Writable original (state.a0 + 4) := argument ▸ buffer.lengthWritable
  have updated := step6c inserted
    { state with
      pc := 108
      a1 := call.wordSlot call.index.toNat
      a3 := call.length + 1
      a5 := call.data } rfl lengthWrite
  have address : (state.a0 + 4).toNat = call.header.toNat + 4 := by
    rw [argument]
    exact headerOffset header 4 (by decide)
  rw [address] at updated
  exact runStep updated (runStep (step70 completed _ rfl) (runStep (step74 completed _ rfl) rfl))

private theorem finalWords (buffer : Buffer base original call)
    (memory : ByteMemory) (progress : Progress base original call call.index.toNat memory)
    (indexBound : call.index.toNat ≤ call.length.toNat) :
    WordAt (finalMemory call memory) call.header.toNat call.data ∧
    WordAt (finalMemory call memory) (call.header.toNat + 4) (call.length + 1) ∧
    WordAt (finalMemory call memory) (call.header.toNat + 8) call.capacity ∧
    (∀ index, index ≤ call.length.toNat →
      WordAt (finalMemory call memory) (call.slot index) (call.result index)) ∧
    call.unchanged original.mem (finalMemory call memory) := by
  have indexApart := buffer.separated call.index.toNat indexBound
  refine ⟨?_, wordAtStore _ _ _, ?_, ?_, ?_⟩
  · apply (progress.data.storeOther ?_).storeOther (Or.inl (by omega))
    unfold Call.outsideHeader at indexApart
    omega
  · apply (progress.capacity.storeOther ?_).storeOther (Or.inr (by omega))
    unfold Call.outsideHeader at indexApart
    omega
  · intro index bound
    apply WordAt.storeOther
    · by_cases before : index < call.index.toNat
      · rw [Call.result, if_pos before]
        apply (progress.source buffer (by omega) (by omega)).storeOther
        left
        unfold Call.slot
        omega
      · by_cases same : index = call.index.toNat
        · subst index
          simpa only [Call.result, lt_irrefl, if_false, if_true] using
            wordAtStore memory (call.slot call.index.toNat) call.value
        · rw [Call.result, if_neg before, if_neg same]
          apply (progress.shifted index (by omega) bound).storeOther
          right
          unfold Call.slot
          omega
    · have apart := buffer.separated index bound
      unfold Call.outsideHeader at apart
      omega
  · intro byte outsideLength outsideData
    unfold finalMemory insertedMemory
    rw [storeWordOutside _ _ _ _ (by omega), storeWordOutside _ _ _ _ ?_]
    · apply progress.outside
      unfold Call.slot at *
      omega
    · unfold Call.slot at *
      omega

private theorem success (environment : Environment base returnAddress original)
    (header : Header original call) (buffer : Buffer base original call)
    (initial : Snapshot) (inputs : arguments call (ready call initial))
    (valid : call.valid) :
    ∃ state memory,
      run (call.count - 6) (synced base original original.mem (ready call initial)) =
        some (synced base original (finalMemory call memory) (returned base returnAddress call state)) ∧
      Progress base original call call.index.toNat memory := by
  let start := ready call initial
  obtain ⟨indexBound, spare⟩ := valid
  have lengthValid : ¬ call.capacity.toNat < call.length.toNat := by omega
  have indexValid : ¬ call.length.toNat < call.index.toNat := by omega
  have space : call.length ≠ call.capacity := by
    intro same
    rw [same] at spare
    exact (Nat.lt_irrefl _) spare
  by_cases append : call.index = call.length
  · have progress : Progress base original call call.index.toNat original.mem := by
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
    let seed := { start with pc := 64#32, a4 := call.wordSlot call.length.toNat, a5 := call.length }
    have setup : run 4 (synced base original original.mem start) =
        some (synced base original original.mem seed) :=
      setupLoop environment buffer start (by simp [start, ready, append]) inputs
    have initialCopy : Progress base original call (call.index.toNat + remaining) original.mem := by
      rw [remainingEq]
      exact initialProgress header buffer
    obtain ⟨state, memory, copied, exited, args, progress⟩ :=
      copyLoop environment buffer remaining seed original.mem (by omega) initialCopy
        (by simp [seed, nonzero]) inputs (by simp [seed, remainingEq])
        (by simp [seed, remainingEq])
    have done := finish environment header buffer state memory progress exited args indexBound
    refine ⟨state, memory, ?_, progress⟩
    simp only [Call.count, lengthValid, indexValid, space, append, if_false]
    rw [show 18 + 6 * remaining - 6 = 4 + (6 * remaining + 8) by omega,
      runAdd, setup, Option.bind_some, runAdd, copied, Option.bind_some, done]

private theorem pcReadReturned (base returnAddress : Word) (frame : Machine) (state : Snapshot)
    (pc : state.pc = returnAddress - base) :
    (sync base frame state).regs.get? Register.PC = some returnAddress := by
  have read := syncReadPC (base := base) (frame := frame) state
  rw [viewPc, pc, BitVec.add_comm, BitVec.sub_add_cancel] at read
  exact readReg_succ.mp read

private theorem a0Read (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x10 = some state.a0 :=
  readReg_succ.mp (syncRead state (index := 10) (by decide))

-- The pointwise output specifies the entire logical sequence. Bytes outside
-- the one length word and the written suffix, including spare slots after the
-- new length, retain their original values.
theorem rawVecU32InsertSailCorrect (base returnAddress : Word) (original : Machine)
    (call : Call) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
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
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged original.mem final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register) := by
  let start := { initial with pc := 0#32 }
  have begins : original = synced base original original.mem start := entry
  have checks := dispatch environment header start rfl headerArgument indexArgument
  suffices ∃ endState memory,
      run call.count original = some (synced base original memory endState) ∧
      endState.pc = returnAddress - base ∧ endState.a0 = call.status ∧
      (¬ call.valid → memory = original.mem) ∧
      (call.valid →
        WordAt memory call.header.toNat call.data ∧
        WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt memory (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt memory (call.slot index) (call.result index)) ∧
        call.unchanged original.mem memory) by
    obtain ⟨endState, memory, ran, pc, result, rejected, accepted⟩ := this
    refine ⟨_, ran, pcReadReturned _ _ _ _ pc, (a0Read _ _ _).trans (congrArg some result),
      ?_, ?_, ?_⟩
    · simpa only [syncMem] using rejected
    · simpa only [syncMem] using accepted
    · intro register outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      obtain ⟨pc, next, a0, a1, a2, a3, a4, a5, a6, a7⟩ := outside
      refine syncFrame endState register pc next ?_
      intro index member
      change index ∈ ([10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 32)) at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5,
        Ne.symm a6, Ne.symm a7]
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
      ⟨headerArgument, indexArgument, valueArgument, rfl⟩
    obtain ⟨state, memory, ran, progress⟩ := success environment header (buffer valid) start args valid
    refine ⟨returned base returnAddress call state, finalMemory call memory, ?_, rfl, ?_, ?_, ?_⟩
    · have checkedRun := checks
      simp only [if_pos valid] at checkedRun
      refine (congrArg (run call.count) begins).trans ?_
      rw [show call.count = 6 + (call.count - 6) by omega, runAdd, checkedRun,
        Option.bind_some, ran]
    · simp [returned, Call.status, goodLength, goodIndex, spare]
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

#print axioms rawVecU32InsertSailCorrect

end Run

def verifyElf (path : String) : IO Unit :=
  Riscfree.verifyElf path "raw_vec_u32_insert" (instructions.map Prod.fst)

end Riscfree.RawVec
