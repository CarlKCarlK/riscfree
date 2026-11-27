import SortedMap.Insert.Instructions
import SortedMap.Search.Correct
import RawVec.PairInsert
import SortedMap.Entries

/-! # Compose the sorted-map insertion with the verified search and vector insertion. -/

namespace Riscfree.SortedMap.Insert

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

structure Call where
  header : Word
  value : Pair
  length : Word
  capacity : Word
  data : Word
  old : Nat → Pair

namespace Call

def search (call : Call) : Search.Call := ⟨call.header, call.value.key, call.length, call.data, call.old⟩

def position (call : Call) : Nat := call.search.result .lower

def lengthValid (call : Call) : Prop := call.length.toNat ≤ call.capacity.toNat

def replaces (call : Call) : Prop :=
  call.lengthValid ∧ call.position < call.length.toNat ∧
    (call.old call.position).key = call.value.key

instance (call : Call) : Decidable call.lengthValid := inferInstanceAs (Decidable (_ ≤ _))
instance (call : Call) : Decidable call.replaces := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def vector (call : Call) : PairInsert.Call :=
  ⟨call.header, BitVec.ofNat 32 call.position, call.value, call.length, call.capacity, call.data, call.old⟩

def status (call : Call) : Word :=
  if ¬ call.lengthValid then 3 else if call.replaces then 4 else call.vector.status

def count (call : Call) : Nat :=
  if ¬ call.lengthValid then 18
  else if call.replaces then 32 + call.search.count .lower
  else (if call.position < call.length.toNat then 32 else 27) +
    call.search.count .lower + call.vector.count

theorem position_le (call : Call) : call.position ≤ call.length.toNat := call.search.result_le .lower

theorem vectorIndex (call : Call) : call.vector.index.toNat = call.position := by
  have := call.position_le
  have := call.length.isLt
  simp only [vector, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem slotSame (call : Call) (index : Nat) : call.vector.slot index = call.search.slot index := by
  simp [RawVec.Insert.Call.slot, Search.Call.slot, vector, search, pairBytes]

end Call

def searchBase (base : Word) : Word := base + searchOffset
def vectorBase (base : Word) : Word := base + vectorOffset

-- The 32-byte frame below the caller's `sp`.
def frameBase (sp : Word) : Word := sp + 0xffffffe0#32

structure Environment (base returnAddress : Word) (original : Machine) : Prop where
  mode : MachineMode original returnAddress
  code : CodeImage instructions base original
  searchCode : CodeImage (Search.instructions .lower) (searchBase base) original
  vectorCode : CodeImage PairInsert.instructions (vectorBase base) original

-- A byte range of `width` bytes at `address` misses the frame below `sp`.
def outsideFrame (sp : Word) (address width : Nat) : Prop :=
  address + width ≤ sp.toNat - 32 ∨ sp.toNat ≤ address

structure Stack (base : Word) (original : Machine) (call : Call) (sp : Word) : Prop where
  fits : 32 ≤ sp.toNat
  readable : ∀ offset ∈ [12, 16, 20, 24, 28], Readable original (frameBase sp + BitVec.ofNat 32 offset)
  writable : ∀ offset ∈ [12, 16, 20, 24, 28], Writable original (frameBase sp + BitVec.ofNat 32 offset)
  apartHeader : outsideFrame sp call.header.toNat 12
  apartEntries : ∀ index < call.length.toNat, outsideFrame sp (call.search.slot index) 8
  apartSpare : call.vector.valid → outsideFrame sp (call.search.slot call.length.toNat) 8
  apartCode : outsideFrame sp base.toNat 176
  apartSearch : outsideFrame sp (searchBase base).toNat 52
  apartVector : outsideFrame sp (vectorBase base).toNat 132

-- Partial stacks mirror the successive stores in the prologue.
private def push (sp : Word) (offset : Word) (value : Word) (memory : ByteMemory) : ByteMemory :=
  storeWord memory (frameBase sp + offset).toNat value

def pushed (memory : ByteMemory) (sp : Word) (state : Snapshot) : ByteMemory :=
  memory |> push sp 28 state.ra |> push sp 24 state.s0 |> push sp 20 state.s1
    |> push sp 16 state.s2 |> push sp 12 state.s3

section Frame

variable {sp : Word}

theorem frameAddress (fits : 32 ≤ sp.toNat) (offset : Word) (small : offset.toNat ≤ 28) :
    (frameBase sp + offset).toNat = sp.toNat - 32 + offset.toNat := by
  have below := sp.isLt
  have le : 32#32 ≤ sp := BitVec.le_def.mpr fits
  have lowered : frameBase sp = sp - 32#32 := by
    rw [frameBase, BitVec.sub_eq_add_neg]
    rfl
  rw [lowered, BitVec.toNat_add, BitVec.toNat_sub_of_le le]
  change (sp.toNat - 32 + offset.toNat) % 2 ^ 32 = _
  exact Nat.mod_eq_of_lt (by omega)

private theorem pushOutside (memory : ByteMemory) (offset value : Word) (fits : 32 ≤ sp.toNat)
    (small : offset.toNat ≤ 28) (byte : Nat) (outside : byte < sp.toNat - 32 ∨ sp.toNat ≤ byte) :
    (push sp offset value memory)[byte]? = memory[byte]? := by
  apply storeWordOutside
  rw [frameAddress fits offset small]
  omega

theorem pushedOutside (memory : ByteMemory) (state : Snapshot) (fits : 32 ≤ sp.toNat) (byte : Nat)
    (outside : byte < sp.toNat - 32 ∨ sp.toNat ≤ byte) :
    (pushed memory sp state)[byte]? = memory[byte]? := by
  unfold pushed
  iterate 5 rw [pushOutside _ _ _ fits (by decide) _ outside]

theorem pushedWord {memory : ByteMemory} {address : Nat} {value : Word} (state : Snapshot)
    (fits : 32 ≤ sp.toNat) (word : WordAt memory address value) (apart : outsideFrame sp address 4) :
    WordAt (pushed memory sp state) address value := by
  intro byte
  rw [pushedOutside _ _ fits _ (by unfold outsideFrame at apart; have := byte.isLt; omega)]
  exact word byte

private theorem pushWord {memory : ByteMemory} {offset other value written : Word}
    (fits : 32 ≤ sp.toNat) (offsetSmall : offset.toNat ≤ 28) (otherSmall : other.toNat ≤ 28)
    (apart : other.toNat + 4 ≤ offset.toNat)
    (word : WordAt memory (frameBase sp + offset).toNat value) :
    WordAt (push sp other written memory) (frameBase sp + offset).toNat value := by
  exact word.storeOther (by
    rw [frameAddress fits _ offsetSmall, frameAddress fits _ otherSmall]
    omega)

private theorem savedWords (memory : ByteMemory) (state : Snapshot) (fits : 32 ≤ sp.toNat) :
    WordAt (pushed memory sp state) (frameBase sp + 28#32).toNat state.ra ∧
      WordAt (pushed memory sp state) (frameBase sp + 24#32).toNat state.s0 ∧
      WordAt (pushed memory sp state) (frameBase sp + 20#32).toNat state.s1 ∧
      WordAt (pushed memory sp state) (frameBase sp + 16#32).toNat state.s2 ∧
      WordAt (pushed memory sp state) (frameBase sp + 12#32).toNat state.s3 := by
  unfold pushed
  refine ⟨?_, ?_, ?_, ?_, wordAtStore _ _ _⟩
  · iterate 4 refine pushWord fits (by decide) (by decide) (by decide) ?_
    exact wordAtStore _ _ _
  · iterate 3 refine pushWord fits (by decide) (by decide) (by decide) ?_
    exact wordAtStore _ _ _
  · iterate 2 refine pushWord fits (by decide) (by decide) (by decide) ?_
    exact wordAtStore _ _ _
  · exact pushWord fits (by decide) (by decide) (by decide) (wordAtStore _ _ _)

private theorem restoredSp : frameBase sp + 32#32 = sp := by
  unfold frameBase
  rw [offsetAdd sp _ _ 0#32 rfl, BitVec.add_zero]

end Frame

/-! ## The run -/

section Run

variable {base returnAddress : Word} {original : Machine} {call : Call}

private theorem mappedTransfer {frame other : Machine} {address : Word}
    {permission : PMA_Region → Prop} (mapped : RawVec.Mapped frame address permission)
    (regions : other.regs.get? Register.pma_regions = frame.regs.get? Register.pma_regions) :
    RawVec.Mapped other address permission := by
  obtain ⟨aligned, found, region, regionsRead, matched, allowed⟩ := mapped
  have stored : frame.regs.get? Register.pma_regions = some found := readReg_succ.mp regionsRead
  exact ⟨aligned, found, region, readReg_succ.mpr (regions.trans stored), matched, allowed⟩

-- Each code image survives any memory change confined to the frame.
private theorem imageAt {sp : Word} (environment : Environment base returnAddress original)
    (stack : Stack base original call sp) (memory : ByteMemory)
    (agrees : ∀ byte, byte < sp.toNat - 32 ∨ sp.toNat ≤ byte → memory[byte]? = original.mem[byte]?) :
    CodeImage instructions base { original with mem := memory } :=
  environment.code.withMemory memory fun byte low high => by
    have apart := stack.apartCode
    unfold outsideFrame at apart
    change byte < base.toNat + 4 * 44 at high
    exact agrees byte (by omega)

private def saved (initial : Snapshot) : Snapshot :=
  { initial with pc := 0x18#32, sp := frameBase initial.sp }

private theorem prologue (environment : Environment base returnAddress original)
    (initial : Snapshot) (stack : Stack base original call initial.sp) :
    run 6 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := pushed original.mem initial.sp initial } (saved initial)) := by
  have machine := environment.mode.toMachineState
  have image (memory : ByteMemory) (agrees : ∀ byte, byte < initial.sp.toNat - 32 ∨
      initial.sp.toNat ≤ byte → memory[byte]? = original.mem[byte]?) :=
    imageAt environment stack memory agrees
  refine runStep (step00 machine (image original.mem fun _ _ => rfl) _ rfl) ?_
  refine runStep (step04 machine (image original.mem fun _ _ => rfl) _ rfl
    (stack.writable 28 (by decide))) ?_
  refine runStep (step08 machine (image _ ?_) _ rfl (stack.writable 24 (by decide))) ?_
  · intro byte outside
    exact pushOutside _ _ _ stack.fits (by decide) _ outside
  refine runStep (step0c machine (image _ ?_) _ rfl (stack.writable 20 (by decide))) ?_
  · intro byte outside
    change (push initial.sp 24 initial.s0 (push initial.sp 28 initial.ra original.mem))[byte]? = _
    iterate 2 rw [pushOutside _ _ _ stack.fits (by decide) _ outside]
  refine runStep (step10 machine (image _ ?_) _ rfl (stack.writable 16 (by decide))) ?_
  · intro byte outside
    change (push initial.sp 20 initial.s1 (push initial.sp 24 initial.s0
      (push initial.sp 28 initial.ra original.mem)))[byte]? = _
    iterate 3 rw [pushOutside _ _ _ stack.fits (by decide) _ outside]
  refine runStep (step14 machine (image _ ?_) _ rfl (stack.writable 12 (by decide))) rfl
  intro byte outside
  change (push initial.sp 16 initial.s2 (push initial.sp 20 initial.s1
    (push initial.sp 24 initial.s0 (push initial.sp 28 initial.ra original.mem))))[byte]? = _
  iterate 4 rw [pushOutside _ _ _ stack.fits (by decide) _ outside]

private def restored (initial state : Snapshot) : Snapshot :=
  { state with
    ra := initial.ra, s0 := initial.s0, s1 := initial.s1, s2 := initial.s2,
    s3 := initial.s3, sp := initial.sp }

-- Both paths that return directly use the same epilogue. A replacement
-- preserves its code bytes and the five saved words.
private theorem epilogue (environment : Environment base returnAddress original)
    (initial : Snapshot) (stack : Stack base original call initial.sp)
    (returnArgument : initial.ra = returnAddress) (state : Snapshot)
    (atEpilogue : state.pc = 0x2c#32) (lowered : state.sp = frameBase initial.sp)
    (memory : ByteMemory) (image : CodeImage instructions base { original with mem := memory })
    (savedWord : ∀ (offset : Word) (value : Word),
      WordAt (pushed original.mem initial.sp initial) (frameBase initial.sp + offset).toNat value →
      offset ∈ [12, 16, 20, 24, 28] →
      WordAt memory (frameBase initial.sp + offset).toNat value) :
    run 7 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        { restored initial state with pc := returnAddress - base }) := by
  have machine := environment.mode.toMachineState
  obtain ⟨ra, s0, s1, s2, s3⟩ := savedWords original.mem initial stack.fits
  refine runStep (step2c machine image state atEpilogue _
    (lowered ▸ stack.readable 28 (by decide)) (lowered ▸ savedWord 28 _ ra (by decide))) ?_
  refine runStep (step30 machine image _ rfl _
    (lowered ▸ stack.readable 24 (by decide)) (lowered ▸ savedWord 24 _ s0 (by decide))) ?_
  refine runStep (step34 machine image _ rfl _
    (lowered ▸ stack.readable 20 (by decide)) (lowered ▸ savedWord 20 _ s1 (by decide))) ?_
  refine runStep (step38 machine image _ rfl _
    (lowered ▸ stack.readable 16 (by decide)) (lowered ▸ savedWord 16 _ s2 (by decide))) ?_
  refine runStep (step3c machine image _ rfl _
    (lowered ▸ stack.readable 12 (by decide)) (lowered ▸ savedWord 12 _ s3 (by decide))) ?_
  refine runStep (step40 machine image _ rfl) ?_
  refine runStep (step44 machine image _ rfl returnAddress returnArgument
    environment.mode.returnLow environment.mode.returnNext) ?_
  simp only [restored, lowered, restoredSp]
  rfl

-- The search's snapshot, from the routine's argument registers.
private def searchEntry (state : Snapshot) : Search.Snapshot :=
  { a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4 }

private def afterSearch (state : Snapshot) (endState : Search.Snapshot) : Snapshot :=
  { state with
    pc := 0x58#32, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2, a3 := endState.a3,
    a4 := endState.a4 }

private theorem searchInside : ∀ index ∈ tracked Search.Snapshot, index ∈ tracked Snapshot := by
  decide

-- From `0x48`, the call to `sorted_map_lower_bound` and its return.
private theorem searchCall (environment : Environment base returnAddress original)
    (initial : Snapshot) (stack : Stack base original call initial.sp)
    (header : RawVec.Insert.Header original call.vector)
    (keys : 0 < call.length.toNat → Search.Keys original call.search)
    (state : Snapshot) (atCall : state.pc = 0x48#32) (headerArgument : state.a0 = call.header)
    (keyArgument : state.a1 = call.value.key) :
    ∃ endState : Search.Snapshot,
      run (4 + call.search.count .lower)
          (sync base { original with mem := pushed original.mem initial.sp initial } state) =
        some (sync base { original with mem := pushed original.mem initial.sp initial }
          (afterSearch { state with s1 := state.a1, s2 := state.a0, ra := base + 0x58#32 } endState)) ∧
      endState.a0 = BitVec.ofNat 32 call.position := by
  let memory := pushed original.mem initial.sp initial
  have machine := environment.mode.toMachineState
  have fits := stack.fits
  have image := imageAt environment stack _ (pushedOutside original.mem initial fits)
  let called : Snapshot :=
    { state with pc := searchOffset, s1 := state.a1, s2 := state.a0, ra := base + 0x58#32 }
  have entering : run 4 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } called) :=
    runStep (step48 machine image _ atCall) (runStep (step4c machine image _ rfl)
      (runStep (step50 machine image _ rfl) (runStep (step54 machine image _ rfl rfl) rfl)))
  let entered := sync base { original with mem := memory } called
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame called _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have enteredMem : entered.mem = memory := syncMem called
  have routineEntered : entered = sync (searchBase base) entered { searchEntry called with pc := 0 } :=
    (syncInside base (searchBase base) called called (searchEntry called) searchInside
      (fun index _ => by fin_cases index <;> rfl) (BitVec.add_zero _).symm).symm
  have returnAligned : (base + 0x58#32).toNat % 4 = 0 := alignedTargetNat environment.code.aligned _ (by decide)
  obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
  have mode : MachineMode entered (base + 0x58#32) :=
    { (machine.withMemory memory).atSync base called with
      returnLow := by rw [BitVec.and_comm]; exact maskEven _ returnBit0
      returnNext := returnBit1
      ra := syncRead called (index := 1) (by decide) }
  have searchImage : CodeImage (Search.instructions .lower) (searchBase base) entered :=
    (environment.searchCode.withMemory memory fun byte low high => by
      have apart := stack.apartSearch
      unfold outsideFrame at apart
      change byte < (searchBase base).toNat + 4 * 13 at high
      exact pushedOutside original.mem initial fits byte (by omega)).atSync base called
  have searchHeader : Search.Header entered call.search := by
    have headerFits : call.header.toNat + 12 ≤ 2 ^ 32 := header.fits
    refine ⟨by change call.header.toNat + 8 ≤ 2 ^ 32; omega,
      mappedTransfer header.lengthReadable regions, ?_⟩
    rw [enteredMem]
    have apart := stack.apartHeader
    unfold outsideFrame at apart
    have word : WordAt original.mem (call.header.toNat + 4) call.length := header.lengthWord
    have result := pushedWord initial fits word (by unfold outsideFrame; omega)
    exact result
  have searchKeys (positive : 0 < call.length.toNat) : Search.Keys entered call.search := by
    have given := keys positive
    refine ⟨given.fits, mappedTransfer given.dataReadable regions, ?_,
      fun index bound => mappedTransfer (given.readable index bound) regions, fun index bound => ?_⟩
    · rw [enteredMem]
      have apart := stack.apartHeader
      unfold outsideFrame at apart
      have word : WordAt original.mem call.header.toNat call.data := given.dataWord
      have result := pushedWord initial fits word (by unfold outsideFrame; omega)
      exact result
    · rw [enteredMem]
      have apart := stack.apartEntries index bound
      unfold outsideFrame at apart
      have result := pushedWord initial fits (given.keyWord index bound) (by unfold outsideFrame; omega)
      exact result
  obtain ⟨endState, ran, endPc, result, -⟩ := Search.sortedMapSearchSailRun .lower (searchBase base)
    (base + 0x58#32) entered call.search (searchEntry called) routineEntered (by
      change state.a0 = call.header; exact headerArgument) (by
      change state.a1 = call.value.key; exact keyArgument)
    (Search.Environment.ofMachine mode searchImage) searchHeader searchKeys
  refine ⟨endState, ?_, result⟩
  have back : run (call.search.count .lower) entered =
      some (sync base { original with mem := memory }
        (afterSearch { state with s1 := state.a1, s2 := state.a0, ra := base + 0x58#32 } endState)) := by
    rw [ran]
    refine congrArg some (syncInside base (searchBase base) called _ endState searchInside
      (fun index _ => by fin_cases index <;> rfl) ?_)
    change base + 0x58#32 = searchBase base + endState.pc
    rw [endPc, BitVec.add_comm (searchBase base), BitVec.sub_add_cancel]
  rw [runAdd, entering, Option.bind_some, back]

-- The insertion's snapshot, from the routine's argument registers.
private def vectorEntry (state : Snapshot) : PairInsert.Snapshot :=
  { t0 := state.t0, t1 := state.t1, a0 := state.a0, a1 := state.a1, a2 := state.a2,
    a3 := state.a3, a4 := state.a4, a5 := state.a5, a6 := state.a6, a7 := state.a7 }

private theorem vectorInside : ∀ index ∈ tracked PairInsert.Snapshot, index ∈ tracked Snapshot := by
  decide

private theorem readRa (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x1 = some state.ra :=
  readReg_succ.mp (syncRead state (index := 1) (by decide))

private theorem readSp (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x2 = some state.sp :=
  readReg_succ.mp (syncRead state (index := 2) (by decide))

private theorem readS0 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x8 = some state.s0 :=
  readReg_succ.mp (syncRead state (index := 8) (by decide))

private theorem readS1 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x9 = some state.s1 :=
  readReg_succ.mp (syncRead state (index := 9) (by decide))

private theorem readS2 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x18 = some state.s2 :=
  readReg_succ.mp (syncRead state (index := 18) (by decide))

private theorem readS3 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x19 = some state.s3 :=
  readReg_succ.mp (syncRead state (index := 19) (by decide))

private theorem readA0 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x10 = some state.a0 :=
  readReg_succ.mp (syncRead state (index := 10) (by decide))

-- Every register the routine restores, or never writes, keeps its value.
private theorem frameRegisters (base : Word) (original : Machine) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 }) (memory : ByteMemory)
    (state : Snapshot) (ra : state.ra = initial.ra) (sp : state.sp = initial.sp)
    (s0 : state.s0 = initial.s0) (s1 : state.s1 = initial.s1) (s2 : state.s2 = initial.s2) (s3 : state.s3 = initial.s3) :
    ∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
      (sync base { original with mem := memory } state).regs.get? register =
        original.regs.get? register := by
  intro register outside
  by_cases isRa : register = Register.x1
  · subst isRa; rw [readRa, entry, readRa, ra]
  by_cases isSp : register = Register.x2
  · subst isSp; rw [readSp, entry, readSp, sp]
  by_cases isS0 : register = Register.x8
  · subst isS0; rw [readS0, entry, readS0, s0]
  by_cases isS1 : register = Register.x9
  · subst isS1; rw [readS1, entry, readS1, s1]
  by_cases isS2 : register = Register.x18
  · subst isS2; rw [readS2, entry, readS2, s2]
  by_cases isS3 : register = Register.x19
  · subst isS3; rw [readS3, entry, readS3, s3]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨pc, next, t0, t1, a0, a1, a2, a3, a4, a5, a6, a7⟩ := outside
  refine syncFrame state register pc next ?_
  intro index member
  change index ∈ ([1, 2, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] : List (Fin 32)) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Ne.symm isRa, Ne.symm isSp, Ne.symm t0, Ne.symm t1, Ne.symm isS0, Ne.symm isS1,
    Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5, Ne.symm a6,
    Ne.symm a7, Ne.symm isS2, Ne.symm isS3]

end Run

/-! ## Guarantees -/

structure Replacement (base : Word) (original : Machine) (call : Call) : Prop where
  writable : Writable original (call.search.wordSlot call.position) ∧
    Writable original (call.search.wordSlot call.position + 4)
  apartCode : RawVec.Insert.outsideCode 176 base 8 (call.search.slot call.position)
  apartHeader : call.vector.outsideHeader (call.search.slot call.position)
  live : ∀ index < call.length.toNat, PairAt original.mem (call.search.slot index) (call.old index)

def Call.replacedEntries (call : Call) : Nat → Pair :=
  fun index => if index = call.position then call.value else call.old index

def finalMemory (call : Call) (frame after : ByteMemory) : Prop :=
  (call.replaces →
    after = storePair frame (call.search.slot call.position) call.value ∧
    WordAt after call.header.toNat call.data ∧
    WordAt after (call.header.toNat + 4) call.length ∧
    WordAt after (call.header.toNat + 8) call.capacity ∧
    ∀ index < call.length.toNat, PairAt after (call.search.slot index) (call.replacedEntries index)) ∧
  (¬ call.replaces → ¬ call.vector.valid ∨ ¬ call.lengthValid → after = frame) ∧
  (¬ call.replaces → call.vector.valid →
    WordAt after call.header.toNat call.data ∧
    WordAt after (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
    WordAt after (call.header.toNat + 8) call.capacity ∧
    (∀ index, index < call.length.toNat + 1 →
      PairAt after (call.vector.slot index) (call.vector.result index)) ∧
    call.vector.unchanged frame after)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem sortedMapInsertSailCorrect (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (keyArgument : initial.a1 = call.value.key)
    (valueArgument : initial.a2 = call.value.value)
    (environment : Environment base returnAddress original)
    (header : RawVec.Insert.Header original call.vector)
    (stack : Stack base original call initial.sp)
    (keys : call.lengthValid → 0 < call.length.toNat → Search.Keys original call.search)
    (replace : call.replaces → Replacement base original call)
    (buffer : ¬ call.replaces → call.vector.valid → PairInsert.Buffer (vectorBase base) original call.vector) :
    ∃ final, run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status ∧
      finalMemory call (pushed original.mem initial.sp initial) final.mem ∧
      (∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register) := by
  let memory := pushed original.mem initial.sp initial
  have machine := environment.mode.toMachineState
  have fits := stack.fits
  have image := imageAt environment stack _ (pushedOutside original.mem initial fits)
  have returnArgument : initial.ra = returnAddress := by
    have stored := readReg_succ.mp environment.mode.ra
    rw [entry, readRa] at stored
    exact Option.some.inj stored
  have headerApart := stack.apartHeader
  unfold outsideFrame at headerApart
  have lengthWord : WordAt memory (call.header.toNat + 4) call.length :=
    pushedWord initial fits header.lengthWord (by unfold outsideFrame; omega)
  have capacityWord : WordAt memory (call.header.toNat + 8) call.capacity :=
    pushedWord initial fits header.capacityWord (by unfold outsideFrame; omega)
  let checked : Snapshot :=
    { saved initial with pc := 0x24#32, s0 := initial.a2, s3 := call.length, a2 := call.capacity }
  have checking : run 9 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } checked) := by
    rw [show 9 = 6 + 3 from rfl, runAdd, prologue environment initial stack, Option.bind_some]
    refine runStep (step18 machine image _ rfl) ?_
    refine runStep (step1c machine image _ rfl _ (headerArgument ▸ header.lengthReadable) ?_)
      (runStep (step20 machine image _ rfl _ (headerArgument ▸ header.capacityReadable) ?_) rfl)
    · have address : (call.header + 4#32).toNat = call.header.toNat + 4 :=
        RawVec.Insert.headerOffset header 4 (by decide)
      change WordAt memory (initial.a0 + 4#32).toNat call.length
      rw [headerArgument, address]; exact lengthWord
    · have address : (call.header + 8#32).toNat = call.header.toNat + 8 :=
        RawVec.Insert.headerOffset header 8 (by decide)
      change WordAt memory (initial.a0 + 8#32).toNat call.capacity
      rw [headerArgument, address]; exact capacityWord
  have returning (state : Snapshot) (pc : state.pc = 0x2c#32)
      (lowered : state.sp = frameBase initial.sp) (status : state.a0 = call.status)
      (count : Nat) (after : ByteMemory)
      (imageAfter : CodeImage instructions base { original with mem := after })
      (savedWord : ∀ (offset : Word) (value : Word),
        WordAt memory (frameBase initial.sp + offset).toNat value →
        offset ∈ [12, 16, 20, 24, 28] → WordAt after (frameBase initial.sp + offset).toNat value)
      (ran : run count (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := after } state)) (total : count + 7 = call.count)
      (memoryResult : finalMemory call memory after) :
      ∃ final, run call.count original = some final ∧
        final.regs.get? Register.PC = some returnAddress ∧
        final.regs.get? Register.x10 = some call.status ∧ finalMemory call memory final.mem ∧
        (∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
          final.regs.get? register = original.regs.get? register) := by
    let done := { restored initial state with pc := returnAddress - base }
    refine ⟨sync base { original with mem := after } done, ?_,
      pcReadReturned base returnAddress _ done rfl, ?_, ?_,
      frameRegisters base original initial entry after done rfl rfl rfl rfl rfl rfl⟩
    · rw [← total, runAdd, (congrArg (run count) entry).trans ran, Option.bind_some,
        epilogue environment initial stack returnArgument state pc lowered after imageAfter savedWord]
    · rw [readA0]; exact congrArg some status
    · rw [syncMem]; exact memoryResult
  by_cases lengthValid : call.lengthValid
  case neg =>
    have notReplaces : ¬ call.replaces := fun replaces => lengthValid replaces.1
    have notVectorValid (valid : call.vector.valid) : False := by
      have spare : call.length.toNat < call.capacity.toNat := valid.2
      exact lengthValid spare.le
    have notTaken : ¬ checked.s3.toNat ≤ checked.a2.toNat := lengthValid
    refine returning { checked with pc := 0x2c#32, a0 := 3#32 } rfl rfl
      (by simp [Call.status, lengthValid]) 11 memory image (fun _ _ word _ => word) ?_
      (by simp [Call.count, lengthValid])
      ⟨fun replaces => (notReplaces replaces).elim, fun _ _ => rfl,
        fun _ valid => (notVectorValid valid).elim⟩
    rw [show 11 = 9 + 2 from rfl, runAdd, checking, Option.bind_some]
    refine runStep (step24 machine image _ rfl) ?_
    rw [if_neg notTaken]
    exact runStep (step28 machine image _ rfl) rfl
  let calling : Snapshot := { checked with pc := 0x48#32 }
  have toCall : run 10 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } calling) := by
    rw [show 10 = 9 + 1 from rfl, runAdd, checking, Option.bind_some]
    refine runStep (step24 machine image _ rfl) ?_
    rw [if_pos (show checked.s3.toNat ≤ checked.a2.toNat from lengthValid)]
    rfl
  obtain ⟨endState, searched, position⟩ := searchCall environment initial stack header
    (keys lengthValid) calling rfl headerArgument keyArgument
  let back := afterSearch { calling with s1 := calling.a1, s2 := calling.a0, ra := base + 0x58#32 }
    endState
  let compared := { back with pc := 0x5c#32, a1 := back.a0 }
  have toCompare : run (10 + (4 + call.search.count .lower) + 1)
      (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } compared) := by
    rw [runAdd, runAdd, toCall, Option.bind_some, searched, Option.bind_some]
    exact runStep (step58 machine image _ rfl) rfl
  have backKey : back.s1 = call.value.key := keyArgument
  have backValue : back.s0 = call.value.value := valueArgument
  have backHeader : back.s2 = call.header := headerArgument
  have backSp : back.sp = frameBase initial.sp := rfl
  have positionWord : back.a0 = BitVec.ofNat 32 call.position := position
  have positionNat : back.a0.toNat = call.position := by rw [positionWord]; exact call.vectorIndex
  have targetSlot : call.data + compared.a1 <<< (3 : Nat) = call.search.wordSlot call.position := by
    show call.data + back.a0 <<< (3 : Nat) = _
    rw [BitVec.add_comm]
    have shifted := call.search.slotShift back.a0
    rw [positionNat] at shifted
    exact shifted
  have vectorPath :
      ¬ call.replaces →
      (∃ (count : Nat) (state : Snapshot), run count (sync base original { initial with pc := 0 }) =
          some (sync base { original with mem := memory } state) ∧
          state.pc = 0x84#32 ∧ state.s0 = call.value.value ∧ state.s1 = call.value.key ∧
          state.s2 = call.header ∧ state.a1 = call.vector.index ∧
          state.sp = frameBase initial.sp ∧ count + 11 + call.vector.count = call.count) →
      ∃ final, run call.count original = some final ∧
        final.regs.get? Register.PC = some returnAddress ∧
        final.regs.get? Register.x10 = some call.status ∧ finalMemory call memory final.mem ∧
        (∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
          final.regs.get? register = original.regs.get? register) := by
    intro replaces takesVector
    obtain ⟨count, state, before, pc, value, key, headerAddress, index, lowered, total⟩ := takesVector
    obtain ⟨ra, s0, s1, s2, s3⟩ := savedWords original.mem initial fits
    let jumped := { restored initial state with
      pc := vectorOffset, a0 := call.header, a2 := call.value.key, a3 := call.value.value,
      t1 := base + 0xa8#32 }
    have toJump : run 11 (sync base { original with mem := memory } state) =
        some (sync base { original with mem := memory } jumped) := by
      let machineAt (snapshot : Snapshot) := sync base { original with mem := memory } snapshot
      let arguments := { state with pc := 0x90#32, a0 := state.s2, a2 := state.s1, a3 := state.s0 }
      have toArguments : run 3 (machineAt state) = some (machineAt arguments) :=
        runStep (step84 machine image state pc) (runStep (step88 machine image _ rfl)
          (runStep (step8c machine image _ rfl) rfl))
      have canRead (offset : Nat) (member : offset ∈ [12, 16, 20, 24, 28]) :
          Readable original (arguments.sp + BitVec.ofNat 32 offset) := by
        show Readable original (state.sp + BitVec.ofNat 32 offset)
        rw [lowered]
        exact stack.readable offset member
      have savedAt (offset : Word) (value : Word)
          (word : WordAt memory (frameBase initial.sp + offset).toNat value) :
          WordAt memory (arguments.sp + offset).toNat value := by
        show WordAt memory (state.sp + offset).toNat value
        rw [lowered]
        exact word
      let savedRegisters := { arguments with
        pc := 0xa4#32, ra := initial.ra, s0 := initial.s0, s1 := initial.s1,
        s2 := initial.s2, s3 := initial.s3 }
      have restoreRegisters : run 5 (machineAt arguments) = some (machineAt savedRegisters) := by
        change run 5 (sync base { original with mem := memory } arguments) =
          some (sync base { original with mem := memory } savedRegisters)
        refine runStep (step90 machine image arguments rfl _ (canRead 28 (by decide)) (savedAt 28 _ ra)) ?_
        refine runStep (step94 machine image _ rfl _ (canRead 24 (by decide)) (savedAt 24 _ s0)) ?_
        refine runStep (step98 machine image _ rfl _ (canRead 20 (by decide)) (savedAt 20 _ s1)) ?_
        refine runStep (step9c machine image _ rfl _ (canRead 16 (by decide)) (savedAt 16 _ s2)) ?_
        exact runStep (stepa0 machine image _ rfl _ (canRead 12 (by decide)) (savedAt 12 _ s3)) rfl
      have jump : run 3 (machineAt savedRegisters) = some (machineAt jumped) := by
        change run 3 (sync base { original with mem := memory } savedRegisters) =
          some (sync base { original with mem := memory } jumped)
        refine runStep (stepa4 machine image savedRegisters rfl)
          (runStep (stepa8 machine image _ rfl) (runStep (stepac machine image _ rfl rfl) ?_))
        have stackRestored : state.sp + 32#32 = initial.sp := lowered ▸ restoredSp
        change some (machineAt { savedRegisters with
          pc := vectorOffset, sp := state.sp + 32#32, t1 := base + 0xa8#32 }) = some (machineAt jumped)
        rw [stackRestored]
        have snapshot : { savedRegisters with
            pc := vectorOffset, sp := initial.sp, t1 := base + 0xa8#32 } = jumped := by
          simp only [savedRegisters, arguments, jumped, restored, value, key, headerAddress]
        rw [snapshot]
      change run 11 (machineAt state) = some (machineAt jumped)
      rw [show 11 = 3 + (5 + 3) from rfl, runAdd, toArguments, Option.bind_some, runAdd,
        restoreRegisters, Option.bind_some, jump]
    let entered := sync base { original with mem := memory } jumped
    have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
      syncFrame jumped _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
    have enteredMem : entered.mem = memory := syncMem jumped
    have routineEntered :
        entered = sync (vectorBase base) entered { vectorEntry jumped with pc := 0 } :=
      (syncInside base (vectorBase base) jumped jumped (vectorEntry jumped) vectorInside
        (fun index _ => by fin_cases index <;> rfl)
        (by show base + vectorOffset = base + vectorOffset + 0#32; rw [BitVec.add_zero])).symm
    have mode : MachineMode entered returnAddress :=
      { (machine.withMemory memory).atSync base jumped with
        returnLow := environment.mode.returnLow
        returnNext := environment.mode.returnNext
        ra := by
          have read := syncRead (base := base) (frame := { original with mem := memory }) jumped
            (index := 1) (by decide)
          rw [show RegisterView.value jumped 1 = returnAddress from returnArgument] at read
          exact read }
    have vectorImage : CodeImage PairInsert.instructions (vectorBase base) entered :=
      (environment.vectorCode.withMemory memory fun byte low high => by
        have apart := stack.apartVector
        unfold outsideFrame at apart
        change byte < (vectorBase base).toNat + 4 * 33 at high
        exact pushedOutside original.mem initial fits byte (by omega)).atSync base jumped
    have vectorHeader : RawVec.Insert.Header entered call.vector := by
      refine ⟨header.fits, mappedTransfer header.lengthReadable regions,
        mappedTransfer header.capacityReadable regions, ?_, ?_⟩
      · rw [enteredMem]; exact lengthWord
      · rw [enteredMem]; exact capacityWord
    have vectorBuffer (valid : call.vector.valid) : PairInsert.Buffer (vectorBase base) entered call.vector := by
      have given := buffer replaces valid
      refine ⟨given.fits, mappedTransfer given.dataReadable regions, ?_,
        mappedTransfer given.lengthWritable regions, given.lengthAwayFromCode, fun index bound => ?_,
        fun index low high => ?_, fun index low high => ?_, given.separated, given.awayFromCode⟩
      · rw [enteredMem]
        have dataWord : WordAt original.mem call.header.toNat call.data := given.dataWord
        have apart : outsideFrame initial.sp call.header.toNat 4 := by
          unfold outsideFrame
          omega
        exact pushedWord initial fits dataWord apart
      · rw [enteredMem]
        have pair := given.live index bound
        have apart := stack.apartEntries index bound
        rw [← call.slotSame] at apart
        unfold outsideFrame at apart
        exact ⟨pushedWord initial fits pair.1 (by unfold outsideFrame; omega),
          pushedWord initial fits pair.2 (by unfold outsideFrame; omega)⟩
      · have mapped := given.readable index low high
        exact ⟨mappedTransfer mapped.1 regions, mappedTransfer mapped.2 regions⟩
      · have mapped := given.writable index low high
        exact ⟨mappedTransfer mapped.1 regions, mappedTransfer mapped.2 regions⟩
    obtain ⟨endState, vectorMemory, vectorRan, endPc, vectorStatus, rejected, accepted⟩ :=
      PairInsert.rawVecPairInsertSailRun (vectorBase base) returnAddress entered call.vector
        (vectorEntry jumped) routineEntered rfl index rfl rfl
        (PairInsert.Environment.ofMachine mode vectorImage) vectorHeader vectorBuffer
    refine ⟨_, ?_, pcReadReturned (vectorBase base) returnAddress { entered with mem := vectorMemory }
      endState endPc, ?_, ?_, fun register outside => ?_⟩
    · rw [← total, runAdd, runAdd, (congrArg (run _) entry).trans before, Option.bind_some, toJump,
        Option.bind_some]
      exact vectorRan
    · have read : (sync (vectorBase base) { entered with mem := vectorMemory } endState).regs.get?
          Register.x10 = some endState.a0 := readReg_succ.mp (syncRead endState (index := 10) (by decide))
      rw [read, vectorStatus, Call.status, if_neg (not_not_intro lengthValid), if_neg replaces]
    · rw [syncMem]
      refine ⟨fun replaced => (replaces replaced).elim, fun _ invalid => ?_, fun _ valid => ?_⟩
      · exact (rejected (invalid.resolve_right (not_not_intro lengthValid))).trans enteredMem
      · obtain ⟨data, length, capacity, entries, unchanged⟩ := accepted valid
        rw [enteredMem] at unchanged
        exact ⟨data, length, capacity, entries, unchanged⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      obtain ⟨pc, next, t0, t1, a0, a1, a2, a3, a4, a5, a6, a7⟩ := outside
      rw [syncFrame endState register pc next (by
        intro trackedIndex member
        change trackedIndex ∈ ([5, 6, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 32)) at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [Ne.symm t0, Ne.symm t1, Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3,
          Ne.symm a4, Ne.symm a5, Ne.symm a6, Ne.symm a7])]
      exact frameRegisters base original initial entry memory jumped rfl rfl rfl rfl rfl rfl
        register (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                     exact ⟨pc, next, t0, t1, a0, a1, a2, a3, a4, a5, a6, a7⟩)
  by_cases inside : call.position < call.length.toNat
  case neg =>
    have notReplaces : ¬ call.replaces := fun replaces => inside replaces.2.1
    apply vectorPath notReplaces
    have taken : compared.s3.toNat ≤ compared.a0.toNat := by
      show call.length.toNat ≤ back.a0.toNat
      rw [positionNat]; omega
    refine ⟨10 + (4 + call.search.count .lower) + 1 + 1, { compared with pc := 0x84#32 },
      ?_, rfl, backValue, backKey, backHeader, positionWord, backSp, ?_⟩
    · rw [runAdd, toCompare, Option.bind_some]
      refine runStep (step5c machine image _ rfl) ?_
      rw [if_pos taken]; rfl
    · simp [Call.count, lengthValid, notReplaces, inside]; omega
  have given := keys lengthValid (by omega)
  have notTaken : ¬ compared.s3.toNat ≤ compared.a0.toNat := by
    show ¬ call.length.toNat ≤ back.a0.toNat
    rw [positionNat]; omega
  have dataRead : Readable original compared.s2 := backHeader ▸ given.dataReadable
  have dataWord : WordAt memory compared.s2.toNat call.data := by
    show WordAt memory back.s2.toNat call.data
    rw [backHeader]
    exact pushedWord initial fits given.dataWord (by unfold outsideFrame; omega)
  let addressed : Snapshot :=
    { compared with
      pc := 0x6c#32, a2 := call.search.wordSlot call.position, a3 := compared.a1 <<< (3 : Nat) }
  have keyRead : Readable original addressed.a2 := given.readable call.position inside
  have keyWord : WordAt memory addressed.a2.toNat (call.old call.position).key := by
    show WordAt memory (call.search.wordSlot call.position).toNat _
    rw [Search.slotNat given inside]
    have apart := stack.apartEntries call.position inside
    unfold outsideFrame at apart
    exact pushedWord initial fits (given.keyWord call.position inside) (by unfold outsideFrame; omega)
  let loaded := { addressed with pc := 0x70#32, a3 := (call.old call.position).key }
  have toLoaded : run (10 + (4 + call.search.count .lower) + 1 + 5)
      (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } loaded) := by
    rw [runAdd, toCompare, Option.bind_some]
    refine runStep (step5c machine image _ rfl) ?_
    rw [if_neg notTaken]
    refine runStep (step60 machine image _ rfl _ dataRead dataWord) ?_
    refine runStep (step64 machine image _ rfl) (runStep (step68 machine image _ rfl) ?_)
    rw [targetSlot]
    exact runStep (step6c machine image addressed rfl _ keyRead keyWord) rfl
  by_cases keyMatches : (call.old call.position).key = call.value.key
  case neg =>
    have notReplaces : ¬ call.replaces := fun replaces => keyMatches replaces.2.2
    apply vectorPath notReplaces
    have differs : ¬ loaded.a3 = loaded.s1 := by
      show ¬ (call.old call.position).key = back.s1
      rw [backKey]; exact keyMatches
    refine ⟨10 + (4 + call.search.count .lower) + 1 + 5 + 1, { loaded with pc := 0x84#32 },
      ?_, rfl, backValue, backKey, backHeader, positionWord, backSp, ?_⟩
    · rw [runAdd, toLoaded, Option.bind_some]
      refine runStep (step70 machine image _ rfl) ?_
      rw [if_neg differs]; rfl
    · simp [Call.count, lengthValid, notReplaces, inside]; omega
  have replaces : call.replaces := ⟨lengthValid, inside, keyMatches⟩
  have same : loaded.a3 = loaded.s1 := by
    show (call.old call.position).key = back.s1
    rwa [backKey]
  have permitted := replace replaces
  let address := call.search.slot call.position
  have addressNat : loaded.a2.toNat = address := Search.slotNat given inside
  have slotFits : address + 8 ≤ 2 ^ 32 := by
    have fits : call.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 := given.fits
    change call.data.toNat + 8 * call.position + 8 ≤ 2 ^ 32
    omega
  have nextAddress : (loaded.a2 + 4#32).toNat = address + 4 := by
    rw [BitVec.toNat_add, addressNat]
    change (address + 4) % 2 ^ 32 = address + 4
    exact Nat.mod_eq_of_lt (by omega)
  let keyMemory := storeWord memory address call.value.key
  let replacedMemory := storePair memory address call.value
  have codeApart := permitted.apartCode
  change address + 8 ≤ base.toNat ∨ base.toNat + 176 ≤ address at codeApart
  let keyImage : CodeImage instructions base { original with mem := keyMemory } :=
    image.withMemory keyMemory fun byte lo hi => storeWordOutside _ _ _ _ (by
      change byte < base.toNat + 176 at hi
      omega)
  let replacementImage : CodeImage instructions base { original with mem := replacedMemory } :=
    image.withMemory replacedMemory fun byte lo hi => Element.storeOutside (α := Pair) _ _ _ _ (by
      change byte < base.toNat + 176 at hi
      change byte < address ∨ address + 8 ≤ byte
      omega)
  have savedWord (offset : Word) (value : Word)
      (word : WordAt memory (frameBase initial.sp + offset).toNat value)
      (member : offset ∈ [12, 16, 20, 24, 28]) :
      WordAt replacedMemory (frameBase initial.sp + offset).toNat value := by
    have small : offset.toNat ≤ 28 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    have apart := stack.apartEntries call.position inside
    change address + 8 ≤ initial.sp.toNat - 32 ∨ initial.sp.toNat ≤ address at apart
    intro byte
    let location := (frameBase initial.sp + offset).toNat + byte.val
    have untouched : location < address ∨ address + Element.bytes Pair ≤ location := by
      change (frameBase initial.sp + offset).toNat + byte.val < address ∨
        address + 8 ≤ (frameBase initial.sp + offset).toNat + byte.val
      rw [frameAddress fits offset small]
      have := byte.isLt
      omega
    exact (Element.storeOutside (α := Pair) memory address call.value location untouched).trans
      (word byte)
  have headerSeparation : address + 8 ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ address := by
    exact permitted.apartHeader
  have keepHeader (offset : Nat) (small : offset ≤ 8) (value : Word)
      (word : WordAt memory (call.header.toNat + offset) value) :
      WordAt replacedMemory (call.header.toNat + offset) value := by
    exact wordStoreElement (α := Pair) word (by change _ ≤ address ∨ address + 8 ≤ _; omega)
  have unchangedData : WordAt memory call.header.toNat call.data :=
    pushedWord initial fits given.dataWord (by unfold outsideFrame; omega)
  have replacedEntries (index : Nat) (bound : index < call.length.toNat) :
      PairAt replacedMemory (call.search.slot index) (call.replacedEntries index) := by
    by_cases matching : index = call.position
    · subst index
      rw [Call.replacedEntries, if_pos rfl]
      exact Element.atStore (α := Pair) memory address call.value
    · rw [Call.replacedEntries, if_neg matching]
      have apart := stack.apartEntries index bound
      unfold outsideFrame at apart
      have originalEntry : Element.At original.mem (call.search.slot index) (call.old index) :=
        permitted.live index bound
      have onStack : Element.At memory (call.search.slot index) (call.old index) :=
        Element.atFrame originalEntry (fun byte low high => by
          rw [pairBytes] at high
          exact pushedOutside original.mem initial fits byte (by omega))
      have separated : call.search.slot index + 8 ≤ address ∨ address + 8 ≤ call.search.slot index := by
        rcases lt_or_gt_of_ne matching with below | above
        · left
          have before := call.vector.slotBefore below
          rw [call.slotSame, call.slotSame, pairBytes] at before
          exact before
        · right
          have before := call.vector.slotBefore above
          rw [call.slotSame, call.slotSame, pairBytes] at before
          exact before
      exact elementStoreElement (α := Pair) onStack separated
  have memoryResult : finalMemory call memory replacedMemory := by
    refine ⟨fun _ => ⟨rfl, keepHeader 0 (by decide) _ unchangedData,
      keepHeader 4 (by decide) _ lengthWord, keepHeader 8 (by decide) _ capacityWord, replacedEntries⟩,
      fun rejected _ => (rejected replaces).elim, fun rejected _ => (rejected replaces).elim⟩
  let epilogueState := { loaded with pc := 0x2c#32, a0 := 4#32 }
  refine returning epilogueState rfl backSp (by simp [epilogueState, Call.status, lengthValid, replaces])
    (10 + (4 + call.search.count .lower) + 1 + 5 + 5) replacedMemory replacementImage savedWord ?_
    (by simp [Call.count, lengthValid, replaces]; omega)
    memoryResult
  rw [runAdd, toLoaded, Option.bind_some]
  refine runStep (step70 machine image _ rfl) ?_
  rw [if_pos same]
  let keyStore := { loaded with pc := 0x74#32 }
  let valueStore := { loaded with pc := 0x78#32 }
  let statusLoad := { loaded with pc := 0x7c#32 }
  have keyWritable : Writable original (keyStore.a2 + 0#32) := by
    rw [BitVec.add_zero]
    exact permitted.writable.1
  have keyStep :
      step (sync base { original with mem := memory } keyStore) =
        some (sync base { original with mem := keyMemory } valueStore) := by
    have storeAddress : (keyStore.a2 + 0#32).toNat = address := by
      rw [BitVec.add_zero]
      exact addressNat
    have key : keyStore.s1 = call.value.key := backKey
    have stored : storeWord memory (keyStore.a2 + 0#32).toNat keyStore.s1 = keyMemory :=
      congrArg₂ (storeWord memory) storeAddress key
    exact (step74 machine image keyStore rfl keyWritable).trans
      (congrArg (fun mem => some (sync base { original with mem } valueStore)) stored)
  have valueStep :
      step (sync base { original with mem := keyMemory } valueStore) =
        some (sync base { original with mem := replacedMemory } statusLoad) := by
    have storeAddress : (valueStore.a2 + 4#32).toNat = address + 4 := nextAddress
    have value : valueStore.s0 = call.value.value := backValue
    have stored : storeWord keyMemory (valueStore.a2 + 4#32).toNat valueStore.s0 = replacedMemory :=
      congrArg₂ (storeWord keyMemory) storeAddress value
    exact (step78 machine keyImage valueStore rfl permitted.writable.2).trans
      (congrArg (fun mem => some (sync base { original with mem } statusLoad)) stored)
  refine runStep keyStep (runStep valueStep ?_)
  exact runStep (step7c machine replacementImage statusLoad rfl)
    (runStep (step80 machine replacementImage _ rfl) rfl)

/-! ## Against the mathematical map -/

theorem sortedMapInsertUpdates (call : Call) (sorted : Sorted (entriesOf call.old call.length.toNat)) :
    (call.replaces → entriesOf call.replacedEntries call.length.toNat =
        insert (entriesOf call.old call.length.toNat) call.value) ∧
    (¬ call.replaces → call.vector.valid → entriesOf call.vector.result (call.length.toNat + 1) =
        insert (entriesOf call.old call.length.toNat) call.value) := by
  let length := call.length.toNat
  let position := call.position
  have le : position ≤ length := call.position_le
  have inserted : insert (entriesOf call.old length) call.value =
      entriesOf call.old position ++ call.value ::
        dropHead (entriesFrom call.old position (length - position)) call.value.key := by
    rw [entriesOf_split call.old le]
    exact insert_split (lowerSplit call.value.key sorted)
  refine ⟨fun replaces => ?_, fun notReplaces valid => ?_⟩
  · have inside : position < length := replaces.2.1
    rw [inserted, entriesOf_split call.replacedEntries le,
      show length - position = (length - position - 1) + 1 by omega,
      entriesFrom_succ, entriesFrom_succ, dropHead, if_pos replaces.2.2]
    congr 1
    · apply entriesOf_congr
      intro index below
      exact if_neg (Nat.ne_of_lt below)
    · have head : call.replacedEntries position = call.value := if_pos rfl
      rw [head]
      congr 1
      apply entriesFrom_congr
      intro offset _
      exact if_neg (by change position + 1 + offset ≠ position; omega)
  · have lengthValid : call.lengthValid := valid.2.le
    have unchanged : dropHead (entriesFrom call.old position (length - position)) call.value.key =
        entriesFrom call.old position (length - position) := by
      by_cases inside : position < length
      · have differs : (call.old position).key ≠ call.value.key :=
          fun same => notReplaces ⟨lengthValid, inside, same⟩
        rw [show length - position = (length - position - 1) + 1 by omega,
          entriesFrom_succ, dropHead, if_neg differs]
      · rw [show length - position = 0 by omega]
        rfl
    rw [inserted, unchanged, entriesOf_split call.vector.result (show position ≤ length + 1 by omega),
      show length + 1 - position = (length - position) + 1 by omega, entriesFrom_succ]
    congr 1
    · apply entriesOf_congr
      intro index below
      simp only [RawVec.Insert.Call.result, call.vectorIndex]
      exact if_pos below
    · have head : call.vector.result position = call.value := by
        rw [RawVec.Insert.Call.result, call.vectorIndex]
        simp only [show call.position = position from rfl, lt_self_iff_false, if_false, if_true]
        rfl
      rw [head]
      congr 1
      unfold entriesFrom
      apply List.map_congr_left
      intro offset _
      simp only [RawVec.Insert.Call.result, call.vectorIndex]
      rw [if_neg (by change ¬ position + 1 + offset < position; omega),
        if_neg (by change position + 1 + offset ≠ position; omega)]
      change call.old (position + 1 + offset - 1) = call.old (position + offset)
      congr 1
      omega

end Riscfree.SortedMap.Insert
