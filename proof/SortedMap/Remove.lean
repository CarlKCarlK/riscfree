import SortedMap.Remove.Instructions
import SortedMap.Search.Correct
import RawVec.PairRemove
import SortedMap.Entries

/-!
# `sorted_map_remove` is correct against Sail

`sorted_map_remove(map, key)` saves four registers, rejects an invalid length,
calls `sorted_map_lower_bound`, and, if the entry at the returned position has
the key, tail-calls `raw_vec_pair_remove` at that position. This proof steps
only through the routine's own 36 instructions. The two callees enter through
their existing theorems: `sortedMapSearchSailRun` for the search, which
returns to the routine, and `rawVecPairRemoveSailRun` for the removal, which
returns to the routine's caller. Neither callee's instructions are stepped
again here.

The guarantee (`sortedMapRemoveSailCorrect`):

* the status is `INVALID_LENGTH` (3) if `length > capacity`, `OK` (0) if an
  entry has the key, and `ABSENT` (5) otherwise;
* after a removal, the map holds exactly what `raw_vec_pair_remove` leaves at
  the key's position, and `sortedMapRemoveErases` shows that for a sorted map
  this is the mathematical `erase`;
* otherwise the map is unchanged. In every case the only other bytes written
  are the 16-byte frame below the caller's `sp`;
* the exact instruction count is `call.count`;
* every register except the PC, `nextPC`, `t1`, and `a0`–`a5` keeps its value,
  so the callee-saved registers, `ra`, and `sp` are restored.
-/

namespace Riscfree.SortedMap.Remove

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

structure Call where
  header : Word
  key : Word
  length : Word
  capacity : Word
  data : Word
  old : Nat → Pair

namespace Call

def search (call : Call) : Search.Call := ⟨call.header, call.key, call.length, call.data, call.old⟩

-- Where `sorted_map_lower_bound` stops.
def position (call : Call) : Nat := call.search.result .lower

def lengthValid (call : Call) : Prop := call.length.toNat ≤ call.capacity.toNat

-- The routine removes an entry: the length is valid and the entry at the
-- search position has the key.
def removes (call : Call) : Prop :=
  call.lengthValid ∧ call.position < call.length.toNat ∧ (call.old call.position).key = call.key

instance (call : Call) : Decidable call.lengthValid := inferInstanceAs (Decidable (_ ≤ _))
instance (call : Call) : Decidable call.removes := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- The `raw_vec_pair_remove` call the routine makes.
def vector (call : Call) : PairRemove.Call :=
  { header := call.header, index := BitVec.ofNat 32 call.position, length := call.length,
    capacity := call.capacity, data := call.data, old := call.old }

def status (call : Call) : Word :=
  if ¬ call.lengthValid then 3 else if call.removes then 0 else 5

def count (call : Call) : Nat :=
  if ¬ call.lengthValid then 16
  else if call.removes then 28 + call.search.count .lower + call.vector.count
  else if call.position < call.length.toNat then 26 + call.search.count .lower
  else 21 + call.search.count .lower

theorem position_le (call : Call) : call.position ≤ call.length.toNat := call.search.result_le .lower

theorem vectorIndex (call : Call) : call.vector.index.toNat = call.position := by
  have := call.position_le
  have := call.length.isLt
  simp only [vector, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem vectorValid {call : Call} (removes : call.removes) : call.vector.valid := by
  refine ⟨?_, removes.1⟩
  rw [vectorIndex]
  exact removes.2.1

theorem slotSame (call : Call) (index : Nat) : call.vector.slot index = call.search.slot index := by
  simp [Remove.Call.slot, Search.Call.slot, vector, search, pairBytes]

end Call

/-! ## Premises -/

def searchBase (base : Word) : Word := base + searchOffset
def vectorBase (base : Word) : Word := base + vectorOffset

-- The 16-byte frame below the caller's `sp`.
def frameBase (sp : Word) : Word := sp + 0xfffffff0#32

structure Environment (base returnAddress : Word) (original : Machine) : Prop where
  mode : MachineMode original returnAddress
  code : CodeImage instructions base original
  searchCode : CodeImage (Search.instructions .lower) (searchBase base) original
  vectorCode : CodeImage PairRemove.instructions (vectorBase base) original

-- A byte range of `width` bytes at `address` misses the frame below `sp`.
def outsideFrame (sp : Word) (address width : Nat) : Prop :=
  address + width ≤ sp.toNat - 16 ∨ sp.toNat ≤ address

structure Stack (base : Word) (original : Machine) (call : Call) (sp : Word) : Prop where
  fits : 16 ≤ sp.toNat
  readable : ∀ offset ∈ [0, 4, 8, 12], Readable original (frameBase sp + BitVec.ofNat 32 offset)
  writable : ∀ offset ∈ [0, 4, 8, 12], Writable original (frameBase sp + BitVec.ofNat 32 offset)
  apartHeader : outsideFrame sp call.header.toNat 12
  apartEntries : ∀ index < call.length.toNat, outsideFrame sp (call.search.slot index) 8
  apartCode : outsideFrame sp base.toNat 144
  apartSearch : outsideFrame sp (searchBase base).toNat 52
  apartVector : outsideFrame sp (vectorBase base).toNat 100

-- The memory after the prologue saves `ra`, `s0`, `s1`, and `s2`.
def pushed (memory : ByteMemory) (sp : Word) (state : Snapshot) : ByteMemory :=
  storeWord (storeWord (storeWord (storeWord memory (frameBase sp + 12#32).toNat state.ra)
    (frameBase sp + 8#32).toNat state.s0) (frameBase sp + 4#32).toNat state.s1)
    (frameBase sp + 0#32).toNat state.s2

section Frame

variable {sp : Word}

theorem frameLowered : frameBase sp = sp - 16#32 := by
  rw [frameBase, BitVec.sub_eq_add_neg]
  rfl

-- Without wrapping, because the frame lies above address 16. (`omega` on the
-- wrapped sum gives a term too deep for the kernel.)
theorem frameAddress (fits : 16 ≤ sp.toNat) (offset : Word) (small : offset.toNat ≤ 12) :
    (frameBase sp + offset).toNat = sp.toNat - 16 + offset.toNat := by
  have below := sp.isLt
  have le : 16#32 ≤ sp := BitVec.le_def.mpr fits
  rw [frameLowered, BitVec.toNat_add, BitVec.toNat_sub_of_le le]
  change (sp.toNat - 16 + offset.toNat) % 2 ^ 32 = _
  exact Nat.mod_eq_of_lt (by omega)

theorem frameAddresses (fits : 16 ≤ sp.toNat) :
    (frameBase sp + 12#32).toNat = sp.toNat - 4 ∧ (frameBase sp + 8#32).toNat = sp.toNat - 8 ∧
      (frameBase sp + 4#32).toNat = sp.toNat - 12 ∧ (frameBase sp + 0#32).toNat = sp.toNat - 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frameAddress fits _ (by decide)]; show sp.toNat - 16 + 12 = _; omega
  · rw [frameAddress fits _ (by decide)]; show sp.toNat - 16 + 8 = _; omega
  · rw [frameAddress fits _ (by decide)]; show sp.toNat - 16 + 4 = _; omega
  · rw [frameAddress fits _ (by decide)]; show sp.toNat - 16 + 0 = _; omega

theorem pushedOutside (memory : ByteMemory) (state : Snapshot) (fits : 16 ≤ sp.toNat) (byte : Nat)
    (outside : byte < sp.toNat - 16 ∨ sp.toNat ≤ byte) :
    (pushed memory sp state)[byte]? = memory[byte]? := by
  obtain ⟨a12, a8, a4, a0⟩ := frameAddresses fits
  unfold pushed
  rw [storeWordOutside _ _ _ _ (by rw [a0]; omega), storeWordOutside _ _ _ _ (by rw [a4]; omega),
    storeWordOutside _ _ _ _ (by rw [a8]; omega), storeWordOutside _ _ _ _ (by rw [a12]; omega)]

theorem pushedWord {memory : ByteMemory} {address : Nat} {value : Word} (state : Snapshot)
    (fits : 16 ≤ sp.toNat) (word : WordAt memory address value) (apart : outsideFrame sp address 4) :
    WordAt (pushed memory sp state) address value := by
  intro byte
  rw [pushedOutside _ _ fits _ (by unfold outsideFrame at apart; have := byte.isLt; omega)]
  exact word byte

theorem savedWords (memory : ByteMemory) (state : Snapshot) (fits : 16 ≤ sp.toNat) :
    WordAt (pushed memory sp state) (frameBase sp + 12#32).toNat state.ra ∧
      WordAt (pushed memory sp state) (frameBase sp + 8#32).toNat state.s0 ∧
      WordAt (pushed memory sp state) (frameBase sp + 4#32).toNat state.s1 ∧
      WordAt (pushed memory sp state) (frameBase sp + 0#32).toNat state.s2 := by
  obtain ⟨a12, a8, a4, a0⟩ := frameAddresses fits
  unfold pushed
  refine ⟨?_, ?_, ?_, wordAtStore _ _ _⟩
  · exact (((wordAtStore _ _ _).storeOther (by rw [a12, a8]; omega)).storeOther
      (by rw [a12, a4]; omega)).storeOther (by rw [a12, a0]; omega)
  · exact ((wordAtStore _ _ _).storeOther (by rw [a8, a4]; omega)).storeOther (by rw [a8, a0]; omega)
  · exact (wordAtStore _ _ _).storeOther (by rw [a4, a0]; omega)

-- The stores before the last one also stay inside the frame.
theorem partialOutside (memory : ByteMemory) (state : Snapshot) (fits : 16 ≤ sp.toNat) (byte : Nat)
    (outside : byte < sp.toNat - 16 ∨ sp.toNat ≤ byte) :
    (storeWord memory (frameBase sp + 12#32).toNat state.ra)[byte]? = memory[byte]? ∧
      (storeWord (storeWord memory (frameBase sp + 12#32).toNat state.ra)
        (frameBase sp + 8#32).toNat state.s0)[byte]? = memory[byte]? ∧
      (storeWord (storeWord (storeWord memory (frameBase sp + 12#32).toNat state.ra)
        (frameBase sp + 8#32).toNat state.s0) (frameBase sp + 4#32).toNat state.s1)[byte]? =
          memory[byte]? := by
  obtain ⟨a12, a8, a4, -⟩ := frameAddresses fits
  refine ⟨?_, ?_, ?_⟩
  · rw [storeWordOutside _ _ _ _ (by rw [a12]; omega)]
  · rw [storeWordOutside _ _ _ _ (by rw [a8]; omega), storeWordOutside _ _ _ _ (by rw [a12]; omega)]
  · rw [storeWordOutside _ _ _ _ (by rw [a4]; omega), storeWordOutside _ _ _ _ (by rw [a8]; omega),
      storeWordOutside _ _ _ _ (by rw [a12]; omega)]

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
    (agrees : ∀ byte, byte < sp.toNat - 16 ∨ sp.toNat ≤ byte → memory[byte]? = original.mem[byte]?) :
    CodeImage instructions base { original with mem := memory } :=
  environment.code.withMemory memory fun byte low high => by
    have apart := stack.apartCode
    unfold outsideFrame at apart
    change byte < base.toNat + 4 * 36 at high
    exact agrees byte (by omega)

private def saved (initial : Snapshot) : Snapshot :=
  { initial with pc := 0x14#32, sp := frameBase initial.sp }

private theorem prologue (environment : Environment base returnAddress original)
    (initial : Snapshot) (stack : Stack base original call initial.sp) :
    run 5 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := pushed original.mem initial.sp initial } (saved initial)) := by
  have machine := environment.mode.toMachineState
  have fits := stack.fits
  have image (memory : ByteMemory) (agrees : ∀ byte, byte < initial.sp.toNat - 16 ∨
      initial.sp.toNat ≤ byte → memory[byte]? = original.mem[byte]?) :=
    imageAt environment stack memory agrees
  have parts := partialOutside original.mem initial fits
  refine runStep (step00 machine (image original.mem fun _ _ => rfl) _ rfl) ?_
  refine runStep (step04 machine (image original.mem fun _ _ => rfl) _ rfl
    (stack.writable 12 (by decide))) ?_
  refine runStep (step08 machine (image _ fun byte outside => (parts byte outside).1) _ rfl
    (stack.writable 8 (by decide))) ?_
  refine runStep (step0c machine (image _ fun byte outside => (parts byte outside).2.1) _ rfl
    (stack.writable 4 (by decide))) ?_
  refine runStep (step10 machine (image _ fun byte outside => (parts byte outside).2.2) _ rfl
    (stack.writable 0 (by decide))) ?_
  rfl

-- Restoring the frame from `0x78` and returning takes six instructions.
private theorem epilogue (environment : Environment base returnAddress original)
    (initial : Snapshot) (stack : Stack base original call initial.sp)
    (returnArgument : initial.ra = returnAddress) (state : Snapshot)
    (atEpilogue : state.pc = 0x78#32) (lowered : state.sp = frameBase initial.sp) :
    run 6 (sync base { original with mem := pushed original.mem initial.sp initial } state) =
      some (sync base { original with mem := pushed original.mem initial.sp initial }
        { state with
          pc := returnAddress - base, ra := initial.ra, s0 := initial.s0, s1 := initial.s1,
          s2 := initial.s2, sp := initial.sp }) := by
  have machine := environment.mode.toMachineState
  have fits := stack.fits
  have image := imageAt environment stack _ (pushedOutside original.mem initial fits)
  obtain ⟨ra, s0, s1, s2⟩ := savedWords original.mem initial fits
  have restored : frameBase initial.sp + 16#32 = initial.sp := by
    unfold frameBase
    rw [offsetAdd initial.sp _ _ 0#32 rfl, BitVec.add_zero]
  refine runStep (step78 machine image state atEpilogue _
    (lowered ▸ stack.readable 12 (by decide)) (lowered ▸ ra)) ?_
  refine runStep (step7c machine image _ rfl _
    (lowered ▸ stack.readable 8 (by decide)) (lowered ▸ s0)) ?_
  refine runStep (step80 machine image _ rfl _
    (lowered ▸ stack.readable 4 (by decide)) (lowered ▸ s1)) ?_
  refine runStep (step84 machine image _ rfl _
    (lowered ▸ stack.readable 0 (by decide)) (lowered ▸ s2)) ?_
  refine runStep (step88 machine image _ rfl) ?_
  refine runStep (step8c machine image _ rfl returnAddress returnArgument
    environment.mode.returnLow environment.mode.returnNext) ?_
  simp only [lowered, restored]
  rfl

-- The search's snapshot, from the routine's argument registers.
private def searchEntry (state : Snapshot) : Search.Snapshot :=
  { a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4 }

private def afterSearch (state : Snapshot) (endState : Search.Snapshot) : Snapshot :=
  { state with
    pc := 0x38#32, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2, a3 := endState.a3,
    a4 := endState.a4 }

private theorem searchInside : ∀ index ∈ tracked Search.Snapshot, index ∈ tracked Snapshot := by
  decide

-- From `0x28`, the call to `sorted_map_lower_bound` and its return.
private theorem searchCall (environment : Environment base returnAddress original)
    (initial : Snapshot) (stack : Stack base original call initial.sp)
    (header : RawVec.Remove.Header original call.vector)
    (keys : 0 < call.length.toNat → Search.Keys original call.search)
    (state : Snapshot) (atCall : state.pc = 0x28#32) (headerArgument : state.a0 = call.header)
    (keyArgument : state.a1 = call.key) :
    ∃ endState : Search.Snapshot,
      run (4 + call.search.count .lower)
          (sync base { original with mem := pushed original.mem initial.sp initial } state) =
        some (sync base { original with mem := pushed original.mem initial.sp initial }
          (afterSearch { state with s0 := state.a1, s2 := state.a0, ra := base + 0x38#32 } endState)) ∧
      endState.a0 = BitVec.ofNat 32 call.position := by
  let memory := pushed original.mem initial.sp initial
  have machine := environment.mode.toMachineState
  have fits := stack.fits
  have image := imageAt environment stack _ (pushedOutside original.mem initial fits)
  let called : Snapshot :=
    { state with pc := searchOffset, s0 := state.a1, s2 := state.a0, ra := base + 0x38#32 }
  have entering : run 4 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } called) :=
    runStep (step28 machine image _ atCall) (runStep (step2c machine image _ rfl)
      (runStep (step30 machine image _ rfl) (runStep (step34 machine image _ rfl rfl) rfl)))
  let entered := sync base { original with mem := memory } called
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame called _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have enteredMem : entered.mem = memory := syncMem called
  have routineEntered : entered = sync (searchBase base) entered { searchEntry called with pc := 0 } :=
    (syncInside base (searchBase base) called called (searchEntry called) searchInside
      (fun index _ => by fin_cases index <;> rfl) (BitVec.add_zero _).symm).symm
  have returnAligned : (base + 0x38#32).toNat % 4 = 0 := alignedTargetNat environment.code.aligned _ (by decide)
  obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
  have mode : MachineMode entered (base + 0x38#32) :=
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
    (base + 0x38#32) entered call.search (searchEntry called) routineEntered (by
      change state.a0 = call.header; exact headerArgument) (by
      change state.a1 = call.key; exact keyArgument)
    (Search.Environment.ofMachine mode searchImage) searchHeader searchKeys
  refine ⟨endState, ?_, result⟩
  have back : run (call.search.count .lower) entered =
      some (sync base { original with mem := memory }
        (afterSearch { state with s0 := state.a1, s2 := state.a0, ra := base + 0x38#32 } endState)) := by
    rw [ran]
    refine congrArg some (syncInside base (searchBase base) called _ endState searchInside
      (fun index _ => by fin_cases index <;> rfl) ?_)
    change base + 0x38#32 = searchBase base + endState.pc
    rw [endPc, BitVec.add_comm (searchBase base), BitVec.sub_add_cancel]
  rw [runAdd, entering, Option.bind_some, back]

-- The removal's snapshot, from the routine's argument registers.
private def vectorEntry (state : Snapshot) : PairRemove.Snapshot :=
  { a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4, a5 := state.a5 }

private theorem vectorInside : ∀ index ∈ tracked PairRemove.Snapshot, index ∈ tracked Snapshot := by
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

private theorem readA0 (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).regs.get? Register.x10 = some state.a0 :=
  readReg_succ.mp (syncRead state (index := 10) (by decide))

-- Every register the routine restores, or never writes, keeps its value.
private theorem frameRegisters (base : Word) (original : Machine) (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 }) (memory : ByteMemory)
    (state : Snapshot) (ra : state.ra = initial.ra) (sp : state.sp = initial.sp)
    (s0 : state.s0 = initial.s0) (s1 : state.s1 = initial.s1) (s2 : state.s2 = initial.s2) :
    ∀ register ∉ [Register.PC, .nextPC, .x6, .x10, .x11, .x12, .x13, .x14, .x15],
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
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨pc, next, t1, a0, a1, a2, a3, a4, a5⟩ := outside
  refine syncFrame state register pc next ?_
  intro index member
  change index ∈ ([1, 2, 6, 8, 9, 10, 11, 12, 13, 14, 15, 18] : List (Fin 32)) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Ne.symm isRa, Ne.symm isSp, Ne.symm t1, Ne.symm isS0, Ne.symm isS1, Ne.symm a0,
    Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5, Ne.symm isS2]

end Run

/-! ## Guarantees -/

/-- The run as a snapshot: the routine returns with the saved registers
restored and the status in `a0`. Composing callers continue from this
snapshot. -/
theorem sortedMapRemoveSailRun (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (keyArgument : initial.a1 = call.key)
    (environment : Environment base returnAddress original)
    (header : RawVec.Remove.Header original call.vector)
    (stack : Stack base original call initial.sp)
    (keys : call.lengthValid → 0 < call.length.toNat → Search.Keys original call.search)
    (buffer : call.removes → PairRemove.Buffer (vectorBase base) original call.vector) :
    ∃ (state : Snapshot) (memory : ByteMemory),
      run call.count original = some (sync base { original with mem := memory } state) ∧
      state.pc = returnAddress - base ∧ state.a0 = call.status ∧
      state.ra = initial.ra ∧ state.sp = initial.sp ∧ state.s0 = initial.s0 ∧
      state.s1 = initial.s1 ∧ state.s2 = initial.s2 ∧
      (¬ call.removes → memory = pushed original.mem initial.sp initial) ∧
      (call.removes →
        WordAt memory call.header.toNat call.data ∧
        WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - 1)) ∧
        WordAt memory (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat - 1 →
          PairAt memory (call.vector.slot index) (call.vector.result index)) ∧
        call.vector.unchanged (pushed original.mem initial.sp initial) memory) := by
  let memory := pushed original.mem initial.sp initial
  have machine := environment.mode.toMachineState
  have fits := stack.fits
  have image := imageAt environment stack _ (pushedOutside original.mem initial fits)
  have returnArgument : initial.ra = returnAddress := by
    have stored := readReg_succ.mp environment.mode.ra
    rw [entry, readRa] at stored
    exact Option.some.inj stored
  have headerFits : call.header.toNat + 12 ≤ 2 ^ 32 := header.fits
  have headerApart := stack.apartHeader
  unfold outsideFrame at headerApart
  have headerAddress (offset : Nat) (small : offset ≤ 8) :
      (call.header + BitVec.ofNat 32 offset).toNat = call.header.toNat + offset :=
    RawVec.Remove.headerOffset header offset small
  have originalLength : WordAt original.mem (call.header.toNat + 4) call.length := header.lengthWord
  have originalCapacity : WordAt original.mem (call.header.toNat + 8) call.capacity :=
    header.capacityWord
  have lengthWord : WordAt memory (call.header.toNat + 4) call.length :=
    pushedWord initial fits originalLength (by unfold outsideFrame; omega)
  have capacityWord : WordAt memory (call.header.toNat + 8) call.capacity :=
    pushedWord initial fits originalCapacity (by unfold outsideFrame; omega)
  have begun := prologue environment initial stack
  -- The length check, from `0x14`.
  let checked : Snapshot := { saved initial with pc := 0x1c#32, s1 := call.length, a2 := call.capacity }
  have checking : run 2 (sync base { original with mem := memory } (saved initial)) =
      some (sync base { original with mem := memory } checked) := by
    refine runStep (step14 machine image _ rfl _ (headerArgument ▸ header.lengthReadable) ?_)
      (runStep (step18 machine image _ rfl _ (headerArgument ▸ header.capacityReadable) ?_) rfl)
    · have address : (call.header + 4#32).toNat = call.header.toNat + 4 := headerAddress 4 (by decide)
      change WordAt memory (initial.a0 + 4#32).toNat call.length
      rw [headerArgument, address]; exact lengthWord
    · have address : (call.header + 8#32).toNat = call.header.toNat + 8 := headerAddress 8 (by decide)
      change WordAt memory (initial.a0 + 8#32).toNat call.capacity
      rw [headerArgument, address]; exact capacityWord
  have lowered : (saved initial).sp = frameBase initial.sp := rfl
  -- Every path that returns itself ends with the epilogue at `0x78`.
  have returning (state : Snapshot) (atEpilogue : state.pc = 0x78#32)
      (frame : state.sp = frameBase initial.sp) (status : state.a0 = call.status)
      (count : Nat) (ran : run count (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } state)) (total : count + 6 = call.count)
      (notRemoves : ¬ call.removes) :
      ∃ (state : Snapshot) (memory : ByteMemory),
        run call.count original = some (sync base { original with mem := memory } state) ∧
        state.pc = returnAddress - base ∧ state.a0 = call.status ∧
        state.ra = initial.ra ∧ state.sp = initial.sp ∧ state.s0 = initial.s0 ∧
        state.s1 = initial.s1 ∧ state.s2 = initial.s2 ∧
        (¬ call.removes → memory = pushed original.mem initial.sp initial) ∧
        (call.removes →
          WordAt memory call.header.toNat call.data ∧
          WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - 1)) ∧
          WordAt memory (call.header.toNat + 8) call.capacity ∧
          (∀ index, index < call.length.toNat - 1 →
            PairAt memory (call.vector.slot index) (call.vector.result index)) ∧
          call.vector.unchanged (pushed original.mem initial.sp initial) memory) := by
    have finish := epilogue environment initial stack returnArgument state atEpilogue frame
    let done : Snapshot :=
      { state with
        pc := returnAddress - base, ra := initial.ra, s0 := initial.s0, s1 := initial.s1,
        s2 := initial.s2, sp := initial.sp }
    refine ⟨done, memory, ?_, rfl, status, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
      fun removes => (notRemoves removes).elim⟩
    rw [← total, runAdd, (congrArg (run count) entry).trans ran, Option.bind_some, finish]
  by_cases lengthValid : call.lengthValid
  case neg =>
    -- `length > capacity`: `li a0, 3`, `j`, and the epilogue.
    have notRemoves : ¬ call.removes := fun removes => lengthValid removes.1
    have branch : ¬ call.length.toNat ≤ call.capacity.toNat := lengthValid
    exact returning
      { checked with pc := 0x78#32, a0 := 3#32 } rfl rfl
      (by simp [Call.status, lengthValid]) 10 (by
        rw [show 10 = 5 + (2 + 3) from rfl, runAdd, begun, Option.bind_some, runAdd, checking,
          Option.bind_some]
        refine runStep (step1c machine image _ rfl) ?_
        simp only [checked, branch, if_false]
        exact runStep (step20 machine image _ rfl) (runStep (step24 machine image _ rfl) rfl))
      (by simp [Call.count, lengthValid]) notRemoves
  -- The search call.
  have branch : call.length.toNat ≤ call.capacity.toNat := lengthValid
  let calling : Snapshot := { checked with pc := 0x28#32 }
  have toCall : run 8 (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } calling) := by
    rw [show 8 = 5 + (2 + 1) from rfl, runAdd, begun, Option.bind_some, runAdd, checking,
      Option.bind_some]
    refine runStep (step1c machine image _ rfl) ?_
    simp only [checked, branch, if_true]
    rfl
  obtain ⟨endState, searched, position⟩ := searchCall environment initial stack header
    (keys lengthValid) calling rfl headerArgument keyArgument
  let back := afterSearch { calling with s0 := calling.a1, s2 := calling.a0, ra := base + 0x38#32 }
    endState
  have toBack : run (8 + (4 + call.search.count .lower)) (sync base original { initial with pc := 0 }) =
      some (sync base { original with mem := memory } back) := by
    rw [runAdd, toCall, Option.bind_some, searched]
  have backKey : back.s0 = call.key := keyArgument
  have backHeader : back.s2 = call.header := headerArgument
  have backLength : back.s1 = call.length := rfl
  have backSp : back.sp = frameBase initial.sp := rfl
  have positionWord : back.a0 = BitVec.ofNat 32 call.position := position
  have positionNat : (BitVec.ofNat 32 call.position).toNat = call.position := call.vectorIndex
  -- `mv a1, a0`, `li a0, 5`, and the position check.
  let compared : Snapshot := { back with pc := 0x40#32, a1 := back.a0, a0 := 5#32 }
  have toCompare : run 2 (sync base { original with mem := memory } back) =
      some (sync base { original with mem := memory } compared) :=
    runStep (step38 machine image _ rfl) (runStep (step3c machine image _ rfl) rfl)
  by_cases inside : call.position < call.length.toNat
  case neg =>
    have notRemoves : ¬ call.removes := fun removes => inside removes.2.1
    have taken : compared.s1.toNat ≤ compared.a1.toNat := by
      show call.length.toNat ≤ back.a0.toNat
      rw [positionWord, positionNat]; omega
    exact returning
      { compared with pc := 0x78#32 } rfl rfl
      (by simp [Call.status, lengthValid, notRemoves]; rfl) (8 + (4 + call.search.count .lower) + 3) (by
        rw [runAdd, toBack, Option.bind_some, show 3 = 2 + 1 from rfl, runAdd, toCompare,
          Option.bind_some]
        refine runStep (step40 machine image _ rfl) ?_
        rw [if_pos taken]
        rfl)
      (by simp [Call.count, lengthValid, notRemoves, inside]; omega) notRemoves
  -- The key comparison at the position.
  have given := keys lengthValid (by omega)
  have notTaken : ¬ compared.s1.toNat ≤ compared.a1.toNat := by
    show ¬ call.length.toNat ≤ back.a0.toNat
    rw [positionWord, positionNat]; omega
  have dataRead : Readable original compared.s2 := backHeader ▸ given.dataReadable
  have originalData : WordAt original.mem call.header.toNat call.data := given.dataWord
  have dataWordHeader : WordAt memory call.header.toNat call.data :=
    pushedWord initial fits originalData (by unfold outsideFrame; omega)
  have dataWord : WordAt memory compared.s2.toNat call.data := by
    show WordAt memory back.s2.toNat call.data
    rw [backHeader]
    exact dataWordHeader
  let addressed : Snapshot :=
    { compared with
      pc := 0x50#32, a3 := call.search.wordSlot call.position, a4 := compared.a1 <<< (3 : Nat) }
  have slot : call.data + compared.a1 <<< (3 : Nat) = call.search.wordSlot call.position := by
    show call.data + back.a0 <<< (3 : Nat) = _
    have shifted := call.search.slotShift (BitVec.ofNat 32 call.position)
    rw [positionNat] at shifted
    rw [positionWord, BitVec.add_comm]
    exact shifted
  have keyRead : Readable original addressed.a3 := given.readable call.position inside
  have keyWord : WordAt memory addressed.a3.toNat (call.old call.position).key := by
    show WordAt memory (call.search.wordSlot call.position).toNat _
    rw [Search.slotNat given inside]
    have apart := stack.apartEntries call.position inside
    unfold outsideFrame at apart
    exact pushedWord initial fits (given.keyWord call.position inside) (by unfold outsideFrame; omega)
  let loaded : Snapshot := { addressed with pc := 0x54#32, a3 := (call.old call.position).key }
  have toLoaded : run 5 (sync base { original with mem := memory } compared) =
      some (sync base { original with mem := memory } loaded) := by
    refine runStep (step40 machine image _ rfl) ?_
    rw [if_neg notTaken]
    refine runStep (step44 machine image _ rfl _ dataRead dataWord) ?_
    refine runStep (step48 machine image _ rfl) (runStep (step4c machine image _ rfl) ?_)
    rw [show call.data + compared.a1 <<< (3 : Nat) = call.search.wordSlot call.position from slot]
    exact runStep (step50 machine image addressed rfl _ keyRead keyWord) rfl
  have toLoadedAll : run (8 + (4 + call.search.count .lower) + 7)
      (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := memory } loaded) := by
    rw [runAdd, toBack, Option.bind_some, show 7 = 2 + 5 from rfl, runAdd, toCompare,
      Option.bind_some, toLoaded]
  by_cases keyMatches : (call.old call.position).key = call.key
  case neg =>
    have notRemoves : ¬ call.removes := fun removes => keyMatches removes.2.2
    have differs : ¬ loaded.a3 = loaded.s0 := by
      show ¬ (call.old call.position).key = back.s0
      rw [backKey]; exact keyMatches
    exact returning
      { loaded with pc := 0x78#32 } rfl rfl
      (by simp [Call.status, lengthValid, notRemoves]; rfl) (8 + (4 + call.search.count .lower) + 7 + 1) (by
        rw [runAdd, toLoadedAll, Option.bind_some]
        refine runStep (step54 machine image _ rfl) ?_
        rw [if_neg differs]
        rfl)
      (by simp [Call.count, lengthValid, notRemoves, inside]; omega) notRemoves
  -- The key matches: restore the frame and tail-call `raw_vec_pair_remove`.
  have removes : call.removes := ⟨lengthValid, inside, keyMatches⟩
  have same : loaded.a3 = loaded.s0 := by
    show (call.old call.position).key = back.s0
    rw [backKey]; exact keyMatches
  obtain ⟨ra, s0, s1, s2⟩ := savedWords original.mem initial fits
  have restored : frameBase initial.sp + 16#32 = initial.sp := by
    unfold frameBase
    rw [offsetAdd initial.sp _ _ 0#32 rfl, BitVec.add_zero]
  let jumped : Snapshot :=
    { loaded with
      pc := vectorOffset, a0 := call.header, ra := initial.ra, s0 := initial.s0, s1 := initial.s1,
      s2 := initial.s2, sp := initial.sp, t1 := base + 0x70#32 }
  have toJump : run 9 (sync base { original with mem := memory } loaded) =
      some (sync base { original with mem := memory } jumped) := by
    refine runStep (step54 machine image _ rfl) ?_
    rw [if_pos same]
    refine runStep (step58 machine image _ rfl) ?_
    refine runStep (step5c machine image _ rfl _ (stack.readable 12 (by decide))
      ra) ?_
    refine runStep (step60 machine image _ rfl _ (stack.readable 8 (by decide))
      s0) ?_
    refine runStep (step64 machine image _ rfl _ (stack.readable 4 (by decide))
      s1) ?_
    refine runStep (step68 machine image _ rfl _ (stack.readable 0 (by decide))
      s2) ?_
    refine runStep (step6c machine image _ rfl) (runStep (step70 machine image _ rfl)
      (runStep (step74 machine image _ rfl rfl) ?_))
    simp only [jumped, loaded, addressed, compared, backSp, restored, backHeader]
    rfl
  -- `raw_vec_pair_remove`, entered from `jumped`.
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
  have vectorImage : CodeImage PairRemove.instructions (vectorBase base) entered :=
    (environment.vectorCode.withMemory memory fun byte low high => by
      have apart := stack.apartVector
      unfold outsideFrame at apart
      change byte < (vectorBase base).toNat + 4 * 25 at high
      exact pushedOutside original.mem initial fits byte (by omega)).atSync base jumped
  have vectorHeader : RawVec.Remove.Header entered call.vector := by
    refine ⟨header.fits, mappedTransfer header.lengthReadable regions,
      mappedTransfer header.capacityReadable regions, ?_, ?_⟩
    · rw [enteredMem]; exact lengthWord
    · rw [enteredMem]; exact capacityWord
  have vectorBuffer (_ : call.vector.valid) : PairRemove.Buffer (vectorBase base) entered call.vector := by
    have given := buffer removes
    refine ⟨given.fits, mappedTransfer given.dataReadable regions, ?_,
      mappedTransfer given.lengthWritable regions, given.lengthAwayFromCode, fun index bound => ?_,
      fun index low high => ?_, fun index low high => ?_, given.separated, given.awayFromCode⟩
    · rw [enteredMem]; exact dataWordHeader
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
  obtain ⟨endState, vectorMemory, vectorRan, endPc, vectorStatus, -, accepted⟩ :=
    PairRemove.rawVecPairRemoveSailRun (vectorBase base) returnAddress entered call.vector
      (vectorEntry jumped) routineEntered rfl (by change back.a0 = _; exact positionWord)
      (PairRemove.Environment.ofMachine mode vectorImage) vectorHeader vectorBuffer
  have valid := call.vectorValid removes
  have total : call.count = 8 + (4 + call.search.count .lower) + 7 + 9 + call.vector.count := by
    simp only [Call.count, lengthValid, removes, if_true, not_true_eq_false, if_false]
    omega
  -- Express the vector routine's end state in this routine's snapshot.
  let merged : Snapshot :=
    { jumped with
      pc := returnAddress - base, a0 := endState.a0, a1 := endState.a1, a2 := endState.a2,
      a3 := endState.a3, a4 := endState.a4, a5 := endState.a5 }
  have resynced : sync (vectorBase base) { entered with mem := vectorMemory } endState =
      sync base { original with mem := vectorMemory } merged := by
    have withMem := syncWithMem base { original with mem := memory } jumped vectorMemory
    have inside := syncInside (frame := { original with mem := vectorMemory }) base (vectorBase base)
      jumped merged endState vectorInside (fun index _ => by fin_cases index <;> rfl) (by
        change base + (returnAddress - base) = vectorBase base + endState.pc
        rw [endPc, BitVec.add_comm base, BitVec.sub_add_cancel, BitVec.add_comm (vectorBase base),
          BitVec.sub_add_cancel])
    change sync (vectorBase base) { sync base { original with mem := memory } jumped with
      mem := vectorMemory } endState = _
    rw [withMem]
    exact inside
  refine ⟨merged, vectorMemory, ?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl,
    fun notRemoves => (notRemoves removes).elim, fun _ => ?_⟩
  · rw [total, runAdd, runAdd, (congrArg (run _) entry).trans toLoadedAll, Option.bind_some, toJump,
      Option.bind_some, ← resynced]
    exact vectorRan
  · have capacityOk : ¬ call.vector.capacity.toNat < call.vector.length.toNat := by
      change ¬ call.capacity.toNat < call.length.toNat; exact Nat.not_lt.mpr lengthValid
    have indexOk : ¬ call.vector.length.toNat ≤ call.vector.index.toNat := by
      rw [call.vectorIndex]; change ¬ call.length.toNat ≤ call.position; omega
    change endState.a0 = call.status
    rw [vectorStatus, RawVec.Remove.Call.status, if_neg capacityOk, if_neg indexOk]
    simp [Call.status, lengthValid, removes]
  · obtain ⟨data, length, capacity, entries, unchanged⟩ := accepted valid
    rw [enteredMem] at unchanged
    exact ⟨data, length, capacity, entries, unchanged⟩

theorem sortedMapRemoveSailCorrect (base returnAddress : Word) (original : Machine) (call : Call)
    (initial : Snapshot)
    (entry : original = sync base original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (keyArgument : initial.a1 = call.key)
    (environment : Environment base returnAddress original)
    (header : RawVec.Remove.Header original call.vector)
    (stack : Stack base original call initial.sp)
    (keys : call.lengthValid → 0 < call.length.toNat → Search.Keys original call.search)
    (buffer : call.removes → PairRemove.Buffer (vectorBase base) original call.vector) :
    ∃ final, run call.count original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.removes → final.mem = pushed original.mem initial.sp initial) ∧
      (call.removes →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat - 1 →
          PairAt final.mem (call.vector.slot index) (call.vector.result index)) ∧
        call.vector.unchanged (pushed original.mem initial.sp initial) final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x6, .x10, .x11, .x12, .x13, .x14, .x15],
        final.regs.get? register = original.regs.get? register) := by
  obtain ⟨state, memory, ran, pc, status, ra, sp, s0, s1, s2, rejected, accepted⟩ :=
    sortedMapRemoveSailRun base returnAddress original call initial entry headerArgument keyArgument
      environment header stack keys buffer
  refine ⟨_, ran, pcReadReturned base returnAddress _ state pc, ?_, fun notRemoves => ?_,
    fun removes => ?_, frameRegisters base original initial entry memory state ra sp s0 s1 s2⟩
  · rw [readA0]
    exact congrArg some status
  · rw [syncMem]
    exact rejected notRemoves
  · rw [syncMem]
    exact accepted removes

/-! ## Against the mathematical map

For a sorted map, the entries the removal leaves are the mathematical `erase`
of the old entries, and a call that returns `ABSENT` is one for which `erase`
changes nothing, so the key was not in the map.
-/

theorem sortedMapRemoveErases (call : Call) (sorted : Sorted (entriesOf call.old call.length.toNat)) :
    (call.removes → entriesOf call.vector.result (call.length.toNat - 1) =
        erase (entriesOf call.old call.length.toNat) call.key) ∧
      (call.lengthValid → ¬ call.removes →
        erase (entriesOf call.old call.length.toNat) call.key = entriesOf call.old call.length.toNat) := by
  let length := call.length.toNat
  let position := call.position
  have le : position ≤ length := call.position_le
  have split := lowerSplit call.key sorted
  have backSorted := sorted_entriesFrom le sorted
  have erased : erase (entriesOf call.old length) call.key =
      entriesOf call.old position ++ dropHead (entriesFrom call.old position (length - position)) call.key := by
    rw [entriesOf_split call.old le]
    exact erase_split split backSorted
  refine ⟨fun removes => ?_, fun lengthValid notRemoves => ?_⟩
  · have inside := removes.2.1
    rw [erased, show length - position = (length - position - 1) + 1 by omega, entriesFrom_succ,
      dropHead, if_pos removes.2.2, entriesOf_split call.vector.result (show position ≤ length - 1 by omega)]
    congr 1
    · apply entriesOf_congr
      intro index below
      simp only [RawVec.Remove.Call.result, call.vectorIndex]
      exact if_pos below
    · rw [show length - 1 - position = length - position - 1 by omega]
      unfold entriesFrom
      apply List.map_congr_left
      intro offset _
      simp only [RawVec.Remove.Call.result, call.vectorIndex]
      rw [if_neg (by omega)]
      change call.old (position + offset + 1) = call.old (position + 1 + offset)
      congr 1
      omega
  · rw [erased]
    by_cases inside : position < length
    · have differs : ¬ (call.old position).key = call.key := fun same =>
        notRemoves ⟨lengthValid, inside, same⟩
      rw [show length - position = (length - position - 1) + 1 by omega, entriesFrom_succ, dropHead,
        if_neg differs, ← entriesFrom_succ, show length - position - 1 + 1 = length - position by omega,
        ← entriesOf_split call.old le]
    · rw [show length - position = 0 by omega]
      simp [entriesFrom, dropHead, show position = length by omega]
      rfl

end Riscfree.SortedMap.Remove
