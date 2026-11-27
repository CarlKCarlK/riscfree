import PopcountSpec
import Riscfree.RV32.Decode
import Riscfree.RV32.Platform

/-!
# Linked RV32 popcount: bit loop

`popcount128` tests one bit per iteration. Sail decodes the linked
instructions, and Pico FV's equivalence theorems give their effects on the
registers. The bit and word loop invariants compose those steps into a proof
of the entire call. The ELF check uses the same words as the Sail decoder.
-/

namespace Riscfree

namespace Popcount

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 hiding Platform

/-! ## Sail decoding of the linked instruction words -/

section SailDecode

-- Each word is a little-endian instruction from the linked popcount128 symbol.
-- The right column records the Sail AST we expect its decoder to return.
def instructions : List (BitVec 32 × instruction) :=
  [ (0x00400293, .ITYPE (4, reg 0, reg 5, .ADDI))
  , (0x00000313, .ITYPE (0, reg 0, reg 6, .ADDI))
  , (0x00052383, .LOAD (0, reg 10, reg 7, false, 4))
  , (0x02000e13, .ITYPE (32, reg 0, reg 28, .ADDI))
  , (0x0013fe93, .ITYPE (1, reg 7, reg 29, .ANDI))
  , (0x01d30333, .RTYPE (reg 29, reg 6, reg 6, .ADD))
  , (0x0013d393, .SHIFTIOP (1, reg 7, reg 7, .SRLI))
  , (0xfffe0e13, .ITYPE (0xfff, reg 28, reg 28, .ADDI))
  , (0xfe0e18e3, .BTYPE (0x1ff0, reg 0, reg 28, .BNE))
  , (0x00450513, .ITYPE (4, reg 10, reg 10, .ADDI))
  , (0xfff28293, .ITYPE (0xfff, reg 5, reg 5, .ADDI))
  , (0xfc029ee3, .BTYPE (0x1fdc, reg 0, reg 5, .BNE))
  , (0x00030513, .ITYPE (0, reg 6, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions, ext_decode entry.1 state = .ok entry.2 state := by
  decode_table instructions [privilege, landingPad]

#print axioms linkedWordsDecode

end SailDecode


/-! ## Proof snapshots and the Sail register frame -/

section SailState

-- A proof snapshot records the relative PC and the six registers the routine
-- updates. Byte memory and all other registers stay in the Sail frame.
structure Snapshot where
  pc : Word := 0
  a0 : Word
  t0 : Word := 0
  t1 : Word := 0
  t2 : Word := 0
  t3 : Word := 0
  t4 : Word := 0

instance : RegisterView Snapshot where
  tracked := [5, 6, 7, 10, 28, 29]
  pc state := state.pc
  value state index :=
    match index.val with
    | 5 => state.t0
    | 6 => state.t1
    | 7 => state.t2
    | 10 => state.a0
    | 28 => state.t3
    | 29 => state.t4
    | _ => 0
  distinct := by decide
  nonzero := by decide

@[simp] theorem viewPc (state : Snapshot) : RegisterView.pc state = state.pc := rfl

end SailState


/-! ## Code mapping, RAM, and processor assumptions -/

section SailPlatform

-- `RV32.Platform` states the assumptions. The routine reads only the four input words.
abbrev Platform (base : Word) (frame : Machine) (input returnAddress : Word) (memory : Memory) : Prop :=
  RV32.Platform Snapshot instructions base frame (inputAddresses input) returnAddress memory

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}

-- Select the actual Sail decoding before considering the effect of the instruction.
theorem fetchAndDecode (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (index : Fin instructions.length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base frame state) =
        .ok (.F_Base instructions[index.val].1) (sync base frame state) ∧
      ext_decode instructions[index.val].1 (sync base frame state) =
        .ok instructions[index.val].2 (sync base frame state) :=
  platform.fetchAndDecode
    (fun state => linkedWordsDecode _ (platform.privilegeAt state) (platform.landingPadAt state))
    (by decide) state index pc

end SailPlatform


/-! ## Effects of the linked instructions -/

section SailInstructions

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}
variable (platform : Platform base frame input returnAddress memory)
include platform

private theorem initializeWordCounter (state : Snapshot) (atPC : state.pc = 0#32) :
    step (sync base frame state) = some (sync base frame { state with pc := 4, t0 := 4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨0, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

private theorem clearTotal (state : Snapshot) (atPC : state.pc = 4#32) :
    step (sync base frame state) = some (sync base frame { state with pc := 8, t1 := 0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨1, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

private theorem loadInputWord (state : Snapshot) (atPC : state.pc = 8#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 12, t2 := memory state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨2, by decide⟩ atPC
  exact platform.lw fetched decoded (syncRead state (by decide)) inRam
    (BitVec.add_zero _) (by decide) (by advance [viewPc, atPC])

private theorem initializeBitCounter (state : Snapshot) (atPC : state.pc = 12#32) :
    step (sync base frame state) = some (sync base frame { state with pc := 16, t3 := 32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨3, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

private theorem extractLowBit (state : Snapshot) (atPC : state.pc = 16#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 20, t4 := state.t2 &&& 1#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨4, by decide⟩ atPC
  exact Step.andi fetched decoded (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem addLowBit (state : Snapshot) (atPC : state.pc = 20#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 24, t1 := state.t1 + state.t4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨5, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (by decide)) (syncRead state (by decide))
    (by decide) (by advance [viewPc, atPC])

private theorem shiftWord (state : Snapshot) (atPC : state.pc = 24#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 28, t2 := state.t2 >>> (1 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨6, by decide⟩ atPC
  exact Step.srli fetched decoded (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem decrementBitCounter (state : Snapshot) (atPC : state.pc = 28#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 32, t3 := state.t3 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨7, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem branchOnBitCounter (state : Snapshot) (atPC : state.pc = 32#32) :
    step (sync base frame state) = some (sync base frame
      { state with pc := if state.t3 = 0#32 then 36#32 else 16#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨8, by decide⟩ atPC
  exact platform.bne fetched decoded (syncRead state (by decide)) rfl
    (by rw [viewPc, atPC]; decide) (by advance [viewPc, atPC])

private theorem advanceInput (state : Snapshot) (atPC : state.pc = 36#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 40, a0 := state.a0 + 4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨9, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem decrementWordCounter (state : Snapshot) (atPC : state.pc = 40#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 44, t0 := state.t0 + 0xffffffff#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨10, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem branchOnWordCounter (state : Snapshot) (atPC : state.pc = 44#32) :
    step (sync base frame state) = some (sync base frame
      { state with pc := if state.t0 = 0#32 then 48#32 else 8#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨11, by decide⟩ atPC
  exact platform.bne fetched decoded (syncRead state (by decide)) rfl
    (by rw [viewPc, atPC]; decide) (by advance [viewPc, atPC])

private theorem moveTotalToA0 (state : Snapshot) (atPC : state.pc = 48#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 52, a0 := state.t1 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨12, by decide⟩ atPC
  exact Step.mv fetched decoded (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem returnToCaller (state : Snapshot) (atPC : state.pc = 52#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨13, by decide⟩ atPC
  exact platform.ret fetched decoded (by decide) (by advance [viewPc])

end SailInstructions


/-! ## Bit and word loop invariants -/

section LoopInvariants

def bitNextPc (counter : Word) : Word :=
  if counter = 0#32 then 36#32 else 16#32

theorem addDecrement (word : Word) : word + 0xffffffff#32 = word - 1#32 := by
  rw [BitVec.sub_eq_add_neg]
  congr 1

def bitUpdate (state : Snapshot) : Snapshot :=
  let counter := state.t3 - 1#32
  { state with
    pc := bitNextPc counter
    t1 := state.t1 + (state.t2 &&& 1#32)
    t2 := state.t2 >>> (1 : Nat)
    t3 := counter
    t4 := state.t2 &&& 1#32 }

@[irreducible] def bitScan (remaining : Nat) : Snapshot → Snapshot :=
  Nat.rec (fun state => state) (fun _ previous state => previous (bitUpdate state)) remaining

@[simp] theorem bitScanZero (state : Snapshot) : bitScan 0 state = state := by unfold bitScan; rfl

@[simp] theorem bitScanSucc (remaining : Nat) (state : Snapshot) :
    bitScan (remaining + 1) state = bitScan remaining (bitUpdate state) := by unfold bitScan; rfl

theorem bitCounterNext (state : Snapshot) (remaining : Nat)
    (counter : state.t3 = BitVec.ofNat 32 (remaining + 1)) :
    (bitUpdate state).t3 = BitVec.ofNat 32 remaining := by
  simp only [bitUpdate, counter, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ 1#32

theorem bitPcNext (state : Snapshot) (remaining : Nat)
    (counter : (bitUpdate state).t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) :
    (bitUpdate state).pc = (if remaining = 0 then 36#32 else 16#32) := by
  simp only [bitUpdate] at counter
  simp only [bitUpdate, bitNextPc, counter]
  by_cases empty : remaining = 0
  · simp [empty]
  · have small : remaining < 2 ^ 32 := by omega
    have nonzero : BitVec.ofNat 32 remaining ≠ 0#32 := by
      intro equal
      have value := congrArg BitVec.toNat equal
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, BitVec.toNat_zero] at value
      exact empty value
    simp only [empty, nonzero, if_false]

theorem bitLoopExit (remaining : Nat) (state : Snapshot)
    (counter : state.t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) (positive : 0 < remaining) :
    (bitScan remaining state).pc = 36#32 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining previous =>
    rw [bitScanSucc]
    have nextCounter := bitCounterNext state remaining counter
    by_cases empty : remaining = 0
    · simpa [empty] using bitPcNext state remaining nextCounter (by omega)
    exact previous (bitUpdate state) nextCounter (by omega) (by omega)

theorem bitScanPreserves (project : Snapshot → α)
    (unchanged : ∀ state, project (bitUpdate state) = project state)
    (remaining : Nat) (state : Snapshot) :
    project (bitScan remaining state) = project state := by
  induction remaining generalizing state with
  | zero => rw [bitScanZero]
  | succ remaining previous =>
    rw [bitScanSucc, previous, unchanged]

theorem bitKeepsPointer (state : Snapshot) : (bitUpdate state).a0 = state.a0 := by
  simp only [bitUpdate]

theorem bitKeepsWordCount (state : Snapshot) : (bitUpdate state).t0 = state.t0 := by
  simp only [bitUpdate]

theorem bitScanTotal (remaining : Nat) (state : Snapshot) :
    (bitScan remaining state).t1 = scan remaining state.t2 state.t1 := by
  induction remaining generalizing state with
  | zero => rw [bitScanZero, scan]
  | succ remaining previous =>
    rw [bitScanSucc, previous, scan.eq_2]
    rfl

def advanceWord (state : Snapshot) : Snapshot :=
  { state with pc := if state.t0 - 1#32 = 0#32 then 48#32 else 8#32
               a0 := state.a0 + 4, t0 := state.t0 - 1#32 }

def loadedWord (memory : Memory) (state : Snapshot) : Snapshot :=
  { state with pc := 16#32, t2 := memory state.a0, t3 := 32#32 }

theorem loadedPc (memory : Memory) (state : Snapshot) : (loadedWord memory state).pc = 16#32 := by simp [loadedWord]

theorem loadedCounter (memory : Memory) (state : Snapshot) :
    (loadedWord memory state).t3 = BitVec.ofNat 32 32 := by simp [loadedWord]

theorem loadedExit (memory : Memory) (state : Snapshot) : (bitScan 32 (loadedWord memory state)).pc = 36#32 :=
  bitLoopExit 32 (loadedWord memory state) (loadedCounter memory state) (by decide) (by decide)

@[irreducible] def wordResult (memory : Memory) (state : Snapshot) : Snapshot :=
  advanceWord (bitScan 32 (loadedWord memory state))

@[simp] theorem wordResultPc (memory : Memory) (state : Snapshot) :
    (wordResult memory state).pc = (if state.t0 - 1#32 = 0#32 then 48#32 else 8#32) := by
  have words := bitScanPreserves Snapshot.t0 bitKeepsWordCount 32 (loadedWord memory state)
  simp only [wordResult, advanceWord, words]
  simp only [loadedWord]

@[simp] theorem wordResultT0 (memory : Memory) (state : Snapshot) : (wordResult memory state).t0 = state.t0 - 1#32 := by
  have words := bitScanPreserves Snapshot.t0 bitKeepsWordCount 32 (loadedWord memory state)
  simp only [wordResult, advanceWord, words]
  simp only [loadedWord]

@[simp] theorem wordResultA0 (memory : Memory) (state : Snapshot) : (wordResult memory state).a0 = state.a0 + 4 := by
  have pointer := bitScanPreserves Snapshot.a0 bitKeepsPointer 32 (loadedWord memory state)
  simp only [wordResult, advanceWord, pointer]
  simp only [loadedWord]

@[simp] theorem wordResultT1 (memory : Memory) (state : Snapshot) :
    (wordResult memory state).t1 = scan 32 (memory state.a0) state.t1 := by
  simp only [wordResult, advanceWord, bitScanTotal, loadedWord]

end LoopInvariants


/-! ## Compose the Sail steps -/

section SailRun

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}
variable (platform : Platform base frame input returnAddress memory)

include platform

private theorem start (state : Snapshot) :
    RV32.run 2 (sync base frame { state with pc := 0 }) =
      some (sync base frame { state with pc := 8, t0 := 4, t1 := 0 }) := by
  have counter := initializeWordCounter platform { state with pc := 0 } rfl
  have total := clearTotal platform { state with pc := 4, t0 := 4 } rfl
  simp only [RV32.run, counter, total, Option.bind_some]

private theorem bitInstructions (state : Snapshot) (pc : state.pc = 16#32) :
    RV32.run 5 (sync base frame state) = some (sync base frame (bitUpdate state)) := by
  let masked := { state with pc := 20#32, t4 := state.t2 &&& 1#32 }
  let counted := { masked with pc := 24#32, t1 := masked.t1 + masked.t4 }
  let shifted := { counted with pc := 28#32, t2 := counted.t2 >>> (1 : Nat) }
  let decremented := { shifted with pc := 32#32, t3 := shifted.t3 + 0xffffffff#32 }
  have lowBit := extractLowBit platform state pc
  have total := addLowBit platform masked rfl
  have shift := shiftWord platform counted rfl
  have counter := decrementBitCounter platform shifted rfl
  have branch := branchOnBitCounter platform decremented rfl
  change RV32.step (sync base frame state) = some (sync base frame masked) at lowBit
  change RV32.step (sync base frame masked) = some (sync base frame counted) at total
  change RV32.step (sync base frame counted) = some (sync base frame shifted) at shift
  change RV32.step (sync base frame shifted) = some (sync base frame decremented) at counter
  simp only [RV32.run, lowBit, total, shift, counter, branch, Option.bind_some]
  simp only [decremented, shifted, counted, masked, bitUpdate, bitNextPc, addDecrement]

private theorem bitLoop (remaining : Nat) (state : Snapshot)
    (atBit : state.pc = 16#32) (counter : state.t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) :
    RV32.run (remaining * 5) (sync base frame state) =
      some (sync base frame (bitScan remaining state)) := by
  induction remaining generalizing state with
  | zero => simp [RV32.run]
  | succ remaining previous =>
    rw [show (remaining + 1) * 5 = 5 + remaining * 5 by omega, RV32.runAdd,
      bitInstructions platform state atBit, Option.bind_some, bitScanSucc]
    by_cases empty : remaining = 0
    · simp [empty, RV32.run]
    have nextCounter := bitCounterNext state remaining counter
    have nextPc := bitPcNext state remaining nextCounter (by omega)
    exact previous (bitUpdate state) (by simpa only [empty, if_false] using nextPc)
      nextCounter (by omega)

private theorem loadWord (state : Snapshot) (pc : state.pc = 8#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    RV32.run 2 (sync base frame state) = some (sync base frame (loadedWord memory state)) := by
  have word := loadInputWord platform state pc inRam
  have counter := initializeBitCounter platform { state with pc := 12, t2 := memory state.a0 } rfl
  simp only [RV32.run, word, counter, Option.bind_some, loadedWord]
  rfl

private theorem nextWord (state : Snapshot) (pc : state.pc = 36#32) :
    RV32.run 3 (sync base frame state) = some (sync base frame (advanceWord state)) := by
  let advanced := { state with pc := 40#32, a0 := state.a0 + 4 }
  let decremented := { advanced with pc := 44#32, t0 := advanced.t0 + 0xffffffff#32 }
  have pointer := advanceInput platform state pc
  have counter := decrementWordCounter platform advanced rfl
  have branch := branchOnWordCounter platform decremented rfl
  change RV32.step (sync base frame state) = some (sync base frame advanced) at pointer
  change RV32.step (sync base frame advanced) = some (sync base frame decremented) at counter
  simp only [RV32.run, pointer, counter, branch, Option.bind_some]
  simp only [advanceWord, decremented, advanced, addDecrement]

private theorem oneWord (state : Snapshot) (pc : state.pc = 8#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    RV32.run 165 (sync base frame state) = some (sync base frame (wordResult memory state)) := by
  have bits := bitLoop platform 32 (loadedWord memory state) (loadedPc memory state)
    (loadedCounter memory state) (by decide)
  rw [show 165 = 2 + (32 * 5 + 3) by decide, RV32.runAdd, loadWord platform state pc inRam,
    Option.bind_some, RV32.runAdd, bits, Option.bind_some, nextWord platform _ (loadedExit memory state)]
  rw [wordResult]

private theorem finish (state : Snapshot) (pc : state.pc = 48#32) :
    RV32.run 2 (sync base frame state) =
      some (sync base frame { state with a0 := state.t1, pc := returnAddress - base }) := by
  have result := moveTotalToA0 platform state pc
  have returned := returnToCaller platform { state with a0 := state.t1, pc := 52 } rfl
  simp only [RV32.run, result, returned, Option.bind_some]

end SailRun

/-! ## Correctness of the linked Sail execution -/

section Correctness

-- The four words of the input view agree with the bytes in Sail memory.
-- Only the six scratch registers and the two PC entries change.
theorem popcount128SailCorrect (base : Word) (machine : Machine) (initial : Snapshot)
    (memory : Memory) (returnAddress : Word)
    (entry : machine = sync base machine { initial with pc := 0 })
    (platform : Platform base machine initial.a0 returnAddress memory) :
    ∃ final, RV32.run 664 machine = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (final.regs.get? Register.x10).map BitVec.toNat =
        some (inputBits memory initial.a0).cpop.toNat ∧
      final.mem = machine.mem ∧
      ∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x7, .x10, .x28, .x29],
        final.regs.get? register = machine.regs.get? register := by
  let seed := { initial with pc := 8#32, t0 := 4#32, t1 := 0#32 }
  let first := wordResult memory seed
  let second := wordResult memory first
  let third := wordResult memory second
  let fourth := wordResult memory third
  let last := { fourth with a0 := fourth.t1, pc := returnAddress - base }
  have setup : RV32.run 2 (sync base machine { initial with pc := 0 }) =
      some (sync base machine seed) := start platform initial
  have firstStep := oneWord platform seed (by simp [seed]) (by simp [seed, inputAddresses])
  have secondStep := oneWord platform first (by simp [first, seed]) (by simp [first, seed, inputAddresses])
  have thirdStep := oneWord platform second
    (by simp [second, first, seed]) (by simp [second, first, seed, inputAddresses])
  have fourthStep := oneWord platform third
    (by simp [third, second, first, seed]) (by simp [third, second, first, seed, inputAddresses])
  have returned := finish platform fourth (by simp [fourth, third, second, first, seed])
  refine ⟨sync base machine last, ?_, ?_, ?_, syncMem _, ?_⟩
  · refine (congrArg (RV32.run 664) entry).trans ?_
    rw [show 664 = 2 + (165 + (165 + (165 + (165 + 2)))) by decide,
      RV32.runAdd, setup, Option.bind_some, RV32.runAdd, firstStep, Option.bind_some,
      RV32.runAdd, secondStep, Option.bind_some, RV32.runAdd, thirdStep, Option.bind_some,
      RV32.runAdd, fourthStep, Option.bind_some, returned]
  · have pcRead := syncReadPC (base := base) (frame := machine) last
    have pc : base + last.pc = returnAddress := by
      change base + (returnAddress - base) = returnAddress
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    rw [viewPc, pc] at pcRead
    exact readReg_succ.mp pcRead
  · have read : Sail.readReg Register.x10 (sync base machine last) =
        .ok last.a0 (sync base machine last) := syncRead last (index := 10) (by decide)
    rw [readReg_succ.mp read, Option.map_some, ← scanInputCorrect]
    simp [last, fourth, third, second, first, seed, scanInput]
  · intro register outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨pc, next, x5, x6, x7, x10, x28, x29⟩ := outside
    refine syncFrame last register pc next ?_
    intro index member
    change index ∈ ([5, 6, 7, 10, 28, 29] : List (Fin 32)) at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ne.symm x5
    · exact Ne.symm x6
    · exact Ne.symm x7
    · exact Ne.symm x10
    · exact Ne.symm x28
    · exact Ne.symm x29

#print axioms popcount128SailCorrect

end Correctness

end Popcount

end Riscfree
