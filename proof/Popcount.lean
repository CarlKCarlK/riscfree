import Std

namespace Riscfree

abbrev Word := BitVec 32
abbrev Memory := Word → Word

-- Model ordinary, aligned, readable RV32 memory through its little-endian
-- word view. The caller supplies the four valid words; MMIO and traps are
-- outside this model. The PC is relative to the aligned code address.
structure State where
  pc : Word := 0
  a0 : Word
  t0 : Word := 0
  t1 : Word := 0
  t2 : Word := 0
  t3 : Word := 0
  t4 : Word := 0
  other : Nat → Word
  memory : Memory

def State.read (state : State) : Nat → Word
  | 0 => 0
  | 5 => state.t0
  | 6 => state.t1
  | 7 => state.t2
  | 10 => state.a0
  | 28 => state.t3
  | 29 => state.t4
  | register => state.other register

def State.write (state : State) (register : Nat) (value : Word) : State :=
  match register with
  | 0 => state
  | 5 => { state with t0 := value }
  | 6 => { state with t1 := value }
  | 7 => { state with t2 := value }
  | 10 => { state with a0 := value }
  | 28 => { state with t3 := value }
  | 29 => { state with t4 := value }
  | register => { state with other := fun index =>
      if index = register then value else state.other index }

-- Little-endian instruction words, in order, from the linked popcount128 symbol.
def code : Array Nat := #[
  0x00400293, 0x00000313, 0x00052383, 0x02000e13,
  0x0013fe93, 0x01d30333, 0x0013d393, 0xfffe0e13,
  0xfe0e18e3, 0x00450513, 0xfff28293, 0xfc029ee3,
  0x00030513, 0x00008067
]

def field (instruction offset width : Nat) : Nat :=
  (instruction >>> offset) % (2 ^ width)

def signedImmediate (width value : Nat) : Word :=
  if value < 2 ^ (width - 1) then BitVec.ofNat 32 value
  else BitVec.ofNat 32 value - BitVec.ofNat 32 (2 ^ width)

inductive Instruction where
  | addi (destination source : Nat) (immediate : Word)
  | andi (destination source : Nat) (immediate : Word)
  | srli (destination source amount : Nat)
  | add (destination source source2 : Nat)
  | lw (destination source : Nat) (immediate : Word)
  | bne (source source2 : Nat) (displacement : Word)
  | jalr (destination source : Nat) (immediate : Word)
  deriving DecidableEq

def decode (instruction : Nat) : Option Instruction :=
  let destination := field instruction 7 5
  let source := field instruction 15 5
  let source2 := field instruction 20 5
  let immediate := signedImmediate 12 (field instruction 20 12)
  match field instruction 0 7, field instruction 12 3, field instruction 25 7 with
  | 0x13, 0, _ => some (.addi destination source immediate)
  | 0x13, 7, _ => some (.andi destination source immediate)
  | 0x13, 5, 0 => some (.srli destination source source2)
  | 0x33, 0, 0 => some (.add destination source source2)
  | 0x03, 2, _ => some (.lw destination source immediate)
  | 0x63, 1, _ =>
    let displacement := signedImmediate 13
      (field instruction 31 1 * 4096 + field instruction 7 1 * 2048 +
        field instruction 25 6 * 32 + field instruction 8 4 * 2)
    some (.bne source source2 displacement)
  | 0x67, 0, _ => some (.jalr destination source immediate)
  | _, _, _ => none

def program := code.map decode

theorem programDecoded :
    program = #[
      some (.addi 5 0 4), some (.addi 6 0 0), some (.lw 7 10 0), some (.addi 28 0 32),
      some (.andi 29 7 1#32), some (.add 6 6 29), some (.srli 7 7 1),
      some (.addi 28 28 0xffffffff), some (.bne 28 0 0xfffffff0), some (.addi 10 10 4),
      some (.addi 5 5 0xffffffff), some (.bne 5 0 0xffffffdc),
      some (.addi 10 6 0), some (.jalr 0 1 0)] := by
  simp [program, code, decode, field, signedImmediate]

-- This compact RV32I model states the loop invariants. The Sail refinement for
-- the linked routine is checked in Riscfree.PopcountSimulation.
def step (codeBase : Word) (state : State) : Option State := do
  if state.pc.toNat % 4 ≠ 0 then none else
  let instruction ← program[state.pc.toNat / 4]?.join
  let next := { state with pc := state.pc + 4 }
  let read := state.read
  some <| match instruction with
  | .addi destination source immediate => next.write destination (read source + immediate)
  | .andi destination source immediate => next.write destination (read source &&& immediate)
  | .srli destination source amount => next.write destination (read source >>> amount)
  | .add destination source source2 => next.write destination (read source + read source2)
  | .lw destination source immediate =>
    next.write destination (state.memory (read source + immediate))
  | .bne source source2 displacement =>
    if read source ≠ read source2 then { state with pc := state.pc + displacement } else next
  | .jalr destination source immediate =>
    let target := (read source + immediate) &&& 0xfffffffe
    { state with pc := target - codeBase }.write destination (codeBase + next.pc)

@[irreducible] def run (codeBase : Word) (steps : Nat) : State → Option State :=
  Nat.rec (fun state => some state)
    (fun _ previous state => (step codeBase state).bind previous) steps

@[simp] theorem runZero (codeBase : Word) (state : State) :
    run codeBase 0 state = some state := by unfold run; rfl

@[simp] theorem runSucc (codeBase : Word) (steps : Nat) (state : State) :
    run codeBase (steps + 1) state = (step codeBase state).bind (run codeBase steps) := by
  unfold run
  rfl

def scan : Nat → Word → Word → Word
  | 0, _, total => total
  | remaining + 1, word, total =>
    scan remaining (word >>> (1 : Nat)) (total + (word &&& 1#32))

def scanInput (memory : Memory) (input : Word) : Word :=
  let next := input + 4
  let third := next + 4
  let fourth := third + 4
  scan 32 (memory fourth) (scan 32 (memory third)
    (scan 32 (memory next) (scan 32 (memory input) 0#32)))

-- Observation of the return state. The writable temporaries are omitted.
def observe (codeBase : Word) (state : State) :=
  (codeBase + state.pc, state.a0, state.other, state.memory)

theorem cpopShift (word : Word) (remaining : Nat) :
    (word >>> (1 : Nat)).cpopNatRec remaining 0 + (word.getLsbD 0).toNat =
      word.cpopNatRec (remaining + 1) 0 := by
  induction remaining with
  | zero => simp
  | succ remaining previous =>
    rw [BitVec.cpopNatRec_succ (x := word >>> (1 : Nat)),
      BitVec.cpopNatRec_eq (acc := 0 + ((word >>> (1 : Nat)).getLsbD remaining).toNat),
      BitVec.cpopNatRec_succ (x := word) (n := remaining + 1),
      BitVec.cpopNatRec_eq (acc := 0 + (word.getLsbD (remaining + 1)).toNat),
      ← previous]
    simp only [BitVec.getLsbD_ushiftRight, Nat.zero_add, Nat.add_comm 1 remaining]
    ac_rfl

theorem scanCorrect (remaining : Nat) (word total : Word)
    (bound : total.toNat + remaining < 2 ^ 32) :
    (scan remaining word total).toNat = total.toNat + word.cpopNatRec remaining 0 := by
  induction remaining generalizing word total with
  | zero => simp [scan]
  | succ remaining previous =>
    have lowBit : (word &&& 1#32).toNat = (word.getLsbD 0).toNat := by
      rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
      cases word.getLsbD 0 <;> decide
    have lowBound : (word.getLsbD 0).toNat ≤ 1 := by cases word.getLsbD 0 <;> decide
    have addExact : (total + (word &&& 1#32)).toNat = total.toNat + (word.getLsbD 0).toNat := by
      rw [BitVec.toNat_add_of_lt, lowBit]
      omega
    have nextBound : (total + (word &&& 1#32)).toNat + remaining < 2 ^ 32 := by omega
    rw [scan, previous _ _ nextBound, addExact, Nat.add_assoc, ← cpopShift]
    ac_rfl

def inputBits (memory : Memory) (input : Word) : BitVec 128 :=
  let next := input + 4
  let third := next + 4
  let fourth := third + 4
  memory fourth ++ memory third ++ memory next ++ memory input

theorem scanInputCorrect (memory : Memory) (input : Word) :
    (scanInput memory input).toNat = (inputBits memory input).cpop.toNat := by
  have scanWord (word total : Word) (bound : total.toNat ≤ 96) :
      (scan 32 word total).toNat = total.toNat + word.cpop.toNat := by
    rw [BitVec.toNat_cpop, scanCorrect]
    omega
  have first := scanWord (memory input) 0#32 (by decide)
  have second := scanWord (memory (input + 4)) (scan 32 (memory input) 0#32) (by
    rw [first, BitVec.toNat_zero, Nat.zero_add]
    have := BitVec.toNat_cpop_le (memory input)
    omega)
  have third := scanWord (memory (input + 4 + 4))
    (scan 32 (memory (input + 4)) (scan 32 (memory input) 0#32)) (by
      rw [second, first, BitVec.toNat_zero, Nat.zero_add]
      have := BitVec.toNat_cpop_le (memory input)
      have := BitVec.toNat_cpop_le (memory (input + 4))
      omega)
  have fourth := scanWord (memory (input + 4 + 4 + 4))
    (scan 32 (memory (input + 4 + 4)) (scan 32 (memory (input + 4)) (scan 32 (memory input) 0#32))) (by
      rw [third, second, first, BitVec.toNat_zero, Nat.zero_add]
      have := BitVec.toNat_cpop_le (memory input)
      have := BitVec.toNat_cpop_le (memory (input + 4))
      have := BitVec.toNat_cpop_le (memory (input + 4 + 4))
      omega)
  simp only [scanInput, fourth, third, second, first, BitVec.toNat_zero,
    Nat.zero_add, inputBits, BitVec.toNat_cpop_append]
  ac_rfl

theorem runAdd (codeBase : Word) (first second : Nat) (state : State) :
    run codeBase (first + second) state =
      (run codeBase first state).bind (run codeBase second) := by
  induction first generalizing state with
  | zero => simp
  | succ first previous =>
    rw [Nat.succ_add, runSucc, runSucc]
    cases step codeBase state <;> simp [previous]

theorem start (codeBase : Word) (state : State) :
    run codeBase 2 { state with pc := 0 } = some { state with pc := 8, t0 := 4, t1 := 0 } := by
  simp [step, programDecoded, State.read, State.write]

def bitNextPc (counter : Word) : Word :=
  if counter = 0#32 then 36#32 else 16#32

theorem addDecrement (word : Word) : word + 0xffffffff#32 = word - 1#32 := by
  rw [BitVec.sub_eq_add_neg]
  congr 1

def bitUpdate (state : State) : State :=
  let counter := state.t3 - 1#32
  { state with
    pc := bitNextPc counter
    t1 := state.t1 + (state.t2 &&& 1#32)
    t2 := state.t2 >>> (1 : Nat)
    t3 := counter
    t4 := state.t2 &&& 1#32 }

theorem bitInstructions (codeBase : Word) (state : State) (atBit : state.pc = 16#32) :
    run codeBase 5 state = some (bitUpdate state) := by
  simp [step, atBit, programDecoded, State.read, State.write, bitUpdate, bitNextPc, addDecrement]
  split <;> simp_all

@[irreducible] def bitScan (remaining : Nat) : State → State :=
  Nat.rec (fun state => state) (fun _ previous state => previous (bitUpdate state)) remaining

@[simp] theorem bitScanZero (state : State) : bitScan 0 state = state := by unfold bitScan; rfl

@[simp] theorem bitScanSucc (remaining : Nat) (state : State) :
    bitScan (remaining + 1) state = bitScan remaining (bitUpdate state) := by unfold bitScan; rfl

theorem bitCounterNext (state : State) (remaining : Nat)
    (counter : state.t3 = BitVec.ofNat 32 (remaining + 1)) :
    (bitUpdate state).t3 = BitVec.ofNat 32 remaining := by
  simp only [bitUpdate, counter, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ 1#32

theorem bitPcNext (state : State) (remaining : Nat)
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

theorem bitChunk (codeBase : Word) (remaining : Nat) (state : State)
    (atBit : state.pc = 16#32) :
    run codeBase ((remaining + 1) * 5) state =
      run codeBase (remaining * 5) (bitUpdate state) := by
  rw [show (remaining + 1) * 5 = 5 + remaining * 5 by omega, runAdd,
    bitInstructions _ _ atBit, Option.bind_some]

theorem bitLoop (codeBase : Word) (remaining : Nat) (state : State)
    (atBit : state.pc = 16#32) (counter : state.t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) :
    run codeBase (remaining * 5) state = some (bitScan remaining state) := by
  induction remaining generalizing state with
  | zero => simp
  | succ remaining previous =>
    rw [bitChunk _ _ _ atBit, bitScanSucc]
    by_cases empty : remaining = 0
    · simp [empty]
    have nextCounter := bitCounterNext state remaining counter
    have nextPc := bitPcNext state remaining nextCounter (by omega)
    exact previous (bitUpdate state) (by simpa only [empty, if_false] using nextPc)
      nextCounter (by omega)

theorem bitLoopExit (remaining : Nat) (state : State)
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

theorem bitScanPreserves (project : State → α)
    (unchanged : ∀ state, project (bitUpdate state) = project state)
    (remaining : Nat) (state : State) :
    project (bitScan remaining state) = project state := by
  induction remaining generalizing state with
  | zero => rw [bitScanZero]
  | succ remaining previous =>
    rw [bitScanSucc, previous, unchanged]

theorem bitKeepsPointer (state : State) : (bitUpdate state).a0 = state.a0 := by
  simp only [bitUpdate]

theorem bitKeepsWordCount (state : State) : (bitUpdate state).t0 = state.t0 := by
  simp only [bitUpdate]

theorem bitKeepsOtherRegisters (state : State) : (bitUpdate state).other = state.other := by
  simp only [bitUpdate]

theorem bitKeepsMemory (state : State) : (bitUpdate state).memory = state.memory := by
  simp only [bitUpdate]

theorem bitScanTotal (remaining : Nat) (state : State) :
    (bitScan remaining state).t1 = scan remaining state.t2 state.t1 := by
  induction remaining generalizing state with
  | zero => rw [bitScanZero, scan]
  | succ remaining previous =>
    rw [bitScanSucc, previous, scan.eq_2]
    rfl

theorem loadWord (codeBase : Word) (state : State) :
    run codeBase 2 { state with pc := 8 } =
      some { state with pc := 16#32, t2 := state.memory state.a0, t3 := 32#32 } := by
  simp [step, programDecoded, State.read, State.write]

def advanceWord (state : State) : State :=
  { state with pc := if state.t0 - 1#32 = 0#32 then 48#32 else 8#32
               a0 := state.a0 + 4, t0 := state.t0 - 1#32 }

theorem nextWord (codeBase : Word) (state : State) (atEnd : state.pc = 36#32) :
    run codeBase 3 state = some (advanceWord state) := by
  simp [step, atEnd, programDecoded, State.read, State.write, advanceWord, addDecrement]
  split <;> simp_all

def loadedWord (state : State) : State :=
  { state with pc := 16#32, t2 := state.memory state.a0, t3 := 32#32 }

theorem loadedPc (state : State) : (loadedWord state).pc = 16#32 := by simp [loadedWord]

theorem loadedCounter (state : State) :
    (loadedWord state).t3 = BitVec.ofNat 32 32 := by simp [loadedWord]

theorem loadedExecution (codeBase : Word) (state : State) :
    run codeBase (32 * 5) (loadedWord state) = some (bitScan 32 (loadedWord state)) :=
  bitLoop codeBase 32 (loadedWord state) (loadedPc state) (loadedCounter state) (by decide)

theorem loadedExit (state : State) : (bitScan 32 (loadedWord state)).pc = 36#32 :=
  bitLoopExit 32 (loadedWord state) (loadedCounter state) (by decide) (by decide)

@[irreducible] def wordResult (state : State) : State :=
  advanceWord (bitScan 32 (loadedWord state))

@[simp] theorem wordResultPc (state : State) :
    (wordResult state).pc = (if state.t0 - 1#32 = 0#32 then 48#32 else 8#32) := by
  have words := bitScanPreserves State.t0 bitKeepsWordCount 32 (loadedWord state)
  simp only [wordResult, advanceWord, words]
  simp only [loadedWord] <;> (split <;> simp_all)

@[simp] theorem wordResultT0 (state : State) : (wordResult state).t0 = state.t0 - 1#32 := by
  have words := bitScanPreserves State.t0 bitKeepsWordCount 32 (loadedWord state)
  simp only [wordResult, advanceWord, words]
  simp only [loadedWord]

@[simp] theorem wordResultA0 (state : State) : (wordResult state).a0 = state.a0 + 4 := by
  have pointer := bitScanPreserves State.a0 bitKeepsPointer 32 (loadedWord state)
  simp only [wordResult, advanceWord, pointer]
  simp only [loadedWord]

@[simp] theorem wordResultT1 (state : State) :
    (wordResult state).t1 = scan 32 (state.memory state.a0) state.t1 := by
  simp only [wordResult, advanceWord, bitScanTotal, loadedWord]

@[simp] theorem wordResultOther (state : State) : (wordResult state).other = state.other := by
  have registers := bitScanPreserves State.other bitKeepsOtherRegisters 32 (loadedWord state)
  simp only [wordResult, advanceWord, registers]
  simp only [loadedWord]

@[simp] theorem wordResultMemory (state : State) : (wordResult state).memory = state.memory := by
  have memory := bitScanPreserves State.memory bitKeepsMemory 32 (loadedWord state)
  simp only [wordResult, advanceWord, memory]
  simp only [loadedWord]

theorem oneWord (codeBase : Word) (state : State) :
    run codeBase 165 { state with pc := 8 } = some (wordResult state) := by
  have pre := loadWord codeBase state
  change run codeBase 2 { state with pc := 8 } = some (loadedWord state) at pre
  rw [show 165 = 2 + (32 * 5 + 3) by decide, runAdd, pre, Option.bind_some,
    runAdd, loadedExecution, Option.bind_some, nextWord _ _ (loadedExit state)]
  simp only [wordResult]

theorem finish (codeBase : Word) (state : State) :
    run codeBase 2 { state with pc := 48 } =
      some { state with a0 := state.t1, pc := (state.other 1 &&& 0xfffffffe) - codeBase } := by
  simp [step, programDecoded, State.read, State.write]

theorem oneWordAt (codeBase : Word) (state : State) (pc : state.pc = 8#32) :
    run codeBase 165 state = some (wordResult state) := by
  have same : { state with pc := 8 } = state := by cases state; simp_all
  have result := oneWord codeBase state
  rwa [same] at result

theorem finishAt (codeBase : Word) (state : State) (pc : state.pc = 48#32) :
    run codeBase 2 state =
      some { state with a0 := state.t1, pc := (state.other 1 &&& 0xfffffffe) - codeBase } := by
  have same : { state with pc := 48 } = state := by cases state; simp_all
  have result := finish codeBase state
  rwa [same] at result

theorem trace (codeBase : Word) (initial : State) :
    (run codeBase 664 { initial with pc := 0 }).map (observe codeBase) =
    some (codeBase + ((initial.other 1 &&& 0xfffffffe) - codeBase),
      scanInput initial.memory initial.a0, initial.other, initial.memory) := by
  let seed := { initial with pc := 8#32, t0 := 4#32, t1 := 0#32 }
  let first := wordResult seed
  let second := wordResult first
  let third := wordResult second
  let fourth := wordResult third
  have setup : run codeBase 2 { initial with pc := 0 } = some seed := by
    simpa [seed] using start codeBase initial
  have firstStep := oneWordAt codeBase seed (by simp [seed])
  have secondStep := oneWordAt codeBase first (by simp [first, seed])
  have thirdStep := oneWordAt codeBase second (by simp [second, first, seed])
  have fourthStep := oneWordAt codeBase third (by simp [third, second, first, seed])
  have last := finishAt codeBase fourth (by simp [fourth, third, second, first, seed])
  rw [show 664 = 2 + (165 + (165 + (165 + (165 + 2)))) by decide,
    runAdd, setup, Option.bind_some, runAdd, firstStep, Option.bind_some,
    runAdd, secondStep, Option.bind_some, runAdd, thirdStep, Option.bind_some,
    runAdd, fourthStep, Option.bind_some, last]
  simp [observe, fourth, third, second, first, seed, scanInput]

theorem popcount128Correct (codeBase : Word) (initial : State)
    (returnAligned : initial.other 1 &&& 0xfffffffe = initial.other 1) :
    (run codeBase 664 { initial with pc := 0 }).map
      (fun final => (codeBase + final.pc, final.a0.toNat, final.other, final.memory)) =
    some (initial.other 1, (inputBits initial.memory initial.a0).cpop.toNat,
      initial.other, initial.memory) := by
  have checked := congrArg
    (Option.map (fun (result : Word × Word × (Nat → Word) × Memory) =>
      (result.1, result.2.1.toNat, result.2.2)))
    (trace codeBase initial)
  rw [returnAligned, BitVec.add_comm codeBase, BitVec.sub_add_cancel] at checked
  simpa only [Option.map_map, Option.map_some, Function.comp_def, observe,
    scanInputCorrect] using checked

#print axioms popcount128Correct

-- GNU binutils supply the ELF symbol and section locations. Compare the raw
-- bytes at the resulting file offset, independently of any disassembly.
def columns (line : String) : List String :=
  (line.splitOn " ").filter (· != "")

def hex (part : String) : IO Nat := do
  let mut value := 0
  for digit in part.toList do
    let ascii := digit.toNat
    let nibble ←
      if '0'.toNat ≤ ascii && ascii ≤ '9'.toNat then pure (ascii - '0'.toNat)
      else if 'a'.toNat ≤ ascii && ascii ≤ 'f'.toNat then pure (ascii - 'a'.toNat + 10)
      else throw (IO.userError s!"Invalid hexadecimal value: {part}")
    value := value * 16 + nibble
  return value

def verifyElf (path : String) : IO Unit := do
  let symbols ← IO.Process.run { cmd := "nm", args := #["-S", "--defined-only", path] }
  let sections ← IO.Process.run { cmd := "objdump", args := #["-h", "-j", ".text", path] }
  let symbolRows := (symbols.splitOn "\n").map columns
  let [[addressText, sizeText, "T", "popcount128"]] :=
    symbolRows.filter (fun row => row.getLast? == some "popcount128")
    | throw (IO.userError "Expected one popcount128 text symbol")
  let [(_ :: ".text" :: sectionSizeText :: baseText :: _ :: offsetText :: _)] :=
    (sections.splitOn "\n").map columns |>.filter (fun row => row[1]? == some ".text")
    | throw (IO.userError "Expected one .text section")
  let address ← hex addressText
  let size ← hex sizeText
  let sectionSize ← hex sectionSizeText
  let base ← hex baseText
  let offset ← hex offsetText
  unless address % 4 == 0 && base ≤ address && address + size ≤ base + sectionSize do
    throw (IO.userError "popcount128 is misaligned or lies outside .text")
  let expected := code.toList.flatMap fun word =>
    (List.range 4).map fun index => UInt8.ofNat (word >>> (8 * index))
  let startOffset := offset + (address - base)
  let elf ← IO.FS.readBinFile path
  let actual := (elf.extract startOffset (startOffset + size)).data.toList
  unless size == expected.length && actual == expected do
    throw (IO.userError "The linked popcount128 bytes differ from the Lean proof")
  IO.println s!"popcount128: verified all {size} linked bytes"

end Riscfree
