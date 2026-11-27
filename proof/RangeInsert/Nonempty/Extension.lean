import RangeInsert.Nonempty.Predecessor
import RangeInsert.Nonempty.MutationSteps
import RangeInsert.DeleteExtra.Helper
import RangeInsert.Arithmetic

/-! The outer path that extends an existing predecessor before calling
the linked deletion helper. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable CodeAgreesFor)
open Empty (Snapshot)
open InsertTable (instructions)
open Mutation

private def calculated (state : Snapshot) (low high : Word) : Snapshot :=
  let resultLow := DeleteExtra.extendedLow low state.a2 state.s1
  { state with
    pc := 0x174#32
    a0 := resultLow
    a2 := DeleteExtra.extendedHigh low high state.a2 state.s1
    a4 := Step.lessWord resultLow 0x1#32 }

/-- The branch to extension and the two-word cache arithmetic cost eleven
instructions. The stores follow this run. -/
theorem extensionArithmetic {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atTest : state.pc = 0x148#32) (grows : state.a2.toNat < state.s1.toNat)
    (low high : Word) (lowReadable : Readable original state.s0)
    (highReadable : Readable original (state.s0 + 4#32))
    (lowWord : WordAt memory state.s0.toNat low)
    (highWord : WordAt memory (state.s0 + 4#32).toNat high) :
    run 11 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } (calculated state low high)) := by
  refine runStep (step148 machine image _ atTest) ?_
  rw [if_neg (Nat.not_le.mpr grows)]
  refine runStep (step14c machine image _ rfl low lowReadable lowWord) ?_
  refine runStep (step150 machine image _ rfl) ?_
  refine runStep (step154 machine image _ rfl high highReadable highWord) ?_
  refine runStep (step158 machine image _ rfl) ?_
  refine runStep (step15c machine image _ rfl) ?_
  refine runStep (step160 machine image _ rfl) ?_
  refine runStep (step164 machine image _ rfl) ?_
  refine runStep (step168 machine image _ rfl) ?_
  refine runStep (step16c machine image _ rfl) ?_
  exact runStep (step170 machine image _ rfl) rfl

/-- The stores from the completed arithmetic to the helper call, in the
order of the instructions. The temporary header lives in the outer frame. -/
def extensionWrites (state : Snapshot) : List (Word × Word) :=
  [(state.s0, state.a0), (state.s0 + 4#32, state.a2), (state.a3, state.s1),
    (state.sp + 8#32, state.s4), (state.sp + 12#32, 0#32), (state.sp + 16#32, state.s3)]

def writeWords (memory : ByteMemory) : List (Word × Word) → ByteMemory
  | [] => memory
  | (address, value) :: remaining => writeWords (storeWord memory address.toNat value) remaining

theorem writeWordsOutside (memory : ByteMemory) (writes : List (Word × Word)) (byte : Nat)
    (outside : ∀ write ∈ writes, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte) :
    (writeWords memory writes)[byte]? = memory[byte]? := by
  induction writes generalizing memory with
  | nil => rfl
  | cons write rest ih =>
    obtain ⟨address, value⟩ := write
    have head := outside (address, value) (by simp)
    have tail (other : Word × Word) (member : other ∈ rest) :
        byte < other.1.toNat ∨ other.1.toNat + 4 ≤ byte :=
      outside other (List.mem_cons_of_mem _ member)
    exact (ih (storeWord memory address.toNat value) tail).trans
      (storeWordOutside _ _ _ _ head)

structure ExtensionSetup (base : Word) (original : Machine) (memory : ByteMemory)
    (state : Snapshot) (key : Word) : Prop where
  low : Writable original state.s0
  high : Writable original (state.s0 + 4#32)
  stop : Writable original state.a3
  scratchData : Writable original (state.sp + 8#32)
  scratchLength : Writable original (state.sp + 12#32)
  scratchCapacity : Writable original (state.sp + 16#32)
  keyReadable : Readable original state.a1
  keyWord : WordAt memory state.a1.toNat key
  keyApart : ∀ byte, state.a1.toNat ≤ byte → byte < state.a1.toNat + 4 →
    ∀ write ∈ (extensionWrites state).take 2, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte
  codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
    ∀ write ∈ extensionWrites state, byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte

def extensionHelperOffset : Word := 0xfffffe2c

def extensionCallState (base : Word) (state : Snapshot) (key : Word) : Snapshot :=
  { state with
    pc := extensionHelperOffset, ra := base + 0x1a8#32,
    a0 := state.sp + 4#32, a1 := state.s0, a2 := key, a3 := state.s1, a4 := state.sp + 8#32 }

/-- Thirteen instructions execute the six stores and call the helper at the
linked offset, with its map-reference and scratch-header arguments in the
outer frame. -/
theorem extensionSetup {base : Word} {original : Machine} {memory : ByteMemory}
    (machine : MachineState original)
    (image : CodeImage instructions base { original with mem := memory })
    (state : Snapshot) (atStores : state.pc = 0x174#32) (key : Word)
    (setup : ExtensionSetup base original memory state key) :
    run 13 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := writeWords memory (extensionWrites state) }
        (extensionCallState base state key)) := by
  let prefixMemory (count : Nat) : ByteMemory := writeWords memory ((extensionWrites state).take count)
  have sameCode (count : Nat) : CodeAgreesFor (4 * instructions.length) base memory (prefixMemory count) := by
    intro byte low high
    exact writeWordsOutside _ _ byte fun write member =>
      setup.codeApart byte low high write (List.mem_of_mem_take member)
  have atPartial (count : Nat) : CodeImage instructions base { original with mem := prefixMemory count } :=
    image.withMemory (prefixMemory count) (sameCode count)
  have keyWord : WordAt (prefixMemory 2) state.a1.toNat key :=
    setup.keyWord.congr fun byte low high =>
      writeWordsOutside _ _ byte (setup.keyApart byte low high)
  refine runStep (step174 machine image _ atStores setup.low) ?_
  refine runStep (step178 machine (atPartial 1) _ rfl setup.high) ?_
  refine runStep (step17c machine (atPartial 2) _ rfl key setup.keyReadable keyWord) ?_
  refine runStep (step180 machine (atPartial 2) _ rfl setup.stop) ?_
  refine runStep (step184 machine (atPartial 3) _ rfl setup.scratchData) ?_
  refine runStep (step188 machine (atPartial 4) _ rfl setup.scratchLength) ?_
  refine runStep (step18c machine (atPartial 5) _ rfl setup.scratchCapacity) ?_
  refine runStep (step190 machine (atPartial 6) _ rfl) ?_
  refine runStep (step194 machine (atPartial 6) _ rfl) ?_
  refine runStep (step198 machine (atPartial 6) _ rfl) ?_
  refine runStep (step19c machine (atPartial 6) _ rfl) ?_
  refine runStep (step1a0 machine (atPartial 6) _ rfl) ?_
  exact runStep (step1a4 machine (atPartial 6) _ rfl rfl) rfl


/-- Extension needs the cache and selected end to be writable, plus the
three words used for the temporary RawVec in the caller's frame. -/
structure ExtensionPrefix (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) (low high : Word) : Prop where
  frame : Empty.Frame base returnAddress original initial
  arguments : Arguments initial call
  map : Map base original initial.sp call
  nonempty : call.start.toNat ≤ call.stop.toNat
  found : 0 < call.rank
  touches : call.start.toNat ≤ call.predecessor.value.toNat + 1
  grows : call.predecessor.value.toNat < call.stop.toNat
  cacheFits : initial.a1.toNat + 8 ≤ 2 ^ 32
  cacheOutside : ∀ byte, initial.a1.toNat ≤ byte → byte < initial.a1.toNat + 8 →
    Empty.OutsideFrame initial.sp byte
  cacheLow : WordAt original.mem initial.a1.toNat low
  cacheHigh : WordAt original.mem (initial.a1.toNat + 4) high
  cacheLowReadable : Readable original initial.a1
  cacheHighReadable : Readable original (initial.a1 + 4#32)
  cacheLowWritable : Writable original initial.a1
  cacheHighWritable : Writable original (initial.a1 + 4#32)
  endWritable : Writable original (call.search.wordSlot (call.rank - 1) + 4#32)
  scratchWritable : ∀ offset ∈ ([8, 12, 16] : List Word),
    Writable original (Empty.frameBase initial.sp + offset)
  codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
    (byte < initial.a1.toNat ∨ initial.a1.toNat + 8 ≤ byte) ∧
      (byte < call.search.slot (call.rank - 1) + 4 ∨ call.search.slot (call.rank - 1) + 8 ≤ byte)
  keyApart : ∀ byte, call.search.slot (call.rank - 1) ≤ byte →
    byte < call.search.slot (call.rank - 1) + 4 →
    byte < initial.a1.toNat ∨ initial.a1.toNat + 8 ≤ byte

private theorem touchFlag {start stop : Word} (touches : start.toNat ≤ stop.toNat + 1) :
    Step.lessWord stop 0xffffffff#32 &&& Step.lessWord (stop + 1#32) start = 0#32 := by
  unfold Step.lessWord
  by_cases increment : stop.toNat < (0xffffffff#32).toNat
  · have noGap : ¬ (stop + 1#32).toNat < start.toNat := by
      intro gap
      have strict := (Riscfree.RangeInsert.predecessorGap start stop).mp ⟨increment, gap⟩
      omega
    rw [if_neg noGap, if_pos increment]
    rfl
  · rw [if_neg increment]
    split <;> rfl

def extendLow (call : Call) (low : Word) : Word :=
  DeleteExtra.extendedLow low call.predecessor.value call.stop

def extendHigh (call : Call) (low high : Word) : Word :=
  DeleteExtra.extendedHigh low high call.predecessor.value call.stop

def extensionStored (initial : Snapshot) (call : Call) (low high : Word)
    (memory : ByteMemory) : ByteMemory :=
  let sp := Empty.frameBase initial.sp
  writeWords memory [
    (initial.a1, extendLow call low), (initial.a1 + 4#32, extendHigh call low high),
    (call.search.wordSlot (call.rank - 1) + 4#32, call.stop),
    (sp + 8#32, initial.a4), (sp + 12#32, 0#32), (sp + 16#32, initial.a5)]

/-- Registers for the helper after the caller has installed the extended end
and updated the cache, with the scratch header initialized to length zero. -/
structure ExtensionCalling (base : Word) (initial : Snapshot) (call : Call) (state : Snapshot) :
    Prop where
  pc : state.pc = extensionHelperOffset
  sp : state.sp = Empty.frameBase initial.sp
  ra : state.ra = base + 0x1a8#32
  mapRef : state.a0 = state.sp + 4#32
  cache : state.a1 = initial.a1
  start : state.a2 = call.predecessor.key
  stop : state.a3 = call.stop
  keys : state.a4 = state.sp + 8#32
  s0 : state.s0 = initial.a1
  s1 : state.s1 = call.stop
  s3 : state.s3 = initial.a5
  s4 : state.s4 = initial.a4
  s5 : state.s5 = initial.a0

theorem ExtensionPrefix.toHelper {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} {low high : Word}
    (premises : ExtensionPrefix base returnAddress original initial call low high) :
    ∃ state : Snapshot,
      run (58 + call.search.count .upper) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := extensionStored initial call low high (Empty.pushed original.mem initial) } state) ∧
      ExtensionCalling base initial call state := by
  obtain ⟨state, inspected, regs⟩ := inspectPredecessor premises.frame premises.arguments premises.map
    premises.nonempty premises.found
  let memory := Empty.pushed original.mem initial
  let testing : Snapshot := { state with pc := 0x148#32 }
  let computed := calculated testing low high
  have frame := premises.frame
  let machine := frame.mode.toMachineState
  have cacheHighNat : (initial.a1 + 4#32).toNat = initial.a1.toNat + 4 := by
    rw [BitVec.toNat_add]
    change (initial.a1.toNat + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by have := premises.cacheFits; omega)
  let index := call.rank - 1
  have inMap : index < call.length.toNat := by
    have bound := call.rank_le
    dsimp only [index]
    have positive := premises.found
    omega
  have keyMap := premises.map.keys (by omega)
  have keyNat : (call.search.wordSlot index).toNat = call.search.slot index :=
    SortedMap.Search.slotNat keyMap inMap
  have endNat : (call.search.wordSlot index + 4#32).toNat = call.search.slot index + 4 := by
    rw [BitVec.toNat_add, keyNat]
    change (call.search.slot index + 4) % 2 ^ 32 = _
    have fits := keyMap.fits
    change call.search.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at fits
    change (call.search.data.toNat + 8 * index + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by omega)
  have kept {address : Nat} {value : Word} (word : WordAt original.mem address value)
      (outside : ∀ byte, address ≤ byte → byte < address + 4 →
        Empty.OutsideFrame initial.sp byte) : WordAt memory address value :=
    pushedWord initial frame.frameFits word outside
  have atTest : step (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory } testing) :=
    branchTouches machine frame.pushedImage state regs.pc (by rw [regs.gap]; exact touchFlag premises.touches)
  have testingCache : testing.s0 = initial.a1 := regs.cached
  have computedCache : computed.s0 = initial.a1 := regs.cached
  have computedSp : computed.sp = Empty.frameBase initial.sp := regs.sp
  have computedKey : computed.a1 = call.search.wordSlot index := regs.predecessorKeyAddress
  have computedEnd : computed.a3 = call.search.wordSlot index + 4#32 := regs.predecessorEndAddress
  have computedStop : computed.s1 = call.stop := regs.stop
  have computedData : computed.s4 = initial.a4 := regs.scratchData
  have computedCapacity : computed.s3 = initial.a5 := regs.scratchCapacity
  have computedLow : computed.a0 = extendLow call low := by
    change DeleteExtra.extendedLow low state.a2 state.s1 = _
    rw [regs.predecessorEnd, regs.stop]
    rfl
  have computedHigh : computed.a2 = extendHigh call low high := by
    change DeleteExtra.extendedHigh low high state.a2 state.s1 = _
    rw [regs.predecessorEnd, regs.stop]
    rfl
  have arithmetic : run 11 (sync base { original with mem := memory } testing) =
      some (sync base { original with mem := memory } computed) := by
    apply extensionArithmetic machine frame.pushedImage testing rfl
    · change state.a2.toNat < state.s1.toNat
      rw [regs.predecessorEnd, regs.stop]
      exact premises.grows
    · rw [testingCache]; exact premises.cacheLowReadable
    · rw [testingCache]; exact premises.cacheHighReadable
    · rw [testingCache]
      exact kept premises.cacheLow fun byte left right => premises.cacheOutside byte left (by omega)
    · rw [testingCache, cacheHighNat]
      exact kept premises.cacheHigh fun byte left right => premises.cacheOutside byte (by omega) (by omega)
  have setup : ExtensionSetup base original memory computed call.predecessor.key := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [computedCache]; exact premises.cacheLowWritable
    · rw [computedCache]; exact premises.cacheHighWritable
    · rw [computedEnd]; exact premises.endWritable
    · rw [computedSp]; exact premises.scratchWritable 8 (by decide)
    · rw [computedSp]; exact premises.scratchWritable 12 (by decide)
    · rw [computedSp]; exact premises.scratchWritable 16 (by decide)
    · rw [computedKey]; exact keyMap.readable index inMap
    · rw [computedKey, keyNat]
      exact kept (keyMap.keyWord index inMap) fun byte left right =>
        premises.map.entriesOutside index inMap byte left (by omega)
    · intro byte left right write member
      rw [computedKey, keyNat] at left right
      have apart := premises.keyApart byte left right
      simp only [extensionWrites, List.take, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [computedCache, cacheHighNat] <;> omega
    · intro byte left right write member
      obtain ⟨cacheApart, oldEndApart⟩ := premises.codeApart byte left right
      have stackApart := frame.codeOutside byte left right
      unfold Empty.OutsideFrame at stackApart
      simp only [extensionWrites, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [computedCache]; omega
      · simp only [computedCache, cacheHighNat]; omega
      · simpa only [computedEnd, endNat, Nat.add_assoc] using oldEndApart
      · rw [computedSp, Empty.frameAddress frame.frameFits 8#32 (by decide)]
        change byte < initial.sp.toNat - 48 + 8 ∨ initial.sp.toNat - 48 + 8 + 4 ≤ byte
        have fits := frame.frameFits
        omega
      · rw [computedSp, Empty.frameAddress frame.frameFits 12#32 (by decide)]
        change byte < initial.sp.toNat - 48 + 12 ∨ initial.sp.toNat - 48 + 12 + 4 ≤ byte
        have fits := frame.frameFits
        omega
      · rw [computedSp, Empty.frameAddress frame.frameFits 16#32 (by decide)]
        change byte < initial.sp.toNat - 48 + 16 ∨ initial.sp.toNat - 48 + 16 + 4 ≤ byte
        have fits := frame.frameFits
        omega
  have entered := extensionSetup machine frame.pushedImage computed rfl call.predecessor.key setup
  refine ⟨extensionCallState base computed call.predecessor.key, ?_, ?_⟩
  · have writes : writeWords memory (extensionWrites computed) = extensionStored initial call low high memory := by
      simp only [extensionWrites, extensionStored, computedCache, computedLow, computedHigh, computedEnd,
        computedStop, computedSp, computedData, computedCapacity, index]
    rw [show 58 + call.search.count .upper = (33 + call.search.count .upper) + 25 by omega,
      runAdd, inspected, Option.bind_some]
    refine runStep atTest ?_
    rw [show 24 = 11 + 13 by decide, runAdd, arithmetic, Option.bind_some, ← writes]
    exact entered
  · exact ⟨rfl, regs.sp, rfl, rfl, regs.cached, rfl, regs.stop, rfl, regs.cached, regs.stop,
      regs.scratchCapacity, regs.scratchData, regs.mapHeader⟩

end Riscfree.RangeInsert.Nonempty
