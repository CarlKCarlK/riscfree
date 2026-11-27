import RangeInsert.DeleteExtra.Removal

/-! The `delete_extra` removal loop. After `j` of the `k` collected keys are
removed, the entries up to the selected one are unchanged and the later ones
have moved down `j` slots, so the next key is at index `position + 1`. -/

namespace Riscfree.RangeInsert.DeleteExtra

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open Nonempty (mappedTransfer)

set_option maxHeartbeats 4000000

/-- The map's entries after `removed` removals at `selected + 1`. -/
def drained (before : Nat → Pair) (selected removed : Nat) (index : Nat) : Pair :=
  if index ≤ selected then before index else before (index + removed)

theorem drained_succ (before : Nat → Pair) (selected removed index : Nat) :
    (if index < selected + 1 then drained before selected removed index
      else drained before selected removed (index + 1)) =
      drained before selected (removed + 1) index := by
  unfold drained
  by_cases low : index ≤ selected
  · rw [if_pos (by omega), if_pos low, if_pos low]
  · rw [if_neg (by omega), if_neg (by omega), if_neg low]
    congr 1
    omega

-- A lower-bound scan passes every entry before `stop` and stops at it.
theorem scan_stopsAt (key : Word) (old : Nat → Pair) (stop : Nat)
    (passes : ∀ index < stop, (old index).key.toNat < key.toNat)
    (fails : ¬ (old stop).key.toNat < key.toNat) :
    ∀ index remaining, index ≤ stop → stop < index + remaining →
      SortedMap.scan .lower key old index remaining = stop := by
  intro index remaining
  induction remaining generalizing index with
  | zero => intro low high; omega
  | succ remaining previous =>
    intro low high
    by_cases here : index = stop
    · subst here
      rw [SortedMap.scan_fail]
      simp only [SortedMap.Bound.passes, decide_eq_false_iff_not]
      exact fails
    · rw [SortedMap.scan_pass]
      · exact previous (index + 1) (by omega) (by omega)
      · simp only [SortedMap.Bound.passes, decide_eq_true_eq]
        exact passes index (by omega)

/-- The bytes the removal loop may write: the callee's 16-byte frame below
`sp`, the map's length word, and the entries after the selected one. -/
def DrainFootprint (sp header : Word) (search : SortedMap.Search.Call) (selected length : Nat) (byte : Nat) : Prop :=
  (sp.toNat - 16 ≤ byte ∧ byte < sp.toNat) ∨ (header.toNat + 4 ≤ byte ∧ byte < header.toNat + 8) ∨
    (search.slot (selected + 1) ≤ byte ∧ byte < search.slot length)

/-- What the removal loop reads and writes. `before` is the map's contents
when the loop starts, and `collected` keys were pushed. -/
structure DrainLayout (base : Word) (original : Machine) (call : Call) (capacity : Word)
    (before : Nat → Pair) (scratch : Scratch) (collected : Nat) (sp : Word) (start : ByteMemory) :
    Prop where
  removeCode : CodeImage SortedMap.Remove.instructions (removeBase base) original
  searchCode : CodeImage (SortedMap.Search.instructions .lower)
    (SortedMap.Remove.searchBase (removeBase base)) original
  vectorCode : CodeImage PairRemove.instructions
    (SortedMap.Remove.vectorBase (removeBase base)) original
  -- Each code byte has its original value at the start and is never written.
  codeKept : ∀ byte, ((base.toNat ≤ byte ∧ byte < base.toNat + 4 * DeleteTable.instructions.length) ∨
      ((removeBase base).toNat ≤ byte ∧ byte < (removeBase base).toNat + 144) ∨
      ((SortedMap.Remove.searchBase (removeBase base)).toNat ≤ byte ∧
        byte < (SortedMap.Remove.searchBase (removeBase base)).toNat + 52) ∨
      ((SortedMap.Remove.vectorBase (removeBase base)).toNat ≤ byte ∧
        byte < (SortedMap.Remove.vectorBase (removeBase base)).toNat + 100)) →
    start[byte]? = original.mem[byte]? ∧
      ¬ DrainFootprint sp call.header call.search call.position call.length.toNat byte
  -- The callee's frame.
  stackFits : 16 ≤ sp.toNat
  stackReadable : ∀ offset ∈ [0, 4, 8, 12],
    Readable original (SortedMap.Remove.frameBase sp + BitVec.ofNat 32 offset)
  stackWritable : ∀ offset ∈ [0, 4, 8, 12],
    Writable original (SortedMap.Remove.frameBase sp + BitVec.ofNat 32 offset)
  stackApartHeader : SortedMap.Remove.outsideFrame sp call.header.toNat 12
  stackApartEntries : ∀ index < call.length.toNat,
    SortedMap.Remove.outsideFrame sp (call.search.slot index) 8
  stackApartCode : SortedMap.Remove.outsideFrame sp (removeBase base).toNat 144
  stackApartSearch : SortedMap.Remove.outsideFrame sp
    (SortedMap.Remove.searchBase (removeBase base)).toNat 52
  stackApartVector : SortedMap.Remove.outsideFrame sp
    (SortedMap.Remove.vectorBase (removeBase base)).toNat 100
  -- The map header.
  headerFits : call.header.toNat + 12 ≤ 2 ^ 32
  dataReadable : Readable original call.header
  lengthReadable : Readable original (call.header + 4)
  capacityReadable : Readable original (call.header + 8)
  lengthWritable : Writable original (call.header + 4)
  dataWord : WordAt start call.header.toNat call.data
  capacityWord : WordAt start (call.header.toNat + 8) capacity
  headerApartRegion : call.header.toNat + 12 ≤ call.search.slot 0 ∨
    call.search.slot call.length.toNat ≤ call.header.toNat
  lengthAway : Insert.outsideCode 100 (SortedMap.Remove.vectorBase (removeBase base)) 4
    (call.header.toNat + 4)
  -- The entries.
  entriesFit : call.search.slot call.length.toNat ≤ 2 ^ 32
  keyReadable : ∀ index < call.length.toNat, Readable original (call.search.wordSlot index)
  pairReadable : ∀ index, call.position + 1 < index → index < call.length.toNat →
    Element.Mapped (α := Pair) original (call.search.wordSlot index)
      (fun region => region.attributes.readable = true)
  pairWritable : ∀ index, call.position + 1 ≤ index → index + 1 < call.length.toNat →
    Element.Mapped (α := Pair) original (call.search.wordSlot index)
      (fun region => region.attributes.writable = true)
  separated : ∀ index < call.length.toNat,
    call.search.slot index + 8 ≤ call.header.toNat ∨ call.header.toNat + 12 ≤ call.search.slot index
  entriesAway : ∀ index, call.position + 1 ≤ index → index + 1 < call.length.toNat →
    Insert.outsideCode 100 (SortedMap.Remove.vectorBase (removeBase base)) 8 (call.search.slot index)
  sorted : ∀ first second, first < second → second < call.length.toNat →
    (before first).key.toNat < (before second).key.toNat
  capacityValid : call.length.toNat ≤ capacity.toNat
  -- The collected keys.
  room : call.position + 1 + collected ≤ call.length.toNat
  keysFit : scratch.slot collected ≤ 2 ^ 32
  keyCountFits : 4 * collected < 2 ^ 32
  collectedReadable : ∀ j < collected, Readable original (scratch.wordSlot j)
  collectedApart : ∀ j < collected, ∀ byte, scratch.slot j ≤ byte → byte < scratch.slot j + 4 →
    ¬ DrainFootprint sp call.header call.search call.position call.length.toNat byte

-- The removal of the `j`-th collected key.
def drainCall (call : Call) (capacity : Word) (before : Nat → Pair) (j : Nat) :
    SortedMap.Remove.Call :=
  { header := call.header, key := (before (call.position + 1 + j)).key,
    length := BitVec.ofNat 32 (call.length.toNat - j), capacity, data := call.data,
    old := drained before call.position j }

def drainCount (call : Call) (capacity : Word) (before : Nat → Pair) : Nat → Nat
  | 0 => 0
  | j + 1 => drainCount call capacity before j + (8 + (drainCall call capacity before j).count)

/-- The removal loop's registers after `j` removals. -/
structure DrainRegisters (call : Call) (scratch : Scratch) (collected : Nat) (sp : Word) (j : Nat)
    (state : Snapshot) : Prop where
  pc : state.pc = if j = collected then 0x184#32 else 0x164#32
  sp : state.sp = sp
  header : state.s0 = call.header
  cursor : state.s1 = scratch.wordSlot j
  remaining : state.s2 = BitVec.ofNat 32 (4 * (collected - j))

/-- The removal loop's memory after `j` removals. -/
structure DrainMemory (call : Call) (before : Nat → Pair) (sp : Word) (start : ByteMemory) (j : Nat)
    (memory : ByteMemory) : Prop where
  lengthWord : WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat - j))
  entries : ∀ index < call.length.toNat - j,
    PairAt memory (call.search.slot index) (drained before call.position j index)
  others : ∀ byte, ¬ DrainFootprint sp call.header call.search call.position call.length.toNat byte →
    memory[byte]? = start[byte]?

-- `addi s2, s2, -4` on the remaining byte count.
theorem remainingNext {count : Nat} (positive : 0 < count) (fits : 4 * count < 2 ^ 32) :
    BitVec.ofNat 32 (4 * count) + 0xfffffffc#32 = BitVec.ofNat 32 (4 * (count - 1)) := by
  have value : (BitVec.ofNat 32 (4 * count)).toNat = 4 * count := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt fits
  have le : 4#32 ≤ BitVec.ofNat 32 (4 * count) := by
    rw [BitVec.le_def, value]; change 4 ≤ 4 * count; omega
  rw [show (0xfffffffc#32 : BitVec 32) = -4#32 by decide, ← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  have result : (BitVec.ofNat 32 (4 * (count - 1))).toNat = 4 * (count - 1) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le le, value, result]
  change 4 * count - 4 = 4 * (count - 1)
  omega

theorem remainingZero {count : Nat} (fits : 4 * count < 2 ^ 32) :
    BitVec.ofNat 32 (4 * count) = 0#32 ↔ count = 0 := by
  constructor
  · intro zero
    have toNat := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at toNat
    simpa using toNat
  · intro zero; subst zero; rfl

theorem Scratch.wordSlotNext (scratch : Scratch) (index : Nat) :
    scratch.wordSlot index + 0x4#32 = scratch.wordSlot (index + 1) := by
  unfold Scratch.wordSlot Scratch.slot
  rw [Nat.mul_succ, ← Nat.add_assoc, BitVec.ofNat_add (scratch.data.toNat + 4 * index) 4]

theorem drain {base returnAddress : Word} {original : Machine} {initial : Snapshot} {call : Call}
    {capacity : Word} {before : Nat → Pair} {scratch : Scratch} {collected : Nat}
    {start : ByteMemory}
    (frame : Frame base returnAddress original initial)
    (layout : DrainLayout base original call capacity before scratch collected
      (frameBase initial.sp) start)
    (collectedWord : ∀ j < collected,
      WordAt start (scratch.slot j) (before (call.position + 1 + j)).key)
    (head : Snapshot)
    (registers : DrainRegisters call scratch collected (frameBase initial.sp) 0 head)
    (memory : DrainMemory call before (frameBase initial.sp) start 0 start) :
    ∀ j ≤ collected, ∃ (state : Snapshot) (after : ByteMemory),
      run (drainCount call capacity before j) (sync base { original with mem := start } head) =
        some (sync base { original with mem := after } state) ∧
      DrainRegisters call scratch collected (frameBase initial.sp) j state ∧
      DrainMemory call before (frameBase initial.sp) start j after := by
  have machine := frame.mode.toMachineState
  intro j
  induction j with
  | zero => exact fun _ => ⟨head, start, rfl, registers, memory⟩
  | succ j previous =>
    intro below
    obtain ⟨state, mem, ran, regs, invariant⟩ := previous (by omega)
    have lengthSmall := call.length.isLt
    have room := layout.room
    have capacityValid := layout.capacityValid
    have lengthNat : (BitVec.ofNat 32 (call.length.toNat - j)).toNat = call.length.toNat - j := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    let removing := drainCall call capacity before j
    -- Code bytes keep their values.
    have codeAt (byte : Nat) (inside : ((base.toNat ≤ byte ∧ byte < base.toNat + 4 * DeleteTable.instructions.length) ∨
        ((removeBase base).toNat ≤ byte ∧ byte < (removeBase base).toNat + 144) ∨
        ((SortedMap.Remove.searchBase (removeBase base)).toNat ≤ byte ∧
          byte < (SortedMap.Remove.searchBase (removeBase base)).toNat + 52) ∨
        ((SortedMap.Remove.vectorBase (removeBase base)).toNat ≤ byte ∧
          byte < (SortedMap.Remove.vectorBase (removeBase base)).toNat + 100))) :
        mem[byte]? = original.mem[byte]? :=
      (invariant.others byte (layout.codeKept byte inside).2).trans (layout.codeKept byte inside).1
    have imageOf (other : ByteMemory) (agree : ∀ byte, base.toNat ≤ byte →
        byte < base.toNat + 4 * DeleteTable.instructions.length → other[byte]? = mem[byte]?) :
        CodeImage DeleteTable.instructions base { original with mem := other } :=
      frame.code.withMemory other fun byte low high =>
        (agree byte low high).trans (codeAt byte (Or.inl ⟨low, high⟩))
    have removeCode := layout.removeCode.withMemory mem fun byte low high =>
      codeAt byte (Or.inr (Or.inl ⟨low, by change byte < (removeBase base).toNat + 4 * 36 at high; omega⟩))
    have searchCode := layout.searchCode.withMemory mem fun byte low high => by
      rw [SortedMap.Search.instructionsLength] at high
      exact codeAt byte (Or.inr (Or.inr (Or.inl ⟨low, by omega⟩)))
    have vectorCode := layout.vectorCode.withMemory mem fun byte low high =>
      codeAt byte (Or.inr (Or.inr (Or.inr ⟨low, by change byte < _ + 4 * 25 at high; omega⟩)))
    have stackFits := layout.stackFits
    have stackApart := layout.stackApartHeader
    have headerRegion := layout.headerApartRegion
    have entriesFit := layout.entriesFit
    unfold SortedMap.Remove.outsideFrame at stackApart
    unfold SortedMap.Search.Call.slot at headerRegion entriesFit
    -- A header byte other than the length word is outside the footprint.
    have headerKept (byte : Nat) (low : call.header.toNat ≤ byte) (high : byte < call.header.toNat + 12)
        (notLength : byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) :
        mem[byte]? = start[byte]? :=
      invariant.others byte fun footprint => by
        unfold DrainFootprint SortedMap.Search.Call.slot at footprint
        change ((frameBase initial.sp).toNat - 16 ≤ byte ∧ byte < (frameBase initial.sp).toNat) ∨
          (call.header.toNat + 4 ≤ byte ∧ byte < call.header.toNat + 8) ∨
          (call.data.toNat + 8 * (call.position + 1) ≤ byte ∧
            byte < call.data.toNat + 8 * call.length.toNat) at footprint
        change call.header.toNat + 12 ≤ call.data.toNat + 8 * 0 ∨
          call.data.toNat + 8 * call.length.toNat ≤ call.header.toNat at headerRegion
        omega
    have dataWord : WordAt mem call.header.toNat call.data :=
      layout.dataWord.congr fun byte low high => (headerKept byte low (by omega) (by omega)).symm ▸ rfl
    have capacityWord : WordAt mem (call.header.toNat + 8) capacity :=
      layout.capacityWord.congr fun byte low high => (headerKept byte (by omega) (by omega) (by omega)).symm ▸ rfl
    have position : removing.position = call.position + 1 := by
      change SortedMap.scan .lower (before (call.position + 1 + j)).key (drained before call.position j) 0
        (BitVec.ofNat 32 (call.length.toNat - j)).toNat = call.position + 1
      rw [lengthNat]
      refine scan_stopsAt _ _ _ (fun index below => ?_) ?_ 0 _ (by omega) (by omega)
      · unfold drained
        rw [if_pos (by omega)]
        exact layout.sorted index (call.position + 1 + j) (by omega) (by omega)
      · unfold drained
        rw [if_neg (by omega)]
        exact Nat.lt_irrefl _
    have removes : removing.removes := by
      refine ⟨?_, ?_, ?_⟩
      · change (BitVec.ofNat 32 (call.length.toNat - j)).toNat ≤ capacity.toNat
        rw [lengthNat]; omega
      · rw [position]
        change call.position + 1 < (BitVec.ofNat 32 (call.length.toNat - j)).toNat
        rw [lengthNat]; omega
      · rw [position]
        change (drained before call.position j (call.position + 1)).key = (before (call.position + 1 + j)).key
        unfold drained
        rw [if_neg (by omega)]
    have vectorIndex : removing.vector.index.toNat = call.position + 1 :=
      removing.vectorIndex.trans position
    have header : PairRemove.Header { original with mem := mem } removing.vector :=
      ⟨layout.headerFits, mappedTransfer layout.lengthReadable rfl,
        mappedTransfer layout.capacityReadable rfl, invariant.lengthWord, capacityWord⟩
    have stack : SortedMap.Remove.Stack (removeBase base) { original with mem := mem } removing
        state.sp := by
      rw [regs.sp]
      exact ⟨layout.stackFits, fun offset member => mappedTransfer (layout.stackReadable offset member) rfl,
        fun offset member => mappedTransfer (layout.stackWritable offset member) rfl,
        layout.stackApartHeader, fun index bound => layout.stackApartEntries index (by
          change index < (BitVec.ofNat 32 (call.length.toNat - j)).toNat at bound
          rw [lengthNat] at bound; omega),
        layout.stackApartCode, layout.stackApartSearch, layout.stackApartVector⟩
    have entriesBound (index : Nat) (bound : index < removing.length.toNat) :
        index < call.length.toNat - j := by
      change index < (BitVec.ofNat 32 (call.length.toNat - j)).toNat at bound
      rwa [lengthNat] at bound
    have keys : SortedMap.Search.Keys { original with mem := mem } removing.search := by
      refine ⟨?_, mappedTransfer layout.dataReadable rfl, dataWord,
        fun index bound => mappedTransfer (layout.keyReadable index (by have := entriesBound index bound; omega)) rfl,
        fun index bound => (invariant.entries index (entriesBound index bound)).1⟩
      change call.data.toNat + 8 * (BitVec.ofNat 32 (call.length.toNat - j)).toNat ≤ 2 ^ 32
      rw [lengthNat]
      change call.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at entriesFit
      omega
    have buffer : PairRemove.Buffer (SortedMap.Remove.vectorBase (removeBase base))
        { original with mem := mem } removing.vector := by
      refine ⟨?_, mappedTransfer layout.dataReadable rfl, dataWord,
        mappedTransfer layout.lengthWritable rfl, layout.lengthAway,
        fun index bound => invariant.entries index (entriesBound index bound),
        fun index low high => ?_, fun index low high => ?_,
        fun index bound => layout.separated index (by have := entriesBound (index + 1) bound; omega),
        fun index low high => layout.entriesAway index (by rw [vectorIndex] at low; exact low)
          (by have := entriesBound (index + 1) high; omega)⟩
      · change call.data.toNat + 8 * (BitVec.ofNat 32 (call.length.toNat - j)).toNat ≤ 2 ^ 32
        rw [lengthNat]
        change call.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at entriesFit
        omega
      · rw [vectorIndex] at low
        have mapped := layout.pairReadable index low (by have := entriesBound index high; omega)
        exact ⟨mappedTransfer mapped.1 rfl, mappedTransfer mapped.2 rfl⟩
      · rw [vectorIndex] at low
        have mapped := layout.pairWritable index low (by have := entriesBound (index + 1) high; omega)
        exact ⟨mappedTransfer mapped.1 rfl, mappedTransfer mapped.2 rfl⟩
    -- The removal footprint lies inside the loop's footprint.
    have removalFootprint (byte : Nat)
        (outside : ¬ DrainFootprint (frameBase initial.sp) call.header call.search call.position
          call.length.toNat byte) :
        (byte < state.sp.toNat - 16 ∨ state.sp.toNat ≤ byte) ∧
        (byte < removing.header.toNat + 4 ∨ removing.header.toNat + 8 ≤ byte) ∧
        (byte < removing.vector.slot removing.vector.index.toNat ∨
          removing.vector.slot (removing.length.toNat - 1) ≤ byte) := by
      rw [regs.sp]
      unfold DrainFootprint SortedMap.Search.Call.slot at outside
      change ¬ (((frameBase initial.sp).toNat - 16 ≤ byte ∧ byte < (frameBase initial.sp).toNat) ∨
          (call.header.toNat + 4 ≤ byte ∧ byte < call.header.toNat + 8) ∨
          (call.data.toNat + 8 * (call.position + 1) ≤ byte ∧
            byte < call.data.toNat + 8 * call.length.toNat)) at outside
      refine ⟨by omega, by change byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte; omega, ?_⟩
      rw [vectorIndex]
      change byte < call.data.toNat + 8 * (call.position + 1) ∨
        call.data.toNat + 8 * ((BitVec.ofNat 32 (call.length.toNat - j)).toNat - 1) ≤ byte
      rw [lengthNat]
      have shorter : 8 * (call.length.toNat - j - 1) ≤ 8 * call.length.toNat := by omega
      omega
    have keySlotFits : scratch.slot j < 2 ^ 32 := by
      have fits := layout.keysFit
      unfold Scratch.slot at fits ⊢; omega
    have keyWord : WordAt mem state.s1.toNat (before (call.position + 1 + j)).key := by
      rw [regs.cursor, scratch.wordSlotNat keySlotFits]
      exact (collectedWord j (by omega)).congr fun byte low high =>
        (invariant.others byte (layout.collectedApart j (by omega) byte low high)).symm ▸ rfl
    have atLoop : state.pc = 0x164#32 := by
      rw [regs.pc, if_neg (by omega)]
    obtain ⟨final, after, ranNext, pc, sp, s0, s1, s2, -, -, -, -, -, -, -, -, dataAfter, lengthAfter,
        capacityAfter, entriesAfter, keptAfter⟩ :=
      removal frame mem imageOf removeCode searchCode vectorCode state atLoop
        (before (call.position + 1 + j)).key (by rw [regs.cursor]; exact layout.collectedReadable j (by omega))
        keyWord removing regs.header.symm rfl removes header stack keys buffer
        fun byte low high => removalFootprint byte (layout.codeKept byte (Or.inl ⟨low, high⟩)).2
    have keyCount := layout.keyCountFits
    refine ⟨final, after, ?_, ⟨?_, sp.trans regs.sp, s0.trans regs.header, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · rw [drainCount, runAdd, ran, Option.bind_some]
      exact ranNext
    · rw [pc, regs.remaining, remainingNext (by omega) (by omega)]
      by_cases last : j + 1 = collected
      · rw [if_pos ((remainingZero (by omega)).mpr (by omega)), if_pos last]
      · rw [if_neg (fun zero => last (by have := (remainingZero (by omega)).mp zero; omega)), if_neg last]
    · rw [s1, regs.cursor]; exact scratch.wordSlotNext j
    · rw [s2, regs.remaining, remainingNext (by omega) (by omega),
        show collected - j - 1 = collected - (j + 1) by omega]
    · have length := lengthAfter
      change WordAt after (call.header.toNat + 4)
        (BitVec.ofNat 32 ((BitVec.ofNat 32 (call.length.toNat - j)).toNat - 1)) at length
      rw [lengthNat] at length
      rw [show call.length.toNat - (j + 1) = call.length.toNat - j - 1 by omega]
      exact length
    · intro index bound
      have entry := entriesAfter index (by
        change index < (BitVec.ofNat 32 (call.length.toNat - j)).toNat - 1
        rw [lengthNat]; omega)
      change PairAt after (call.search.slot index)
        (if index < removing.vector.index.toNat then drained before call.position j index
          else drained before call.position j (index + 1)) at entry
      rw [vectorIndex, drained_succ] at entry
      exact entry
    · intro byte outside
      obtain ⟨frameOutside, lengthOutside, slotsOutside⟩ := removalFootprint byte outside
      rw [keptAfter byte frameOutside lengthOutside slotsOutside]
      exact invariant.others byte outside

/-- A layout stated for one memory holds for another that agrees on the code,
the header's data and capacity words. -/
theorem DrainLayout.transfer {base : Word} {original : Machine} {call : Call} {capacity : Word}
    {before : Nat → Pair} {scratch : Scratch} {collected : Nat} {sp : Word}
    {start other : ByteMemory}
    (layout : DrainLayout base original call capacity before scratch collected sp start)
    (code : ∀ byte, ((base.toNat ≤ byte ∧ byte < base.toNat + 4 * DeleteTable.instructions.length) ∨
      ((removeBase base).toNat ≤ byte ∧ byte < (removeBase base).toNat + 144) ∨
      ((SortedMap.Remove.searchBase (removeBase base)).toNat ≤ byte ∧
        byte < (SortedMap.Remove.searchBase (removeBase base)).toNat + 52) ∨
      ((SortedMap.Remove.vectorBase (removeBase base)).toNat ≤ byte ∧
        byte < (SortedMap.Remove.vectorBase (removeBase base)).toNat + 100)) →
      other[byte]? = start[byte]?)
    (header : ∀ byte, call.header.toNat ≤ byte → byte < call.header.toNat + 12 →
      (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) → other[byte]? = start[byte]?) :
    DrainLayout base original call capacity before scratch collected sp other :=
  { layout with
    codeKept := fun byte inside =>
      ⟨(code byte inside).trans (layout.codeKept byte inside).1, (layout.codeKept byte inside).2⟩
    dataWord := layout.dataWord.congr fun byte low high => header byte low (by omega) (by omega)
    capacityWord := layout.capacityWord.congr fun byte low high =>
      header byte (by omega) (by omega) (by omega) }

-- `slli s2, s2, 2` on the key count.
theorem countShift {count : Nat} (fits : 4 * count < 2 ^ 32) :
    BitVec.ofNat 32 count <<< (2 : Nat) = BitVec.ofNat 32 (4 * count) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show count < 2 ^ 32 by omega)]
  change count * 4 % 2 ^ 32 = 4 * count % 2 ^ 32
  rw [Nat.mul_comm]

theorem Scratch.wordSlotZero (scratch : Scratch) : scratch.wordSlot 0 = scratch.data := by
  unfold Scratch.wordSlot Scratch.slot
  rw [Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The removal loop's entry from `+0x154`: no collected keys go straight to
the epilogue in two instructions; otherwise four instructions reach the loop
at `+0x164`. -/
theorem drainEntry {base : Word} {original : Machine} {memory : ByteMemory}
    {scratch : Scratch} {collected : Nat}
    (machine : MachineState original)
    (image : CodeImage DeleteTable.instructions base { original with mem := memory })
    (state : Snapshot) (atStart : state.pc = 0x154#32)
    (lengthReadable : Readable original (state.s1 + 0x4#32))
    (lengthWord : WordAt memory (state.s1 + 0x4#32).toNat (BitVec.ofNat 32 collected))
    (dataReadable : Readable original state.s1)
    (dataWord : WordAt memory state.s1.toNat scratch.data) (fits : 4 * collected < 2 ^ 32) :
    (collected = 0 → run 2 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        { state with pc := 0x184#32, s2 := BitVec.ofNat 32 collected })) ∧
    (0 < collected → run 4 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        { state with
          pc := 0x164#32, s1 := scratch.wordSlot 0,
          s2 := BitVec.ofNat 32 (4 * (collected - 0)) })) := by
  constructor
  · intro none
    refine runStep (step154 machine image _ atStart _ lengthReadable lengthWord) ?_
    refine runStep (step158 machine image _ rfl) ?_
    rw [if_pos (by rw [none])]
    rfl
  · intro some
    have nonzero : BitVec.ofNat 32 collected ≠ 0#32 := by
      intro zero
      have := (remainingZero (count := collected) fits).mp (by
        rw [← countShift fits, zero]; rfl)
      omega
    refine runStep (step154 machine image _ atStart _ lengthReadable lengthWord) ?_
    refine runStep (step158 machine image _ rfl) ?_
    rw [if_neg nonzero]
    refine runStep (step15c machine image _ rfl _ dataReadable dataWord) ?_
    refine runStep (step160 machine image _ rfl) ?_
    rw [countShift fits, Nat.sub_zero, scratch.wordSlotZero]
    rfl

end Riscfree.RangeInsert.DeleteExtra
