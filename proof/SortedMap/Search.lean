import SortedMap.Spec
import RawVec.Access

/-!
# The part of the two sorted-map searches that the machine code does not fix

`sorted_map_lower_bound` and `sorted_map_upper_bound`
(`research/vec-ffi/linked/sorted_map.rs`) are two instances of one generic
linear scan. They differ in one branch, which decides whether the scan passes
over an entry: `Bound.passes .lower` or `Bound.passes .upper`. This module
gives what both share: the scan as a function on the buffer's contents
(`scan`), its relation to the mathematical `rank` for a sorted map, the call
record, the premises, and the slot arithmetic.

`scan` and `rank` are separate on purpose. `scan` describes what the routine
does for any contents, sorted or not. `scan_eq_rank` shows that for a sorted
map it computes the mathematical rank.
-/

namespace Riscfree.SortedMap

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

-- The first `length` elements of a buffer, as a list.
def entriesOf (old : Nat → Pair) (length : Nat) : List Pair :=
  (List.range length).map old

theorem entriesOf_length (old : Nat → Pair) (length : Nat) :
    (entriesOf old length).length = length := by
  simp [entriesOf]

theorem entriesOf_getElem (old : Nat → Pair) (length index : Nat)
    (bound : index < (entriesOf old length).length) :
    (entriesOf old length)[index] = old index := by
  simp [entriesOf]

theorem sorted_entriesOf {old : Nat → Pair} {length : Nat} (sorted : Sorted (entriesOf old length))
    {first second : Nat} (ordered : first < second) (bound : second < length) :
    (old first).key.toNat < (old second).key.toNat := by
  have pairwise := List.pairwise_iff_getElem.mp sorted first second
    (by rw [entriesOf_length]; omega) (by rw [entriesOf_length]; exact bound) ordered
  simpa only [entriesOf_getElem] using pairwise

-- A search that passes an entry passes every entry with a smaller key.
theorem Bound.passes_mono (bound : Bound) {entry other key : Word}
    (smaller : entry.toNat ≤ other.toNat) (passes : bound.passes other key = true) :
    bound.passes entry key = true := by
  cases bound <;> simp only [Bound.passes, decide_eq_true_eq] at passes ⊢ <;> omega

/-! ## The scan -/

-- Scan at most `remaining` entries from `index`, stopping at the first entry
-- the search does not pass.
def scan (bound : Bound) (key : Word) (old : Nat → Pair) : Nat → Nat → Nat
  | index, 0 => index
  | index, remaining + 1 =>
    if bound.passes (old index).key key then scan bound key old (index + 1) remaining else index

section Scan

variable {bound : Bound} {key : Word} {old : Nat → Pair}

theorem scan_bounds (index remaining : Nat) :
    index ≤ scan bound key old index remaining ∧
      scan bound key old index remaining ≤ index + remaining := by
  induction remaining generalizing index with
  | zero => simp [scan]
  | succ remaining previous =>
    simp only [scan]
    split
    · have := previous (index + 1)
      omega
    · omega

theorem scan_passes (index remaining : Nat) :
    ∀ observed, index ≤ observed → observed < scan bound key old index remaining →
      bound.passes (old observed).key key = true := by
  induction remaining generalizing index with
  | zero => intro observed low high; simp [scan] at high; omega
  | succ remaining previous =>
    intro observed low high
    simp only [scan] at high
    split at high
    · rename_i passes
      by_cases same : observed = index
      · rw [same]; exact passes
      · exact previous (index + 1) observed (by omega) high
    · omega

theorem scan_stops (index remaining : Nat)
    (early : scan bound key old index remaining < index + remaining) :
    bound.passes (old (scan bound key old index remaining)).key key = false := by
  induction remaining generalizing index with
  | zero => simp [scan] at early
  | succ remaining previous =>
    simp only [scan] at early ⊢
    split at early
    · rename_i passes
      rw [if_pos passes]
      exact previous (index + 1) (by omega)
    · rename_i fails
      rw [if_neg fails]
      simpa using fails

-- Passing an entry moves the scan forward, and failing it stops the scan.
theorem scan_pass (index remaining : Nat) (passes : bound.passes (old index).key key = true) :
    scan bound key old index (remaining + 1) = scan bound key old (index + 1) remaining := by
  simp [scan, passes]

theorem scan_fail (index remaining : Nat) (fails : bound.passes (old index).key key = false) :
    scan bound key old index (remaining + 1) = index := by
  simp [scan, fails]

-- The count of a predicate over `range length` that holds exactly below `boundary`.
private theorem countRange (predicate : Nat → Bool) (length boundary : Nat) (within : boundary ≤ length)
    (holds : ∀ index < length, predicate index = true ↔ index < boundary) :
    (List.range length).countP predicate = boundary := by
  induction length generalizing boundary with
  | zero => simp only [List.range_zero, List.countP_nil]; omega
  | succ length previous =>
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    by_cases top : boundary = length + 1
    · subst top
      have below := previous length (Nat.le_refl _) fun index bound => by
        rw [holds index (by omega)]; omega
      have last : predicate length = true := (holds length (by omega)).mpr (by omega)
      simp [below, last]
    · have below := previous boundary (by omega) fun index bound => holds index (by omega)
      have last : predicate length = false := by
        cases value : predicate length
        · rfl
        · have := (holds length (by omega)).mp value
          omega
      simp [below, last]

-- For a sorted map, the scan computes the rank.
theorem scan_eq_rank {length : Nat} (sorted : Sorted (entriesOf old length)) :
    scan bound key old 0 length = rank bound (entriesOf old length) key := by
  have bounds := scan_bounds (bound := bound) (key := key) (old := old) 0 length
  let result := scan bound key old 0 length
  unfold rank entriesOf
  rw [List.countP_map]
  symm
  apply countRange _ length result (by omega)
  intro index inside
  simp only [Function.comp_apply]
  constructor
  · intro passes
    apply Classical.byContradiction
    intro notBelow
    have early : result < 0 + length := by omega
    have stops := scan_stops (bound := bound) (key := key) (old := old) 0 length early
    by_cases same : index = result
    · rw [show index = scan bound key old 0 length from same, stops] at passes
      exact Bool.noConfusion passes
    · have larger := sorted_entriesOf sorted (show result < index by omega) inside
      rw [Bound.passes_mono _ (Nat.le_of_lt larger) passes] at stops
      exact Bool.noConfusion stops
  · intro below
    exact scan_passes 0 length index (by omega) below

end Scan

/-! ## The call -/

namespace Search

structure Call where
  header : Word
  key : Word
  length : Word
  data : Word
  old : Nat → Pair

namespace Call

def slot (call : Call) (index : Nat) : Nat := call.data.toNat + 8 * index

def wordSlot (call : Call) (index : Nat) : Word := BitVec.ofNat 32 (call.slot index)

-- The routine's result: how many leading entries the search passes over.
def result (bound : Bound) (call : Call) : Nat := scan bound call.key call.old 0 call.length.toNat

-- An empty map, a scan that stops at entry `r`, and a scan that passes every
-- entry. Each pass costs five instructions.
def count (bound : Bound) (call : Call) : Nat :=
  if call.length.toNat = 0 then 4
  else if call.result bound < call.length.toNat then 7 + 5 * call.result bound
  else 6 + 5 * call.length.toNat

theorem result_le (bound : Bound) (call : Call) : call.result bound ≤ call.length.toNat := by
  have := scan_bounds (bound := bound) (key := call.key) (old := call.old) 0 call.length.toNat
  unfold result
  omega

-- `slli` by 3 and `add` give an element's address, and adding 8 steps one
-- slot. Both wrap modulo `2 ^ 32`, so neither needs a bound.
theorem slotNext (call : Call) (index : Nat) :
    call.wordSlot index + 8#32 = call.wordSlot (index + 1) := by
  rw [wordSlot, wordSlot, slot, slot, Nat.mul_succ, ← Nat.add_assoc,
    BitVec.ofNat_add (call.data.toNat + 8 * index) 8]

theorem slotShift (call : Call) (index : Word) :
    index <<< 3 + call.data = call.wordSlot index.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [wordSlot, slot, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_add_mod]
  rw [Nat.add_comm, Nat.mul_comm]

theorem slotZero (call : Call) : call.wordSlot 0 = call.data := by
  simp [wordSlot, slot]

end Call

/-! ## Premises

Every call needs the readable length word. A call on a nonempty map also
needs the data pointer and the key word of each live entry. The routine
never reads a value word or the capacity.
-/

structure Header (original : Machine) (call : Call) : Prop where
  fits : call.header.toNat + 8 ≤ 2 ^ 32
  lengthReadable : Readable original (call.header + 4)
  lengthWord : WordAt original.mem (call.header.toNat + 4) call.length

structure Keys (original : Machine) (call : Call) : Prop where
  fits : call.slot call.length.toNat ≤ 2 ^ 32
  dataReadable : Readable original call.header
  dataWord : WordAt original.mem call.header.toNat call.data
  readable : ∀ index, index < call.length.toNat → Readable original (call.wordSlot index)
  keyWord : ∀ index, index < call.length.toNat →
    WordAt original.mem (call.slot index) (call.old index).key

section Arithmetic

variable {original : Machine} {call : Call}

theorem headerOffset (header : Header original call) :
    (call.header + 4#32).toNat = call.header.toNat + 4 := by
  have fits := header.fits
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by change call.header.toNat + 4 < 2 ^ 32; omega)

theorem slotNat (keys : Keys original call) {index : Nat} (bound : index < call.length.toNat) :
    (call.wordSlot index).toNat = call.slot index := by
  have fits := keys.fits
  change call.slot index % 2 ^ 32 = call.slot index
  unfold Call.slot at fits ⊢
  omega

-- The counter `addi a0, a0, 1` keeps the entry index as a word.
theorem counterNext (index : Nat) : BitVec.ofNat 32 index + 1#32 = BitVec.ofNat 32 (index + 1) := by
  rw [BitVec.ofNat_add]

theorem counterReached {index : Nat} (bound : index + 1 ≤ call.length.toNat) :
    call.length = BitVec.ofNat 32 (index + 1) ↔ index + 1 = call.length.toNat := by
  have small := call.length.isLt
  constructor
  · intro same
    have toNat := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at toNat
    omega
  · intro same
    rw [same, Insert.ofWordNat]

end Arithmetic

end Search

end Riscfree.SortedMap
