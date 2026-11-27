import RangeInsert.Nonempty.Predecessor
import RangeInsert.Empty

/-! The linked run for a nonempty input whose end is covered by its
predecessor. After the shared prefix and the verified upper-bound search,
the entry point loads the predecessor's end, finds no strict gap, finds
that the end is already covered, and returns through the common epilogue
without writing the map or the cached length. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open InsertTable (instructions)
open Empty (Snapshot Frame frameBase OutsideFrame pushed pushedOutside restore restoreRegisters
  returnPc)

set_option maxHeartbeats 2000000

/-- The exact instruction count of the covered path: 19 to the call, the
verified search, 16 to the epilogue, and the 9-instruction epilogue. -/
def Call.containedCount (call : Call) : Nat := 44 + call.search.count .upper

/-- Premises of the covered path. `found` and `covered` select the path:
some key is at most `start`, and the last such entry ends at or after
`stop`. The path writes neither the map nor the cached length, so it needs
no write permission outside the frame. -/
structure ContainedPremises (base returnAddress : Word) (original : Machine) (initial : Snapshot)
    (call : Call) : Prop extends Frame base returnAddress original initial where
  arguments : Arguments initial call
  map : Map base original initial.sp call
  nonempty : call.start.toNat ≤ call.stop.toNat
  found : 0 < call.rank
  covered : call.stop.toNat ≤ call.predecessor.value.toNat

-- No strict gap follows a predecessor that ends at or after `start`,
-- including a predecessor that ends at `u32::MAX`.
theorem noStrictGap {predecessorEnd start : Word} (reaches : start.toNat ≤ predecessorEnd.toNat) :
    Step.lessWord predecessorEnd 0xffffffff#32 &&& Step.lessWord (predecessorEnd + 1#32) start =
      0#32 := by
  unfold Step.lessWord
  by_cases below : predecessorEnd.toNat < (0xffffffff#32).toNat
  · have noGap : ¬ (predecessorEnd + 1#32).toNat < start.toNat := by
      rw [BitVec.toNat_add]
      change ¬ (predecessorEnd.toNat + 1) % 2 ^ 32 < start.toNat
      change predecessorEnd.toNat < 4294967295 at below
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg noGap]
    split <;> rfl
  · rw [if_neg below]
    split <;> rfl

theorem runContained {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (premises : ContainedPremises base returnAddress original initial call) :
    ∃ state : Snapshot,
      run call.containedCount (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := pushed original.mem initial }
          (restore initial state (returnAddress - base))) := by
  obtain ⟨endState, toSearch, rankWord⟩ :=
    toPredecessor premises.toFrame premises.arguments premises.map premises.nonempty
  have machine := premises.mode.toMachineState
  have image := premises.toFrame.pushedImage
  have fits := premises.frameFits
  have map := premises.map
  have arguments := premises.arguments
  have found := premises.found
  have rankBound := call.rank_le
  have lengthSmall := call.length.isLt
  have keys := map.keys (by omega)
  obtain ⟨index, indexNext⟩ : ∃ index, index + 1 = call.rank := ⟨call.rank - 1, by omega⟩
  have inside : index < call.length.toNat := by omega
  have predecessorAt : call.predecessor = call.old index := by
    unfold Call.predecessor
    rw [← indexNext, Nat.add_sub_cancel]
  have rankNat : (BitVec.ofNat 32 call.rank).toNat = call.rank := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have rankNonzero : BitVec.ofNat 32 call.rank ≠ 0#32 := by
    intro zero
    have toNat := congrArg BitVec.toNat zero
    rw [rankNat] at toNat
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at toNat
    omega
  have slotNext : call.search.wordSlot index + 8#32 = call.search.wordSlot call.rank := by
    rw [call.search.slotNext index, indexNext]
  have dataAddress :
      call.data + BitVec.ofNat 32 call.rank <<< (3 : Nat) = call.search.wordSlot call.rank := by
    rw [BitVec.add_comm]
    have shifted := call.search.slotShift (BitVec.ofNat 32 call.rank)
    rw [rankNat] at shifted
    exact shifted
  have keyAddress : call.search.wordSlot call.rank + 0xfffffff8#32 = call.search.wordSlot index := by
    rw [← slotNext, BitVec.add_assoc, show 8#32 + 0xfffffff8#32 = 0#32 from rfl, BitVec.add_zero]
  have valueAddress :
      call.search.wordSlot call.rank + 0xfffffffc#32 = call.search.wordSlot index + 4#32 := by
    rw [← slotNext, BitVec.add_assoc, show 8#32 + 0xfffffffc#32 = 4#32 from rfl]
  have slotFits : call.search.slot index + 8 ≤ 2 ^ 32 := by
    have total := keys.fits
    unfold SortedMap.Search.Call.slot at total ⊢
    change call.search.data.toNat + 8 * index + 8 ≤ 2 ^ 32
    change call.search.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at total
    have scaled : 8 * index + 8 ≤ 8 * call.length.toNat := by omega
    omega
  have keyNat : (call.search.wordSlot index).toNat = call.search.slot index :=
    SortedMap.Search.slotNat keys inside
  have valueNat : (call.search.wordSlot index + 4#32).toNat = call.search.slot index + 4 := by
    rw [BitVec.toNat_add, keyNat]
    exact Nat.mod_eq_of_lt (by change call.search.slot index + 4 < 2 ^ 32; omega)
  have keyNonnull : call.search.wordSlot index ≠ 0#32 := by
    intro zero
    have toNat := congrArg BitVec.toNat zero
    rw [keyNat] at toNat
    have positive := map.dataNonnull
    unfold SortedMap.Search.Call.slot at toNat
    change call.data.toNat + 8 * index = 0 at toNat
    omega
  constructor
  rw [show call.containedCount = (19 + call.search.count .upper) + 25 by
      unfold Call.containedCount; omega,
    runAdd, toSearch, Option.bind_some]
  refine runStep (branchFound machine image _ rfl (by
    change endState.a0 ≠ 0#32
    rw [rankWord]
    exact rankNonzero)) ?_
  refine runStep (step50 machine image _ rfl) ?_
  refine runStep (step54 machine image _ rfl) ?_
  refine runStep (step58 machine image _ rfl call.data (by
    change Readable original initial.a0
    rw [arguments.header]
    exact keys.dataReadable) (by
    change WordAt (pushed original.mem initial) initial.a0.toNat call.data
    rw [arguments.header]
    exact pushedWord initial fits keys.dataWord fun byte low high =>
      map.headerOutside byte low (by omega))) ?_
  refine runStep (step5c machine image _ rfl) ?_
  refine runStep (step60 machine image _ rfl) ?_
  refine runStep (step64 machine image _ rfl) ?_
  refine runStep (step68 machine image _ rfl) ?_
  refine runStep (branchKeyPointer machine image _ rfl (by
    change call.data + endState.a0 <<< (3 : Nat) + 0xfffffff8#32 ≠ 0#32
    rw [rankWord, dataAddress, keyAddress]
    exact keyNonnull)) ?_
  refine runStep (step70 machine image _ rfl call.predecessor.value (by
    change Readable original (call.data + endState.a0 <<< (3 : Nat) + 0xfffffffc#32)
    rw [rankWord, dataAddress, valueAddress]
    exact map.valueReadable index inside) (by
    change WordAt (pushed original.mem initial)
      (call.data + endState.a0 <<< (3 : Nat) + 0xfffffffc#32).toNat call.predecessor.value
    rw [rankWord, dataAddress, valueAddress, valueNat, predecessorAt]
    exact pushedWord initial fits (map.valueWord index inside) fun byte low high =>
      map.entriesOutside index inside byte (by omega) (by omega))) ?_
  refine runStep (step74 machine image _ rfl) ?_
  refine runStep (step78 machine image _ rfl) ?_
  refine runStep (step7c machine image _ rfl) ?_
  refine runStep (step80 machine image _ rfl) ?_
  refine runStep (branchTouches machine image _ rfl (by
    change Step.lessWord call.predecessor.value 0xffffffff#32 &&&
      Step.lessWord (call.predecessor.value + 1#32) initial.a2 = 0#32
    rw [arguments.start]
    exact noStrictGap (Nat.le_trans premises.nonempty premises.covered))) ?_
  refine runStep (branchCovered machine image _ rfl (by
    change initial.a3.toNat ≤ call.predecessor.value.toNat
    rw [arguments.stop]
    exact premises.covered)) ?_
  exact premises.toFrame.epilogue _ rfl rfl

/-- A nonempty input covered by its predecessor returns after exactly
`44 + upper-bound count` instructions. Every register except PC, nextPC,
and a0–a5 is preserved, including the stack pointer and the callee-saved
registers. Only the entry's 48-byte stack frame can be modified, so the
map and the cached length are unchanged. -/
theorem ContainedPremises.run {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call}
    (premises : ContainedPremises base returnAddress original initial call) :
    ∃ final, Riscfree.RV32.run call.containedCount original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (∀ key ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]? := by
  obtain ⟨state, ran⟩ := runContained premises
  let final := restore initial state (returnAddress - base)
  have pc := returnPc (base := base) { original with mem := pushed original.mem initial } final rfl
  have registers := restoreRegisters premises.entry (pushed original.mem initial) state
    (returnAddress - base)
  refine ⟨_, (congrArg (Riscfree.RV32.run call.containedCount) premises.entry).trans ran,
    pc, registers, fun byte outside => ?_⟩
  rw [syncMem]
  exact pushedOutside original.mem initial premises.frameFits byte outside

end Riscfree.RangeInsert.Nonempty
