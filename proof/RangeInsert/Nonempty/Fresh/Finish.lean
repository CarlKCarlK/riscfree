import RangeInsert.Nonempty.Fresh.Return
import RangeInsert.Nonempty.Layout

/-! The fresh path adds the incoming range width after the deletion helper,
writes the resulting cache words, and executes the shared epilogue. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word)
open Empty (Snapshot)

def freshCacheMemory (memory : ByteMemory) (address low high : Word) : ByteMemory :=
  storeWord (storeWord memory address.toNat low) (address + 4#32).toNat high

theorem cacheHighAddress {address : Word} (fits : address.toNat + 8 ≤ 2 ^ 32) :
    (address + 4#32).toNat = address.toNat + 4 := by
  rw [BitVec.toNat_add]
  change (address.toNat + 4) % 2 ^ 32 = _
  exact Nat.mod_eq_of_lt (by omega)

theorem freshCacheOutside (memory : ByteMemory) (address low high : Word) (byte : Nat)
    (fits : address.toNat + 8 ≤ 2 ^ 32) (outside : ¬ (cacheWords address).Contains byte) :
    (freshCacheMemory memory address low high)[byte]? = memory[byte]? := by
  change ¬ (address.toNat ≤ byte ∧ byte < address.toNat + 8) at outside
  unfold freshCacheMemory
  rw [cacheHighAddress fits, storeWordOutside _ _ _ _ (by omega), storeWordOutside _ _ _ _ (by omega)]

theorem freshCacheWords (memory : ByteMemory) (address low high : Word)
    (fits : address.toNat + 8 ≤ 2 ^ 32) :
    WordAt (freshCacheMemory memory address low high) address.toNat low ∧
      WordAt (freshCacheMemory memory address low high) (address.toNat + 4) high := by
  unfold freshCacheMemory
  rw [cacheHighAddress fits]
  exact ⟨(wordAtStore _ _ _).storeOther (Or.inl (Nat.le_refl _)), wordAtStore _ _ _⟩

theorem finishFresh {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Empty.Frame base returnAddress original initial) {memory : ByteMemory}
    (image : CodeImage InsertTable.instructions base { original with mem := memory })
    (state : Snapshot) (atReturn : state.pc = 0xf8#32) (lowered : state.sp = Empty.frameBase initial.sp)
    {low high : Word} (cache : CacheStorage { original with mem := memory } state.s0 low high)
    (codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      ¬ (cacheWords state.s0).Contains byte)
    (savedApart : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      ¬ (cacheWords state.s0).Contains byte)
    (saved : ∀ (offset : Word) (value : Word),
      offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word) →
      WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value →
      WordAt memory (Empty.frameBase initial.sp + offset).toNat value) :
    let distance := state.s1 - state.s2
    let stored := freshCacheMemory memory state.s0 (freshLow low distance) (freshHigh low high distance)
    run 20 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := stored }
        (Empty.restore initial (freshCacheState state low high) (returnAddress - base))) := by
  let calculated := freshCacheState state low high
  let stored := freshCacheMemory memory state.s0 calculated.a0 calculated.a1
  have machine := frame.mode.toMachineState
  have arithmetic := freshArithmetic machine image state atReturn low high
    (mappedTransfer cache.readable.1 rfl) (mappedTransfer cache.readable.2 rfl)
    cache.low (by rw [cacheHighAddress cache.fits]; exact cache.high)
  have stores := freshStores machine image calculated rfl
    (mappedTransfer cache.writable.1 rfl) (mappedTransfer cache.writable.2 rfl) (by
      intro byte low high
      have apart := codeApart byte low high
      change ¬ (state.s0.toNat ≤ byte ∧ byte < state.s0.toNat + 8) at apart
      change byte < state.s0.toNat ∨ state.s0.toNat + 4 ≤ byte
      omega)
  have finalImage : CodeImage InsertTable.instructions base { original with mem := stored } :=
    image.withMemory stored fun byte low high => freshCacheOutside memory state.s0
      calculated.a0 calculated.a1 byte cache.fits (codeApart byte low high)
  have finalSaved (offset : Word) (value : Word)
      (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word))
      (word : WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value) :
      WordAt stored (Empty.frameBase initial.sp + offset).toNat value := by
    have bound : 20 ≤ offset.toNat ∧ offset.toNat ≤ 44 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine (saved offset value member word).congr fun byte low high => ?_
    rw [Empty.frameAddress frame.frameFits offset bound.2] at low high
    have fits := frame.frameFits
    exact freshCacheOutside memory state.s0 calculated.a0 calculated.a1 byte cache.fits
      (savedApart byte (by omega) (by omega))
  have epilogue := frame.epilogueFrom (machine.withMemory stored) finalImage
    (fun offset member => mappedTransfer (frame.readable offset member) rfl)
    finalSaved { calculated with pc := 0x124#32 } rfl lowered
  rw [show 20 = 9 + 2 + 9 by decide, runAdd, runAdd, arithmetic, Option.bind_some, stores, Option.bind_some]
  exact epilogue

end Riscfree.RangeInsert.Nonempty
