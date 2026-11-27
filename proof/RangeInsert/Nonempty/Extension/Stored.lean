import RangeInsert.Nonempty.Extension

namespace Riscfree.RangeInsert.Nonempty

open Riscfree.RV32
open Riscfree.RawVec (Word)

theorem writeWordsAppend (original : ByteMemory)
    (first later : List (Word × Word)) :
    writeWords original (first ++ later) = writeWords (writeWords original first) later := by
  induction first generalizing original with
  | nil => rfl
  | cons write first ih =>
    obtain ⟨address, value⟩ := write
    exact ih (storeWord original address.toNat value)

theorem writeWordsAt (original : ByteMemory) (before after : List (Word × Word))
    (address value : Word)
    (apart : ∀ write ∈ after, ∀ byte, address.toNat ≤ byte → byte < address.toNat + 4 →
      byte < write.1.toNat ∨ write.1.toNat + 4 ≤ byte) :
    WordAt (writeWords original (before ++ (address, value) :: after)) address.toNat value := by
  rw [writeWordsAppend]
  change WordAt (writeWords (storeWord (writeWords original before) address.toNat value) after)
    address.toNat value
  exact (wordAtStore _ _ _).congr fun byte low high =>
    writeWordsOutside _ _ byte fun write member => apart write member byte low high

private theorem callerSlots {sp : Word} (fits : 48 ≤ sp.toNat) :
    let lower := Empty.frameBase sp
    (lower + 4#32).toNat = sp.toNat - 48 + 4 ∧
      (lower + 8#32).toNat = sp.toNat - 48 + 8 ∧
      (lower + 12#32).toNat = sp.toNat - 48 + 12 ∧
      (lower + 16#32).toNat = sp.toNat - 48 + 16 := by
  exact ⟨Empty.frameAddress fits 4#32 (by decide), Empty.frameAddress fits 8#32 (by decide),
    Empty.frameAddress fits 12#32 (by decide), Empty.frameAddress fits 16#32 (by decide)⟩

/-- The three scratch header words installed by the extension prefix. -/
theorem extensionScratchWords (initial : Empty.Snapshot) (call : Call) (low high : Word)
    (memory : ByteMemory) (fits : 48 ≤ initial.sp.toNat) :
    let base := (Empty.frameBase initial.sp + 8#32).toNat
    let stored := extensionStored initial call low high memory
    WordAt stored base initial.a4 ∧ WordAt stored (base + 4) 0#32 ∧
      WordAt stored (base + 8) initial.a5 := by
  let sp := Empty.frameBase initial.sp
  obtain ⟨_, slot8, slot12, slot16⟩ := callerSlots fits
  let first : List (Word × Word) :=
    [(initial.a1, extendLow call low), (initial.a1 + 4#32, extendHigh call low high),
      (call.search.wordSlot (call.rank - 1) + 4#32, call.stop)]
  have at8 := writeWordsAt memory first [(sp + 12#32, 0#32), (sp + 16#32, initial.a5)]
    (sp + 8#32) initial.a4 (by
      intro write member byte inside last
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change byte < (sp + 12#32).toNat ∨ (sp + 12#32).toNat + 4 ≤ byte
        rw [slot8] at last
        rw [slot12]
        omega
      · change byte < (sp + 16#32).toNat ∨ (sp + 16#32).toNat + 4 ≤ byte
        rw [slot8] at last
        rw [slot16]
        omega)
  have at12 := writeWordsAt memory (first ++ [(sp + 8#32, initial.a4)]) [(sp + 16#32, initial.a5)]
    (sp + 12#32) 0#32 (by
      intro write member byte inside last
      simp only [List.mem_singleton] at member
      subst write
      change byte < (sp + 16#32).toNat ∨ (sp + 16#32).toNat + 4 ≤ byte
      rw [slot12] at last
      rw [slot16]
      omega)
  have at16 := writeWordsAt memory (first ++ [(sp + 8#32, initial.a4), (sp + 12#32, 0#32)]) []
    (sp + 16#32) initial.a5 (by simp)
  have joined12 : (sp + 12#32).toNat = (sp + 8#32).toNat + 4 := by rw [slot12, slot8, Nat.add_assoc]
  have joined16 : (sp + 16#32).toNat = (sp + 8#32).toNat + 8 := by rw [slot16, slot8, Nat.add_assoc]
  rw [joined12] at at12
  rw [joined16] at at16
  exact ⟨at8, at12, at16⟩

theorem pushedMapReference (initial : Empty.Snapshot) (memory : ByteMemory) :
    WordAt (Empty.pushed memory initial) (Empty.frameBase initial.sp + 4#32).toNat initial.a0 := by
  unfold Empty.pushed
  exact wordAtStore _ _ _

end Riscfree.RangeInsert.Nonempty
