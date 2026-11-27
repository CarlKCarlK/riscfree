import RangeInsert.Nonempty.HelperReturn
import RangeInsert.Nonempty.Extension.Layout
import RangeInsert.Empty

/-! Continue the actual range insertion machine through the linked helper
and the caller's return while preserving the helper's memory result. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word)
open Empty (Snapshot)

private theorem ExtensionPrefix.writesAway {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {low high : Word}
    (premises : ExtensionPrefix base returnAddress original initial call low high)
    (byte : Nat)
    (cacheAway : byte < initial.a1.toNat ∨ initial.a1.toNat + 8 ≤ byte)
    (endAway : byte < call.search.slot (call.rank - 1) + 4 ∨
      call.search.slot (call.rank - 1) + 8 ≤ byte)
    (stackAway : byte < initial.sp.toNat - 48 + 8 ∨ initial.sp.toNat - 48 + 20 ≤ byte) :
    (extensionStored initial call low high (Empty.pushed original.mem initial))[byte]? =
      (Empty.pushed original.mem initial)[byte]? := by
  apply writeWordsOutside
  have frameFits := premises.frame.frameFits
  have highAddress : (initial.a1 + 4#32).toNat = initial.a1.toNat + 4 := by
    rw [BitVec.toNat_add]
    change (initial.a1.toNat + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by have := premises.cacheFits; omega)
  have indexInside : call.rank - 1 < call.length.toNat := by
    have := premises.found
    have := call.rank_le
    omega
  have keys := premises.map.keys (Nat.zero_lt_of_lt indexInside)
  have slot := SortedMap.Search.slotNat keys indexInside
  have endAddress : (call.search.wordSlot (call.rank - 1) + 4#32).toNat =
      call.search.slot (call.rank - 1) + 4 := by
    rw [BitVec.toNat_add, slot]
    change (call.search.slot (call.rank - 1) + 4) % 2 ^ 32 = _
    have fits := keys.fits
    change call.search.data.toNat + 8 * call.length.toNat ≤ 2 ^ 32 at fits
    change (call.search.data.toNat + 8 * (call.rank - 1) + 4) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt (by omega)
  intro write member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · change byte < initial.a1.toNat ∨ initial.a1.toNat + 4 ≤ byte
    omega
  · rw [highAddress]; omega
  · rw [endAddress]; omega
  · rw [Empty.frameAddress frameFits 8#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 8 ∨ initial.sp.toNat - 48 + 8 + 4 ≤ byte
    omega
  · rw [Empty.frameAddress frameFits 12#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 12 ∨ initial.sp.toNat - 48 + 12 + 4 ≤ byte
    omega
  · rw [Empty.frameAddress frameFits 16#32 (by decide)]
    change byte < initial.sp.toNat - 48 + 16 ∨ initial.sp.toNat - 48 + 16 + 4 ≤ byte
    omega

theorem ExtensionPrefix.writesAwayFromCode {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {low high : Word}
    (premises : ExtensionPrefix base returnAddress original initial call low high)
    (byte : Nat) (first : base.toNat ≤ byte) (last : byte < base.toNat + 4 * InsertTable.instructions.length) :
    (extensionStored initial call low high (Empty.pushed original.mem initial))[byte]? =
      original.mem[byte]? := by
  have outside := premises.frame.codeOutside byte first last
  have ⟨cacheAway, endAway⟩ := premises.codeApart byte first last
  refine (premises.writesAway byte cacheAway endAway ?_).trans
    (Empty.pushedOutside _ _ premises.frame.frameFits _ outside)
  unfold Empty.OutsideFrame at outside
  have fits := premises.frame.frameFits
  omega

theorem ExtensionPrefix.writesAwayFromSaved {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {low high : Word}
    (premises : ExtensionPrefix base returnAddress original initial call low high)
    (byte : Nat) (first : initial.sp.toNat - 28 ≤ byte) (last : byte < initial.sp.toNat) :
    (extensionStored initial call low high (Empty.pushed original.mem initial))[byte]? =
      (Empty.pushed original.mem initial)[byte]? := by
  have cacheAway : byte < initial.a1.toNat ∨ initial.a1.toNat + 8 ≤ byte := by
    by_contra neither
    push_neg at neither
    have outside := premises.cacheOutside byte neither.1 neither.2
    unfold Empty.OutsideFrame at outside
    omega
  have indexInside : call.rank - 1 < call.length.toNat := by
    have := premises.found
    have := call.rank_le
    omega
  have endAway : byte < call.search.slot (call.rank - 1) + 4 ∨
      call.search.slot (call.rank - 1) + 8 ≤ byte := by
    by_contra neither
    push_neg at neither
    have outside := premises.map.entriesOutside _ indexInside byte (by omega) (by omega)
    unfold Empty.OutsideFrame at outside
    omega
  have fits := premises.frame.frameFits
  exact premises.writesAway byte cacheAway endAway (Or.inr (by omega))

/-- After the helper returns to `+0x1a8`, the caller returns in 10
instructions. `caller` is the caller's snapshot at the call and `background`
the machine under it. -/
private theorem resumeExtension {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} (frame : Empty.Frame base returnAddress original initial)
    (background : Machine) (machine : MachineState background)
    (regions : background.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions)
    (caller : Snapshot) (helperBase : Word) (helperFinal : DeleteExtra.Snapshot) (memory : ByteMemory)
    (target : base + 0x1a8#32 = helperBase + helperFinal.pc)
    (sp : helperFinal.sp = Empty.frameBase initial.sp)
    (codeKept : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      memory[byte]? = original.mem[byte]?)
    (savedKept : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      memory[byte]? = (Empty.pushed original.mem initial)[byte]?) :
    run 10 (sync helperBase { sync base background caller with mem := memory } helperFinal) =
      some (sync base { background with mem := memory }
        (Empty.restore initial (helperReturned 0x1a8#32 caller helperFinal) (returnAddress - base))) := by
  let outer := helperReturned 0x1a8#32 caller helperFinal
  have withMem := syncWithMem base background caller memory
  have returned := helperReturnedSync base helperBase 0x1a8#32 { background with mem := memory }
    caller helperFinal target
  have resumed : sync helperBase { sync base background caller with mem := memory } helperFinal =
      sync base { background with mem := memory } outer := by
    rw [withMem]
    exact returned
  have image : CodeImage InsertTable.instructions base { background with mem := memory } :=
    (frame.code.withMemory memory codeKept).transfer regions rfl
  have saved (offset : Word) (value : Word) (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word))
      (contents : WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value) :
      WordAt ({ background with mem := memory } : Machine).mem
        (Empty.frameBase initial.sp + offset).toNat value := by
    have bound : 20 ≤ offset.toNat ∧ offset.toNat ≤ 44 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine contents.congr fun byte first last => ?_
    rw [Empty.frameAddress frame.frameFits offset bound.2] at first last
    have fits := frame.frameFits
    exact savedKept byte (by omega) (by omega)
  rw [resumed]
  exact finishExtension frame (machine.withMemory memory) image regions saved outer rfl sp

theorem completeExtensionRun {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} (frame : Empty.Frame base returnAddress original initial)
    (background : Machine) (machine : MachineState background)
    (regions : background.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions)
    (caller : Snapshot) {count helperCount : Nat} {helperCall : DeleteExtra.Call}
    {scratch : DeleteExtra.Scratch} {accepted : Nat} {helperSp : Word}
    {helperFinal : DeleteExtra.Snapshot} {memory : ByteMemory}
    (ran : run count original = some (sync base background caller))
    (ranHelper : run helperCount (sync base background caller) =
      some (sync (base + extensionHelperOffset) { sync base background caller with mem := memory }
        helperFinal))
    (result : DeleteExtra.ResultMemory helperSp helperCall scratch accepted background.mem memory)
    (target : base + 0x1a8#32 = (base + extensionHelperOffset) + helperFinal.pc)
    (sp : helperFinal.sp = Empty.frameBase initial.sp)
    (codeApart : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      ¬ DeleteExtra.HelperFootprint helperSp helperCall scratch accepted byte)
    (codeKept : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      background.mem[byte]? = original.mem[byte]?)
    (savedApart : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      ¬ DeleteExtra.HelperFootprint helperSp helperCall scratch accepted byte)
    (savedKept : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      background.mem[byte]? = (Empty.pushed original.mem initial)[byte]?) :
    run (count + helperCount + 10) original =
      some (sync base { background with mem := memory }
        (Empty.restore initial (helperReturned 0x1a8#32 caller helperFinal) (returnAddress - base))) := by
  have codeAfter : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      memory[byte]? = original.mem[byte]? := fun byte first last =>
    (result.others byte (codeApart byte first last)).trans (codeKept byte first last)
  have savedAfter : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      memory[byte]? = (Empty.pushed original.mem initial)[byte]? := fun byte first last =>
    (result.others byte (savedApart byte first last)).trans (savedKept byte first last)
  have rest := resumeExtension frame background machine regions caller (base + extensionHelperOffset)
    helperFinal memory target sp codeAfter savedAfter
  rw [runAdd, runAdd, ran, Option.bind_some, ranHelper, Option.bind_some]
  exact rest

end Riscfree.RangeInsert.Nonempty
