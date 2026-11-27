import RangeInsert.Nonempty.Extension

/-! Switch from the helper's register snapshot back to the entry-point
snapshot while retaining the actual returned machine. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable)
open Empty (Snapshot)

def helperReturned (pc : Word) (state : DeleteExtra.Snapshot) : Snapshot where
  pc := pc
  sp := state.sp
  ra := state.ra
  s0 := state.s0
  s1 := state.s1
  a0 := state.a0
  a1 := state.a1
  a2 := state.a2
  a3 := state.a3
  a4 := state.a4
  a5 := state.a5
  s2 := state.s2
  s3 := state.s3
  s4 := state.s4
  s5 := state.s5

/-- Resuming the caller keeps the helper's values in registers the caller
does not track. -/
theorem helperReturnedSync (base helperBase pc : Word) (background : Machine)
    (state : DeleteExtra.Snapshot) (target : base + pc = helperBase + state.pc) :
    sync base (sync helperBase background state) (helperReturned pc state) =
      sync helperBase background state := by
  refine syncInside helperBase base state state (helperReturned pc state)
    (by decide) ?_ target.symm
  intro index _
  fin_cases index <;> rfl

/-- The linked return at offset 0x1a8 jumps to the common epilogue. -/
theorem finishExtension {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Empty.Frame base returnAddress original initial)
    {background : Machine} (machine : MachineState background)
    (image : CodeImage InsertTable.instructions base background)
    (regions : background.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions)
    (saved : ∀ (offset : Word) (value : Word),
      offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word) →
      WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value →
      WordAt background.mem (Empty.frameBase initial.sp + offset).toNat value)
    (state : Snapshot) (atReturn : state.pc = 0x1a8#32) (sp : state.sp = Empty.frameBase initial.sp) :
    run 10 (sync base background state) =
      some (sync base background (Empty.restore initial state (returnAddress - base))) := by
  have stepped := Mutation.step1a8 (memory := background.mem) machine image state atReturn
  have unchanged : { background with mem := background.mem } = background := by
    cases background
    rfl
  rw [unchanged] at stepped
  refine runStep stepped ?_
  exact frame.epilogueFrom machine image (fun offset member =>
    mappedTransfer (frame.readable offset member) regions) saved _ rfl sp

end Riscfree.RangeInsert.Nonempty
