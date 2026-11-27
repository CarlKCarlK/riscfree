import RangeInsert.Nonempty.Extension

/-! Switch from the helper's register snapshot back to the entry-point
snapshot while retaining the actual returned machine. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable)
open Empty (Snapshot)

/-- The caller's registers after a helper call: the helper's final values
over the caller's own registers. -/
def helperReturned (pc : Word) (caller : Snapshot) (state : DeleteExtra.Snapshot) : Snapshot :=
  { caller with
    pc := pc, ra := state.ra, sp := state.sp, t1 := state.t1, s0 := state.s0, s1 := state.s1,
    a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4,
    a5 := state.a5, a6 := state.a6, a7 := state.a7, s2 := state.s2, s3 := state.s3,
    s4 := state.s4, s5 := state.s5, s6 := state.s6, s7 := state.s7, s8 := state.s8,
    s9 := state.s9, s10 := state.s10 }

theorem helperInside : ∀ index ∈ tracked DeleteExtra.Snapshot, index ∈ tracked Snapshot := by
  decide

/-- The helper's end machine, over the caller's machine, is the caller's
snapshot of the returned registers. -/
theorem helperReturnedSync (base helperBase pc : Word) (background : Machine) (caller : Snapshot)
    (state : DeleteExtra.Snapshot) (target : base + pc = helperBase + state.pc) :
    sync helperBase (sync base background caller) state =
      sync base background (helperReturned pc caller state) :=
  syncInside base helperBase caller (helperReturned pc caller state) state helperInside
    (fun index _ => by fin_cases index <;> rfl) target

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
