import RangeInsert.Bounded.OuterLayout
import RangeInsert.Bounded.HelperFrame

namespace Riscfree.RangeInsert.Bounded.OuterView

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word)
open Empty (Snapshot)

set_option maxHeartbeats 2000000

/-- The caller's registers after a helper call: the helper's final values
over the caller's own registers. -/
def helperReturned (pc : Word) (caller : Snapshot) (state : Helper.Snapshot) : Snapshot :=
  { caller with
    pc := pc, ra := state.ra, sp := state.sp, t1 := state.t1, s0 := state.s0, s1 := state.s1,
    a0 := state.a0, a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4,
    a5 := state.a5, a6 := state.a6, a7 := state.a7, s2 := state.s2, s3 := state.s3,
    s4 := state.s4, s5 := state.s5, s6 := state.s6, s7 := state.s7, s8 := state.s8,
    s9 := state.s9, s10 := state.s10 }

theorem helperInside : ∀ index ∈ tracked Helper.Snapshot, index ∈ tracked Snapshot := by
  decide

/-- The helper's end machine, over the caller's machine, is the caller's
snapshot of the returned registers. -/
theorem helperReturnedSync (base helperBase pc : Word) (background : Machine) (caller : Snapshot)
    (state : Helper.Snapshot) (target : base + pc = helperBase + state.pc) :
    sync helperBase (sync base background caller) state =
      sync base background (helperReturned pc caller state) :=
  syncInside base helperBase caller (helperReturned pc caller state) state helperInside
    (fun index _ => by fin_cases index <;> rfl) target

/-- The helper's registers in the caller's snapshot. -/
def helperView (state : Snapshot) (pc : Word) : Helper.Snapshot where
  pc := pc
  ra := state.ra
  sp := state.sp
  t1 := state.t1
  s0 := state.s0
  s1 := state.s1
  a0 := state.a0
  a1 := state.a1
  a2 := state.a2
  a3 := state.a3
  a4 := state.a4
  a5 := state.a5
  a6 := state.a6
  a7 := state.a7
  s2 := state.s2
  s3 := state.s3
  s4 := state.s4
  s5 := state.s5
  s6 := state.s6
  s7 := state.s7
  s8 := state.s8
  s9 := state.s9
  s10 := state.s10

/-- At a helper call the caller's machine satisfies the helper's entry
equation for the projected snapshot. -/
theorem helperEntry {base helperBase : Word} (frame : Machine) (state : Snapshot)
    (target : base + state.pc = helperBase + 0#32) :
    sync base frame state =
      sync helperBase (sync base frame state) { helperView state 0 with pc := 0 } := by
  have inside := syncInside (frame := frame) base helperBase state state (helperView state 0)
    helperInside (fun index _ => by fin_cases index <;> rfl) target
  exact inside.symm

end Riscfree.RangeInsert.Bounded.OuterView
