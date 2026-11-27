import RangeInsert.Nonempty.HelperReturn

/-! The caller's machine at a helper call, viewed as the helper's snapshot.
The caller's snapshot tracks every register the helper does, so the helper's
view is a projection and the machine is unchanged. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word)
open Empty (Snapshot)

set_option maxHeartbeats 2000000

/-- The helper's registers in the caller's snapshot. -/
def helperView (state : Snapshot) (pc : Word) : DeleteExtra.Snapshot where
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

end Riscfree.RangeInsert.Nonempty
