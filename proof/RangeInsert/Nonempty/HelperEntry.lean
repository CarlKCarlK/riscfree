import RangeInsert.Nonempty.HelperReturn

/-! The caller's machine at a helper call, viewed as the helper's snapshot.
The helper tracks more registers than the caller. When the machine already
holds the helper's extra registers (`wide`), the caller's snapshot widens to
a helper snapshot without changing the machine. -/

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word)
open Empty (Snapshot)

set_option maxHeartbeats 2000000

/-- The caller's registers over the helper's extra registers from `wide`. -/
def widened (wide : DeleteExtra.Snapshot) (state : Snapshot) (pc : Word) : DeleteExtra.Snapshot :=
  { wide with
    pc := pc, ra := state.ra, sp := state.sp, s0 := state.s0, s1 := state.s1, a0 := state.a0,
    a1 := state.a1, a2 := state.a2, a3 := state.a3, a4 := state.a4, a5 := state.a5,
    s2 := state.s2, s3 := state.s3, s4 := state.s4, s5 := state.s5 }

theorem outerInside : ∀ index ∈ tracked Snapshot, index ∈ tracked DeleteExtra.Snapshot := by
  decide

-- Moving the base into the PC does not change a synchronized machine.
theorem syncShift {base other : Word} (frame : Machine) (state : DeleteExtra.Snapshot) (pc : Word)
    (same : base + state.pc = other + pc) :
    sync base frame state = sync other frame { state with pc := pc } := by
  simp only [sync]
  change write_reg_state (write_reg_state (writeTracked (tracked DeleteExtra.Snapshot)
      (RegisterView.value state) frame) Register.nextPC (base + state.pc)) Register.PC
        (base + state.pc) = _
  rw [same]
  rfl

/-- At a helper call, the caller's machine is the helper's snapshot. -/
theorem enteredAsHelper {base helperBase : Word} {original : Machine} (memory : ByteMemory)
    (wide : DeleteExtra.Snapshot) (wideEntry : original = sync base original { wide with pc := 0 })
    (state : Snapshot) (target : base + state.pc = helperBase + 0#32) :
    sync base { original with mem := memory } state =
      sync helperBase { original with mem := memory } (widened wide state 0) := by
  have background : ({ original with mem := memory } : Machine) =
      sync base { original with mem := memory } { wide with pc := 0 } := by
    have moved : ({ original with mem := memory } : Machine) =
        { sync base original { wide with pc := 0 } with mem := memory } := by
      conv_lhs => rw [wideEntry]
    have withMem := syncWithMem base original { wide with pc := 0 } memory
    exact moved.trans withMem
  have inside := syncInside (frame := { original with mem := memory }) base base
    { wide with pc := 0 } (widened wide state state.pc) state outerInside
    (fun index _ => by fin_cases index <;> rfl) rfl
  have shifted := syncShift (base := base) (other := helperBase) { original with mem := memory }
    (widened wide state state.pc) 0 target
  have rewritten := congrArg (fun machine : Machine => sync base machine state) background
  have chain := rewritten.trans (inside.trans shifted)
  exact chain

/-- The helper's entry equation for that machine. -/
theorem helperEntryEquation {helperBase : Word} (frame : Machine) (state : DeleteExtra.Snapshot)
    (atEntry : state.pc = 0) :
    sync helperBase frame state =
      sync helperBase (sync helperBase frame state) { state with pc := 0 } := by
  rw [syncSync]
  cases state
  subst atEntry
  rfl

end Riscfree.RangeInsert.Nonempty
