import Riscfree.RV32.RegisterFrame

/-!
# Register snapshots

An application proof records the relative PC and the general-purpose
registers its routine writes. `sync` writes those values over a Sail frame.
Memory and every other register keep their values from the frame.
-/

namespace Riscfree.RV32

open LeanRV32D RV32IM

-- Write a general-purpose register through Pico's index mapping, as `write_xreg` does.
def writeX (state : Machine) (index : Fin 32) (value : BitVec 32) : Machine :=
  write_reg_state state (reg_of_fin index) ((register_type_reg_of_fin_equiv index) ▸ value)

-- A snapshot type names the tracked registers and reads their values.
-- `reg_of_fin 0` is x31, so x0 must not be tracked.
class RegisterView (Snapshot : Type) where
  tracked : List (Fin 32)
  pc : Snapshot → BitVec 32
  value : Snapshot → Fin 32 → BitVec 32
  distinct : tracked.Nodup
  nonzero : (0 : Fin 32) ∉ tracked

export RegisterView (tracked)

def writeTracked : List (Fin 32) → (Fin 32 → BitVec 32) → Machine → Machine
  | [], _, frame => frame
  | index :: rest, value, frame => writeX (writeTracked rest value frame) index (value index)

-- PC and nextPC are synchronized at retirement.
def sync {S : Type} [RegisterView S] (base : BitVec 32) (frame : Machine) (state : S) : Machine :=
  let pc := base + RegisterView.pc state
  write_reg_state (write_reg_state (writeTracked (tracked S) (RegisterView.value state) frame)
    Register.nextPC pc) Register.PC pc


/-! ## General-purpose register indices -/

private def registerIndex : Register → Fin 32
  | .x1 => 1 | .x2 => 2 | .x3 => 3 | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7 | .x8 => 8
  | .x9 => 9 | .x10 => 10 | .x11 => 11 | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19 | .x20 => 20 | .x21 => 21 | .x22 => 22
  | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27 | .x28 => 28 | .x29 => 29
  | .x30 => 30 | .x31 => 31 | _ => 0

private theorem registerIndexOf (index : Fin 32) (nonzero : index ≠ 0) :
    registerIndex (reg_of_fin index) = index := by
  fin_cases index
  · simp at nonzero
  all_goals rfl

theorem regOfFinInjective {first second : Fin 32}
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0) (different : first ≠ second) :
    reg_of_fin first ≠ reg_of_fin second := by
  intro same
  apply different
  rw [← registerIndexOf first firstNonzero, ← registerIndexOf second secondNonzero, same]

theorem regOfFinNePC (index : Fin 32) : reg_of_fin index ≠ Register.PC := by
  fin_cases index <;> simp [reg_of_fin]

@[simp] theorem writeXMem (state : Machine) (index : Fin 32) (value : BitVec 32) :
    (writeX state index value).mem = state.mem := rfl

theorem readWriteX (state : Machine) (index : Fin 32) (value : BitVec 32) (nonzero : index ≠ 0) :
    read_xreg index (writeX state index value) = .ok value (writeX state index value) := by
  obtain ⟨number, bound⟩ := index
  match number, bound, nonzero with
  | 0, _, nonzero => simp at nonzero
  | _ + 1, _, _ => exact readXReg_succ.mpr (writeReg_get_same _)


/-! ## Writing the tracked registers -/

section Tracked

variable {registers : List (Fin 32)} {frame : Machine}

theorem writeTrackedMem (value : Fin 32 → BitVec 32) :
    (writeTracked registers value frame).mem = frame.mem := by
  induction registers with
  | nil => rfl
  | cons index rest previous => simpa [writeTracked] using previous

theorem writeTrackedOther (value : Fin 32 → BitVec 32) (key : Register)
    (outside : ∀ index ∈ registers, reg_of_fin index ≠ key) :
    (writeTracked registers value frame).regs.get? key = frame.regs.get? key := by
  induction registers with
  | nil => rfl
  | cons index rest previous =>
    simp only [List.mem_cons, forall_eq_or_imp] at outside
    simp only [writeTracked, writeX]
    rw [readUnchanged _ _ outside.1, previous outside.2]

theorem writeTrackedRead (value : Fin 32 → BitVec 32) {index : Fin 32}
    (nonzero : (0 : Fin 32) ∉ registers) (member : index ∈ registers) :
    read_xreg index (writeTracked registers value frame) =
      .ok (value index) (writeTracked registers value frame) := by
  induction registers with
  | nil => simp at member
  | cons head rest previous =>
    simp only [List.mem_cons, not_or] at nonzero member
    by_cases same : index = head
    · subst same
      exact readWriteX _ _ _ (Ne.symm nonzero.1)
    · have inside := member.resolve_left same
      have indexNonzero : index ≠ 0 := fun zero => nonzero.2 (zero ▸ inside)
      exact read_xreg_write_other_reg_state _ (previous nonzero.2 inside)
        (regOfFinInjective indexNonzero (Ne.symm nonzero.1) same)

theorem writeTrackedCongr {first second : Fin 32 → BitVec 32}
    (agree : ∀ index ∈ registers, first index = second index) :
    writeTracked registers first frame = writeTracked registers second frame := by
  induction registers with
  | nil => rfl
  | cons head rest previous =>
    simp only [List.mem_cons, forall_eq_or_imp] at agree
    simp only [writeTracked, agree.1, previous agree.2]

-- Overwriting one tracked register equals tracking the updated value.
theorem writeTrackedUpdate (value : Fin 32 → BitVec 32) {index : Fin 32} (written : BitVec 32)
    (distinct : registers.Nodup) (nonzero : (0 : Fin 32) ∉ registers) (member : index ∈ registers) :
    writeX (writeTracked registers value frame) index written =
      writeTracked registers (fun other => if other = index then written else value other) frame := by
  induction registers with
  | nil => simp at member
  | cons head rest previous =>
    simp only [List.nodup_cons] at distinct
    simp only [List.mem_cons, not_or] at nonzero member
    by_cases same : index = head
    · subst same
      have unchanged : writeTracked rest value frame =
          writeTracked rest (fun other => if other = index then written else value other) frame := by
        apply writeTrackedCongr
        intro other inside
        have different : other ≠ index := fun equal => distinct.1 (equal ▸ inside)
        simp [different]
      simp only [writeTracked, ↓reduceIte, ← unchanged]
      unfold writeX
      rw [writeOverwrite]
    · have inside := member.resolve_left same
      have indexNonzero : index ≠ 0 := fun zero => nonzero.2 (zero ▸ inside)
      simp only [writeTracked]
      unfold writeX
      rw [writeCommute _ _ _ _ _ (regOfFinInjective (Ne.symm nonzero.1) indexNonzero (Ne.symm same))]
      have updated := previous distinct.2 nonzero.2 inside
      unfold writeX at updated
      rw [updated]
      simp [Ne.symm same]

end Tracked


/-! ## Synchronized machine states -/

section Sync

variable {S : Type} [RegisterView S] {base : BitVec 32} {frame : Machine}

@[simp] theorem syncMem (state : S) : (sync base frame state).mem = frame.mem :=
  writeTrackedMem _

theorem syncFrame (state : S) (key : Register)
    (notPC : key ≠ Register.PC) (notNext : key ≠ Register.nextPC)
    (untracked : ∀ index ∈ tracked S, reg_of_fin index ≠ key) :
    (sync base frame state).regs.get? key = frame.regs.get? key := by
  simp only [sync]
  rw [readUnchanged _ _ (Ne.symm notPC), readUnchanged _ _ (Ne.symm notNext),
    writeTrackedOther _ _ untracked]

theorem syncReadFrame (state : S) (key : Register)
    (notPC : key ≠ Register.PC) (notNext : key ≠ Register.nextPC)
    (untracked : ∀ index ∈ tracked S, reg_of_fin index ≠ key)
    {value : RegisterType key} (read : Sail.readReg key frame = .ok value frame) :
    Sail.readReg key (sync base frame state) = .ok value (sync base frame state) :=
  readReg_succ.mpr ((syncFrame state key notPC notNext untracked).trans (readReg_succ.mp read))

theorem syncReadPC (state : S) :
    Sail.readReg Register.PC (sync base frame state) =
      .ok (base + RegisterView.pc state) (sync base frame state) :=
  readReg_succ.mpr (writeReg_get_same _)

theorem syncRead (state : S) {index : Fin 32} (member : index ∈ tracked S) :
    read_xreg index (sync base frame state) =
      .ok (RegisterView.value state index) (sync base frame state) := by
  simp only [sync]
  apply read_xreg_write_other_reg_state _ _ (regOfFinNePC index)
  apply read_xreg_write_other_reg_state _ _ reg_of_fin_neq_nextPC
  exact writeTrackedRead _ RegisterView.nonzero member

-- Retiring a register write and committing the PC gives the next snapshot.
theorem syncWrite (state next : S) {index : Fin 32} (written : BitVec 32)
    (member : index ∈ tracked S)
    (agree : ∀ other ∈ tracked S, RegisterView.value next other =
      if other = index then written else RegisterView.value state other) :
    write_reg_state (writeX (write_reg_state (sync base frame state) Register.nextPC
      (base + RegisterView.pc next)) index written) Register.PC (base + RegisterView.pc next) =
      sync base frame next := by
  simp only [sync]
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite]
  unfold writeX
  rw [writeCommute _ .PC _ _ _ (Ne.symm (regOfFinNePC index)), writeOverwrite,
    writeCommute _ .nextPC _ _ _ (Ne.symm reg_of_fin_neq_nextPC)]
  have updated := writeTrackedUpdate (frame := frame) (RegisterView.value state) written
    RegisterView.distinct RegisterView.nonzero member
  unfold writeX at updated
  rw [updated, writeTrackedCongr (fun other inside => (agree other inside).symm)]

-- Retiring a control transfer and committing the PC gives the next snapshot.
theorem syncSetPC (state next : S)
    (agree : ∀ other ∈ tracked S, RegisterView.value next other = RegisterView.value state other) :
    write_reg_state (write_reg_state (sync base frame state) Register.nextPC
      (base + RegisterView.pc next)) Register.PC (base + RegisterView.pc next) =
      sync base frame next := by
  simp only [sync]
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite, writeOverwrite,
    writeTrackedCongr (fun other inside => (agree other inside).symm)]

end Sync

end Riscfree.RV32
