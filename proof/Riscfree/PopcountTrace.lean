import Popcount
import Mathlib.Tactic.IntervalCases

namespace Riscfree.Popcount

-- The trace records the precondition of each load without changing the
-- abstract machine or duplicating its computation of the population count.
def Safe (input : Word) (state : State) : Prop :=
  state.pc = 8#32 → state.a0 ∈ [input, input + 4, input + 4 + 4, input + 4 + 4 + 4]

inductive Trace (codeBase input : Word) : Nat → State → State → Prop where
  | done (state : State) : Trace codeBase input 0 state state
  | next (safe : Safe input first) (step : Riscfree.step codeBase first = some middle)
      (rest : Trace codeBase input count middle last) :
      Trace codeBase input (count + 1) first last

theorem Trace.append
    (left : Trace codeBase input firstCount first middle)
    (right : Trace codeBase input secondCount middle last) :
    Trace codeBase input (firstCount + secondCount) first last := by
  induction left with
  | done => simpa using right
  | next safe step _ ih =>
    simpa only [Nat.add_right_comm] using Trace.next safe step (ih right)

theorem Trace.run_eq (trace : Trace codeBase input count first last) :
    Riscfree.run codeBase count first = some last := by
  induction trace with
  | done => simp
  | next _ step _ ih => simp [step, ih]

-- Deterministic execution allows the short, straight-line blocks to reuse the
-- existing execution lemmas once their individual load guards are checked.
theorem traceOfRun (safe : ∀ index < count, ∀ state,
      Riscfree.run codeBase index first = some state → Safe input state)
    (run : Riscfree.run codeBase count first = some last) :
    Trace codeBase input count first last := by
  induction count generalizing first with
  | zero =>
    simp at run
    subst last
    exact .done _
  | succ count ih =>
    rw [Riscfree.runSucc] at run
    cases step : Riscfree.step codeBase first with
    | none => simp [step] at run
    | some middle =>
      simp only [step, Option.bind_some] at run
      exact .next (safe 0 (by omega) _ (by simp)) step (ih
        (fun index bound state reach =>
          safe (index + 1) (by omega) state (by simpa [step] using reach)) run)

private theorem startTrace (codeBase input : Word) (state : State) :
    Trace codeBase input 2 { state with pc := 0 } { state with pc := 8, t0 := 4, t1 := 0 } := by
  apply traceOfRun _ (start codeBase state)
  intro index bound current reached
  interval_cases index <;>
    simp [Riscfree.step, programDecoded, State.read, State.write] at reached <;>
    subst current <;> simp [Safe]

private theorem loadTrace (codeBase input : Word) (state : State)
    (pointer : state.a0 ∈ [input, input + 4, input + 4 + 4, input + 4 + 4 + 4]) :
    Trace codeBase input 2 { state with pc := 8 } (loadedWord state) := by
  apply traceOfRun _ (loadWord codeBase state)
  intro index bound current reached
  interval_cases index <;>
    simp [Riscfree.step, programDecoded, State.read, State.write] at reached <;>
    subst current
  · exact fun _ => pointer
  · simp [Safe]

private theorem fiveTrace (codeBase input : Word) (state : State) (pc : state.pc = 16) :
    Trace codeBase input 5 state (bitUpdate state) := by
  apply traceOfRun _ (bitInstructions codeBase state pc)
  intro index bound current reached
  interval_cases index <;>
    simp [Riscfree.step, programDecoded, State.read, State.write, pc] at reached <;>
    subst current <;> simp [Safe, pc]

private theorem bitTrace (codeBase input : Word) (remaining : Nat) (state : State)
    (pc : state.pc = 16) (counter : state.t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) :
    Trace codeBase input (remaining * 5) state (bitScan remaining state) := by
  induction remaining generalizing state with
  | zero => simpa using Trace.done (codeBase := codeBase) (input := input) state
  | succ remaining ih =>
    rw [bitScanSucc, show (remaining + 1) * 5 = 5 + remaining * 5 by omega]
    apply (fiveTrace codeBase input state pc).append
    by_cases zero : remaining = 0
    · subst remaining
      simpa using Trace.done (codeBase := codeBase) (input := input) (bitUpdate state)
    · have next := bitCounterNext state remaining counter
      exact ih _ (by simpa [zero] using bitPcNext state remaining next (by omega)) next (by omega)

private theorem advanceTrace (codeBase input : Word) (state : State) (pc : state.pc = 36) :
    Trace codeBase input 3 state (advanceWord state) := by
  apply traceOfRun _ (nextWord codeBase state pc)
  intro index bound current reached
  interval_cases index <;>
    simp [Riscfree.step, programDecoded, State.read, State.write, pc] at reached <;>
    subst current <;> simp [Safe, pc]

private theorem wordTrace (codeBase input : Word) (state : State) (pc : state.pc = 8)
    (pointer : state.a0 ∈ [input, input + 4, input + 4 + 4, input + 4 + 4 + 4]) :
    Trace codeBase input 165 state (wordResult state) := by
  have same : { state with pc := 8 } = state := by cases state; simp_all
  have load := loadTrace codeBase input state pointer
  rw [same] at load
  have bits := bitTrace codeBase input 32 (loadedWord state) (loadedPc state)
    (loadedCounter state) (by decide)
  have tail := advanceTrace codeBase input (bitScan 32 (loadedWord state)) (loadedExit state)
  simpa only [wordResult] using load.append (bits.append tail)

private theorem finishTrace (codeBase input : Word) (state : State) (pc : state.pc = 48) :
    Trace codeBase input 2 state
      { state with a0 := state.t1, pc := (state.other 1 &&& 0xfffffffe) - codeBase } := by
  apply traceOfRun _ (finishAt codeBase state pc)
  intro index bound current reached
  interval_cases index <;>
    simp [Riscfree.step, programDecoded, State.read, State.write, pc] at reached <;>
    subst current <;> simp [Safe, pc]

theorem wholeTrace (codeBase : Word) (initial : State) :
    ∃ final, Trace codeBase initial.a0 664 { initial with pc := 0 } final := by
  let seed := { initial with pc := 8#32, t0 := 4#32, t1 := 0#32 }
  let first := wordResult seed
  let second := wordResult first
  let third := wordResult second
  let fourth := wordResult third
  have setup := startTrace codeBase initial.a0 initial
  have firstStep := wordTrace codeBase initial.a0 seed (by simp [seed]) (by simp [seed])
  have secondStep := wordTrace codeBase initial.a0 first
    (by simp [first, seed]) (by simp [first, seed])
  have thirdStep := wordTrace codeBase initial.a0 second
    (by simp [second, first, seed]) (by simp [second, first, seed])
  have fourthStep := wordTrace codeBase initial.a0 third
    (by simp [third, second, first, seed]) (by simp [third, second, first, seed])
  have last := finishTrace codeBase initial.a0 fourth (by simp [fourth, third, second, first, seed])
  exact ⟨_, setup.append (firstStep.append (secondStep.append (thirdStep.append (fourthStep.append last))))⟩

end Riscfree.Popcount
