/-!
# Running `EStateM` computations on a known state

These rewrite rules apply a state-monad computation to its state and push that
state into every continuation and branch, without introducing lambdas. A
symbolic `simp` over a Sail function then keeps the starting state visible
everywhere, so hypotheses about that state, such as register reads, can rewrite
reads that happen after earlier steps. Nothing here is specific to RISC-V.
-/

namespace Riscfree

variable {ε σ α β : Type}

/-- Run the continuation of a `bind` on the result of its first computation. -/
def continueWith (result : EStateM.Result ε σ α) (next : α → EStateM ε σ β) :
    EStateM.Result ε σ β :=
  match result with
  | .ok value state => next value state
  | .error error state => .error error state

theorem bind_run (first : EStateM ε σ α) (next : α → EStateM ε σ β) (state : σ) :
    (first >>= next) state = continueWith (first state) next := by
  show EStateM.bind first next state = _
  unfold EStateM.bind continueWith
  rfl

theorem pure_run (value : α) (state : σ) : (pure value : EStateM ε σ α) state = .ok value state :=
  rfl

theorem continueWith_ok (value : α) (state : σ) (next : α → EStateM ε σ β) :
    continueWith (.ok value state) next = next value state :=
  rfl

theorem continueWith_error (error : ε) (state : σ) (next : α → EStateM ε σ β) :
    continueWith (.error error state) next = .error error state :=
  rfl

theorem continueWith_ite (condition : Prop) [Decidable condition]
    (thenResult elseResult : EStateM.Result ε σ α) (next : α → EStateM ε σ β) :
    continueWith (if condition then thenResult else elseResult) next =
      if condition then continueWith thenResult next else continueWith elseResult next := by
  split <;> rfl

theorem continueWith_dite (condition : Prop) [Decidable condition]
    (thenResult : condition → EStateM.Result ε σ α)
    (elseResult : ¬condition → EStateM.Result ε σ α) (next : α → EStateM ε σ β) :
    continueWith (if h : condition then thenResult h else elseResult h) next =
      if h : condition then continueWith (thenResult h) next
      else continueWith (elseResult h) next := by
  split <;> rfl

-- `simp` cannot use Mathlib's `ite_apply` here: `EStateM` is not reducible, so the
-- branches do not look like functions.
theorem ite_run (condition : Prop) [Decidable condition]
    (thenAction elseAction : EStateM ε σ α) (state : σ) :
    (if condition then thenAction else elseAction) state =
      if condition then thenAction state else elseAction state := by
  split <;> rfl

theorem dite_run (condition : Prop) [Decidable condition]
    (thenAction : condition → EStateM ε σ α) (elseAction : ¬condition → EStateM ε σ α)
    (state : σ) :
    (if h : condition then thenAction h else elseAction h) state =
      if h : condition then thenAction h state else elseAction h state := by
  split <;> rfl

end Riscfree
