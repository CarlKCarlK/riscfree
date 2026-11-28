import Riscfree.RV32.RegisterFrame
import Riscfree.RV32.DecoderNormalForm

/-!
# Sail decoding of linked instruction words

`decode_word [facts]` proves `encdec_backwards word state = .ok ast state`
for one concrete 32-bit word. The facts describe the state the decoder reads,
such as the privilege level and the landing-pad setting. It tries, in order:

1. The pre-simplified decoder: rewrite with `decodeMachineMode.eq`, using the
   facts for its hypotheses, and let the kernel reduce `decodeMachineMode word
   state` to the expected result. The kernel checks each word as an auxiliary
   theorem. No per-instruction lemma is involved.
2. `decode_word_simp [facts]`: a per-word `simp` over the Sail decoder with a
   hand-picked rule set. It covers the instructions that the first method
   cannot finish because they read state that the normal form leaves symbolic.
   Today that is `mul`, whose decoding reads `misa`.

`decode_table` applies `decode_word` to every entry of an instruction table.
-/

namespace Riscfree.RV32

open LeanRV32D RV32IM

-- Instruction tables name registers by their five-bit index.
def reg (index : BitVec 5) : regidx := .Regidx index

end Riscfree.RV32

namespace Riscfree.RV32

open Lean Meta Elab Tactic LeanRV32D.Functions

/-- Close `encdec_backwards word state = result` with `decodeMachineMode.eq` and a
kernel reduction. Each hypothesis of `decodeMachineMode.eq` must be proved by one of
`facts`. Returns `false`, with the goal and metavariable state unchanged, if the
goal has another shape, a fact is missing, or, when `kernelPrecheck` is set, the
kernel cannot reduce the normal form to `result`.

Without `kernelPrecheck`, a wrong `result` is not detected here: the goal is closed,
and the kernel rejects the auxiliary theorem with an error after the tactic has
finished. Use that only where nothing should be tried after a failure. -/
def decodeByNormalForm (facts : Array Expr) (goal : MVarId) (kernelPrecheck : Bool := true) :
    MetaM Bool :=
  goal.withContext <| commitWhen do
  let some (_, lhs, result) := (← instantiateMVars (← goal.getType)).eq? | return false
  -- Other goals could make `isDefEq` below unfold the whole Sail decoder.
  unless lhs.isAppOfArity ``encdec_backwards 2 || lhs.isAppOfArity ``ext_decode 2 do
    return false
  -- The kernel rejects metavariables, such as a `_` left in the expected instruction.
  if result.hasMVar then
    return false
  let equation ← mkConstWithFreshMVarLevels ``decodeMachineMode.eq
  let (arguments, _, statement) ← forallMetaTelescope (← inferType equation)
  let some (_, decoded, _) := statement.eq? | return false
  unless ← isDefEq decoded lhs do
    return false
  for argument in arguments do
    if (← argument.mvarId!.isAssigned) then
      continue
    let argumentType ← instantiateMVars (← inferType argument)
    let some fact ← facts.findM? fun fact => do isDefEq (← inferType fact) argumentType
      | return false
    argument.mvarId!.assign fact
  let rewrite ← instantiateMVars (mkAppN equation arguments)
  let some (_, _, normal) := (← inferType rewrite).eq? | return false
  -- Ask the kernel first: a failed check inside `mkAuxTheorem` is reported only after
  -- the tactic has finished, too late to fall back. The kernel checks the reduction
  -- again when it adds the auxiliary theorem, so callers without a fallback skip this
  -- first check, which roughly doubles the cost of each word.
  if kernelPrecheck then
    unless ← ofExceptKernelException (Kernel.isDefEq (← getEnv) (← getLCtx) normal result) do
      return false
  let reduction ← mkAuxTheorem (← mkEq normal result) (← mkEqRefl result)
  goal.assign (← mkExpectedTypeHint (← mkEqTrans rewrite reduction) (← goal.getType))
  return true

end Riscfree.RV32

syntax "decode_word_simp" "[" term,* "]" : tactic

open LeanRV32D LeanRV32D.Functions RV32IM in
macro_rules
  | `(tactic| decode_word_simp [$facts,*]) => do
  let lemmas ← facts.getElems.mapM fun fact => `(Lean.Parser.Tactic.simpLemma| $fact:term)
  let facts : Array (Lean.TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma]) := lemmas.map fun fact => ⟨fact.raw⟩
  `(tactic|
  set_option linter.unusedSimpArgs false in (
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) only [
    EStateM.instMonad, Sail.BitVec.extractLsb, BitVec.ofNat_eq_ofNat, BitVec.extractLsb_ofNat,
    Nat.reduceSub, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceShiftRight,
    encdec_reg_backwards_matches, Functions.not, Sail.BitVec.access, BitVec.reduceOfNat,
    Nat.lt_add_one, getElem!_pos, BitVec.getElem_zero, BitVec.ofBool_false, BEq.rfl,
    Bool.or_true, ↓reduceIte, Bool.and_true, Nat.sub_zero, Nat.shiftRight_zero,
    BitVec.reduceBEq, Bool.and_false, Bool.false_eq_true, pure, currentlyEnabled.eq_47,
    hartSupports.eq_21, currentlyEnabled.eq_41, currentlyEnabled.eq_93, hartSupports.eq_18,
    hartSupports.eq_15, Bool.false_and, bind_equiv, EStateM.pure, BitVec.reduceGetElem,
    encdec_uop_backwards_matches, BitVec.reduceEq, imp_self, Bool.and_self, Bool.true_and,
    encdec_iop_backwards_matches, encdec_reg_backwards, Nat.zero_mod, encdec_iop_backwards,
    Bool.and_self_left, currentlyEnabled.eq_94, hartSupports.eq_103, EStateM.Result.ok.injEq,
    instruction.ITYPE.injEq, Prod.mk.injEq, regidx.Regidx.injEq, ↓dreduceIte, and_true,
    true_and, Bool.and_eq_true, BitVec.ofBool_true, Bool.or_false, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.if_false_right, Bool.decide_eq_false, sail_assert_equiv, throw_equiv,
    BitVec.getElem_one, OfNat.ofNat_ne_zero, decide_false, Functions.xlen, Nat.reduceBEq,
    instruction.SHIFTIOP.injEq, and_self, encdec_bop_backwards_matches, encdec_bop_backwards,
    BitVec.reduceAppend, BitVec.one_eq_zero_iff, currentlyEnabled.eq_101, hartSupports.eq_10,
    instruction.BTYPE.injEq, Nat.one_mod, instruction.JALR.injEq, Riscfree.RV32.reg, $facts,*]
  all_goals simp [bool_bit_backwards_matches, width_enc_backwards_matches, bool_bit_backwards,
    width_enc_backwards, valid_load_encdec, EStateM.pure, encdec_uop_backwards,
    encdec_mul_op_backwards, encdec_mul_op_backwards_matches, LeanRV32D.Functions.base_E_enabled,
    LeanRV32D.Functions.regidx_bit_width, $facts,*]))

syntax "decode_word" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| decode_word [$facts,*]) => withMainContext do
    let factProofs ← facts.getElems.mapM fun fact => elabTerm fact none
    if ← Riscfree.RV32.decodeByNormalForm factProofs (← getMainGoal) then
      replaceMainGoal []
    else
      evalTactic (← `(tactic| decode_word_simp [$facts,*]))

/-- Like `decode_word`, but fails instead of falling back to `decode_word_simp`.

It skips the kernel pre-check: when the normal form does not reduce to the expected
instruction, the kernel's rejection of the auxiliary theorem is the error, reported
after the tactic has finished. So do not put this tactic before another alternative
in `first`; a kernel failure would not reach it. -/
syntax "decode_word_normal_form" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| decode_word_normal_form [$facts,*]) => withMainContext do
    let factProofs ← facts.getElems.mapM fun fact => elabTerm fact none
    unless ← Riscfree.RV32.decodeByNormalForm factProofs (← getMainGoal)
        (kernelPrecheck := false) do
      throwError "decode_word_normal_form: the normal form does not decode this word from the facts"
    replaceMainGoal []

-- Prove `∀ entry ∈ table, ext_decode entry.1 state = .ok entry.2 state` word by word.
-- The goal is split structurally: an `rcases` `rfl` pattern would be hygienic here.
syntax "decode_table" ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| decode_table $table [$facts,*]) => `(tactic| (
    unfold $table
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals (show LeanRV32D.Functions.encdec_backwards _ _ = _; decode_word [$facts,*])))

/-- Like `decode_table`, but every word must decode from the normal form. -/
syntax "decode_table_normal_form" ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| decode_table_normal_form $table [$facts,*]) => `(tactic| (
    unfold $table
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals
      (show LeanRV32D.Functions.encdec_backwards _ _ = _; decode_word_normal_form [$facts,*])))
