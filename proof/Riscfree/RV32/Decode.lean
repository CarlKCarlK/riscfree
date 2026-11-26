import Riscfree.RV32.RegisterFrame

/-!
# Sail decoding of linked instruction words

`decode_word [facts]` proves `encdec_backwards word state = .ok ast state`
for one concrete 32-bit word. The facts describe the state the decoder reads,
such as the privilege level and the landing-pad setting. The simp set is
restricted to what the decoder needs: the opcode imports add rules that
otherwise expand unrelated instruction families.
-/

namespace Riscfree.RV32

open LeanRV32D RV32IM

-- Instruction tables name registers by their five-bit index.
def reg (index : BitVec 5) : regidx := .Regidx index

end Riscfree.RV32

syntax "decode_word" "[" term,* "]" : tactic

open LeanRV32D LeanRV32D.Functions RV32IM in
macro_rules
  | `(tactic| decode_word [$facts,*]) => do
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

-- Prove `∀ entry ∈ table, ext_decode entry.1 state = .ok entry.2 state` word by word.
-- The goal is split structurally: an `rcases` `rfl` pattern would be hygienic here.
syntax "decode_table" ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| decode_table $table [$facts,*]) => `(tactic| (
    unfold $table
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals (show LeanRV32D.Functions.encdec_backwards _ _ = _; decode_word [$facts,*])))
