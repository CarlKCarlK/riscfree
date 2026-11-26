import PicoFV.RV32IM.RVSail.Opcodes.add
import PicoFV.RV32IM.RVSail.Opcodes.andi
import PicoFV.RV32IM.RVSail.Opcodes.jalr
import PicoFV.RV32IM.RVSail.Opcodes.srli
import Riscfree.RV32.Branch
import Riscfree.RV32.Memory

/-!
# Linked RV32 popcount

The mathematical specification counts the bits of four little-endian words.
Sail decodes the linked instructions, and Pico FV's equivalence theorems give
their effects on the registers. The bit and word loop invariants compose those
steps into a proof of the entire call. The ELF check uses the same words as
the Sail decoder.
-/

namespace Riscfree


/-! ## Mathematical specification -/

section Specification

abbrev Word := BitVec 32
abbrev Memory := Word → Word

-- A proof snapshot records the relative PC and the six registers the routine
-- updates. Byte memory and all other registers stay in the Sail frame.
structure Snapshot where
  pc : Word := 0
  a0 : Word
  t0 : Word := 0
  t1 : Word := 0
  t2 : Word := 0
  t3 : Word := 0
  t4 : Word := 0


def scan : Nat → Word → Word → Word
  | 0, _, total => total
  | remaining + 1, word, total =>
    scan remaining (word >>> (1 : Nat)) (total + (word &&& 1#32))

def scanInput (memory : Memory) (input : Word) : Word :=
  let next := input + 4
  let third := next + 4
  let fourth := third + 4
  scan 32 (memory fourth) (scan 32 (memory third)
    (scan 32 (memory next) (scan 32 (memory input) 0#32)))

theorem cpopShift (word : Word) (remaining : Nat) :
    (word >>> (1 : Nat)).cpopNatRec remaining 0 + (word.getLsbD 0).toNat =
      word.cpopNatRec (remaining + 1) 0 := by
  induction remaining with
  | zero => simp
  | succ remaining previous =>
    rw [BitVec.cpopNatRec_succ (x := word >>> (1 : Nat)),
      BitVec.cpopNatRec_eq (acc := 0 + ((word >>> (1 : Nat)).getLsbD remaining).toNat),
      BitVec.cpopNatRec_succ (x := word) (n := remaining + 1),
      BitVec.cpopNatRec_eq (acc := 0 + (word.getLsbD (remaining + 1)).toNat),
      ← previous]
    simp only [BitVec.getLsbD_ushiftRight, Nat.zero_add, Nat.add_comm 1 remaining]
    ac_rfl

theorem scanCorrect (remaining : Nat) (word total : Word)
    (bound : total.toNat + remaining < 2 ^ 32) :
    (scan remaining word total).toNat = total.toNat + word.cpopNatRec remaining 0 := by
  induction remaining generalizing word total with
  | zero => simp [scan]
  | succ remaining previous =>
    have lowBit : (word &&& 1#32).toNat = (word.getLsbD 0).toNat := by
      rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
      cases word.getLsbD 0 <;> decide
    have lowBound : (word.getLsbD 0).toNat ≤ 1 := by cases word.getLsbD 0 <;> decide
    have addExact : (total + (word &&& 1#32)).toNat = total.toNat + (word.getLsbD 0).toNat := by
      rw [BitVec.toNat_add_of_lt, lowBit]
      omega
    have nextBound : (total + (word &&& 1#32)).toNat + remaining < 2 ^ 32 := by omega
    rw [scan, previous _ _ nextBound, addExact, Nat.add_assoc, ← cpopShift]
    ac_rfl

def inputBits (memory : Memory) (input : Word) : BitVec 128 :=
  let next := input + 4
  let third := next + 4
  let fourth := third + 4
  memory fourth ++ memory third ++ memory next ++ memory input

theorem scanInputCorrect (memory : Memory) (input : Word) :
    (scanInput memory input).toNat = (inputBits memory input).cpop.toNat := by
  have scanWord (word total : Word) (bound : total.toNat ≤ 96) :
      (scan 32 word total).toNat = total.toNat + word.cpop.toNat := by
    rw [BitVec.toNat_cpop, scanCorrect]
    omega
  have first := scanWord (memory input) 0#32 (by decide)
  have second := scanWord (memory (input + 4)) (scan 32 (memory input) 0#32) (by
    rw [first, BitVec.toNat_zero, Nat.zero_add]
    have := BitVec.toNat_cpop_le (memory input)
    omega)
  have third := scanWord (memory (input + 4 + 4))
    (scan 32 (memory (input + 4)) (scan 32 (memory input) 0#32)) (by
      rw [second, first, BitVec.toNat_zero, Nat.zero_add]
      have := BitVec.toNat_cpop_le (memory input)
      have := BitVec.toNat_cpop_le (memory (input + 4))
      omega)
  have fourth := scanWord (memory (input + 4 + 4 + 4))
    (scan 32 (memory (input + 4 + 4)) (scan 32 (memory (input + 4)) (scan 32 (memory input) 0#32))) (by
      rw [third, second, first, BitVec.toNat_zero, Nat.zero_add]
      have := BitVec.toNat_cpop_le (memory input)
      have := BitVec.toNat_cpop_le (memory (input + 4))
      have := BitVec.toNat_cpop_le (memory (input + 4 + 4))
      omega)
  simp only [scanInput, fourth, third, second, first, BitVec.toNat_zero,
    Nat.zero_add, inputBits, BitVec.toNat_cpop_append]
  ac_rfl

end Specification


namespace Popcount

/-! ## Sail decoding of the linked instruction words -/

section SailDecode

open LeanRV32D LeanRV32D.Functions RV32IM RV32

private def reg (index : BitVec 5) : regidx := .Regidx index

-- Each word is a little-endian instruction from the linked popcount128 symbol.
-- The right column records the Sail AST we expect its decoder to return.
def instructions : List (BitVec 32 × instruction) :=
  [ (0x00400293, .ITYPE (4, reg 0, reg 5, .ADDI))
  , (0x00000313, .ITYPE (0, reg 0, reg 6, .ADDI))
  , (0x00052383, .LOAD (0, reg 10, reg 7, false, 4))
  , (0x02000e13, .ITYPE (32, reg 0, reg 28, .ADDI))
  , (0x0013fe93, .ITYPE (1, reg 7, reg 29, .ANDI))
  , (0x01d30333, .RTYPE (reg 29, reg 6, reg 6, .ADD))
  , (0x0013d393, .SHIFTIOP (1, reg 7, reg 7, .SRLI))
  , (0xfffe0e13, .ITYPE (0xfff, reg 28, reg 28, .ADDI))
  , (0xfe0e18e3, .BTYPE (0x1ff0, reg 0, reg 28, .BNE))
  , (0x00450513, .ITYPE (4, reg 10, reg 10, .ADDI))
  , (0xfff28293, .ITYPE (0xfff, reg 5, reg 5, .ADDI))
  , (0xfc029ee3, .BTYPE (0x1fdc, reg 0, reg 5, .BNE))
  , (0x00030513, .ITYPE (0, reg 6, reg 10, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

section
variable (state : Machine)
variable (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
variable (landingPad : get_xLPE .Machine state = .ok false state)

include privilege landingPad

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- Restrict the decoder to the simplifications it needs. The execution
-- imports add rules that otherwise expand unrelated instruction families.
local macro "reduce_decoder" privilege:ident landingPad:ident : tactic => do
  let privilege : Lean.TSyntax `term := ⟨privilege.raw⟩
  let landingPad : Lean.TSyntax `term := ⟨landingPad.raw⟩
  `(tactic|
    set_option linter.unusedSimpArgs false in
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
      instruction.BTYPE.injEq, Nat.one_mod, instruction.JALR.injEq,
      $privilege:term, $landingPad:term, reg])

private theorem decode0 :
    encdec_backwards 0x00400293 state = .ok (.ITYPE (4, reg 0, reg 5, .ADDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode1 :
    encdec_backwards 0x00000313 state = .ok (.ITYPE (0, reg 0, reg 6, .ADDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode2 :
    encdec_backwards 0x00052383 state = .ok (.LOAD (0, reg 10, reg 7, false, 4)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [bool_bit_backwards_matches, width_enc_backwards_matches,
    bool_bit_backwards, width_enc_backwards, valid_load_encdec, EStateM.pure,
    LeanRV32D.Functions.regidx_bit_width]

private theorem decode3 :
    encdec_backwards 0x02000e13 state = .ok (.ITYPE (32, reg 0, reg 28, .ADDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode4 :
    encdec_backwards 0x0013fe93 state = .ok (.ITYPE (1, reg 7, reg 29, .ANDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode5 :
    encdec_backwards 0x01d30333 state = .ok (.RTYPE (reg 29, reg 6, reg 6, .ADD)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode6 :
    encdec_backwards 0x0013d393 state = .ok (.SHIFTIOP (1, reg 7, reg 7, .SRLI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode7 :
    encdec_backwards 0xfffe0e13 state = .ok (.ITYPE (0xfff, reg 28, reg 28, .ADDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode8 :
    encdec_backwards 0xfe0e18e3 state = .ok (.BTYPE (0x1ff0, reg 0, reg 28, .BNE)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode9 :
    encdec_backwards 0x00450513 state = .ok (.ITYPE (4, reg 10, reg 10, .ADDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode10 :
    encdec_backwards 0xfff28293 state = .ok (.ITYPE (0xfff, reg 5, reg 5, .ADDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode11 :
    encdec_backwards 0xfc029ee3 state = .ok (.BTYPE (0x1fdc, reg 0, reg 5, .BNE)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode12 :
    encdec_backwards 0x00030513 state = .ok (.ITYPE (0, reg 6, reg 10, .ADDI)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode13 :
    encdec_backwards 0x00008067 state = .ok (.JALR (0, reg 1, reg 0)) state := by
  unfold encdec_backwards
  reduce_decoder privilege landingPad
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]


theorem linkedWordsDecode (entry : BitVec 32 × instruction) (member : entry ∈ instructions) :
    ext_decode entry.1 state = .ok entry.2 state := by
  simp only [instructions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same |
    same | same | same | same | same | same <;> subst entry
  · exact decode0 state privilege landingPad
  · exact decode1 state privilege landingPad
  · exact decode2 state privilege landingPad
  · exact decode3 state privilege landingPad
  · exact decode4 state privilege landingPad
  · exact decode5 state privilege landingPad
  · exact decode6 state privilege landingPad
  · exact decode7 state privilege landingPad
  · exact decode8 state privilege landingPad
  · exact decode9 state privilege landingPad
  · exact decode10 state privilege landingPad
  · exact decode11 state privilege landingPad
  · exact decode12 state privilege landingPad
  · exact decode13 state privilege landingPad

#print axioms linkedWordsDecode

end

end SailDecode


/-! ## Proof snapshots and the Sail register frame -/

section SailState

open LeanRV32D RV32IM Riscfree.RV32

-- PC and nextPC are synchronized at retirement. The remaining registers
-- and all byte memory come from the original Sail state.
def scratch (frame : Machine) (state : Snapshot) : Machine :=
  let frame := write_reg_state frame Register.x5 state.t0
  let frame := write_reg_state frame Register.x6 state.t1
  let frame := write_reg_state frame Register.x7 state.t2
  let frame := write_reg_state frame Register.x10 state.a0
  let frame := write_reg_state frame Register.x28 state.t3
  write_reg_state frame Register.x29 state.t4

def sync (base : Word) (frame : Machine) (state : Snapshot) : Machine :=
  let pc := base + state.pc
  write_reg_state (write_reg_state (scratch frame state) Register.nextPC pc) Register.PC pc

@[simp] theorem syncMem (base : Word) (frame : Machine) (state : Snapshot) :
    (sync base frame state).mem = frame.mem := rfl

theorem syncFrame (base : Word) (frame : Machine) (state : Snapshot) (register : Register)
    (outside : register ∉ [Register.PC, .nextPC, .x5, .x6, .x7, .x10, .x28, .x29]) :
    (sync base frame state).regs.get? register = frame.regs.get? register := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨pc, next, x5, x6, x7, x10, x28, x29⟩ := outside
  simp [sync, scratch, readUnchanged, Ne.symm pc, Ne.symm next, Ne.symm x5,
    Ne.symm x6, Ne.symm x7, Ne.symm x10, Ne.symm x28, Ne.symm x29]

theorem syncReadFrame (base : Word) (frame : Machine) (state : Snapshot) (register : Register)
    (outside : register ∉ [Register.PC, .nextPC, .x5, .x6, .x7, .x10, .x28, .x29])
    {value : RegisterType register}
    (read : Sail.readReg register frame = .ok value frame) :
    Sail.readReg register (sync base frame state) = .ok value (sync base frame state) :=
  readReg_succ.mpr ((syncFrame base frame state register outside).trans (readReg_succ.mp read))

theorem syncReadPC (base : Word) (frame : Machine) (state : Snapshot) :
    Sail.readReg Register.PC (sync base frame state) = .ok (base + state.pc) (sync base frame state) :=
  readReg_succ.mpr (writeReg_get_same _)

theorem syncSetPC (base : Word) (frame : Machine) (state : Snapshot) (next : Word) :
    write_reg_state (write_reg_state (sync base frame state) Register.nextPC (base + next))
      Register.PC (base + next) = sync base frame { state with pc := next } := by
  unfold sync
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite, writeOverwrite]
  rfl

theorem syncSetX5 (base : Word) (frame : RV32.Machine) (state : Snapshot) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x5
      value) Register.PC (base + next) = sync base frame { state with pc := next, t0 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x5 _ _ (by decide), writeCommute _ .nextPC .x5 _ _ (by decide),
    writeCommute _ .x29 .x5 _ _ (by decide),
    writeCommute _ .x28 .x5 _ _ (by decide),
    writeCommute _ .x10 .x5 _ _ (by decide),
    writeCommute _ .x7 .x5 _ _ (by decide),
    writeCommute _ .x6 .x5 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX5 (base : Word) (frame : RV32.Machine) (state : Snapshot) :
    read_xreg (5 : Fin 32) (sync base frame state) = .ok state.t0 (sync base frame state) := by
  change Sail.readReg Register.x5 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX6 (base : Word) (frame : RV32.Machine) (state : Snapshot) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x6
      value) Register.PC (base + next) = sync base frame { state with pc := next, t1 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x6 _ _ (by decide), writeCommute _ .nextPC .x6 _ _ (by decide),
    writeCommute _ .x29 .x6 _ _ (by decide),
    writeCommute _ .x28 .x6 _ _ (by decide),
    writeCommute _ .x10 .x6 _ _ (by decide),
    writeCommute _ .x7 .x6 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX6 (base : Word) (frame : RV32.Machine) (state : Snapshot) :
    read_xreg (6 : Fin 32) (sync base frame state) = .ok state.t1 (sync base frame state) := by
  change Sail.readReg Register.x6 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX7 (base : Word) (frame : RV32.Machine) (state : Snapshot) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x7
      value) Register.PC (base + next) = sync base frame { state with pc := next, t2 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x7 _ _ (by decide), writeCommute _ .nextPC .x7 _ _ (by decide),
    writeCommute _ .x29 .x7 _ _ (by decide),
    writeCommute _ .x28 .x7 _ _ (by decide),
    writeCommute _ .x10 .x7 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX7 (base : Word) (frame : RV32.Machine) (state : Snapshot) :
    read_xreg (7 : Fin 32) (sync base frame state) = .ok state.t2 (sync base frame state) := by
  change Sail.readReg Register.x7 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX10 (base : Word) (frame : RV32.Machine) (state : Snapshot) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x10
      value) Register.PC (base + next) = sync base frame { state with pc := next, a0 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x10 _ _ (by decide), writeCommute _ .nextPC .x10 _ _ (by decide),
    writeCommute _ .x29 .x10 _ _ (by decide),
    writeCommute _ .x28 .x10 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX10 (base : Word) (frame : RV32.Machine) (state : Snapshot) :
    read_xreg (10 : Fin 32) (sync base frame state) = .ok state.a0 (sync base frame state) := by
  change Sail.readReg Register.x10 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX28 (base : Word) (frame : RV32.Machine) (state : Snapshot) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x28
      value) Register.PC (base + next) = sync base frame { state with pc := next, t3 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x28 _ _ (by decide), writeCommute _ .nextPC .x28 _ _ (by decide),
    writeCommute _ .x29 .x28 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX28 (base : Word) (frame : RV32.Machine) (state : Snapshot) :
    read_xreg (28 : Fin 32) (sync base frame state) = .ok state.t3 (sync base frame state) := by
  change Sail.readReg Register.x28 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

theorem syncSetX29 (base : Word) (frame : RV32.Machine) (state : Snapshot) (next value : Word) :
    write_reg_state (write_reg_state
      (write_reg_state (sync base frame state) Register.nextPC (base + next)) Register.x29
      value) Register.PC (base + next) = sync base frame { state with pc := next, t4 := value } := by
  unfold sync scratch
  rw [writeCommute _ .PC .nextPC _ _ (by decide), writeOverwrite,
    writeCommute _ .PC .x29 _ _ (by decide), writeCommute _ .nextPC .x29 _ _ (by decide),
    writeOverwrite, writeOverwrite]

theorem syncReadX29 (base : Word) (frame : RV32.Machine) (state : Snapshot) :
    read_xreg (29 : Fin 32) (sync base frame state) = .ok state.t4 (sync base frame state) := by
  change Sail.readReg Register.x29 _ = .ok _ _
  apply readReg_succ.mpr
  simp [sync, scratch, readUnchanged, writeReg_get_same]

end SailState


/-! ## Code mapping, RAM, and processor assumptions -/

section SailPlatform

open LeanRV32D LeanRV32D.Functions RV32IM RV32

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}

def inputAddresses (input : Word) : List Word :=
  [input, input + 4, input + 4 + 4, input + 4 + 4 + 4]

-- The instruction-side platform premise describes just the loaded code image.
-- It applies after any change to the six scratch registers and the PC.
-- RAM permissions are checked per word. No writable flash or global PMA is assumed.
structure Platform (base : Word) (frame : Machine) (input returnAddress : Word) (memory : Memory) : Prop where
  alignedCode : base % 4 = 0
  returnLow : returnAddress &&& 0xfffffffe = returnAddress
  returnNext : (returnAddress)[1] = false
  ra : Sail.readReg Register.x1 frame = .ok (returnAddress) frame
  privilege : Sail.readReg Register.cur_privilege frame = .ok .Machine frame
  misa : ∃ value, Sail.readReg Register.misa frame = .ok value frame
  mseccfg : ∃ value, Sail.readReg Register.mseccfg frame = .ok value frame
  landingPad : get_xLPE .Machine frame = .ok false frame
  status : ∃ value, Sail.readReg Register.mstatus frame = .ok value frame ∧
    value.extractLsb 17 17 = 0#1
  htif : Sail.readReg Register.htif_tohost_base frame = .ok none frame
  ram : ∀ address ∈ inputAddresses input,
    ∃ regions region byte0 byte1 byte2 byte3,
      Sail.readReg Register.pma_regions frame = .ok regions frame ∧
      matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region ∧
      region.attributes.readable = true ∧ address.toNat % 4 = 0 ∧
      frame.mem[address.toNat]? = some byte0 ∧ frame.mem[address.toNat + 1]? = some byte1 ∧
      frame.mem[address.toNat + 2]? = some byte2 ∧ frame.mem[address.toNat + 3]? = some byte3 ∧
      memory address = byte3 ++ byte2 ++ byte1 ++ byte0
  code : ∀ (state : Snapshot) (index : Fin instructions.length),
    state.pc = BitVec.ofNat 32 (index.val * 4) →
    InstructionWord (sync base frame state) (base + state.pc) instructions[index.val].1

theorem Platform.fetchAt (platform : Platform base frame input returnAddress memory) (state : Snapshot)
    (index : Fin instructions.length) (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base frame state) = .ok (.F_Base instructions[index.val].1) (sync base frame state) := by
  obtain ⟨misa, read⟩ := platform.misa
  apply (platform.code state index pc).fetch (syncReadPC base frame state)
    (syncReadFrame base frame state Register.misa (by decide) read)
  fin_cases index <;> rfl

theorem Platform.privilegeAt (platform : Platform base frame input returnAddress memory) (state : Snapshot) :
    Sail.readReg Register.cur_privilege (sync base frame state) =
      .ok .Machine (sync base frame state) :=
  syncReadFrame _ _ _ _ (by decide) platform.privilege

theorem Platform.landingPadAt (platform : Platform base frame input returnAddress memory) (state : Snapshot) :
    get_xLPE .Machine (sync base frame state) = .ok false (sync base frame state) := by
  obtain ⟨config, read⟩ := platform.mseccfg
  have same := syncReadFrame base frame state Register.mseccfg (by decide) read
  have disabled := platform.landingPad
  simp [get_xLPE, read] at disabled
  simp [get_xLPE, same, disabled]

theorem Platform.readWord (platform : Platform base frame input returnAddress memory) (state : Snapshot)
    (next address : Word) (inRam : address ∈ inputAddresses input) :
    let entered := write_reg_state (sync base frame state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) 0 4 (.Load .Data) false false false entered =
      .ok (.Ok (memory address)) entered := by
  dsimp only
  obtain ⟨regions, region, byte0, byte1, byte2, byte3, pma, matched, readable, aligned,
    bytes0, bytes1, bytes2, bytes3, word⟩ := platform.ram address inRam
  obtain ⟨status, statusRead, mprv⟩ := platform.status
  rw [word]
  refine readAlignedRamWord _ address 0 region regions status byte0 byte1 byte2 byte3 ?_ ?_
    mprv ?_ matched readable ?_ aligned ?_ ?_ ?_ ?_
  · exact readReg_of_write_other_reg_state (platform.privilegeAt state) (by decide)
  · exact readReg_of_write_other_reg_state (syncReadFrame _ _ _ _ (by decide) statusRead) (by decide)
  · exact readReg_of_write_other_reg_state (syncReadFrame _ _ _ _ (by decide) pma) (by decide)
  · exact readReg_of_write_other_reg_state (syncReadFrame _ _ _ _ (by decide) platform.htif) (by decide)
  all_goals simp only [writeMem, syncMem]; assumption

end SailPlatform


/-! ## Effects of the linked instructions -/

section SailInstructions

open LeanRV32D LeanRV32D.Functions RV32IM RV32

private abbrev instructionRegister (index : BitVec 5) : regidx := .Regidx index

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}

private theorem alignedOffset (base offset : Word)
    (aligned : base % 4 = 0) (offsetAligned : offset.toNat % 4 = 0) :
    (base + offset) % 4 = 0 := by
  have h := congrArg BitVec.toNat aligned
  change base.toNat % 4 = 0 at h
  apply BitVec.eq_of_toNat_eq
  change (base + offset).toNat % 4 = 0
  rw [BitVec.toNat_add]
  omega

private theorem fallthrough {base pc offset : Word} (atPC : pc = offset) :
    base + pc + 4#32 = base + (offset + 4#32) := by
  rw [atPC, BitVec.add_assoc]

-- Select the actual Sail decoding before considering the effect of the instruction.
private theorem fetchAndDecode (platform : Platform base frame input returnAddress memory) (state : Snapshot)
    (index : Fin instructions.length) (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base frame state) = .ok (.F_Base instructions[index.val].1) (sync base frame state) ∧
    ext_decode instructions[index.val].1 (sync base frame state) =
      .ok instructions[index.val].2 (sync base frame state) :=
  ⟨platform.fetchAt state index pc, linkedWordsDecode _ (platform.privilegeAt state) (platform.landingPadAt state)
    _ (List.getElem_mem index.isLt)⟩

private theorem initializeWordCounter (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 0#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 4, t0 := 4 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨0, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 4#32 := fallthrough atPC
  have retired := RV32.stepADDI machine _ (instructionRegister 0) (instructionRegister 5) 4
    (base + state.pc) 0 fetched decoded pcRead (by rfl) (by decide)
  rw [next] at retired
  exact retired.trans (congrArg some (syncSetX5 base frame state 4 _))

private theorem clearTotal (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 4#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 8, t1 := 0 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨1, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 8#32 := fallthrough atPC
  have retired := RV32.stepADDI machine _ (instructionRegister 0) (instructionRegister 6) 0
    (base + state.pc) 0 fetched decoded pcRead (by rfl) (by decide)
  rw [next] at retired
  exact retired.trans (congrArg some (syncSetX6 base frame state 8 _))

private theorem loadInputWord (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 8#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 12, t2 := memory state.a0 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨2, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 12#32 := fallthrough atPC
  have wordRead := platform.readWord state (base + 12#32) state.a0 inRam
  have effect := executeWordLoad machine (instructionRegister 10) (instructionRegister 7) 0
    (base + state.pc) state.a0 (memory state.a0) pcRead (syncReadX10 base frame state) (by
      simpa [next] using wordRead)
  have retired := RV32.stepWrite machine _ _ 7 (base + 12#32) (memory state.a0)
    fetched decoded (by
      simpa [writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
  exact retired.trans (congrArg some (syncSetX7 base frame state 12 _))

private theorem initializeBitCounter (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 12#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 16, t3 := 32 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨3, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 16#32 := fallthrough atPC
  have retired := RV32.stepADDI machine _ (instructionRegister 0) (instructionRegister 28) 32
    (base + state.pc) 0 fetched decoded pcRead (by rfl) (by decide)
  rw [next] at retired
  exact retired.trans (congrArg some (syncSetX28 base frame state 16 _))

private theorem extractLowBit (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 16#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 20, t4 := state.t2 &&& 1#32 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨4, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 20#32 := fallthrough atPC
  have effect := OpcodeSpec.RV32.execute_ANDI_equiv
    ((OpcodeSpec.RV32.spec_ANDI_hypotheses (r1 := instructionRegister 7) (rd := instructionRegister 29) (imm := 1#12)).mpr ⟨pcRead, (syncReadX7 base frame state)⟩)
  have retired := RV32.stepWrite machine _ _ 29 (base + 20#32) (state.t2 &&& 1#32)
    fetched decoded (by
      simpa [OpcodeSpec.RV32.spec_ANDI, operation_list_effect, operation_effect,
        writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
  exact retired.trans (congrArg some (syncSetX29 base frame state 20 _))

private theorem addLowBit (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 20#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 24, t1 := state.t1 + state.t4 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨5, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 24#32 := fallthrough atPC
  have effect := OpcodeSpec.RV32.execute_ADD_equiv
    ((OpcodeSpec.RV32.spec_ADD_hypotheses (r1 := instructionRegister 6) (r2 := instructionRegister 29) (rd := instructionRegister 6)).mpr ⟨pcRead, (syncReadX6 base frame state), (syncReadX29 base frame state)⟩)
  have retired := RV32.stepWrite machine _ _ 6 (base + 24#32) (state.t1 + state.t4)
    fetched decoded (by
      simpa [OpcodeSpec.RV32.spec_ADD, operation_list_effect, operation_effect,
        writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
  exact retired.trans (congrArg some (syncSetX6 base frame state 24 _))

private theorem shiftWord (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 24#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 28, t2 := state.t2 >>> (1 : Nat) }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨6, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 28#32 := fallthrough atPC
  have effect := OpcodeSpec.RV32.execute_SRLI_equiv
    ((OpcodeSpec.RV32.spec_SRLI_hypotheses (r1 := instructionRegister 7) (rd := instructionRegister 7) (imm := 1#6)).mpr ⟨pcRead, (syncReadX7 base frame state)⟩)
  have retired := RV32.stepWrite machine _ _ 7 (base + 28#32) (state.t2 >>> (1 : Nat))
    fetched decoded (by
      simpa [OpcodeSpec.RV32.spec_SRLI, operation_list_effect, operation_effect,
        writeReg_state_success, write_xreg, regidx_to_fin, next] using effect)
  exact retired.trans (congrArg some (syncSetX7 base frame state 28 _))

private theorem decrementBitCounter (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 28#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 32, t3 := state.t3 + 0xffffffff#32 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨7, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 32#32 := fallthrough atPC
  have retired := RV32.stepADDI machine _ (instructionRegister 28) (instructionRegister 28) 4095
    (base + state.pc) state.t3 fetched decoded pcRead (syncReadX28 base frame state) (by decide)
  rw [next] at retired
  exact retired.trans (congrArg some (syncSetX28 base frame state 32 _))

private theorem branchOnBitCounter (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 32#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := if state.t3 = 0#32 then 36#32 else 16#32 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨8, by decide⟩ atPC
  obtain ⟨misa, misaRead⟩ := platform.misa
  have misaAt := syncReadFrame base frame state Register.misa (by decide) misaRead
  have branch : (base + state.pc + (0x1ff0#13).signExtend 32) = base + 16#32 := by
    rw [atPC, BitVec.add_assoc]
    rfl
  have next : base + state.pc + 4#32 = base + 36#32 := fallthrough atPC
  have effect := branchEffect machine (instructionRegister 28) (instructionRegister 0) 0x1ff0#13
    (base + state.pc) state.t3 0#32 pcRead
    (syncReadX28 base frame state) (by rfl) misaAt (by
      intro
      rw [branch]
      exact alignedOffset base 16 platform.alignedCode (by decide))
  by_cases zero : state.t3 = 0#32
  · have retired := RV32.stepSetPC machine _ _ (base + 36#32)
      fetched decoded (by
        simpa only [if_pos zero, next] using effect)
    rw [syncSetPC] at retired
    simpa [zero] using retired
  · have retired := RV32.stepSetPC machine _ _ (base + 16#32)
      fetched decoded (by
        simpa only [if_neg zero, branch] using effect)
    rw [syncSetPC] at retired
    simpa [zero] using retired

private theorem advanceInput (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 36#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 40, a0 := state.a0 + 4 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨9, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 40#32 := fallthrough atPC
  have retired := RV32.stepADDI machine _ (instructionRegister 10) (instructionRegister 10) 4
    (base + state.pc) state.a0 fetched decoded pcRead (syncReadX10 base frame state) (by decide)
  rw [next] at retired
  exact retired.trans (congrArg some (syncSetX10 base frame state 40 _))

private theorem decrementWordCounter (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 40#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 44, t0 := state.t0 + 0xffffffff#32 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨10, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 44#32 := fallthrough atPC
  have retired := RV32.stepADDI machine _ (instructionRegister 5) (instructionRegister 5) 4095
    (base + state.pc) state.t0 fetched decoded pcRead (syncReadX5 base frame state) (by decide)
  rw [next] at retired
  exact retired.trans (congrArg some (syncSetX5 base frame state 44 _))

private theorem branchOnWordCounter (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 44#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := if state.t0 = 0#32 then 48#32 else 8#32 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨11, by decide⟩ atPC
  obtain ⟨misa, misaRead⟩ := platform.misa
  have misaAt := syncReadFrame base frame state Register.misa (by decide) misaRead
  have branch : (base + state.pc + (0x1fdc#13).signExtend 32) = base + 8#32 := by
    rw [atPC, BitVec.add_assoc]
    rfl
  have next : base + state.pc + 4#32 = base + 48#32 := fallthrough atPC
  have effect := branchEffect machine (instructionRegister 5) (instructionRegister 0) 0x1fdc#13
    (base + state.pc) state.t0 0#32 pcRead
    (syncReadX5 base frame state) (by rfl) misaAt (by
      intro
      rw [branch]
      exact alignedOffset base 8 platform.alignedCode (by decide))
  by_cases zero : state.t0 = 0#32
  · have retired := RV32.stepSetPC machine _ _ (base + 48#32)
      fetched decoded (by
        simpa only [if_pos zero, next] using effect)
    rw [syncSetPC] at retired
    simpa [zero] using retired
  · have retired := RV32.stepSetPC machine _ _ (base + 8#32)
      fetched decoded (by
        simpa only [if_neg zero, branch] using effect)
    rw [syncSetPC] at retired
    simpa [zero] using retired

private theorem moveTotalToA0 (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 48#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := 52, a0 := state.t1 }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨12, by decide⟩ atPC
  have next : base + state.pc + 4#32 = base + 52#32 := fallthrough atPC
  have retired := RV32.stepADDI machine _ (instructionRegister 6) (instructionRegister 10) 0
    (base + state.pc) state.t1 fetched decoded pcRead (syncReadX6 base frame state) (by decide)
  rw [next] at retired
  simp only [show (0 : BitVec 12).signExtend 32 = 0#32 from rfl, BitVec.add_zero] at retired
  exact retired.trans (congrArg some (syncSetX10 base frame state 52 _))

private theorem returnToCaller (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (atPC : state.pc = 52#32) :
    RV32.step (sync base frame state) = some (sync base frame { state with pc := returnAddress - base }) := by
  let machine := sync base frame state
  have pcRead := syncReadPC base frame state
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨13, by decide⟩ atPC
  obtain ⟨misa, misaRead⟩ := platform.misa
  obtain ⟨config, configRead⟩ := platform.mseccfg
  have raRead : read_xreg 1 machine = .ok (returnAddress) machine := by
    exact syncReadFrame base frame state Register.x1 (by decide) platform.ra
  have mask : returnAddress &&& 0xfffffffe#32 = returnAddress := platform.returnLow
  have returned : 0xfffffffe#32 &&& returnAddress = returnAddress := by
    rw [BitVec.and_comm, mask]
  have effect := OpcodeSpec.RV32.execute_JALR_equiv
    ((OpcodeSpec.RV32.spec_JALR_hypotheses (rs1 := instructionRegister 1) (rd := instructionRegister 0) (imm := 0#12)).mpr
      ⟨pcRead, raRead⟩)
    (syncReadFrame base frame state Register.misa (by decide) misaRead)
    (platform.privilegeAt state)
    (syncReadFrame base frame state Register.mseccfg (by decide) configRead)
    (by simp [platform.returnNext, BitVec.ofBool])
  have next : base + (returnAddress - base) = returnAddress := by
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have retired := RV32.stepSetPC machine _ _ (base + (returnAddress - base))
    fetched decoded (by
      simpa [OpcodeSpec.RV32.spec_JALR, operation_list_effect, operation_effect,
        writeReg_state_success, write_xreg, regidx_to_fin, returned, next] using effect)
  rw [syncSetPC] at retired
  exact retired

end SailInstructions


/-! ## Bit and word loop invariants -/

section LoopInvariants

def bitNextPc (counter : Word) : Word :=
  if counter = 0#32 then 36#32 else 16#32

theorem addDecrement (word : Word) : word + 0xffffffff#32 = word - 1#32 := by
  rw [BitVec.sub_eq_add_neg]
  congr 1

def bitUpdate (state : Snapshot) : Snapshot :=
  let counter := state.t3 - 1#32
  { state with
    pc := bitNextPc counter
    t1 := state.t1 + (state.t2 &&& 1#32)
    t2 := state.t2 >>> (1 : Nat)
    t3 := counter
    t4 := state.t2 &&& 1#32 }

@[irreducible] def bitScan (remaining : Nat) : Snapshot → Snapshot :=
  Nat.rec (fun state => state) (fun _ previous state => previous (bitUpdate state)) remaining

@[simp] theorem bitScanZero (state : Snapshot) : bitScan 0 state = state := by unfold bitScan; rfl

@[simp] theorem bitScanSucc (remaining : Nat) (state : Snapshot) :
    bitScan (remaining + 1) state = bitScan remaining (bitUpdate state) := by unfold bitScan; rfl

theorem bitCounterNext (state : Snapshot) (remaining : Nat)
    (counter : state.t3 = BitVec.ofNat 32 (remaining + 1)) :
    (bitUpdate state).t3 = BitVec.ofNat 32 remaining := by
  simp only [bitUpdate, counter, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ 1#32

theorem bitPcNext (state : Snapshot) (remaining : Nat)
    (counter : (bitUpdate state).t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) :
    (bitUpdate state).pc = (if remaining = 0 then 36#32 else 16#32) := by
  simp only [bitUpdate] at counter
  simp only [bitUpdate, bitNextPc, counter]
  by_cases empty : remaining = 0
  · simp [empty]
  · have small : remaining < 2 ^ 32 := by omega
    have nonzero : BitVec.ofNat 32 remaining ≠ 0#32 := by
      intro equal
      have value := congrArg BitVec.toNat equal
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, BitVec.toNat_zero] at value
      exact empty value
    simp only [empty, nonzero, if_false]

theorem bitLoopExit (remaining : Nat) (state : Snapshot)
    (counter : state.t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) (positive : 0 < remaining) :
    (bitScan remaining state).pc = 36#32 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining previous =>
    rw [bitScanSucc]
    have nextCounter := bitCounterNext state remaining counter
    by_cases empty : remaining = 0
    · simpa [empty] using bitPcNext state remaining nextCounter (by omega)
    exact previous (bitUpdate state) nextCounter (by omega) (by omega)

theorem bitScanPreserves (project : Snapshot → α)
    (unchanged : ∀ state, project (bitUpdate state) = project state)
    (remaining : Nat) (state : Snapshot) :
    project (bitScan remaining state) = project state := by
  induction remaining generalizing state with
  | zero => rw [bitScanZero]
  | succ remaining previous =>
    rw [bitScanSucc, previous, unchanged]

theorem bitKeepsPointer (state : Snapshot) : (bitUpdate state).a0 = state.a0 := by
  simp only [bitUpdate]

theorem bitKeepsWordCount (state : Snapshot) : (bitUpdate state).t0 = state.t0 := by
  simp only [bitUpdate]

theorem bitScanTotal (remaining : Nat) (state : Snapshot) :
    (bitScan remaining state).t1 = scan remaining state.t2 state.t1 := by
  induction remaining generalizing state with
  | zero => rw [bitScanZero, scan]
  | succ remaining previous =>
    rw [bitScanSucc, previous, scan.eq_2]
    rfl

def advanceWord (state : Snapshot) : Snapshot :=
  { state with pc := if state.t0 - 1#32 = 0#32 then 48#32 else 8#32
               a0 := state.a0 + 4, t0 := state.t0 - 1#32 }

def loadedWord (memory : Memory) (state : Snapshot) : Snapshot :=
  { state with pc := 16#32, t2 := memory state.a0, t3 := 32#32 }

theorem loadedPc (memory : Memory) (state : Snapshot) : (loadedWord memory state).pc = 16#32 := by simp [loadedWord]

theorem loadedCounter (memory : Memory) (state : Snapshot) :
    (loadedWord memory state).t3 = BitVec.ofNat 32 32 := by simp [loadedWord]

theorem loadedExit (memory : Memory) (state : Snapshot) : (bitScan 32 (loadedWord memory state)).pc = 36#32 :=
  bitLoopExit 32 (loadedWord memory state) (loadedCounter memory state) (by decide) (by decide)

@[irreducible] def wordResult (memory : Memory) (state : Snapshot) : Snapshot :=
  advanceWord (bitScan 32 (loadedWord memory state))

@[simp] theorem wordResultPc (memory : Memory) (state : Snapshot) :
    (wordResult memory state).pc = (if state.t0 - 1#32 = 0#32 then 48#32 else 8#32) := by
  have words := bitScanPreserves Snapshot.t0 bitKeepsWordCount 32 (loadedWord memory state)
  simp only [wordResult, advanceWord, words]
  simp only [loadedWord]

@[simp] theorem wordResultT0 (memory : Memory) (state : Snapshot) : (wordResult memory state).t0 = state.t0 - 1#32 := by
  have words := bitScanPreserves Snapshot.t0 bitKeepsWordCount 32 (loadedWord memory state)
  simp only [wordResult, advanceWord, words]
  simp only [loadedWord]

@[simp] theorem wordResultA0 (memory : Memory) (state : Snapshot) : (wordResult memory state).a0 = state.a0 + 4 := by
  have pointer := bitScanPreserves Snapshot.a0 bitKeepsPointer 32 (loadedWord memory state)
  simp only [wordResult, advanceWord, pointer]
  simp only [loadedWord]

@[simp] theorem wordResultT1 (memory : Memory) (state : Snapshot) :
    (wordResult memory state).t1 = scan 32 (memory state.a0) state.t1 := by
  simp only [wordResult, advanceWord, bitScanTotal, loadedWord]

end LoopInvariants


/-! ## Compose the Sail steps -/

section SailRun

open LeanRV32D RV32IM RV32

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}
variable (platform : Platform base frame input returnAddress memory)

include platform

private theorem start (state : Snapshot) :
    RV32.run 2 (sync base frame { state with pc := 0 }) =
      some (sync base frame { state with pc := 8, t0 := 4, t1 := 0 }) := by
  have counter := initializeWordCounter platform { state with pc := 0 } rfl
  have total := clearTotal platform { state with pc := 4, t0 := 4 } rfl
  simp only [RV32.run, counter, total, Option.bind_some]

private theorem bitInstructions (state : Snapshot) (pc : state.pc = 16#32) :
    RV32.run 5 (sync base frame state) = some (sync base frame (bitUpdate state)) := by
  let masked := { state with pc := 20#32, t4 := state.t2 &&& 1#32 }
  let counted := { masked with pc := 24#32, t1 := masked.t1 + masked.t4 }
  let shifted := { counted with pc := 28#32, t2 := counted.t2 >>> (1 : Nat) }
  let decremented := { shifted with pc := 32#32, t3 := shifted.t3 + 0xffffffff#32 }
  have lowBit := extractLowBit platform state pc
  have total := addLowBit platform masked rfl
  have shift := shiftWord platform counted rfl
  have counter := decrementBitCounter platform shifted rfl
  have branch := branchOnBitCounter platform decremented rfl
  change RV32.step (sync base frame state) = some (sync base frame masked) at lowBit
  change RV32.step (sync base frame masked) = some (sync base frame counted) at total
  change RV32.step (sync base frame counted) = some (sync base frame shifted) at shift
  change RV32.step (sync base frame shifted) = some (sync base frame decremented) at counter
  simp only [RV32.run, lowBit, total, shift, counter, branch, Option.bind_some]
  simp only [decremented, shifted, counted, masked, bitUpdate, bitNextPc, addDecrement]

private theorem bitLoop (remaining : Nat) (state : Snapshot)
    (atBit : state.pc = 16#32) (counter : state.t3 = BitVec.ofNat 32 remaining)
    (bound : remaining ≤ 32) :
    RV32.run (remaining * 5) (sync base frame state) =
      some (sync base frame (bitScan remaining state)) := by
  induction remaining generalizing state with
  | zero => simp [RV32.run]
  | succ remaining previous =>
    rw [show (remaining + 1) * 5 = 5 + remaining * 5 by omega, RV32.runAdd,
      bitInstructions platform state atBit, Option.bind_some, bitScanSucc]
    by_cases empty : remaining = 0
    · simp [empty, RV32.run]
    have nextCounter := bitCounterNext state remaining counter
    have nextPc := bitPcNext state remaining nextCounter (by omega)
    exact previous (bitUpdate state) (by simpa only [empty, if_false] using nextPc)
      nextCounter (by omega)

private theorem loadWord (state : Snapshot) (pc : state.pc = 8#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    RV32.run 2 (sync base frame state) = some (sync base frame (loadedWord memory state)) := by
  have word := loadInputWord platform state pc inRam
  have counter := initializeBitCounter platform { state with pc := 12, t2 := memory state.a0 } rfl
  simp only [RV32.run, word, counter, Option.bind_some, loadedWord]
  rfl

private theorem nextWord (state : Snapshot) (pc : state.pc = 36#32) :
    RV32.run 3 (sync base frame state) = some (sync base frame (advanceWord state)) := by
  let advanced := { state with pc := 40#32, a0 := state.a0 + 4 }
  let decremented := { advanced with pc := 44#32, t0 := advanced.t0 + 0xffffffff#32 }
  have pointer := advanceInput platform state pc
  have counter := decrementWordCounter platform advanced rfl
  have branch := branchOnWordCounter platform decremented rfl
  change RV32.step (sync base frame state) = some (sync base frame advanced) at pointer
  change RV32.step (sync base frame advanced) = some (sync base frame decremented) at counter
  simp only [RV32.run, pointer, counter, branch, Option.bind_some]
  simp only [advanceWord, decremented, advanced, addDecrement]

private theorem oneWord (state : Snapshot) (pc : state.pc = 8#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    RV32.run 165 (sync base frame state) = some (sync base frame (wordResult memory state)) := by
  have bits := bitLoop platform 32 (loadedWord memory state) (loadedPc memory state)
    (loadedCounter memory state) (by decide)
  rw [show 165 = 2 + (32 * 5 + 3) by decide, RV32.runAdd, loadWord platform state pc inRam,
    Option.bind_some, RV32.runAdd, bits, Option.bind_some, nextWord platform _ (loadedExit memory state)]
  rw [wordResult]

private theorem finish (state : Snapshot) (pc : state.pc = 48#32) :
    RV32.run 2 (sync base frame state) =
      some (sync base frame { state with a0 := state.t1, pc := returnAddress - base }) := by
  have result := moveTotalToA0 platform state pc
  have returned := returnToCaller platform { state with a0 := state.t1, pc := 52 } rfl
  simp only [RV32.run, result, returned, Option.bind_some]

end SailRun

/-! ## Correctness of the linked Sail execution -/

section Correctness

open LeanRV32D RV32IM RV32

-- The four words of the input view agree with the bytes in Sail memory.
-- Only the six scratch registers and the two PC entries change.
theorem popcount128SailCorrect (base : Word) (machine : Machine) (initial : Snapshot)
    (memory : Memory) (returnAddress : Word)
    (entry : machine = sync base machine { initial with pc := 0 })
    (platform : Platform base machine initial.a0 returnAddress memory) :
    ∃ final, RV32.run 664 machine = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (final.regs.get? Register.x10).map BitVec.toNat =
        some (inputBits memory initial.a0).cpop.toNat ∧
      final.mem = machine.mem ∧
      ∀ register ∉ [Register.PC, .nextPC, .x5, .x6, .x7, .x10, .x28, .x29],
        final.regs.get? register = machine.regs.get? register := by
  let seed := { initial with pc := 8#32, t0 := 4#32, t1 := 0#32 }
  let first := wordResult memory seed
  let second := wordResult memory first
  let third := wordResult memory second
  let fourth := wordResult memory third
  let last := { fourth with a0 := fourth.t1, pc := returnAddress - base }
  have setup : RV32.run 2 (sync base machine { initial with pc := 0 }) =
      some (sync base machine seed) := start platform initial
  have firstStep := oneWord platform seed (by simp [seed]) (by simp [seed, inputAddresses])
  have secondStep := oneWord platform first (by simp [first, seed]) (by simp [first, seed, inputAddresses])
  have thirdStep := oneWord platform second
    (by simp [second, first, seed]) (by simp [second, first, seed, inputAddresses])
  have fourthStep := oneWord platform third
    (by simp [third, second, first, seed]) (by simp [third, second, first, seed, inputAddresses])
  have returned := finish platform fourth (by simp [fourth, third, second, first, seed])
  refine ⟨sync base machine last, ?_, ?_, ?_, syncMem _ _ _, syncFrame _ _ _⟩
  · refine (congrArg (RV32.run 664) entry).trans ?_
    rw [show 664 = 2 + (165 + (165 + (165 + (165 + 2)))) by decide,
      RV32.runAdd, setup, Option.bind_some, RV32.runAdd, firstStep, Option.bind_some,
      RV32.runAdd, secondStep, Option.bind_some, RV32.runAdd, thirdStep, Option.bind_some,
      RV32.runAdd, fourthStep, Option.bind_some, returned]
  · have pcRead := syncReadPC base machine last
    have pc : base + last.pc = returnAddress := by
      change base + (returnAddress - base) = returnAddress
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    rw [pc] at pcRead
    exact readReg_succ.mp pcRead
  · have read : Sail.readReg Register.x10 (sync base machine last) =
        .ok last.a0 (sync base machine last) := syncReadX10 base machine last
    rw [readReg_succ.mp read, Option.map_some, ← scanInputCorrect]
    simp [last, fourth, third, second, first, seed, scanInput]

#print axioms popcount128SailCorrect

end Correctness


end Popcount

/-! ## ELF byte verification -/

section LinkedElf

-- GNU binutils supply the ELF symbol and section locations. Compare the raw
-- bytes at the resulting file offset, independently of any disassembly.
def columns (line : String) : List String :=
  (line.splitOn " ").filter (· != "")

def hex (part : String) : IO Nat := do
  let mut value := 0
  for digit in part.toList do
    let ascii := digit.toNat
    let nibble ←
      if '0'.toNat ≤ ascii && ascii ≤ '9'.toNat then pure (ascii - '0'.toNat)
      else if 'a'.toNat ≤ ascii && ascii ≤ 'f'.toNat then pure (ascii - 'a'.toNat + 10)
      else throw (IO.userError s!"Invalid hexadecimal value: {part}")
    value := value * 16 + nibble
  return value

def verifyElf (path : String) : IO Unit := do
  let symbols ← IO.Process.run { cmd := "nm", args := #["-S", "--defined-only", path] }
  let sections ← IO.Process.run { cmd := "objdump", args := #["-h", "-j", ".text", path] }
  let symbolRows := (symbols.splitOn "\n").map columns
  let [[addressText, sizeText, "T", "popcount128"]] :=
    symbolRows.filter (fun row => row.getLast? == some "popcount128")
    | throw (IO.userError "Expected one popcount128 text symbol")
  let [(_ :: ".text" :: sectionSizeText :: baseText :: _ :: offsetText :: _)] :=
    (sections.splitOn "\n").map columns |>.filter (fun row => row[1]? == some ".text")
    | throw (IO.userError "Expected one .text section")
  let address ← hex addressText
  let size ← hex sizeText
  let sectionSize ← hex sectionSizeText
  let base ← hex baseText
  let offset ← hex offsetText
  unless address % 4 == 0 && base ≤ address && address + size ≤ base + sectionSize do
    throw (IO.userError "popcount128 is misaligned or lies outside .text")
  let expected := Popcount.instructions.flatMap fun (word, _) =>
    (List.range 4).map fun index => UInt8.ofNat (word.toNat >>> (8 * index))
  let startOffset := offset + (address - base)
  let elf ← IO.FS.readBinFile path
  let actual := (elf.extract startOffset (startOffset + size)).data.toList
  unless size == expected.length && actual == expected do
    throw (IO.userError "The linked popcount128 bytes differ from the Lean proof")
  IO.println s!"popcount128: verified all {size} linked bytes"

end LinkedElf


end Riscfree
