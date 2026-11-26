import PicoFV.RV32IM.RVSail.Auxiliaries

namespace Riscfree.Popcount

open LeanRV32D LeanRV32D.Functions RV32IM

private def reg (index : BitVec 5) : regidx := .Regidx index

private abbrev Machine := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

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

private theorem decode0 :
    encdec_backwards 0x00400293 state = .ok (.ITYPE (4, reg 0, reg 5, .ADDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode1 :
    encdec_backwards 0x00000313 state = .ok (.ITYPE (0, reg 0, reg 6, .ADDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode2 :
    encdec_backwards 0x00052383 state = .ok (.LOAD (0, reg 10, reg 7, false, 4)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [bool_bit_backwards_matches, width_enc_backwards_matches,
    bool_bit_backwards, width_enc_backwards, valid_load_encdec, EStateM.pure,
    LeanRV32D.Functions.regidx_bit_width]

private theorem decode3 :
    encdec_backwards 0x02000e13 state = .ok (.ITYPE (32, reg 0, reg 28, .ADDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode4 :
    encdec_backwards 0x0013fe93 state = .ok (.ITYPE (1, reg 7, reg 29, .ANDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode5 :
    encdec_backwards 0x01d30333 state = .ok (.RTYPE (reg 29, reg 6, reg 6, .ADD)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode6 :
    encdec_backwards 0x0013d393 state = .ok (.SHIFTIOP (1, reg 7, reg 7, .SRLI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode7 :
    encdec_backwards 0xfffe0e13 state = .ok (.ITYPE (0xfff, reg 28, reg 28, .ADDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode8 :
    encdec_backwards 0xfe0e18e3 state = .ok (.BTYPE (0x1ff0, reg 0, reg 28, .BNE)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_bop_backwards_matches, encdec_bop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.base_E_enabled, EStateM.pure, LeanRV32D.Functions.regidx_bit_width]

private theorem decode9 :
    encdec_backwards 0x00450513 state = .ok (.ITYPE (4, reg 10, reg 10, .ADDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode10 :
    encdec_backwards 0xfff28293 state = .ok (.ITYPE (0xfff, reg 5, reg 5, .ADDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode11 :
    encdec_backwards 0xfc029ee3 state = .ok (.BTYPE (0x1fdc, reg 0, reg 5, .BNE)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_bop_backwards_matches, encdec_bop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode12 :
    encdec_backwards 0x00030513 state = .ok (.ITYPE (0, reg 6, reg 10, .ADDI)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards, encdec_iop_backwards,
    privilege, landingPad, EStateM.pure, reg]
  all_goals simp [LeanRV32D.Functions.regidx_bit_width]

private theorem decode13 :
    encdec_backwards 0x00008067 state = .ok (.JALR (0, reg 1, reg 0)) state := by
  unfold encdec_backwards
  simp (config := { maxSteps := 2000000 }) [Sail.BitVec.extractLsb, encdec_reg_backwards_matches,
    encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_reg_backwards,
    privilege, landingPad, EStateM.pure, reg]
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

end Riscfree.Popcount
