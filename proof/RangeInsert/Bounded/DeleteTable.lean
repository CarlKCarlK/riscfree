import RawVec.Access

/-! The words are taken from the linked uncompressed Rust object.
The capacity-failure instruction is included in the byte check. Its AST
entry is a placeholder, and it is excluded from the returning-path decode
lemma. -/

namespace Riscfree.RangeInsert.Bounded.DeleteTable

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

def symbol : String :=
  "_RINvNtCs54hP9qYEcxs_12range_insert22range_insert_algorithm12delete_extramNtB4_5ErrorNtB4_10BoundedMapNtB4_11BoundedKeysEB4_"

def instructions : List (Word × instruction) :=
  [ (0xfd010113, .ITYPE (0xfd0, reg 2, reg 2, .ADDI))
  , (0x02112623, .STORE (0x2c, reg 1, reg 2, 4))
  , (0x02812423, .STORE (0x28, reg 8, reg 2, 4))
  , (0x02912223, .STORE (0x24, reg 9, reg 2, 4))
  , (0x03212023, .STORE (0x20, reg 18, reg 2, 4))
  , (0x01312e23, .STORE (0x1c, reg 19, reg 2, 4))
  , (0x01412c23, .STORE (0x18, reg 20, reg 2, 4))
  , (0x01512a23, .STORE (0x14, reg 21, reg 2, 4))
  , (0x01612823, .STORE (0x10, reg 22, reg 2, 4))
  , (0x01712623, .STORE (0xc, reg 23, reg 2, 4))
  , (0x01812423, .STORE (0x8, reg 24, reg 2, 4))
  , (0x01912223, .STORE (0x4, reg 25, reg 2, 4))
  , (0x01a12023, .STORE (0x0, reg 26, reg 2, 4))
  , (0x00070493, .ITYPE (0x0, reg 14, reg 9, .ADDI))
  , (0x00068993, .ITYPE (0x0, reg 13, reg 19, .ADDI))
  , (0x00052403, .LOAD (0x0, reg 10, reg 8, false, 4))
  , (0x00058913, .ITYPE (0x0, reg 11, reg 18, .ADDI))
  , (0x00040513, .ITYPE (0x0, reg 8, reg 10, .ADDI))
  , (0x00060593, .ITYPE (0x0, reg 12, reg 11, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xebc080e7, .JALR (0xebc, reg 1, reg 1))
  , (0x00442603, .LOAD (0x4, reg 8, reg 12, false, 4))
  , (0x16c50c63, .BTYPE (0x178, reg 12, reg 10, .BEQ))
  , (0x00042b83, .LOAD (0x0, reg 8, reg 23, false, 4))
  , (0x00351693, .SHIFTIOP (0x3, reg 10, reg 13, .SLLI))
  , (0x00361593, .SHIFTIOP (0x3, reg 12, reg 11, .SLLI))
  , (0x00c54533, .RTYPE (reg 12, reg 10, reg 10, .XOR))
  , (0x00198613, .ITYPE (0x1, reg 19, reg 12, .ADDI))
  , (0x00153713, .ITYPE (0x1, reg 10, reg 14, .SLTIU))
  , (0x00db8533, .RTYPE (reg 13, reg 23, reg 10, .ADD))
  , (0xfff70693, .ITYPE (0xfff, reg 14, reg 13, .ADDI))
  , (0x00098b13, .ITYPE (0x0, reg 19, reg 22, .ADDI))
  , (0x01366463, .BTYPE (0x8, reg 19, reg 12, .BLTU))
  , (0x00060b13, .ITYPE (0x0, reg 12, reg 22, .ADDI))
  , (0x00092603, .LOAD (0x0, reg 18, reg 12, false, 4))
  , (0x00492c03, .LOAD (0x4, reg 18, reg 24, false, 4))
  , (0x00bb8bb3, .RTYPE (reg 11, reg 23, reg 23, .ADD))
  , (0x00a6fa33, .RTYPE (reg 10, reg 13, reg 20, .AND))
  , (0x00850513, .ITYPE (0x8, reg 10, reg 10, .ADDI))
  , (0x00098a93, .ITYPE (0x0, reg 19, reg 21, .ADDI))
  , (0x0b750c63, .BTYPE (0xb8, reg 23, reg 10, .BEQ))
  , (0x00052583, .LOAD (0x0, reg 10, reg 11, false, 4))
  , (0x0abb6863, .BTYPE (0xb0, reg 11, reg 22, .BLTU))
  , (0x017546b3, .RTYPE (reg 23, reg 10, reg 13, .XOR))
  , (0x0016b713, .ITYPE (0x1, reg 13, reg 14, .SLTIU))
  , (0xfff70713, .ITYPE (0xfff, reg 14, reg 14, .ADDI))
  , (0x00a77733, .RTYPE (reg 10, reg 14, reg 14, .AND))
  , (0x00472703, .LOAD (0x4, reg 14, reg 14, false, 4))
  , (0x01576463, .BTYPE (0x8, reg 21, reg 14, .BLTU))
  , (0x00070a93, .ITYPE (0x0, reg 14, reg 21, .ADDI))
  , (0x40b70733, .RTYPE (reg 11, reg 14, reg 14, .SUB))
  , (0xfff74593, .ITYPE (0xfff, reg 14, reg 11, .XORI))
  , (0x00b60cb3, .RTYPE (reg 11, reg 12, reg 25, .ADD))
  , (0x00d036b3, .RTYPE (reg 13, reg 0, reg 13, .SLTU))
  , (0x00ccb733, .RTYPE (reg 12, reg 25, reg 14, .SLTU))
  , (0x00052603, .LOAD (0x0, reg 10, reg 12, false, 4))
  , (0x0044a583, .LOAD (0x4, reg 9, reg 11, false, 4))
  , (0x00ec0733, .RTYPE (reg 14, reg 24, reg 14, .ADD))
  , (0x00369693, .SHIFTIOP (0x3, reg 13, reg 13, .SLLI))
  , (0x00d50d33, .RTYPE (reg 13, reg 10, reg 26, .ADD))
  , (0xfff70c13, .ITYPE (0xfff, reg 14, reg 24, .ADDI))
  , (0x01992023, .STORE (0x0, reg 25, reg 18, 4))
  , (0x01892223, .STORE (0x4, reg 24, reg 18, 4))
  , (0x00048513, .ITYPE (0x0, reg 9, reg 10, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xc20080e7, .JALR (0xc20, reg 1, reg 1))
  , (0x00050593, .ITYPE (0x0, reg 10, reg 11, .ADDI))
  , (0x000c8613, .ITYPE (0x0, reg 25, reg 12, .ADDI))
  , (0x000d0513, .ITYPE (0x0, reg 26, reg 10, .ADDI))
  , (0xf80586e3, .BTYPE (0x1f8c, reg 0, reg 11, .BEQ))
  , (0x00100513, .ITYPE (0x1, reg 0, reg 10, .ADDI))
  , (0x0aa59e63, .BTYPE (0xbc, reg 10, reg 11, .BNE))
  , (0x02c12083, .LOAD (0x2c, reg 2, reg 1, false, 4))
  , (0x02812403, .LOAD (0x28, reg 2, reg 8, false, 4))
  , (0x02412483, .LOAD (0x24, reg 2, reg 9, false, 4))
  , (0x02012903, .LOAD (0x20, reg 2, reg 18, false, 4))
  , (0x01c12983, .LOAD (0x1c, reg 2, reg 19, false, 4))
  , (0x01812a03, .LOAD (0x18, reg 2, reg 20, false, 4))
  , (0x01412a83, .LOAD (0x14, reg 2, reg 21, false, 4))
  , (0x01012b03, .LOAD (0x10, reg 2, reg 22, false, 4))
  , (0x00c12b83, .LOAD (0xc, reg 2, reg 23, false, 4))
  , (0x00812c03, .LOAD (0x8, reg 2, reg 24, false, 4))
  , (0x00412c83, .LOAD (0x4, reg 2, reg 25, false, 4))
  , (0x00012d03, .LOAD (0x0, reg 2, reg 26, false, 4))
  , (0x03010113, .ITYPE (0x30, reg 2, reg 2, .ADDI))
  , (0x00008067, .JALR (0x0, reg 1, reg 0))
  , (0x0359fc63, .BTYPE (0x38, reg 21, reg 19, .BGEU))
  , (0x00092503, .LOAD (0x0, reg 18, reg 10, false, 4))
  , (0xfff9c593, .ITYPE (0xfff, reg 19, reg 11, .XORI))
  , (0x00492603, .LOAD (0x4, reg 18, reg 12, false, 4))
  , (0x00ba85b3, .RTYPE (reg 11, reg 21, reg 11, .ADD))
  , (0x00a58533, .RTYPE (reg 10, reg 11, reg 10, .ADD))
  , (0x00b535b3, .RTYPE (reg 11, reg 10, reg 11, .SLTU))
  , (0x00150513, .ITYPE (0x1, reg 10, reg 10, .ADDI))
  , (0x00b605b3, .RTYPE (reg 11, reg 12, reg 11, .ADD))
  , (0x00153613, .ITYPE (0x1, reg 10, reg 12, .SLTIU))
  , (0x00c585b3, .RTYPE (reg 12, reg 11, reg 11, .ADD))
  , (0x00a92023, .STORE (0x0, reg 10, reg 18, 4))
  , (0x00b92223, .STORE (0x4, reg 11, reg 18, 4))
  , (0x015a2223, .STORE (0x4, reg 21, reg 20, 4))
  , (0x0044a903, .LOAD (0x4, reg 9, reg 18, false, 4))
  , (0x02090663, .BTYPE (0x2c, reg 0, reg 18, .BEQ))
  , (0x0004a483, .LOAD (0x0, reg 9, reg 9, false, 4))
  , (0x00291913, .SHIFTIOP (0x2, reg 18, reg 18, .SLLI))
  , (0x0004a583, .LOAD (0x0, reg 9, reg 11, false, 4))
  , (0x00040513, .ITYPE (0x0, reg 8, reg 10, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xd94080e7, .JALR (0xd94, reg 1, reg 1))
  , (0x00051c63, .BTYPE (0x18, reg 0, reg 10, .BNE))
  , (0xffc90913, .ITYPE (0xffc, reg 18, reg 18, .ADDI))
  , (0x00448493, .ITYPE (0x4, reg 9, reg 9, .ADDI))
  , (0xfe0912e3, .BTYPE (0x1fe4, reg 0, reg 18, .BNE))
  , (0x00000513, .ITYPE (0x0, reg 0, reg 10, .ADDI))
  , (0xf5dff06f, .JAL (0x1fff5c, reg 0))
  , (0xc0001073, .ILLEGAL 0xc0001073)
  , (0xc0001073, .ILLEGAL 0xc0001073)
  , (0xc0001073, .ILLEGAL 0xc0001073)
  , (0xc0001073, .ILLEGAL 0xc0001073)
  , (0xc0001073, .ILLEGAL 0xc0001073)
  , (0xc0001073, .ILLEGAL 0xc0001073)
  ]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 32000000 in
theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions, entry.1 ≠ 0xc0001073 →
      ext_decode entry.1 state = .ok entry.2 state := by
  unfold instructions
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  repeat' apply And.intro
  all_goals
    intro notTrap
    first
    | exact False.elim (notTrap rfl)
    | (show encdec_backwards _ _ = _; decode_word_normal_form [privilege, landingPad])

end Riscfree.RangeInsert.Bounded.DeleteTable
