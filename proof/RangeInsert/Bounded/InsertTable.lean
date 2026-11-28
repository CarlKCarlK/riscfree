import RawVec.Access

/-! The words are taken from the linked uncompressed Rust object.
The capacity-failure instruction is included in the byte check. Its AST
entry is a placeholder, and it is excluded from the returning-path decode
lemma. -/

namespace Riscfree.RangeInsert.Bounded.InsertTable

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

def symbol : String :=
  "range_insert_u32"

def instructions : List (Word × instruction) :=
  [ (0xfd010113, .ITYPE (0xfd0, reg 2, reg 2, .ADDI))
  , (0x02112623, .STORE (0x2c, reg 1, reg 2, 4))
  , (0x02812423, .STORE (0x28, reg 8, reg 2, 4))
  , (0x02912223, .STORE (0x24, reg 9, reg 2, 4))
  , (0x03212023, .STORE (0x20, reg 18, reg 2, 4))
  , (0x01312e23, .STORE (0x1c, reg 19, reg 2, 4))
  , (0x01412c23, .STORE (0x18, reg 20, reg 2, 4))
  , (0x01512a23, .STORE (0x14, reg 21, reg 2, 4))
  , (0x00a12223, .STORE (0x4, reg 10, reg 2, 4))
  , (0x00c6f663, .BTYPE (0xc, reg 12, reg 13, .BGEU))
  , (0x00000513, .ITYPE (0x0, reg 0, reg 10, .ADDI))
  , (0x1780006f, .JAL (0x178, reg 0))
  , (0x00078993, .ITYPE (0x0, reg 15, reg 19, .ADDI))
  , (0x00070a13, .ITYPE (0x0, reg 14, reg 20, .ADDI))
  , (0x00068493, .ITYPE (0x0, reg 13, reg 9, .ADDI))
  , (0x00060913, .ITYPE (0x0, reg 12, reg 18, .ADDI))
  , (0x00058413, .ITYPE (0x0, reg 11, reg 8, .ADDI))
  , (0x00050a93, .ITYPE (0x0, reg 10, reg 21, .ADDI))
  , (0x00060593, .ITYPE (0x0, reg 12, reg 11, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xda0080e7, .JALR (0xda0, reg 1, reg 1))
  , (0x06050063, .BTYPE (0x60, reg 0, reg 10, .BEQ))
  , (0x00050593, .ITYPE (0x0, reg 10, reg 11, .ADDI))
  , (0x000a8513, .ITYPE (0x0, reg 21, reg 10, .ADDI))
  , (0x000aa603, .LOAD (0x0, reg 21, reg 12, false, 4))
  , (0x00359593, .SHIFTIOP (0x3, reg 11, reg 11, .SLLI))
  , (0x00b60633, .RTYPE (reg 11, reg 12, reg 12, .ADD))
  , (0xff860593, .ITYPE (0xff8, reg 12, reg 11, .ADDI))
  , (0xffc60693, .ITYPE (0xffc, reg 12, reg 13, .ADDI))
  , (0x04058663, .BTYPE (0x4c, reg 0, reg 11, .BEQ))
  , (0x0006a603, .LOAD (0x0, reg 13, reg 12, false, 4))
  , (0x00160713, .ITYPE (0x1, reg 12, reg 14, .ADDI))
  , (0xfff63793, .ITYPE (0xfff, reg 12, reg 15, .SLTIU))
  , (0x01273733, .RTYPE (reg 18, reg 14, reg 14, .SLTU))
  , (0x00e7f733, .RTYPE (reg 14, reg 15, reg 14, .AND))
  , (0x0a070263, .BTYPE (0xa4, reg 0, reg 14, .BEQ))
  , (0x00090593, .ITYPE (0x0, reg 18, reg 11, .ADDI))
  , (0x00048613, .ITYPE (0x0, reg 9, reg 12, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xbe0080e7, .JALR (0xbe0, reg 1, reg 1))
  , (0x02050a63, .BTYPE (0x34, reg 0, reg 10, .BEQ))
  , (0x00100593, .ITYPE (0x1, reg 0, reg 11, .ADDI))
  , (0x0eb50c63, .BTYPE (0xf8, reg 11, reg 10, .BEQ))
  , (0xc0001073, .ILLEGAL 0xc0001073)
  , (0xc0001073, .ILLEGAL 0xc0001073)
  , (0x00000593, .ITYPE (0x0, reg 0, reg 11, .ADDI))
  , (0x000a8513, .ITYPE (0x0, reg 21, reg 10, .ADDI))
  , (0xfa059ee3, .BTYPE (0x1fbc, reg 0, reg 11, .BNE))
  , (0x00090593, .ITYPE (0x0, reg 18, reg 11, .ADDI))
  , (0x00048613, .ITYPE (0x0, reg 9, reg 12, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xbb0080e7, .JALR (0xbb0, reg 1, reg 1))
  , (0x0c051463, .BTYPE (0xc8, reg 0, reg 10, .BNE))
  , (0x01412423, .STORE (0x8, reg 20, reg 2, 4))
  , (0x00012623, .STORE (0xc, reg 0, reg 2, 4))
  , (0x01312823, .STORE (0x10, reg 19, reg 2, 4))
  , (0x00410513, .ITYPE (0x4, reg 2, reg 10, .ADDI))
  , (0x00810713, .ITYPE (0x8, reg 2, reg 14, .ADDI))
  , (0x00040593, .ITYPE (0x0, reg 8, reg 11, .ADDI))
  , (0x00090613, .ITYPE (0x0, reg 18, reg 12, .ADDI))
  , (0x00048693, .ITYPE (0x0, reg 9, reg 13, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xd2c080e7, .JALR (0xd2c, reg 1, reg 1))
  , (0x0a051263, .BTYPE (0xa4, reg 0, reg 10, .BNE))
  , (0x00042583, .LOAD (0x0, reg 8, reg 11, false, 4))
  , (0x00442603, .LOAD (0x4, reg 8, reg 12, false, 4))
  , (0x412486b3, .RTYPE (reg 18, reg 9, reg 13, .SUB))
  , (0x00b685b3, .RTYPE (reg 11, reg 13, reg 11, .ADD))
  , (0x00d5b6b3, .RTYPE (reg 13, reg 11, reg 13, .SLTU))
  , (0x00158593, .ITYPE (0x1, reg 11, reg 11, .ADDI))
  , (0x00d60633, .RTYPE (reg 13, reg 12, reg 12, .ADD))
  , (0x0015b693, .ITYPE (0x1, reg 11, reg 13, .SLTIU))
  , (0x00d60633, .RTYPE (reg 13, reg 12, reg 12, .ADD))
  , (0x00b42023, .STORE (0x0, reg 11, reg 8, 4))
  , (0x00c42223, .STORE (0x4, reg 12, reg 8, 4))
  , (0x0780006f, .JAL (0x78, reg 0))
  , (0xee967ce3, .BTYPE (0x1ef8, reg 9, reg 12, .BGEU))
  , (0x00042503, .LOAD (0x0, reg 8, reg 10, false, 4))
  , (0xfff64613, .ITYPE (0xfff, reg 12, reg 12, .XORI))
  , (0x00442703, .LOAD (0x4, reg 8, reg 14, false, 4))
  , (0x00c48633, .RTYPE (reg 12, reg 9, reg 12, .ADD))
  , (0x00a60533, .RTYPE (reg 10, reg 12, reg 10, .ADD))
  , (0x00c53633, .RTYPE (reg 12, reg 10, reg 12, .SLTU))
  , (0x00150513, .ITYPE (0x1, reg 10, reg 10, .ADDI))
  , (0x00c70633, .RTYPE (reg 12, reg 14, reg 12, .ADD))
  , (0x00153713, .ITYPE (0x1, reg 10, reg 14, .SLTIU))
  , (0x00e60633, .RTYPE (reg 14, reg 12, reg 12, .ADD))
  , (0x00a42023, .STORE (0x0, reg 10, reg 8, 4))
  , (0x00c42223, .STORE (0x4, reg 12, reg 8, 4))
  , (0x0005a603, .LOAD (0x0, reg 11, reg 12, false, 4))
  , (0x0096a023, .STORE (0x0, reg 9, reg 13, 4))
  , (0x01412423, .STORE (0x8, reg 20, reg 2, 4))
  , (0x00012623, .STORE (0xc, reg 0, reg 2, 4))
  , (0x01312823, .STORE (0x10, reg 19, reg 2, 4))
  , (0x00410513, .ITYPE (0x4, reg 2, reg 10, .ADDI))
  , (0x00810713, .ITYPE (0x8, reg 2, reg 14, .ADDI))
  , (0x00040593, .ITYPE (0x0, reg 8, reg 11, .ADDI))
  , (0x00048693, .ITYPE (0x0, reg 9, reg 13, .ADDI))
  , (0x00000097, .UTYPE (0x0, reg 1, .AUIPC))
  , (0xc98080e7, .JALR (0xc98, reg 1, reg 1))
  , (0x00051863, .BTYPE (0x10, reg 0, reg 10, .BNE))
  , (0x0100006f, .JAL (0x10, reg 0))
  , (0x00100593, .ITYPE (0x1, reg 0, reg 11, .ADDI))
  , (0x02b51663, .BTYPE (0x2c, reg 11, reg 10, .BNE))
  , (0x00100513, .ITYPE (0x1, reg 0, reg 10, .ADDI))
  , (0x02c12083, .LOAD (0x2c, reg 2, reg 1, false, 4))
  , (0x02812403, .LOAD (0x28, reg 2, reg 8, false, 4))
  , (0x02412483, .LOAD (0x24, reg 2, reg 9, false, 4))
  , (0x02012903, .LOAD (0x20, reg 2, reg 18, false, 4))
  , (0x01c12983, .LOAD (0x1c, reg 2, reg 19, false, 4))
  , (0x01812a03, .LOAD (0x18, reg 2, reg 20, false, 4))
  , (0x01412a83, .LOAD (0x14, reg 2, reg 21, false, 4))
  , (0x03010113, .ITYPE (0x30, reg 2, reg 2, .ADDI))
  , (0x00008067, .JALR (0x0, reg 1, reg 0))
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

end Riscfree.RangeInsert.Bounded.InsertTable
