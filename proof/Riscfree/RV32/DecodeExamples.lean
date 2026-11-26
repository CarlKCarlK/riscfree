import Riscfree.RV32.Decode

/-!
# Decoding instructions that no popcount proof uses

A regression test for the pre-simplified decoder: these words come from
instruction families that the popcount routines never execute, such as stores,
calls, unsigned comparisons, and byte loads. They decode from the same two
platform facts as every other word, with no instruction-specific lemma, so a
new program supplies only its table.
-/

namespace Riscfree.RV32.DecodeExamples

open LeanRV32D LeanRV32D.Functions RV32IM

def instructions : List (BitVec 32 × instruction) :=
  [ (0xfe112e23, .STORE (0xffc, reg 1, reg 2, 4))          -- sw ra, -4(sp)
  , (0x010000ef, .JAL (16, reg 1))                         -- jal ra, 16
  , (0x008580e7, .JALR (8, reg 11, reg 1))                 -- jalr ra, 8(a1)
  , (0x12345517, .UTYPE (0x12345, reg 10, .AUIPC))         -- auipc a0, 0x12345
  , (0x00c5b533, .RTYPE (reg 12, reg 11, reg 10, .SLTU))   -- sltu a0, a1, a2
  , (0x00b56463, .BTYPE (8, reg 11, reg 10, .BLTU))        -- bltu a0, a1, 8
  , (0x00251513, .SHIFTIOP (2, reg 10, reg 10, .SLLI))     -- slli a0, a0, 2
  , (0x0005c503, .LOAD (0, reg 11, reg 10, true, 1))       -- lbu a0, 0(a1)
  , (0x00a580a3, .STORE (1, reg 10, reg 11, 1))            -- sb a0, 1(a1)
  ]

theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions, ext_decode entry.1 state = .ok entry.2 state := by
  decode_table_normal_form instructions [privilege, landingPad]

end Riscfree.RV32.DecodeExamples
