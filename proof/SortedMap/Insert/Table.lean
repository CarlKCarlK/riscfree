import RawVec.Access

/-! # Linked instructions of the sorted-map insertion

The routine saves five registers in a 32-byte stack frame. Its only calls are
to the lower-bound search and, for a new key, a tail call to vector insertion.
The words include the linker's `auipc`/`jalr` immediates.
-/

namespace Riscfree.SortedMap.Insert

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec

def instructions : List (Word × instruction) :=
  [ (0xfe010113, .ITYPE (0xfe0, reg 2, reg 2, .ADDI))
  , (0x00112e23, .STORE (28, reg 1, reg 2, 4))
  , (0x00812c23, .STORE (24, reg 8, reg 2, 4))
  , (0x00912a23, .STORE (20, reg 9, reg 2, 4))
  , (0x01212823, .STORE (16, reg 18, reg 2, 4))
  , (0x01312623, .STORE (12, reg 19, reg 2, 4))
  , (0x00060413, .ITYPE (0, reg 12, reg 8, .ADDI))
  , (0x00452983, .LOAD (4, reg 10, reg 19, false, 4))
  , (0x00852603, .LOAD (8, reg 10, reg 12, false, 4))
  , (0x03367263, .BTYPE (0x24, reg 19, reg 12, .BGEU))
  , (0x00300513, .ITYPE (3, reg 0, reg 10, .ADDI))
  , (0x01c12083, .LOAD (28, reg 2, reg 1, false, 4))
  , (0x01812403, .LOAD (24, reg 2, reg 8, false, 4))
  , (0x01412483, .LOAD (20, reg 2, reg 9, false, 4))
  , (0x01012903, .LOAD (16, reg 2, reg 18, false, 4))
  , (0x00c12983, .LOAD (12, reg 2, reg 19, false, 4))
  , (0x02010113, .ITYPE (32, reg 2, reg 2, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  , (0x00058493, .ITYPE (0, reg 11, reg 9, .ADDI))
  , (0x00050913, .ITYPE (0, reg 10, reg 18, .ADDI))
  , (0x00000097, .UTYPE (0, reg 1, .AUIPC))
  , (0x060080e7, .JALR (0x060, reg 1, reg 1))
  , (0x00050593, .ITYPE (0, reg 10, reg 11, .ADDI))
  , (0x03357463, .BTYPE (0x28, reg 19, reg 10, .BGEU))
  , (0x00092603, .LOAD (0, reg 18, reg 12, false, 4))
  , (0x00359693, .SHIFTIOP (3, reg 11, reg 13, .SLLI))
  , (0x00d60633, .RTYPE (reg 13, reg 12, reg 12, .ADD))
  , (0x00062683, .LOAD (0, reg 12, reg 13, false, 4))
  , (0x00969a63, .BTYPE (0x14, reg 9, reg 13, .BNE))
  , (0x00962023, .STORE (0, reg 9, reg 12, 4))
  , (0x00862223, .STORE (4, reg 8, reg 12, 4))
  , (0x00400513, .ITYPE (4, reg 0, reg 10, .ADDI))
  , (0xfadff06f, .JAL (0x1fffac, reg 0))
  , (0x00090513, .ITYPE (0, reg 18, reg 10, .ADDI))
  , (0x00048613, .ITYPE (0, reg 9, reg 12, .ADDI))
  , (0x00040693, .ITYPE (0, reg 8, reg 13, .ADDI))
  , (0x01c12083, .LOAD (28, reg 2, reg 1, false, 4))
  , (0x01812403, .LOAD (24, reg 2, reg 8, false, 4))
  , (0x01412483, .LOAD (20, reg 2, reg 9, false, 4))
  , (0x01012903, .LOAD (16, reg 2, reg 18, false, 4))
  , (0x00c12983, .LOAD (12, reg 2, reg 19, false, 4))
  , (0x02010113, .ITYPE (32, reg 2, reg 2, .ADDI))
  , (0x00000317, .UTYPE (0, reg 6, .AUIPC))
  , (0xd9c30067, .JALR (0xd9c, reg 6, reg 0))
  ]

-- The two callees at their linked offsets from `sorted_map_insert`.
def searchOffset : Word := 0xb0
def vectorOffset : Word := 0xfffffe44

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions, ext_decode entry.1 state = .ok entry.2 state := by
  decode_table_normal_form instructions [privilege, landingPad]

end Riscfree.SortedMap.Insert
