import LeanRV32D.InstsEnd

namespace Riscfree.SailProbe

open LeanRV32D.Functions

abbrev Machine := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

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

def decodeState : Machine :=
  let state : Machine := default
  { state with regs := (state.regs.insert Register.cur_privilege .Machine)
      |>.insert Register.mseccfg 0 |>.insert Register.misa 0 }

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem linkedWordsDecode :
    (instructions.mapM (fun entry => encdec_backwards entry.1)) decodeState =
      .ok (instructions.map Prod.snd) decodeState := by
  rfl

-- ADDI a0, a0, 4 from the loop, with a symbolic input pointer.
theorem sailAdvancePointer (state : Machine) (pointer : BitVec 32)
    (readPointer : state.regs.get? Register.x10 = some pointer) :
    execute_ITYPE 4 (reg 10) (reg 10) .ADDI state =
      .ok (.Retire_Success ()) { state with regs := state.regs.insert Register.x10 (pointer + 4) } := by
  simp [execute_ITYPE, reg, rX_bits, wX_bits, rX, wX, Sail.readReg,
    PreSail.readReg, Sail.writeReg, PreSail.writeReg, regval_from_reg, regval_into_reg,
    xreg_write_callback, Sail.BitVec.toNatInt,
    sign_extend, Sail.BitVec.signExtend, RETIRE_SUCCESS]
  simp [get, modify, MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get, EStateM.modifyGet,
    Bind.bind, Pure.pure, Functor.map, EStateM.instMonad, EStateM.bind, EStateM.pure, EStateM.map,
    readPointer, reg_name_forwards, to_bits, encdec_reg_forwards]

#print axioms linkedWordsDecode
#print axioms sailAdvancePointer

end Riscfree.SailProbe
