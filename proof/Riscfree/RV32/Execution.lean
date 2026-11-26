import Riscfree.RV32.Effects
import PicoFV.RV32IM.RVSail.Opcodes.addi

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

-- Sail fetches a base instruction as two little-endian halfwords. The
-- platform supplies the executable mapping and the two physical reads.
theorem fetchBaseWord (state : Machine) (pc : BitVec 32) (low high : BitVec 16)
    (lowPhysical highPhysical : physaddr)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (pcLow : pc[0] = false) (pcNext : pc[1] = false)
    (uncompressed : isRVC low = false)
    (translateLow : translateAddr (.Virtaddr pc) (.InstructionFetch ()) state =
      .ok (.Ok (lowPhysical, ())) state)
    (translateHigh : translateAddr (.Virtaddr (pc + 2#32)) (.InstructionFetch ()) state =
      .ok (.Ok (highPhysical, ())) state)
    (readLow : mem_read (.InstructionFetch ()) lowPhysical 2 false false false state =
      .ok (.Ok low) state)
    (readHigh : mem_read (.InstructionFetch ()) highPhysical 2 false false false state =
      .ok (.Ok high) state) :
    fetch () state = .ok (.F_Base (high ++ low)) state := by
  simp [fetch, ext_fetch_check_pc, pcRead, misaRead, pcLow, pcNext, uncompressed,
    -translateAddr, -mem_read, translateLow, translateHigh, readLow, readHigh]

-- The code mapping is a platform premise. Sail still checks alignment,
-- reads the two physical halfwords, and determines the instruction width.
def InstructionWord (state : Machine) (pc word : BitVec 32) : Prop :=
  pc[0] = false ∧ pc[1] = false ∧ ∃ lowPhysical highPhysical,
    translateAddr (.Virtaddr pc) (.InstructionFetch ()) state = .ok (.Ok (lowPhysical, ())) state ∧
    translateAddr (.Virtaddr (pc + 2#32)) (.InstructionFetch ()) state =
      .ok (.Ok (highPhysical, ())) state ∧
    mem_read (.InstructionFetch ()) lowPhysical 2 false false false state =
      .ok (.Ok (word.extractLsb' 0 16)) state ∧
    mem_read (.InstructionFetch ()) highPhysical 2 false false false state =
      .ok (.Ok (word.extractLsb' 16 16)) state

theorem InstructionWord.fetch {state : Machine} {pc word : BitVec 32}
    (mapped : InstructionWord state pc word)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (uncompressed : isRVC (word.extractLsb' 0 16) = false) :
    LeanRV32D.Functions.fetch () state = .ok (.F_Base word) state := by
  obtain ⟨pcLow, pcNext, lowPhysical, highPhysical, translateLow, translateHigh, readLow, readHigh⟩ := mapped
  simpa only [BitVec.extractLsb'_append_extractLsb'] using
    fetchBaseWord state pc _ _ lowPhysical highPhysical pcRead misaRead pcLow pcNext uncompressed
      translateLow translateHigh readLow readHigh

-- One uninterrupted 32-bit instruction. Sail supplies fetch, decode, the
-- instruction effect, and the PC commit. Pico initializes the fall-through PC.
noncomputable def step (state : Machine) : Option Machine :=
  match fetch () state with
  | .ok (.F_Base word) fetched =>
    match ext_decode word fetched with
    | .ok operation decoded =>
      match execute_instruction operation decoded with
      | .ok (.Retire_Success ()) executed =>
        match tick_pc () executed with
        | .ok () retired => some retired
        | .error .. => none
      | _ => none
    | .error .. => none
  | _ => none

noncomputable def run : Nat → Machine → Option Machine
  | 0, state => some state
  | count + 1, state => (step state).bind (run count)

theorem runAdd (first second : Nat) (state : Machine) :
    run (first + second) state = (run first state).bind (run second) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
    simp only [Nat.succ_add, run, ih]
    cases step state <;> rfl

theorem stepOfEffects (state executed : Machine) (word : BitVec 32)
    (operation : instruction) (next : BitVec 32)
    (fetched : fetch () state = .ok (.F_Base word) state)
    (decoded : ext_decode word state = .ok operation state)
    (effect : execute_instruction operation state = .ok (.Retire_Success ()) executed)
    (nextPC : Sail.readReg Register.nextPC executed = .ok next executed) :
    step state = some (write_reg_state executed Register.PC next) := by
  simp only [step, fetched, decoded, effect]
  have committed : tick_pc () executed = .ok () (write_reg_state executed Register.PC next) := by
    unfold tick_pc
    simp [nextPC, writeReg_state_success]
  rw [committed]


theorem stepADDI (state : Machine) (word : BitVec 32) (base dest : regidx) (imm : BitVec 12)
    (pc sourceValue : BitVec 32)
    (fetched : fetch () state = .ok (.F_Base word) state)
    (decoded : ext_decode word state = .ok (.ITYPE (imm, base, dest, .ADDI)) state)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (sourceRead : read_xreg (regidx_to_fin base) state = .ok sourceValue state)
    (nonzero : (regidx_to_fin dest).val ≠ 0) :
    let advanced := write_reg_state state Register.nextPC (pc + 4#32)
    let executed := write_reg_state advanced (reg_of_fin (regidx_to_fin dest))
      ((register_type_reg_of_fin_equiv _) ▸ (sourceValue + imm.signExtend 32))
    Riscfree.RV32.step state = some (write_reg_state executed Register.PC (pc + 4#32)) := by
  dsimp only
  have effect := OpcodeSpec.RV32.execute_ADDI_equiv
    ((OpcodeSpec.RV32.spec_ADDI_hypotheses (imm := imm) (rd := dest)).mpr ⟨pcRead, sourceRead⟩)
  apply stepOfEffects state _ word _ _ fetched decoded
  · simpa [OpcodeSpec.RV32.spec_ADDI, operation_list_effect, operation_effect,
      writeReg_state_success, write_xreg, nonzero] using effect
  · apply readReg_of_write_other_reg_state _ reg_of_fin_neq_nextPC.symm
    exact readReg_succ.mpr (writeReg_get_same state)

end Riscfree.RV32
