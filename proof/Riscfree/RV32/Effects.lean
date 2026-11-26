import PicoFV.RV32IM.RVSail.Opcodes.lw
import PicoFV.RV32IM.RVSail.Opcodes.sw

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

abbrev Machine := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

-- A naturally aligned word uses one translation and one physical read. The
-- premises refer only to this address and permit other, non-RAM regions.
theorem alignedWordRead (state : Machine)
    (address offset : BitVec 32) (physical : physaddr) (word : BitVec 32)
    (aligned : address.toNat % 4 = 0)
    (translation : translateAddr (.Virtaddr address) (.Load .Data) state =
      .ok (.Ok (physical, ())) state)
    (read : mem_read (.Load .Data) physical 4 false false false state =
      .ok (.Ok word) state) :
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false state =
      .ok (.Ok word) state := by
  have divides : (4 : Int) ∣ address.toNat := by omega
  simp [vmem_read_addr, divides, -translateAddr, -mem_read, translation, read]

-- A 32-bit word already fills the destination register, so either execution
-- constructor writes the same value. This lemma concerns execution after decode.
theorem loadWordExecutionIgnoresExtension (imm : BitVec 12) (base dest : regidx) :
    execute_LOAD imm base dest false 4 = execute_LOAD imm base dest true 4 := by
  have sameWidth (data : BitVec 32) : extend_value false data = extend_value true data := by
    simp [extend_value, zero_extend, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend]
  simp only [execute_LOAD, sameWidth]

-- A byte outside an aligned word store retains its original contents.
theorem alignedStorePreservesDisjointByte
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (base source : regidx) (offset : BitVec 12)
    (pc pointer value : BitVec 32) (observed : Nat)
    (reads : (operation_list_effect
      (OpcodeSpec.RV32.spec_SW base source offset pc pointer value) state).hypotheses)
    (platform : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (inRange : (pointer + offset.signExtend 32).toNat < Pico_address_space_size_32)
    (aligned : (4 : Int) ∣ (pointer + offset.signExtend 32).toNat)
    (disjoint : observed < (pointer + offset.signExtend 32).toNat ∨
      (pointer + offset.signExtend 32).toNat + 4 ≤ observed) :
    (match execute_instruction (.STORE (offset, source, base, 4)) state with
      | .ok _ finalState => finalState.mem[observed]?
      | .error _ _ => none) = state.mem[observed]? := by
  rw [OpcodeSpec.RV32.execute_SW_equiv reads platform inRange aligned]
  let address := (pointer + offset.signExtend 32).toNat
  change observed < address ∨ address + 4 ≤ observed at disjoint
  have outsideStart : address ≠ observed := by omega
  have outsideSecond : address + 1 ≠ observed := by omega
  have outsideThird : address + 2 ≠ observed := by omega
  have outsideFourth : address + 3 ≠ observed := by omega
  simp [OpcodeSpec.RV32.spec_SW, operation_list_effect, operation_effect,
    Sail.writeReg, PreSail.writeReg, Std.ExtHashMap.getElem?_insert]
  simp [address] at outsideStart outsideSecond outsideThird outsideFourth
  simp [outsideStart, outsideSecond, outsideThird, outsideFourth]

end Riscfree.RV32
