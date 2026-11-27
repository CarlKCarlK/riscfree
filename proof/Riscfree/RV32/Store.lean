import Riscfree.RV32.Platform

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

abbrev ByteMemory := Std.ExtHashMap Nat (BitVec 8)

def storeWord (memory : ByteMemory) (address : Nat) (value : BitVec 32) : ByteMemory :=
  (((memory.insert address (value.extractLsb' 0 8)).insert (address + 1)
    (value.extractLsb' 8 8)).insert (address + 2) (value.extractLsb' 16 8)).insert (address + 3)
    (value.extractLsb' 24 8)

def setWord (state : Machine) (address : Nat) (value : BitVec 32) : Machine :=
  { state with mem := storeWord state.mem address value }

private theorem fullExtract (value : BitVec 32) : value.extractLsb 31 0 = value := by
  simp [BitVec.extractLsb, BitVec.extractLsb']

theorem storeWordOutside (memory : ByteMemory) (address : Nat) (value : BitVec 32)
    (observed : Nat) (outside : observed < address ∨ address + 4 ≤ observed) :
    (storeWord memory address value)[observed]? = memory[observed]? := by
  have first : address ≠ observed := by omega
  have second : address + 1 ≠ observed := by omega
  have third : address + 2 ≠ observed := by omega
  have fourth : address + 3 ≠ observed := by omega
  simp [storeWord, Std.ExtHashMap.getElem?_insert, first, second, third, fourth]

-- An initialized word is represented by its four little-endian bytes.
def WordAt (memory : ByteMemory) (address : Nat) (value : BitVec 32) : Prop :=
  ∀ byte : Fin 4, memory[address + byte.val]? = some (value.extractLsb' (8 * byte.val) 8)

theorem wordAtStore (memory : ByteMemory) (address : Nat) (value : BitVec 32) :
    WordAt (storeWord memory address value) address value := by
  intro byte
  fin_cases byte <;>
    simp (disch := omega) only [storeWord, Std.ExtHashMap.getElem?_insert,
      Nat.reduceMul, Nat.add_zero, beq_iff_eq, if_true, if_neg]

theorem WordAt.storeOther {memory : ByteMemory} {address written : Nat} {value data : BitVec 32}
    (word : WordAt memory address value)
    (apart : address + 4 ≤ written ∨ written + 4 ≤ address) :
    WordAt (storeWord memory written data) address value := by
  intro byte
  rw [storeWordOutside _ _ _ _ (by have := byte.isLt; omega)]
  exact word byte

-- A word depends only on its own four bytes.
theorem WordAt.congr {memory other : ByteMemory} {address : Nat} {value : BitVec 32}
    (word : WordAt memory address value)
    (same : ∀ byte, address ≤ byte → byte < address + 4 → other[byte]? = memory[byte]?) :
    WordAt other address value := by
  intro byte
  rw [same _ (by omega) (by have := byte.isLt; omega)]
  exact word byte

set_option maxHeartbeats 2000000 in
theorem writeAlignedRamWord (state : Machine) (address value : BitVec 32)
    (region : PMA_Region) (regions : List PMA_Region)
    (status : RegisterType Register.mstatus)
    (machine : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (mstatusRead : Sail.readReg Register.mstatus state = .ok status state)
    (mprv : status.extractLsb 17 17 = 0#1)
    (loadedRegions : Sail.readReg Register.pma_regions state = .ok regions state)
    (pmaMatch : matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region)
    (writable : region.attributes.writable = true)
    (htifOff : Sail.readReg Register.htif_tohost_base state = .ok none state)
    (aligned : address.toNat % 4 = 0) :
    vmem_write_addr (.Virtaddr address) 4 value (.Store .Data) false false false state =
      .ok (.Ok true) (setWord state address.toNat value) := by
  have divides : (4 : Int) ∣ address.toNat := by omega
  have bound := address.isLt
  have nonMmio : ¬ (address.toNat : Int) + 4 ≤ 0 := by omega
  have physBound : address.toNat < 17179869184 := by omega
  have machineEq : (Privilege.Machine == Privilege.Machine) = true := rfl
  cases fault : region.attributes.misaligned_fault <;>
    simp [vmem_write_addr, ExceptT.run, machineEq, machine, mstatusRead, mprv, translationMode,
      init_ext_ptw, divides, loadedRegions, -matching_pma, pmaMatch, writable, fault, htifOff,
      nonMmio, Nat.mod_eq_of_lt physBound, setWord, storeWord, Sail.BitVec.extractLsb, fullExtract]

theorem executeWordStore (state : Machine) (base source : regidx) (imm : BitVec 12)
    (pc pointer value : BitVec 32)
    (pcRead : Sail.readReg Register.PC state = .ok pc state)
    (baseRead : read_xreg (regidx_to_fin base) state = .ok pointer state)
    (sourceRead : read_xreg (regidx_to_fin source) state = .ok value state)
    (write : let entered := write_reg_state state Register.nextPC (pc + 4#32)
      vmem_write_addr (.Virtaddr (pointer + imm.signExtend 32)) 4 value
        (.Store .Data) false false false entered =
        .ok (.Ok true) (setWord entered (pointer + imm.signExtend 32).toNat value)) :
    execute_instruction (.STORE (imm, source, base, 4)) state = .ok (.Retire_Success ())
      (setWord (write_reg_state state Register.nextPC (pc + 4#32))
        (pointer + imm.signExtend 32).toNat value) := by
  have index (register : regidx) :
      register = .Regidx (BitVec.ofNat 5 (regidx_to_fin register).val) := by
    cases register
    simp [regidx_to_fin]
  have baseNext := read_xreg_write_other_reg_state (write_val := pc + 4#32)
    (regidx_to_fin base) baseRead reg_of_fin_neq_nextPC
  have sourceNext := read_xreg_write_other_reg_state (write_val := pc + 4#32)
    (regidx_to_fin source) sourceRead reg_of_fin_neq_nextPC
  dsimp only at write
  simp [execute_instruction, pcRead, writeReg_state_success, execute, execute_STORE, vmem_write,
    rX_read_xreg_equiv _ base _ (index base), rX_read_xreg_equiv _ source _ (index source)]
  simp [baseNext, sourceNext, fullExtract, write]

private theorem writeTrackedMemory {S : Type} [RegisterView S] (state : S)
    (frame : Machine) (registers : List (Fin 32)) (mem : ByteMemory) :
    writeTracked registers (RegisterView.value state) { frame with mem } =
      { writeTracked registers (RegisterView.value state) frame with mem } := by
  induction registers with
  | nil => rfl
  | cons head tail ih => simp only [writeTracked, ih]; rfl

theorem syncSetWord {S : Type} [RegisterView S] (base : BitVec 32) (frame : Machine)
    (state : S) (address : Nat) (value : BitVec 32) :
    setWord (sync base frame state) address value = sync base (setWord frame address value) state := by
  have unchanged := syncMem (base := base) (frame := frame) state
  unfold sync at unchanged
  simp only [setWord, sync, unchanged, writeTrackedMemory]
  rfl

theorem syncWithMem {S : Type} [RegisterView S] (base : BitVec 32) (frame : Machine)
    (state : S) (mem : ByteMemory) :
    { sync base frame state with mem } = sync base { frame with mem } state := by
  simp only [sync, writeTrackedMemory]
  rfl

theorem Step.sw {S : Type} [RegisterView S] {base : BitVec 32} {frame : Machine} {state next : S}
    {word : BitVec 32} {pointer value : BitVec 32} {address source : regidx} {imm : BitVec 12}
    (fetched : fetch () (sync base frame state) = .ok (.F_Base word) (sync base frame state))
    (decoded : ext_decode word (sync base frame state) =
      .ok (.STORE (imm, source, address, 4)) (sync base frame state))
    (addressRead : read_xreg (regidx_to_fin address) (sync base frame state) =
      .ok pointer (sync base frame state))
    (sourceRead : read_xreg (regidx_to_fin source) (sync base frame state) =
      .ok value (sync base frame state))
    (write : let entered := write_reg_state (sync base frame state) Register.nextPC (base + RegisterView.pc state + 4#32)
      vmem_write_addr (.Virtaddr (pointer + imm.signExtend 32)) 4 value
        (.Store .Data) false false false entered =
          .ok (.Ok true) (setWord entered (pointer + imm.signExtend 32).toNat value))
    (advances : Jumps state next (RegisterView.pc state + 4#32)) :
    step (sync base frame state) =
      some (sync base (setWord frame (pointer + imm.signExtend 32).toNat value) next) := by
  have effect := executeWordStore _ address source imm _ pointer value (syncReadPC state)
    addressRead sourceRead write
  refine (stepOfEffects _ _ _ _ (base + RegisterView.pc state + 4#32)
    fetched decoded effect ?_).trans ?_
  · exact readReg_succ.mpr (writeReg_get_same _)
  · rw [BitVec.add_assoc, ← advances.1]
    have committed := syncSetPC (base := base) (frame := frame) state next advances.2
    exact congrArg some ((congrArg (fun retired =>
      setWord retired (pointer + imm.signExtend 32).toNat value) committed).trans
        (syncSetWord _ _ _ _ _))

end Riscfree.RV32
