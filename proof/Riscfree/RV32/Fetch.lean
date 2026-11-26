import Riscfree.RV32.Store

/-!
# Instruction fetch from executable RAM

In machine mode, Sail's instruction fetch uses the current privilege even when
`mstatus.MPRV` is set, so the address is not translated. Each halfword read
then needs only the PMA of the region that matches it and the two bytes in
memory. These lemmas derive `InstructionWord` from those facts, so a proof
need not assume the code mapping.
-/

namespace Riscfree.RV32

open LeanRV32D LeanRV32D.Functions RV32IM

-- `effectivePrivilege` applies `mstatus.MPRV` only to accesses other than a fetch.
private theorem fetchIsFetch :
    (MemoryAccessType.InstructionFetch () != (MemoryAccessType.InstructionFetch () :
      MemoryAccessType mem_payload)) = false := by
  decide

theorem machineFetchTranslation (state : Machine) (address : BitVec 32)
    (status : RegisterType Register.mstatus)
    (machine : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (mstatusRead : Sail.readReg Register.mstatus state = .ok status state) :
    translateAddr (.Virtaddr address) (.InstructionFetch ()) state =
      .ok (.Ok (.Physaddr (address.setWidth 34), ())) state := by
  have machineEq : (Privilege.Machine == Privilege.Machine) = true := rfl
  simp [machineEq, fetchIsFetch, machine, mstatusRead, effectivePrivilege, translationMode, init_ext_ptw]

set_option maxHeartbeats 1500000 in
theorem fetchPhysicalHalfword (state : Machine)
    (address : BitVec 32) (region : PMA_Region) (regions : List PMA_Region)
    (status : RegisterType Register.mstatus) (byte0 byte1 : BitVec 8)
    (machine : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (mstatusRead : Sail.readReg Register.mstatus state = .ok status state)
    (loadedRegions : Sail.readReg Register.pma_regions state = .ok regions state)
    (pmaMatch : matching_pma regions (.Physaddr (address.setWidth 34)) 2 = some region)
    (executable : region.attributes.executable = true)
    (htifOff : Sail.readReg Register.htif_tohost_base state = .ok none state)
    (aligned : (2 : Int) ∣ address.toNat)
    (bytes0 : state.mem[address.toNat]? = some byte0)
    (bytes1 : state.mem[address.toNat + 1]? = some byte1) :
    mem_read (.InstructionFetch ()) (.Physaddr (address.setWidth 34)) 2 false false false state =
      .ok (.Ok (byte1 ++ byte0)) state := by
  have bound : address.toNat < 17179869184 := by
    have := address.isLt
    omega
  have nonMmio : ¬ (address.toNat : Int) + 2 ≤ 0 := by omega
  cases fault : region.attributes.misaligned_fault <;>
    simp [machine, fetchIsFetch, mstatusRead, effectivePrivilege, loadedRegions, -matching_pma, pmaMatch,
      executable, fault, aligned, htifOff, nonMmio, Nat.mod_eq_of_lt bound,
      bytes0, bytes1]

-- A word-aligned address has its two low bits clear.
theorem alignedBits (address : BitVec 32) (aligned : address.toNat % 4 = 0) :
    address[0] = false ∧ address[1] = false := by
  constructor
  · rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_zero]
    simp; omega
  · rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.one_and_eq_mod_two,
      Nat.shiftRight_eq_div_pow]
    simp; omega

-- `jalr` clears bit 0 of its target, which changes nothing when the bit is clear.
theorem maskEven (address : BitVec 32) (even : address[0] = false) :
    0xfffffffe#32 &&& address = address := by
  ext index bound
  simp only [BitVec.getElem_and]
  by_cases zero : index = 0
  · subst zero
    simp [even]
  · have set : (0xfffffffe#32)[index] = true := by
      simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
      interval_cases index <;> first | omega | decide
    simp [set]

-- The PMA region that Sail matches for one halfword fetch is executable.
def ExecutableHalfword (regions : List PMA_Region) (address : BitVec 32) : Prop :=
  ∃ region, matching_pma regions (.Physaddr (address.setWidth 34)) 2 = some region ∧
    region.attributes.executable = true

-- A fetch from a word-aligned PC in machine mode reads the four bytes at the PC
-- from executable memory. Nothing is assumed about other addresses.
theorem instructionWordOfMemory (state : Machine) (pc word : BitVec 32)
    (status : RegisterType Register.mstatus) (regions : List PMA_Region)
    (machine : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (mstatusRead : Sail.readReg Register.mstatus state = .ok status state)
    (loadedRegions : Sail.readReg Register.pma_regions state = .ok regions state)
    (htifOff : Sail.readReg Register.htif_tohost_base state = .ok none state)
    (aligned : pc.toNat % 4 = 0)
    (lowExecutable : ExecutableHalfword regions pc)
    (highExecutable : ExecutableHalfword regions (pc + 2#32))
    (bytes : WordAt state.mem pc.toNat word) :
    InstructionWord state pc word := by
  obtain ⟨lowRegion, lowMatch, lowFlag⟩ := lowExecutable
  obtain ⟨highRegion, highMatch, highFlag⟩ := highExecutable
  have highNat : (pc + 2#32).toNat = pc.toNat + 2 := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by simp; omega)
  obtain ⟨bit0, bit1⟩ := alignedBits pc aligned
  refine ⟨bit0, bit1, _, _, machineFetchTranslation state pc status machine mstatusRead,
    machineFetchTranslation state (pc + 2#32) status machine mstatusRead, ?_, ?_⟩
  · have low := fetchPhysicalHalfword state pc lowRegion regions status _ _ machine mstatusRead
      loadedRegions lowMatch lowFlag htifOff (by omega) (by simpa using bytes 0) (by simpa using bytes 1)
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := word) (start₁ := 0) (start₂ := 8)
      (len₁ := 8) (len₂ := 8) rfl] at low
    exact low
  · have high := fetchPhysicalHalfword state (pc + 2#32) highRegion regions status _ _ machine
      mstatusRead loadedRegions highMatch highFlag htifOff (by rw [highNat]; omega)
      (by rw [highNat]; simpa using bytes 2) (by rw [highNat]; simpa [Nat.add_assoc] using bytes 3)
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := word) (start₁ := 16)
      (start₂ := 24) (len₁ := 8) (len₂ := 8) rfl] at high
    exact high

/-! ## Code images

`CodeImage` states where a routine's instruction words lie in memory and that
Sail's PMA check lets each halfword be fetched. With machine mode and the host
interface disabled, it gives the `code` field of `Platform` for every
register snapshot.
-/

structure CodeImage (instructions : List (BitVec 32 × instruction)) (base : BitVec 32)
    (frame : Machine) : Prop where
  fits : base.toNat + 4 * instructions.length ≤ 2 ^ 32
  aligned : base.toNat % 4 = 0
  executable : ∃ regions, Sail.readReg Register.pma_regions frame = .ok regions frame ∧
    ∀ index < instructions.length,
      ExecutableHalfword regions (base + BitVec.ofNat 32 (index * 4)) ∧
      ExecutableHalfword regions (base + BitVec.ofNat 32 (index * 4) + 2#32)
  words : ∀ (index : Nat) (bound : index < instructions.length),
    WordAt frame.mem (base.toNat + index * 4) instructions[index].1

namespace CodeImage

variable {instructions : List (BitVec 32 × instruction)} {base : BitVec 32} {frame : Machine}

-- The image depends on memory only through the code bytes.
theorem withMemory (image : CodeImage instructions base frame) (memory : ByteMemory)
    (agrees : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * instructions.length →
      memory[byte]? = frame.mem[byte]?) :
    CodeImage instructions base { frame with mem := memory } := by
  obtain ⟨regions, regionsRead, executable⟩ := image.executable
  have stored : frame.regs.get? Register.pma_regions = some regions := readReg_succ.mp regionsRead
  refine ⟨image.fits, image.aligned, ⟨regions, readReg_succ.mpr stored, executable⟩,
    fun index bound byte => ?_⟩
  change memory[_]? = _
  rw [agrees _ (by omega) (by have := byte.isLt; omega)]
  exact image.words index bound byte

-- The image depends on registers only through `pma_regions`.
theorem transfer {other : Machine} (image : CodeImage instructions base frame)
    (regions : other.regs.get? Register.pma_regions = frame.regs.get? Register.pma_regions)
    (memory : other.mem = frame.mem) : CodeImage instructions base other := by
  obtain ⟨found, regionsRead, executable⟩ := image.executable
  have stored : frame.regs.get? Register.pma_regions = some found := readReg_succ.mp regionsRead
  refine ⟨image.fits, image.aligned, ⟨found, readReg_succ.mpr (regions.trans stored), executable⟩,
    fun index bound => ?_⟩
  rw [memory]
  exact image.words index bound

theorem atSync {S : Type} [RegisterView S] (image : CodeImage instructions base frame)
    (outerBase : BitVec 32) (state : S) :
    CodeImage instructions base (sync outerBase frame state) :=
  image.transfer (syncFrame state _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions))
    (syncMem state)

theorem code {S : Type} [RegisterView S] (image : CodeImage instructions base frame)
    (machine : Sail.readReg Register.cur_privilege frame = .ok .Machine frame)
    (status : ∃ value, Sail.readReg Register.mstatus frame = .ok value frame)
    (htifOff : Sail.readReg Register.htif_tohost_base frame = .ok none frame)
    (state : S) (index : Fin instructions.length)
    (pc : RegisterView.pc state = BitVec.ofNat 32 (index.val * 4)) :
    InstructionWord (sync base frame state) (base + RegisterView.pc state) instructions[index.val].1 := by
  obtain ⟨regions, regionsRead, executable⟩ := image.executable
  obtain ⟨value, statusRead⟩ := status
  have fits := image.fits
  have aligned := image.aligned
  have address : (base + BitVec.ofNat 32 (index.val * 4)).toNat = base.toNat + index.val * 4 := by
    have := index.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : index.val * 4 < 2 ^ 32)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [pc]
  refine instructionWordOfMemory _ _ _ value regions
    (Platform.systemRead state (fun _ => reg_of_fin_neq_cur_privilege) (by decide) (by decide) machine)
    (Platform.systemRead state (fun _ => reg_of_fin_neq_mstatus) (by decide) (by decide) statusRead)
    (Platform.systemRead state (fun _ => reg_of_fin_neq_pma_regions) (by decide) (by decide)
      regionsRead)
    (Platform.systemRead state (fun _ => reg_of_fin_neq_htif_tohost_base) (by decide) (by decide)
      htifOff)
    (by rw [address]; omega) (executable index.val index.isLt).1 (executable index.val index.isLt).2 ?_
  rw [syncMem, address]
  exact image.words index.val index.isLt

end CodeImage

/-! ## Platforms from machine-mode registers

`MachineState` holds the register facts that instruction fetch and data
accesses need. `MachineMode` adds the return address that `Platform` checks.
Together with a `CodeImage` and the RAM words, they give a `Platform` whose
code mapping is derived from Sail's fetch instead of assumed.
-/

structure MachineState (frame : Machine) : Prop where
  privilege : Sail.readReg Register.cur_privilege frame = .ok .Machine frame
  misa : ∃ value, Sail.readReg Register.misa frame = .ok value frame
  mseccfg : ∃ value, Sail.readReg Register.mseccfg frame = .ok value frame
  landingPad : get_xLPE .Machine frame = .ok false frame
  status : ∃ value, Sail.readReg Register.mstatus frame = .ok value frame ∧
    value.extractLsb 17 17 = 0#1
  htif : Sail.readReg Register.htif_tohost_base frame = .ok none frame

structure MachineMode (frame : Machine) (returnAddress : BitVec 32) : Prop
    extends MachineState frame where
  returnLow : returnAddress &&& 0xfffffffe = returnAddress
  returnNext : (returnAddress)[1] = false
  ra : Sail.readReg Register.x1 frame = .ok returnAddress frame

-- Two machines with the same value for every register that `MachineState`
-- reads.
private theorem readTransfer {first second : Machine} {key : Register} {value : RegisterType key}
    (same : second.regs.get? key = first.regs.get? key)
    (read : Sail.readReg key first = .ok value first) :
    Sail.readReg key second = .ok value second :=
  readReg_succ.mpr (same.trans (readReg_succ.mp read))

namespace MachineState

variable {frame : Machine}

theorem transfer {other : Machine} (machine : MachineState frame)
    (same : ∀ key, (∀ index : Fin 32, reg_of_fin index ≠ key) → key ≠ Register.PC →
      key ≠ Register.nextPC → other.regs.get? key = frame.regs.get? key) :
    MachineState other := by
  obtain ⟨misa, misaRead⟩ := machine.misa
  obtain ⟨config, configRead⟩ := machine.mseccfg
  obtain ⟨status, statusRead, mprv⟩ := machine.status
  have disabled := machine.landingPad
  simp [get_xLPE, configRead] at disabled
  have configOther := readTransfer (same _ (by decide) (by decide) (by decide)) configRead
  refine ⟨readTransfer (same _ (by decide) (by decide) (by decide)) machine.privilege,
    ⟨misa, readTransfer (same _ (by decide) (by decide) (by decide)) misaRead⟩, ⟨config, configOther⟩, ?_,
    ⟨status, readTransfer (same _ (by decide) (by decide) (by decide)) statusRead, mprv⟩,
    readTransfer (same _ (by decide) (by decide) (by decide)) machine.htif⟩
  simp [get_xLPE, configOther, disabled]

-- The facts concern registers only, so they hold for every memory.
theorem withMemory (machine : MachineState frame) (memory : ByteMemory) :
    MachineState { frame with mem := memory } :=
  machine.transfer fun _ _ _ _ => rfl

-- Synchronizing a snapshot writes only general-purpose registers and the PC.
theorem atSync {S : Type} [RegisterView S] (machine : MachineState frame) (base : BitVec 32)
    (state : S) : MachineState (sync base frame state) :=
  machine.transfer fun key notX notPC notNext => syncFrame state key notPC notNext
    (fun index _ => notX index)

end MachineState

namespace MachineMode

variable {frame : Machine} {returnAddress : BitVec 32}

theorem withMemory (mode : MachineMode frame returnAddress) (memory : ByteMemory) :
    MachineMode { frame with mem := memory } returnAddress :=
  { mode.toMachineState.withMemory memory with
    returnLow := mode.returnLow
    returnNext := mode.returnNext
    ra := readTransfer (first := frame) (second := { frame with mem := memory }) rfl mode.ra }

end MachineMode

/-! ## RAM words

A naturally aligned word access in machine mode needs only the PMA region that
matches it, the memory bytes for a load, and the `MachineState` facts.
-/

section Ram

variable {S : Type} [RegisterView S] {base : BitVec 32} {frame : Machine}

private theorem joinBytes (value : BitVec 32) :
    BitVec.append (BitVec.append (BitVec.append (value.extractLsb' 24 8)
      (value.extractLsb' 16 8)) (value.extractLsb' 8 8)) (value.extractLsb' 0 8) = value := by
  have high := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := value) (start₁ := 16)
    (start₂ := 24) (len₁ := 8) (len₂ := 8) rfl
  have middle := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := value) (start₁ := 8)
    (start₂ := 16) (len₁ := 8) (len₂ := 16) rfl
  exact (congrArg (fun first => BitVec.append (BitVec.append first (value.extractLsb' 8 8))
    (value.extractLsb' 0 8)) high).trans
      ((congrArg (fun first => BitVec.append first (value.extractLsb' 0 8)) middle).trans
        (BitVec.extractLsb'_append_extractLsb' (w := 24) (len := 8) (x := value)))

theorem MachineState.loadWord (machine : MachineState frame) (state : S)
    (next offset address value : BitVec 32) (regions : List PMA_Region) (region : PMA_Region)
    (regionsRead : Sail.readReg Register.pma_regions frame = .ok regions frame)
    (matched : matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region)
    (readable : region.attributes.readable = true) (aligned : address.toNat % 4 = 0)
    (word : WordAt frame.mem address.toNat value) :
    let entered := write_reg_state (sync base frame state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false entered =
      .ok (.Ok value) entered := by
  dsimp only
  have synced := machine.atSync base state
  obtain ⟨status, statusRead, mprv⟩ := synced.status
  have read := readAlignedRamWord (write_reg_state (sync base frame state) Register.nextPC next)
    address offset region regions status
    (value.extractLsb' 0 8) (value.extractLsb' 8 8) (value.extractLsb' 16 8)
    (value.extractLsb' 24 8) (readReg_of_write_other_reg_state synced.privilege (by decide))
    (readReg_of_write_other_reg_state statusRead (by decide)) mprv
    (readReg_of_write_other_reg_state (Platform.systemRead state (by decide) (by decide) (by decide)
      regionsRead) (by decide))
    matched readable (readReg_of_write_other_reg_state synced.htif (by decide)) aligned
    (by simpa using word 0) (by simpa using word 1) (by simpa using word 2) (by simpa using word 3)
  exact read.trans (congrArg (fun word => EStateM.Result.ok (Sail.Ok word)
    (write_reg_state (sync base frame state) Register.nextPC next)) (joinBytes value))

theorem MachineState.storeWord (machine : MachineState frame) (state : S)
    (next address value : BitVec 32) (regions : List PMA_Region) (region : PMA_Region)
    (regionsRead : Sail.readReg Register.pma_regions frame = .ok regions frame)
    (matched : matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region)
    (writable : region.attributes.writable = true) (aligned : address.toNat % 4 = 0) :
    let entered := write_reg_state (sync base frame state) Register.nextPC next
    vmem_write_addr (.Virtaddr address) 4 value (.Store .Data) false false false entered =
      .ok (.Ok true) (setWord entered address.toNat value) := by
  dsimp only
  have synced := machine.atSync base state
  obtain ⟨status, statusRead, mprv⟩ := synced.status
  exact writeAlignedRamWord (write_reg_state (sync base frame state) Register.nextPC next)
    address value region regions status
    (readReg_of_write_other_reg_state synced.privilege (by decide))
    (readReg_of_write_other_reg_state statusRead (by decide)) mprv
    (readReg_of_write_other_reg_state (Platform.systemRead state (by decide) (by decide) (by decide)
      regionsRead) (by decide))
    matched writable (readReg_of_write_other_reg_state synced.htif (by decide)) aligned

end Ram

theorem Platform.ofCodeImage {S : Type} [RegisterView S] {instructions : List (BitVec 32 × instruction)}
    {base : BitVec 32} {frame : Machine} {addresses : List (BitVec 32)} {returnAddress : BitVec 32}
    {memory : BitVec 32 → BitVec 32}
    (mode : MachineMode frame returnAddress) (image : CodeImage instructions base frame)
    (ram : ∀ address ∈ addresses,
      ∃ regions region byte0 byte1 byte2 byte3,
        Sail.readReg Register.pma_regions frame = .ok regions frame ∧
        matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region ∧
        region.attributes.readable = true ∧ address.toNat % 4 = 0 ∧
        frame.mem[address.toNat]? = some byte0 ∧ frame.mem[address.toNat + 1]? = some byte1 ∧
        frame.mem[address.toNat + 2]? = some byte2 ∧ frame.mem[address.toNat + 3]? = some byte3 ∧
        memory address = byte3 ++ byte2 ++ byte1 ++ byte0) :
    Platform S instructions base frame addresses returnAddress memory where
  alignedCode := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod]
    exact image.aligned
  returnLow := mode.returnLow
  returnNext := mode.returnNext
  ra := mode.ra
  privilege := mode.privilege
  misa := mode.misa
  mseccfg := mode.mseccfg
  landingPad := mode.landingPad
  status := mode.status
  htif := mode.htif
  ram := ram
  code := image.code mode.privilege (mode.status.imp fun _ read => read.1) mode.htif

end Riscfree.RV32
