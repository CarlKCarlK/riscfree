import Riscfree.RV32.Decode
import Riscfree.RV32.Store
import Riscfree.RV32.Fetch

/-!
# Memory access and code mapping shared by the RawVec routines

Each linked routine has its own instruction table, register snapshot, and code
size. This module states, once for all of them, what a routine needs from the
memory system: readable and writable data words, and a code mapping that
survives every data write that misses the code.
-/

namespace Riscfree.RawVec

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

abbrev Word := BitVec 32

-- The memory system maps these executable bytes independently of data writes.
def CodeAgreesFor (codeBytes : Nat) (base : Word) (original memory : ByteMemory) : Prop :=
  ∀ byte, base.toNat ≤ byte → byte < base.toNat + codeBytes →
    memory[byte]? = original[byte]?

def Mapped (frame : Machine) (address : Word) (permission : PMA_Region → Prop) : Prop :=
  address.toNat % 4 = 0 ∧ ∃ regions region,
    Sail.readReg Register.pma_regions frame = .ok regions frame ∧
    matching_pma regions (.Physaddr (address.setWidth 34)) 4 = some region ∧ permission region

abbrev Readable (frame : Machine) (address : Word) :=
  Mapped frame address (fun region => region.attributes.readable = true)

abbrev Writable (frame : Machine) (address : Word) :=
  Mapped frame address (fun region => region.attributes.writable = true)

-- The code of `codeBytes` bytes at `base` stays fetchable for every memory that
-- keeps those bytes.
structure EnvironmentFor (S : Type) [RegisterView S] (instructions : List (Word × instruction))
    (codeBytes : Nat) (base returnAddress : Word) (original : Machine) : Prop where
  codeFits : base.toNat + codeBytes ≤ 2 ^ 32
  platform : ∀ memory, CodeAgreesFor codeBytes base original.mem memory →
    Platform S instructions base { original with mem := memory } [] returnAddress (fun _ => 0)

-- In machine mode, Sail's fetch reads the code bytes from executable memory,
-- so the code mapping for every memory that keeps those bytes follows from the
-- original machine. No RAM words are needed: the routine's data accesses
-- carry their own `Readable` and `Writable` premises.
theorem EnvironmentFor.ofMachine {S : Type} [RegisterView S] {instructions : List (Word × instruction)}
    {codeBytes : Nat} {base returnAddress : Word} {original : Machine}
    (mode : MachineMode original returnAddress) (image : CodeImage instructions base original)
    (size : codeBytes = 4 * instructions.length) :
    EnvironmentFor S instructions codeBytes base returnAddress original where
  codeFits := size ▸ image.fits
  platform memory agrees :=
    Platform.ofCodeImage (mode.withMemory memory)
      (image.withMemory memory fun byte low high => agrees byte low (size ▸ high))
      (fun _ inside => nomatch inside)

section Platform

variable {S : Type} [RegisterView S] {instructions : List (Word × instruction)}
  {base returnAddress : Word} {original : Machine} {memory : ByteMemory}

set_option maxHeartbeats 1500000 in
theorem Platform.loadWord
    (platform : Platform S instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : S) (next offset address value : Word)
    (permission : Readable original address) (word : WordAt memory address.toNat value) :
    let entered := write_reg_state (sync base {original with mem := memory} state) Register.nextPC next
    vmem_read_addr (.Virtaddr address) offset 4 (.Load .Data) false false false entered =
      .ok (.Ok value) entered := by
  dsimp only
  obtain ⟨aligned, regions, region, readRegions, matched, readable⟩ := permission
  obtain ⟨status, statusRead, mprv⟩ := platform.status
  have combined : BitVec.append (BitVec.append (BitVec.append (value.extractLsb' 24 8)
      (value.extractLsb' 16 8)) (value.extractLsb' 8 8)) (value.extractLsb' 0 8) = value := by
    have high := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := value) (start₁ := 16)
      (start₂ := 24) (len₁ := 8) (len₂ := 8) rfl
    have middle := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := value) (start₁ := 8)
      (start₂ := 16) (len₁ := 8) (len₂ := 16) rfl
    exact (congrArg (fun first => BitVec.append (BitVec.append first (value.extractLsb' 8 8))
      (value.extractLsb' 0 8)) high).trans
        ((congrArg (fun first => BitVec.append first (value.extractLsb' 0 8)) middle).trans
          (BitVec.extractLsb'_append_extractLsb' (w := 24) (len := 8) (x := value)))
  have regionsReg : original.regs.get? Register.pma_regions = some regions :=
    readReg_succ.mp readRegions
  refine (readAlignedRamWord _ address offset region regions status
    (value.extractLsb' 0 8) (value.extractLsb' 8 8) (value.extractLsb' 16 8)
    (value.extractLsb' 24 8) ?_ ?_ mprv ?_
    matched readable ?_ aligned ?_ ?_ ?_ ?_).trans ?_
  · exact readReg_of_write_other_reg_state (platform.privilegeAt state) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) statusRead)
      (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide)
        (readReg_succ.mpr regionsReg)) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) platform.htif)
      (by decide)
  · simpa only [writeMem, syncMem, Fin.val_ofNat, Nat.zero_mod, Nat.add_zero] using word 0
  · simpa only [writeMem, syncMem] using word 1
  · simpa only [writeMem, syncMem] using word 2
  · simpa only [writeMem, syncMem] using word 3
  · exact congrArg (fun word => EStateM.Result.ok (Sail.Ok word)
      (write_reg_state (sync base {original with mem := memory} state) Register.nextPC next)) combined

theorem Platform.storeWord
    (platform : Platform S instructions base {original with mem := memory} [] returnAddress
      (fun _ => 0)) (state : S) (next address value : Word)
    (permission : Writable original address) :
    let entered := write_reg_state (sync base {original with mem := memory} state) Register.nextPC next
    vmem_write_addr (.Virtaddr address) 4 value (.Store .Data) false false false entered =
      .ok (.Ok true) (setWord entered address.toNat value) := by
  dsimp only
  obtain ⟨aligned, regions, region, readRegions, matched, writable⟩ := permission
  obtain ⟨status, statusRead, mprv⟩ := platform.status
  have regionsReg : original.regs.get? Register.pma_regions = some regions :=
    readReg_succ.mp readRegions
  refine writeAlignedRamWord _ address value region regions status ?_ ?_ mprv ?_
    matched writable ?_ aligned
  · exact readReg_of_write_other_reg_state (platform.privilegeAt state) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) statusRead)
      (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide)
        (readReg_succ.mpr regionsReg)) (by decide)
  · exact readReg_of_write_other_reg_state
      (Riscfree.RV32.Platform.systemRead state (by decide) (by decide) (by decide) platform.htif)
      (by decide)

end Platform

theorem addLiteralZero (value : Word) : value + (0 : Word) = value :=
  BitVec.add_zero _

-- A snapshot whose PC is the return address minus the code base reads back as
-- the return address.
theorem pcReadReturned {S : Type} [RegisterView S] (base returnAddress : Word) (frame : Machine)
    (state : S) (pc : RegisterView.pc state = returnAddress - base) :
    (sync base frame state).regs.get? Register.PC = some returnAddress := by
  have read := syncReadPC (base := base) (frame := frame) state
  rw [pc, BitVec.add_comm, BitVec.sub_add_cancel] at read
  exact readReg_succ.mp read

end Riscfree.RawVec
