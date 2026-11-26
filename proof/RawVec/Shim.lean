import RawVec

/-!
# The calling shim

`call_raw_vec_u32_insert` (in `examples/raw_vec_call.S`) is what the Rust demo
calls. It saves `ra` on the stack, calls `raw_vec_u32_insert` with a
word-aligned return address, restores `ra`, and returns:

```text
addi sp, sp, -16
sw   ra, 12(sp)
auipc ra, 0x1          ; `call raw_vec_u32_insert`
jalr  ra, -0x2a8(ra)   ; lands 0xd60 bytes after the shim
lw   ra, 12(sp)
addi sp, sp, 16
ret
```

The `auipc` and `jalr` immediates come from the linker, so the table records
the words of the linked demo. `verifyElf` checks those bytes and that the
routine lies exactly `routineOffset` bytes after the shim.

The pinned Sail configuration does not support Zca (`hartSupports Ext_Zca`
is `false`), so Sail faults on a jump to an address with bit 1 set. The Rust
caller is compiled with compressed instructions, so its return address may
have bit 1 set. `callRawVecU32InsertSailAtReturn` therefore covers the first
six instructions for any caller. It stops at the final `ret`, with `ra` and
`sp` restored. `callRawVecU32InsertSailCorrect` adds the `ret` for a caller
whose return address is word-aligned.
-/

namespace Riscfree.RawVec

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32

def shimInstructions : List (Word × instruction) :=
  [ (0xff010113, .ITYPE (0xff0, reg 2, reg 2, .ADDI))
  , (0x00112623, .STORE (12, reg 1, reg 2, 4))
  , (0x00001097, .UTYPE (0x00001, reg 1, .AUIPC))
  , (0xd58080e7, .JALR (0xd58, reg 1, reg 1))
  , (0x00c12083, .LOAD (12, reg 2, reg 1, false, 4))
  , (0x01010113, .ITYPE (16, reg 2, reg 2, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

-- `auipc ra, 0x1` at offset 8 and `jalr ra, -0x2a8(ra)` reach this offset.
def routineOffset : Word := 0xd60

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem shimWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ shimInstructions, ext_decode entry.1 state = .ok entry.2 state := by
  decode_table_normal_form shimInstructions [privilege, landingPad]

structure ShimSnapshot where
  pc : Word := 0
  ra : Word
  sp : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word
  a5 : Word
  a6 : Word
  a7 : Word

instance : RegisterView ShimSnapshot where
  tracked := [1, 2, 10, 11, 12, 13, 14, 15, 16, 17]
  pc state := state.pc
  value state index := match index.val with
    | 1 => state.ra
    | 2 => state.sp
    | 10 => state.a0
    | 11 => state.a1
    | 12 => state.a2
    | 13 => state.a3
    | 14 => state.a4
    | 15 => state.a5
    | 16 => state.a6
    | 17 => state.a7
    | _ => 0
  distinct := by decide
  nonzero := by decide

@[simp] theorem shimViewPc (state : ShimSnapshot) : RegisterView.pc state = state.pc := rfl

-- The word `sw ra, 12(sp)` writes after `addi sp, sp, -16`.
def saveSlot (stackPointer : Word) : Word := stackPointer + 0xfffffffc#32

section Steps

variable {shimBase : Word} {original : Machine} {memory : ByteMemory}

private theorem shimFetchDecode (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (state : ShimSnapshot) (index : Fin shimInstructions.length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync shimBase { original with mem := memory } state) =
        .ok (.F_Base shimInstructions[index.val].1) (sync shimBase { original with mem := memory } state) ∧
      ext_decode shimInstructions[index.val].1 (sync shimBase { original with mem := memory } state) =
        .ok shimInstructions[index.val].2 (sync shimBase { original with mem := memory } state) := by
  have here := machine.withMemory memory
  have synced := here.atSync shimBase state
  obtain ⟨misa, misaRead⟩ := synced.misa
  have member := List.getElem_mem index.isLt
  exact ⟨(image.code here.privilege (here.status.imp fun _ read => read.1) here.htif state index pc).fetch
      (syncReadPC state) misaRead ((by decide : ∀ entry ∈ shimInstructions,
        isRVC (entry.1.extractLsb' 0 16) = false) _ member),
    shimWordsDecode _ synced.privilege synced.landingPad _ member⟩

theorem shimStep0 (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (state : ShimSnapshot) (atPC : state.pc = 0#32) :
    step (sync shimBase { original with mem := memory } state) =
      some (sync shimBase { original with mem := memory }
        { state with pc := 4#32, sp := state.sp + 0xfffffff0#32 }) := by
  obtain ⟨fetched, decoded⟩ := shimFetchDecode machine image state ⟨0, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [shimViewPc, atPC])

theorem shimStep1 (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (state : ShimSnapshot) (atPC : state.pc = 4#32)
    (permission : Writable original (state.sp + 12#32)) :
    step (sync shimBase { original with mem := memory } state) =
      some (sync shimBase { original with mem := storeWord memory (state.sp + 12#32).toNat state.ra }
        { state with pc := 8#32 }) := by
  obtain ⟨fetched, decoded⟩ := shimFetchDecode machine image state ⟨1, by decide⟩ atPC
  obtain ⟨aligned, regions, region, regionsRead, matched, writable⟩ := permission
  have stored : original.regs.get? Register.pma_regions = some regions := readReg_succ.mp regionsRead
  have write := (machine.withMemory memory).storeWord (base := shimBase) state
    (shimBase + state.pc + 4#32) (state.sp + 12#32) state.ra regions region
    (readReg_succ.mpr stored) matched writable aligned
  have stepped := Step.sw (next := { state with pc := 8#32 }) (pointer := state.sp) (value := state.ra)
    fetched decoded (syncRead state (index := 2) (by decide)) (syncRead state (index := 1) (by decide))
    write (by advance [shimViewPc, atPC])
  exact stepped

private theorem offsetAdd (base first second sum : Word) (adds : first + second = sum) :
    base + first + second = base + sum := by
  rw [BitVec.add_assoc, adds]

theorem shimStep2 (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (state : ShimSnapshot) (atPC : state.pc = 8#32) :
    step (sync shimBase { original with mem := memory } state) =
      some (sync shimBase { original with mem := memory }
        { state with pc := 12#32, ra := shimBase + 0x1008#32 }) := by
  obtain ⟨fetched, decoded⟩ := shimFetchDecode machine image state ⟨2, by decide⟩ atPC
  refine Step.auipc fetched decoded (by decide) ?_
  rw [shimViewPc, atPC, offsetAdd shimBase _ _ 0x1008#32 (by decide)]
  advance [shimViewPc, atPC]

-- `jalr ra, -0x2a8(ra)` enters the routine and links the shim's next word.
theorem shimStep3 (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (aligned : shimBase.toNat % 4 = 0)
    (state : ShimSnapshot) (atPC : state.pc = 12#32) (link : state.ra = shimBase + 0x1008#32) :
    step (sync shimBase { original with mem := memory } state) =
      some (sync shimBase { original with mem := memory }
        { state with pc := routineOffset, ra := shimBase + 16#32 }) := by
  obtain ⟨fetched, decoded⟩ := shimFetchDecode machine image state ⟨3, by decide⟩ atPC
  have synced := (machine.withMemory memory).atSync shimBase state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  have target : state.ra + (0xd58#12).signExtend 32 = shimBase + routineOffset := by
    rw [link, offsetAdd shimBase _ _ routineOffset (by decide)]
  have targetAligned : (shimBase + routineOffset).toNat % 4 = 0 := by
    rw [BitVec.toNat_add]
    change (shimBase.toNat + 0xd60) % 2 ^ 32 % 4 = 0
    omega
  obtain ⟨bit0, bit1⟩ := alignedBits _ targetAligned
  refine Step.jalrLink fetched decoded (syncRead state (index := 1) (by decide)) misaRead
    synced.privilege configRead ?_ ?_ (by decide) rfl ?_
  · change BitVec.ofBool (state.ra + (0xd58#12).signExtend 32)[1] = 0#1
    rw [target, bit1]
    rfl
  · change shimBase + routineOffset = 0xfffffffe#32 &&& (state.ra + (0xd58#12).signExtend 32)
    rw [target, maskEven _ bit0]
  · intro other _
    fin_cases other <;> first
      | rfl
      | (simp [shimViewPc, atPC]; exact (offsetAdd shimBase 12#32 4#32 16#32 rfl).symm)

theorem shimStep4 (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (state : ShimSnapshot) (atPC : state.pc = 16#32) (value : Word)
    (permission : Readable original (state.sp + 12#32))
    (contents : WordAt memory (state.sp + 12#32).toNat value) :
    step (sync shimBase { original with mem := memory } state) =
      some (sync shimBase { original with mem := memory } { state with pc := 20#32, ra := value }) := by
  obtain ⟨fetched, decoded⟩ := shimFetchDecode machine image state ⟨4, by decide⟩ atPC
  obtain ⟨aligned, regions, region, regionsRead, matched, readable⟩ := permission
  have stored : original.regs.get? Register.pma_regions = some regions := readReg_succ.mp regionsRead
  have read := (machine.withMemory memory).loadWord (base := shimBase) state
    (shimBase + state.pc + 4#32) (BitVec.signExtend 32 (12#12)) (state.sp + 12#32) value regions region
    (readReg_succ.mpr stored) matched readable aligned contents
  exact Step.lw fetched decoded (syncRead state (index := 2) (by decide)) read (by decide)
    (by advance [shimViewPc, atPC])

theorem shimStep5 (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (state : ShimSnapshot) (atPC : state.pc = 20#32) :
    step (sync shimBase { original with mem := memory } state) =
      some (sync shimBase { original with mem := memory }
        { state with pc := 24#32, sp := state.sp + 16#32 }) := by
  obtain ⟨fetched, decoded⟩ := shimFetchDecode machine image state ⟨5, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (index := 2) (by decide)) (by decide)
    (by advance [shimViewPc, atPC])

-- `ret` reaches a caller whose return address is word-aligned.
theorem shimStep6 (machine : MachineState original)
    (image : CodeImage shimInstructions shimBase { original with mem := memory })
    (state : ShimSnapshot) (atPC : state.pc = 24#32) (returnAddress : Word)
    (link : state.ra = returnAddress) (returnLow : returnAddress &&& 0xfffffffe = returnAddress)
    (returnNext : returnAddress[1] = false) :
    step (sync shimBase { original with mem := memory } state) =
      some (sync shimBase { original with mem := memory }
        { state with pc := returnAddress - shimBase }) := by
  obtain ⟨fetched, decoded⟩ := shimFetchDecode machine image state ⟨6, by decide⟩ atPC
  have synced := (machine.withMemory memory).atSync shimBase state
  obtain ⟨misa, misaRead⟩ := synced.misa
  obtain ⟨config, configRead⟩ := synced.mseccfg
  refine Step.jalr (imm := 0#12) (sourceValue := returnAddress) fetched decoded
    (link ▸ syncRead state (index := 1) (by decide)) misaRead synced.privilege configRead ?_ ?_
    (by advance [shimViewPc])
  · simp [returnNext, BitVec.ofBool]
  · have mask : returnAddress &&& 0xfffffffe#32 = returnAddress := returnLow
    rw [BitVec.add_comm shimBase, BitVec.sub_add_cancel,
      show (0#12).signExtend 32 = 0#32 from rfl, BitVec.add_zero, BitVec.and_comm, mask]

end Steps

/-! ## Premises -/

def Call.outsideShim (shimBase : Word) (address : Nat) : Prop :=
  address + 4 ≤ shimBase.toNat ∨ shimBase.toNat + 28 ≤ address

-- The hart and both code images. The routine follows the shim at `routineOffset`.
structure ShimEnvironment (shimBase : Word) (original : Machine) : Prop where
  machine : MachineState original
  shimCode : CodeImage shimInstructions shimBase original
  routineCode : CodeImage instructions (shimBase + routineOffset) original

-- The stack word where the shim saves `ra`, and its separation from the data
-- and code. The routine's own writes must also miss the shim's code.
structure ShimLayout (shimBase : Word) (original : Machine) (call : Call)
    (stackPointer : Word) : Prop where
  slotReadable : Readable original (saveSlot stackPointer)
  slotWritable : Writable original (saveSlot stackPointer)
  slotApartHeader : call.outsideHeader (saveSlot stackPointer).toNat
  slotApartBuffer : call.valid → ∀ index ≤ call.length.toNat,
    (saveSlot stackPointer).toNat + 4 ≤ call.slot index ∨
      call.slot index + 4 ≤ (saveSlot stackPointer).toNat
  slotApartShim : Call.outsideShim shimBase (saveSlot stackPointer).toNat
  slotApartRoutine : Call.outsideCode (shimBase + routineOffset) (saveSlot stackPointer).toNat
  writesApartShim : call.valid → Call.outsideShim shimBase (call.header.toNat + 4) ∧
    ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
      Call.outsideShim shimBase (call.slot index)

/-! ## Composition -/

section Composition

private theorem mappedTransfer {frame other : Machine} {address : Word}
    {permission : PMA_Region → Prop} (mapped : Mapped frame address permission)
    (regions : other.regs.get? Register.pma_regions = frame.regs.get? Register.pma_regions) :
    Mapped other address permission := by
  obtain ⟨aligned, found, region, regionsRead, matched, allowed⟩ := mapped
  have stored : frame.regs.get? Register.pma_regions = some found := readReg_succ.mp regionsRead
  exact ⟨aligned, found, region, readReg_succ.mpr (regions.trans stored), matched, allowed⟩

private theorem saveSlotAddress (stackPointer : Word) :
    stackPointer + 0xfffffff0#32 + 12#32 = saveSlot stackPointer :=
  offsetAdd stackPointer _ _ _ rfl

private theorem restoredStack (stackPointer : Word) :
    stackPointer + 0xfffffff0#32 + 16#32 = stackPointer := by
  rw [offsetAdd stackPointer _ _ 0#32 rfl, BitVec.add_zero]

-- A memory that differs from `original` only away from the shim keeps its image.
private theorem shimImage {shimBase : Word} {original : Machine} {memory : ByteMemory}
    (image : CodeImage shimInstructions shimBase original)
    (agrees : ∀ byte, shimBase.toNat ≤ byte → byte < shimBase.toNat + 28 →
      memory[byte]? = original.mem[byte]?) :
    CodeImage shimInstructions shimBase { original with mem := memory } :=
  image.withMemory memory agrees

-- A routine snapshot with the shim's argument registers.
private def routineEntry (state : ShimSnapshot) : Snapshot where
  pc := 0
  a0 := state.a0
  a1 := state.a1
  a2 := state.a2
  a3 := state.a3
  a4 := state.a4
  a5 := state.a5
  a6 := state.a6
  a7 := state.a7

-- The shim's snapshot after the routine returns with `endState`.
private def afterRoutine (state : ShimSnapshot) (endState : Snapshot) : ShimSnapshot :=
  { state with
    pc := 16#32
    a0 := endState.a0
    a1 := endState.a1
    a2 := endState.a2
    a3 := endState.a3
    a4 := endState.a4
    a5 := endState.a5
    a6 := endState.a6
    a7 := endState.a7 }

private theorem routineInside : ∀ index ∈ tracked Snapshot, index ∈ tracked ShimSnapshot := by
  decide

-- A byte that misses every slot from `low` to `high` misses the range they tile.
private theorem outsideSlots (call : Call) (low high byte : Nat)
    (avoid : ∀ index, low ≤ index → index ≤ high →
      byte < call.slot index ∨ call.slot index + 4 ≤ byte) :
    byte < call.slot low ∨ call.slot (high + 1) ≤ byte := by
  by_contra inside
  have within : call.slot low ≤ byte ∧ byte < call.slot (high + 1) := by omega
  unfold Call.slot at within
  have hit := avoid ((byte - call.data.toNat) / 4) (by omega) (by omega)
  unfold Call.slot at hit
  omega

private theorem shimRun (shimBase : Word) (original : Machine) (call : Call)
    (initial : ShimSnapshot)
    (entry : original = sync shimBase original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
    (environment : ShimEnvironment shimBase original)
    (layout : ShimLayout shimBase original call initial.sp)
    (header : Header original call)
    (buffer : call.valid → Buffer (shimBase + routineOffset) original call) :
    ∃ (endState : ShimSnapshot) (memory : ByteMemory),
      run (call.count + 6) original = some (sync shimBase { original with mem := memory } endState) ∧
      CodeImage shimInstructions shimBase { original with mem := memory } ∧
      endState.pc = 24#32 ∧ endState.ra = initial.ra ∧ endState.sp = initial.sp ∧
      endState.a0 = call.status ∧
      (¬ call.valid → memory = storeWord original.mem (saveSlot initial.sp).toNat initial.ra) ∧
      (call.valid →
        WordAt memory call.header.toNat call.data ∧
        WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt memory (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt memory (call.slot index) (call.result index)) ∧
        call.unchanged (storeWord original.mem (saveSlot initial.sp).toNat initial.ra) memory) := by
  let slot := (saveSlot initial.sp).toNat
  let stacked := storeWord original.mem slot initial.ra
  let routineBase := shimBase + routineOffset
  have machine := environment.machine
  have aligned := environment.shimCode.aligned
  have apartShim := layout.slotApartShim
  have apartRoutine := layout.slotApartRoutine
  unfold Call.outsideShim at apartShim
  unfold Call.outsideCode at apartRoutine
  -- The four instructions before the call.
  let start : ShimSnapshot := { initial with pc := 0 }
  let lowered : ShimSnapshot := { initial with pc := 4#32, sp := initial.sp + 0xfffffff0#32 }
  let saved : ShimSnapshot := { lowered with pc := 8#32 }
  let linked : ShimSnapshot := { saved with pc := 12#32, ra := shimBase + 0x1008#32 }
  let called : ShimSnapshot := { saved with pc := routineOffset, ra := shimBase + 16#32 }
  have firstImage : CodeImage shimInstructions shimBase { original with mem := original.mem } :=
    shimImage environment.shimCode (fun _ _ _ => rfl)
  have stackedImage : CodeImage shimInstructions shimBase { original with mem := stacked } :=
    shimImage environment.shimCode fun byte low high =>
      storeWordOutside _ _ _ _ (by omega)
  have slotAddress : lowered.sp + 12#32 = saveSlot initial.sp := saveSlotAddress _
  have storing : step (sync shimBase { original with mem := original.mem } lowered) =
      some (sync shimBase { original with mem := stacked } saved) := by
    have stepped := shimStep1 machine firstImage lowered rfl (slotAddress ▸ layout.slotWritable)
    rwa [slotAddress] at stepped
  have entering : run 4 (sync shimBase { original with mem := original.mem } start) =
      some (sync shimBase { original with mem := stacked } called) :=
    runStep (shimStep0 machine firstImage start rfl) (runStep storing
      (runStep (shimStep2 machine stackedImage saved rfl)
        (runStep (shimStep3 machine stackedImage aligned linked rfl rfl) rfl)))
  -- The routine, started from the shim's state.
  let entered := sync shimBase { original with mem := stacked } called
  have regions : entered.regs.get? Register.pma_regions = original.regs.get? Register.pma_regions :=
    syncFrame called _ (by decide) (by decide) (fun _ _ => reg_of_fin_neq_pma_regions)
  have enteredMem : entered.mem = stacked := syncMem called
  have routineEntered : entered = sync routineBase entered { routineEntry called with pc := 0 } :=
    (syncInside shimBase routineBase called called (routineEntry called) routineInside
      (fun index _ => by fin_cases index <;> rfl) (BitVec.add_zero _).symm).symm
  have returnAligned : (shimBase + 16#32).toNat % 4 = 0 := by
    rw [BitVec.toNat_add]
    change (shimBase.toNat + 16) % 2 ^ 32 % 4 = 0
    omega
  obtain ⟨returnBit0, returnBit1⟩ := alignedBits _ returnAligned
  have mode : MachineMode entered (shimBase + 16#32) :=
    { (machine.withMemory stacked).atSync shimBase called with
      returnLow := by rw [BitVec.and_comm]; exact maskEven _ returnBit0
      returnNext := returnBit1
      ra := syncRead called (index := 1) (by decide) }
  have routineLength : 4 * instructions.length = 120 := rfl
  have routineImage : CodeImage instructions routineBase entered :=
    (environment.routineCode.withMemory stacked fun byte low high =>
      storeWordOutside _ _ _ _ (by omega)).atSync shimBase called
  have keepsHeader {offset : Nat} {value : Word} (small : offset ≤ 8)
      (word : WordAt original.mem (call.header.toNat + offset) value) :
      WordAt entered.mem (call.header.toNat + offset) value := by
    rw [enteredMem]
    apply word.storeOther
    have apart := layout.slotApartHeader
    unfold Call.outsideHeader at apart
    omega
  have routineHeader : Header entered call :=
    ⟨header.fits, mappedTransfer header.lengthReadable regions,
      mappedTransfer header.capacityReadable regions, keepsHeader (by decide) header.lengthWord,
      keepsHeader (by decide) header.capacityWord⟩
  have routineBuffer (valid : call.valid) : Buffer routineBase entered call := by
    have given := buffer valid
    refine ⟨given.fits, mappedTransfer given.dataReadable regions,
      by simpa using keepsHeader (offset := 0) (by decide) (by simpa using given.dataWord),
      mappedTransfer given.lengthWritable regions, given.lengthAwayFromCode,
      fun index bound => ?_, fun index low high => mappedTransfer (given.readable index low high) regions,
      fun index low high => mappedTransfer (given.writable index low high) regions,
      given.separated, given.awayFromCode⟩
    rw [enteredMem]
    have apart := layout.slotApartBuffer valid index (by omega)
    exact (given.live index bound).storeOther (by omega)
  obtain ⟨endState, memory, ran, endPc, endStatus, rejected, accepted⟩ :=
    rawVecU32InsertSailRun routineBase (shimBase + 16#32) entered call (routineEntry called)
      routineEntered headerArgument indexArgument valueArgument (Environment.ofMachine mode routineImage)
      routineHeader routineBuffer
  -- Back in the shim.
  let returned := afterRoutine called endState
  have back : run call.count entered =
      some (sync shimBase { original with mem := memory } returned) := by
    rw [ran, syncWithMem]
    refine congrArg some (syncInside shimBase routineBase called returned endState routineInside
      (fun index _ => by fin_cases index <;> rfl) ?_)
    change shimBase + 16#32 = routineBase + endState.pc
    rw [endPc, BitVec.add_comm routineBase, BitVec.sub_add_cancel]
  have finalMemory : (¬ call.valid → memory = stacked) ∧ (call.valid →
      WordAt memory call.header.toNat call.data ∧
      WordAt memory (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
      WordAt memory (call.header.toNat + 8) call.capacity ∧
      (∀ index, index < call.length.toNat + 1 →
        WordAt memory (call.slot index) (call.result index)) ∧
      call.unchanged stacked memory) := by
    rw [← enteredMem]
    exact ⟨rejected, accepted⟩
  -- Every byte away from the routine's writes keeps its stacked value.
  have keeps (byte : Nat)
      (avoid : call.valid → (byte < call.header.toNat + 4 ∨ call.header.toNat + 8 ≤ byte) ∧
        ∀ index, call.index.toNat ≤ index → index ≤ call.length.toNat →
          byte < call.slot index ∨ call.slot index + 4 ≤ byte) :
      memory[byte]? = stacked[byte]? := by
    by_cases valid : call.valid
    · exact (finalMemory.2 valid).2.2.2.2 byte (avoid valid).1
        (outsideSlots call _ _ byte (avoid valid).2)
    · rw [finalMemory.1 valid]
  have finalImage : CodeImage shimInstructions shimBase { original with mem := memory } :=
    shimImage environment.shimCode fun byte low high => by
      rw [keeps byte fun valid => ⟨?_, fun index above below => ?_⟩]
      · exact storeWordOutside _ _ _ _ (by omega)
      · have apart := (layout.writesApartShim valid).1
        unfold Call.outsideShim at apart
        omega
      · have apart := (layout.writesApartShim valid).2 index above below
        unfold Call.outsideShim at apart
        omega
  -- The saved return address survives the routine.
  have savedWord : WordAt memory slot initial.ra := by
    intro byte
    rw [keeps _ fun valid => ⟨?_, fun index _ below => ?_⟩]
    · exact wordAtStore original.mem slot initial.ra byte
    · have apart := layout.slotApartHeader
      unfold Call.outsideHeader at apart
      have := byte.isLt
      omega
    · have apart := layout.slotApartBuffer valid index below
      have := byte.isLt
      omega
  let restored : ShimSnapshot := { returned with pc := 20#32, ra := initial.ra }
  let finished : ShimSnapshot := { restored with pc := 24#32, sp := restored.sp + 16#32 }
  have reloadAddress : returned.sp + 12#32 = saveSlot initial.sp := slotAddress
  have leaving : run 2 (sync shimBase { original with mem := memory } returned) =
      some (sync shimBase { original with mem := memory } finished) :=
    runStep (shimStep4 machine finalImage returned rfl initial.ra
        (by rw [reloadAddress]; exact layout.slotReadable) (by rw [reloadAddress]; exact savedWord))
      (runStep (shimStep5 machine finalImage restored rfl) rfl)
  have begun := (congrArg (run 4) entry).trans entering
  refine ⟨finished, memory, ?_, finalImage, rfl, rfl, restoredStack initial.sp, endStatus, finalMemory⟩
  rw [show call.count + 6 = 4 + (call.count + 2) by omega, runAdd, begun, Option.bind_some, runAdd,
    back, Option.bind_some, leaving]

private theorem syncRa (base : Word) (frame : Machine) (state : ShimSnapshot) :
    (sync base frame state).regs.get? Register.x1 = some state.ra :=
  readReg_succ.mp (syncRead state (index := 1) (by decide))

private theorem syncSp (base : Word) (frame : Machine) (state : ShimSnapshot) :
    (sync base frame state).regs.get? Register.x2 = some state.sp :=
  readReg_succ.mp (syncRead state (index := 2) (by decide))

-- The shim restores `ra` and `sp`. Every other register outside `a0`–`a7`
-- keeps its value, as do the PC-independent system registers.
private theorem finalRegisters (shimBase : Word) (original : Machine) (initial : ShimSnapshot)
    (entry : original = sync shimBase original { initial with pc := 0 })
    (memory : ByteMemory) (state : ShimSnapshot) (ra : state.ra = initial.ra)
    (sp : state.sp = initial.sp) :
    (sync shimBase { original with mem := memory } state).regs.get? Register.x1 = some initial.ra ∧
      ∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        (sync shimBase { original with mem := memory } state).regs.get? register =
          original.regs.get? register := by
  have finalRa := (syncRa shimBase { original with mem := memory } state).trans (congrArg some ra)
  have originalRa : original.regs.get? Register.x1 = some initial.ra :=
    (congrArg (fun machine => machine.regs.get? Register.x1) entry).trans
      (syncRa shimBase original { initial with pc := 0 })
  refine ⟨finalRa, fun register outside => ?_⟩
  by_cases isRa : register = Register.x1
  · rw [isRa, finalRa, originalRa]
  by_cases isSp : register = Register.x2
  · rw [isSp, (syncSp shimBase { original with mem := memory } state).trans (congrArg some sp),
      (congrArg (fun machine => machine.regs.get? Register.x2) entry).trans
        (syncSp shimBase original { initial with pc := 0 })]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨pc, next, a0, a1, a2, a3, a4, a5, a6, a7⟩ := outside
  refine syncFrame state register pc next ?_
  intro index member
  change index ∈ ([1, 2, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 32)) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Ne.symm isRa, Ne.symm isSp, Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4,
    Ne.symm a5, Ne.symm a6, Ne.symm a7]

end Composition

/-! ## Guarantees -/

-- Through `addi sp, sp, 16`, for any caller: the shim stands at its `ret`
-- with the caller's `ra` and `sp` restored and the routine's status in `a0`.
-- Memory differs from the routine's result only in the saved `ra` slot.
theorem callRawVecU32InsertSailAtReturn (shimBase : Word) (original : Machine) (call : Call)
    (initial : ShimSnapshot)
    (entry : original = sync shimBase original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
    (environment : ShimEnvironment shimBase original)
    (layout : ShimLayout shimBase original call initial.sp)
    (header : Header original call)
    (buffer : call.valid → Buffer (shimBase + routineOffset) original call) :
    ∃ final, run (call.count + 6) original = some final ∧
      final.regs.get? Register.PC = some (shimBase + 24#32) ∧
      final.regs.get? Register.x1 = some initial.ra ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = storeWord original.mem (saveSlot initial.sp).toNat initial.ra) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged (storeWord original.mem (saveSlot initial.sp).toNat initial.ra) final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register) := by
  obtain ⟨endState, memory, ran, _, atRet, ra, sp, status, rejected, accepted⟩ :=
    shimRun shimBase original call initial entry headerArgument indexArgument valueArgument
      environment layout header buffer
  obtain ⟨finalRa, preserved⟩ := finalRegisters shimBase original initial entry memory endState ra sp
  refine ⟨_, ran, ?_, finalRa, ?_, ?_, ?_, preserved⟩
  · rw [← atRet]
    exact readReg_succ.mp (syncReadPC endState)
  · rw [← status]
    exact readReg_succ.mp (syncRead endState (index := 10) (by decide))
  · simpa only [syncMem] using rejected
  · simpa only [syncMem] using accepted

-- All seven instructions, for a caller whose return address is word-aligned.
-- The pinned Sail configuration faults on any other return target.
theorem callRawVecU32InsertSailCorrect (shimBase : Word) (original : Machine) (call : Call)
    (initial : ShimSnapshot)
    (entry : original = sync shimBase original { initial with pc := 0 })
    (headerArgument : initial.a0 = call.header)
    (indexArgument : initial.a1 = call.index)
    (valueArgument : initial.a2 = call.value)
    (returnLow : initial.ra &&& 0xfffffffe = initial.ra)
    (returnNext : initial.ra[1] = false)
    (environment : ShimEnvironment shimBase original)
    (layout : ShimLayout shimBase original call initial.sp)
    (header : Header original call)
    (buffer : call.valid → Buffer (shimBase + routineOffset) original call) :
    ∃ final, run (call.count + 7) original = some final ∧
      final.regs.get? Register.PC = some initial.ra ∧
      final.regs.get? Register.x10 = some call.status ∧
      (¬ call.valid → final.mem = storeWord original.mem (saveSlot initial.sp).toNat initial.ra) ∧
      (call.valid →
        WordAt final.mem call.header.toNat call.data ∧
        WordAt final.mem (call.header.toNat + 4) (BitVec.ofNat 32 (call.length.toNat + 1)) ∧
        WordAt final.mem (call.header.toNat + 8) call.capacity ∧
        (∀ index, index < call.length.toNat + 1 →
          WordAt final.mem (call.slot index) (call.result index)) ∧
        call.unchanged (storeWord original.mem (saveSlot initial.sp).toNat initial.ra) final.mem) ∧
      (∀ register ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = original.regs.get? register) := by
  obtain ⟨endState, memory, ran, image, atRet, ra, sp, status, rejected, accepted⟩ :=
    shimRun shimBase original call initial entry headerArgument indexArgument valueArgument
      environment layout header buffer
  let returned : ShimSnapshot := { endState with pc := initial.ra - shimBase }
  have returning := shimStep6 environment.machine image endState atRet initial.ra ra returnLow
    returnNext
  obtain ⟨_, preserved⟩ := finalRegisters shimBase original initial entry memory returned ra sp
  refine ⟨_, ?_, ?_, ?_, ?_, ?_, preserved⟩
  · rw [show call.count + 7 = (call.count + 6) + 1 from rfl, runAdd, ran, Option.bind_some]
    exact runStep returning rfl
  · have read := readReg_succ.mp (syncReadPC (base := shimBase) (frame := { original with mem := memory })
      returned)
    rwa [show RegisterView.pc returned = initial.ra - shimBase from rfl, BitVec.add_comm,
      BitVec.sub_add_cancel] at read
  · rw [← status]
    exact readReg_succ.mp (syncRead returned (index := 10) (by decide))
  · simpa only [syncMem] using rejected
  · simpa only [syncMem] using accepted

end Riscfree.RawVec

namespace Riscfree.RawVec.Shim

-- Check the shim's and the routine's linked bytes, and that the shim's call
-- reaches the routine.
def verifyElf (path : String) : IO Unit := do
  let routine ← Riscfree.verifyElfSymbol path "raw_vec_u32_insert" (instructions.map Prod.fst)
  let shim ← Riscfree.verifyElfSymbol path "call_raw_vec_u32_insert" (shimInstructions.map Prod.fst)
  unless routine == shim + routineOffset.toNat do
    throw (IO.userError s!"raw_vec_u32_insert is {routine - shim} bytes after the shim, but the \
      proof's call reaches {routineOffset.toNat}")
  IO.println s!"call_raw_vec_u32_insert: calls raw_vec_u32_insert {routineOffset.toNat} bytes ahead"

end Riscfree.RawVec.Shim
