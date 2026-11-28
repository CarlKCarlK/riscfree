import RangeInsert.Bounded.ExtensionLayout

/-! Both outcomes of the bounded extension path. After the helper returns
to `+0x190`, the caller tests its status. OK jumps to the common epilogue;
FULL takes the common OOM return at `+0x1a0`. Either way the caller runs
eleven more instructions. -/

namespace Riscfree.RangeInsert.Bounded.EntryExtension

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable Writable)
open Empty (Snapshot)
open EntryEmpty (Frame)
open Entry
open OuterLayout
open OuterView (helperView helperReturned helperReturnedSync)
open OuterHelper (HelperInput helperAsOuter)
open Nonempty (Call Arguments mapHeader cacheWords stackAllocation stackDisjointOuter mappedTransfer
  WritableByte)

set_option maxHeartbeats 2500000

/-- Outside the helper's static footprint, the helper's frame and its scan
footprint are both untouched. -/
theorem outsideOfHelperFootprint {sp : Word} {call : DeleteExtra.Call} {scratch : DeleteExtra.Scratch}
    {accepted byte : Nat} (outside : ¬ DeleteExtra.HelperFootprint sp call scratch accepted byte) :
    HelperFrame.OutsideFrame sp byte ∧ ¬ DeleteExtra.Footprint call scratch accepted byte := by
  simp only [DeleteExtra.HelperFootprint, not_or, not_not] at outside
  exact ⟨outside.1, outside.2.1⟩

/-- The helper's final registers, seen from the caller at the return site. -/
private theorem returnTarget (base : Word) (first last : Helper.Snapshot) :
    base + 0x190#32 = helperBase base +
      (HelperFrame.restore first last (base + 0x190#32 - helperBase base)).pc := by
  change base + 0x190#32 = helperBase base + (base + 0x190#32 - helperBase base)
  rw [BitVec.add_comm (helperBase base), BitVec.sub_add_cancel]

/-- From the helper's return site, an OK status reaches the common
epilogue and a FULL status the common OOM return. -/
theorem resume {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (frame : Frame base returnAddress original initial) (memory : ByteMemory)
    (codeKept : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
      memory[byte]? = original.mem[byte]?)
    (savedKept : ∀ byte, initial.sp.toNat - 28 ≤ byte → byte < initial.sp.toNat →
      memory[byte]? = (Empty.pushed original.mem initial)[byte]?)
    (state : Snapshot) (pc : state.pc = 0x190#32) (sp : state.sp = Empty.frameBase initial.sp) :
    run 11 (sync base { original with mem := memory } state) =
      some (sync base { original with mem := memory }
        (Empty.restore initial
          (if state.a0 = 0#32 then { state with pc := 0x1a4 } else { state with pc := 0x1a4, a0 := 1 })
          (returnAddress - base))) := by
  have machine := frame.mode.toMachineState.withMemory memory
  have image : CodeImage InsertTable.instructions base { original with mem := memory } :=
    frame.code.withMemory memory codeKept
  have readable (offset : Word) (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word)) :
      Readable { original with mem := memory } (Empty.frameBase initial.sp + offset) :=
    mappedTransfer (frame.readable offset member) rfl
  have saved (offset value : Word) (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word))
      (contents : WordAt (Empty.pushed original.mem initial) (Empty.frameBase initial.sp + offset).toNat value) :
      WordAt memory (Empty.frameBase initial.sp + offset).toNat value := by
    have bound : 20 ≤ offset.toNat ∧ offset.toNat ≤ 44 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine contents.congr fun byte first last => ?_
    rw [Empty.frameAddress frame.frameFits offset bound.2] at first last
    have fits := frame.frameFits
    exact savedKept byte (by omega) (by omega)
  have test := step190 machine image state pc
  by_cases ok : state.a0 = 0#32
  · rw [if_pos ok] at test ⊢
    refine runStep test ?_
    refine runStep (step194 machine image _ rfl) ?_
    exact frame.epilogueFrom machine image readable saved _ rfl sp
  · rw [if_neg ok] at test ⊢
    refine runStep test ?_
    refine runStep (step1a0 machine image _ rfl) ?_
    exact frame.epilogueFrom machine image readable saved _ rfl sp

/-- The caller's view of the helper's call: its entry machine, the projected
helper registers, and the input layout. -/
private theorem ExtensionPrefix.called {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)) :
    ∃ caller : Snapshot,
      Riscfree.RV32.run (toHelperCount call) original =
        some (sync base { original with mem := extensionMemory original initial call low high } caller) ∧
      ExtensionCalling base initial call caller ∧
      HelperInput base (sync base { original with mem := extensionMemory original initial call low high } caller)
        initial (call.extensionHelper initial low high) capacity := by
  obtain ⟨caller, toCall, regs⟩ := premises.toHelper
  exact ⟨caller, (congrArg (Riscfree.RV32.run (toHelperCount call)) premises.frame.entry).trans toCall,
    regs, premises.helperInput layout sorted⟩

/-- Bytes outside every region the path may write keep their values. -/
private theorem ExtensionPrefix.keptOutside {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    {caller : Snapshot}
    (input : HelperInput base (sync base { original with mem := extensionMemory original initial call low high } caller)
      initial (call.extensionHelper initial low high) capacity)
    {accepted : Nat} (room : accepted ≤ initial.a5.toNat) (byte : Nat)
    (outside : ¬ WritableByte initial call capacity byte) :
    ¬ DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) (call.extensionHelper initial low high)
      ⟨initial.a4, initial.a5⟩ accepted byte ∧
    (extensionMemory original initial call low high)[byte]? = original.mem[byte]? := by
  simp only [WritableByte, not_or] at outside
  obtain ⟨stack, cache, scratchApart, header, map⟩ := outside
  refine ⟨fun wrote => ?_, premises.keptByte byte cache
    (fun endpoint => map (premises.endContained layout endpoint))
    (stackDisjointOuter layout.stack.fits stack)⟩
  rcases input.footprintRegions room wrote with helperStack | helperCache | helperScratch | helperHeader | helperMap
  · apply stack
    have fits := layout.stack.fits
    change initial.sp.toNat - 112 ≤ byte ∧ byte < initial.sp.toNat - 112 + 112
    omega
  · exact cache helperCache
  · exact scratchApart helperScratch
  · exact header helperHeader
  · exact map helperMap

set_option maxHeartbeats 4000000 in
/-- With enough scratch for every accepted successor, the extension path
returns OK with the helper's result in memory. -/
theorem ExtensionPrefix.runSuccess {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (room : (call.extensionHelper initial low high).acceptCount ≤ initial.a5.toNat) :
    let helperCall := call.extensionHelper initial low high
    ∃ final, Riscfree.RV32.run (toHelperCount call +
        HelperRun.successCount helperCall capacity helperCall.acceptCount + 11) original = some final ∧
      final.regs.get? Register.PC = some ret ∧
      final.regs.get? Register.x10 = some (0#32) ∧
      DeleteExtra.ResultMemory (Empty.frameBase initial.sp) helperCall ⟨initial.a4, initial.a5⟩
        helperCall.acceptCount (extensionMemory original initial call low high) final.mem ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]? := by
  intro helperCall
  let memory := extensionMemory original initial call low high
  let background : Machine := { original with mem := memory }
  obtain ⟨caller, toCall, regs, input⟩ := premises.called layout sorted
  let entered := sync base background caller
  have enteredMemory : entered.mem = memory := syncMem (base := base) (frame := background) caller
  have mode : MachineState background := premises.frame.mode.toMachineState.withMemory memory
  have arguments : HelperEntry.Arguments (helperView caller 0) helperCall :=
    regs.helperArguments rfl rfl rfl rfl rfl
  have helperPremises := input.premises mode (by decide : (0x190#32).toNat % 4 = 0)
    regs.pc regs.sp regs.ra arguments room (extensionKeysIncreasing sorted)
  obtain ⟨tail, after, ran, result⟩ := helperPremises.run
  let helperFinal := HelperFrame.restore (helperView caller 0) { tail with a0 := 0 }
    (base + 0x190#32 - helperBase base)
  let returned := helperReturned 0x190#32 caller helperFinal
  have switched : sync (helperBase base) { entered with mem := after } helperFinal =
      sync base { background with mem := after } returned := by
    rw [syncWithMem]
    exact helperReturnedSync base (helperBase base) 0x190#32 { background with mem := after } caller
      helperFinal (returnTarget base _ _)
  have effects : DeleteExtra.ResultMemory (Empty.frameBase initial.sp) helperCall ⟨initial.a4, initial.a5⟩
      helperCall.acceptCount memory after := by
    have sp : (helperView caller 0).sp = Empty.frameBase initial.sp := regs.sp
    rw [← sp, ← enteredMemory]
    exact result
  have codeKept (byte : Nat) (first : base.toNat ≤ byte)
      (last : byte < base.toNat + 4 * InsertTable.instructions.length) : after[byte]? = original.mem[byte]? :=
    (effects.others byte (input.codeApartAll room byte first last)).trans
      (premises.writesAwayFromCode byte first last)
  have savedKept (byte : Nat) (first : initial.sp.toNat - 28 ≤ byte) (last : byte < initial.sp.toNat) :
      after[byte]? = (Empty.pushed original.mem initial)[byte]? :=
    (effects.others byte (input.savedApartAll room byte first last)).trans
      (premises.writesAwayFromSaved byte first last)
  have resumed := resume premises.frame after codeKept savedKept returned rfl regs.sp
  have ok : returned.a0 = 0#32 := rfl
  rw [if_pos ok] at resumed
  let last := Empty.restore initial { returned with pc := 0x1a4 } (ret - base)
  let final := sync base { background with mem := after } last
  have finalMemory : final.mem = after := syncMem (base := base) (frame := { background with mem := after }) last
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runAdd, runAdd, toCall, Option.bind_some]
    change (Riscfree.RV32.run (HelperRun.successCount helperCall capacity helperCall.acceptCount) entered).bind
      (Riscfree.RV32.run 11) = _
    rw [ran, Option.bind_some, switched]
    exact resumed
  · exact Empty.returnPc (base := base) { background with mem := after } last rfl
  · exact readReg_succ.mp (syncRead (base := base) (frame := { background with mem := after }) last
      (index := 10) (by decide))
  · rw [finalMemory]
    exact effects
  · exact Empty.restoreRegistersCalls premises.frame.entry after
      { returned with pc := 0x1a4 } (ret - base) regs.saved
  · intro byte outside
    obtain ⟨noHelper, prefixKept⟩ := premises.keptOutside layout input room byte outside
    rw [finalMemory]
    exact (effects.others byte noHelper).trans prefixKept

/-- After a FULL return, the map header is unchanged and every byte the
path may not write keeps its value. -/
structure FullResult (initial : Snapshot) (call : Call) (capacity : Word) (original final : Machine) :
    Prop where
  header : ∀ byte, (mapHeader call).Contains byte → final.mem[byte]? = original.mem[byte]?
  kept : ∀ byte, ¬ WritableByte initial call capacity byte → final.mem[byte]? = original.mem[byte]?

set_option maxHeartbeats 4000000 in
/-- With too little scratch, the helper returns FULL at the first eligible
key that does not fit, and the caller returns FULL. The map header is
untouched, so the caller can dispose of the allocation. -/
theorem ExtensionPrefix.runFull {base ret : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (premises : ExtensionPrefix base ret original initial call low high)
    (layout : InitialLayout base original initial call capacity low high)
    (sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat))
    (short : initial.a5.toNat < (call.extensionHelper initial low high).acceptCount) :
    let helperCall := call.extensionHelper initial low high
    ∃ final, Riscfree.RV32.run (toHelperCount call +
        HelperRun.fullCount helperCall initial.a5.toNat + 11) original = some final ∧
      final.regs.get? Register.PC = some ret ∧
      final.regs.get? Register.x10 = some (1#32) ∧
      (∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? key = original.regs.get? key) ∧
      FullResult initial call capacity original final := by
  intro helperCall
  let memory := extensionMemory original initial call low high
  let background : Machine := { original with mem := memory }
  let scratch : DeleteExtra.Scratch := ⟨initial.a4, initial.a5⟩
  obtain ⟨caller, toCall, regs, input⟩ := premises.called layout sorted
  let entered := sync base background caller
  have enteredMemory : entered.mem = memory := syncMem (base := base) (frame := background) caller
  have mode : MachineState background := premises.frame.mode.toMachineState.withMemory memory
  have arguments : HelperEntry.Arguments (helperView caller 0) helperCall :=
    regs.helperArguments rfl rfl rfl rfl rfl
  have scanPremises := input.scanPremises mode (by decide : (0x190#32).toNat % 4 = 0)
    regs.pc regs.sp regs.ra arguments (accepted := initial.a5.toNat) (Nat.le_refl _) (Nat.le_of_lt short)
  obtain ⟨tail, after, ran, unchanged⟩ := scanPremises.runFull short
  let helperFinal := HelperFrame.restore (helperView caller 0)
    { tail with a0 := 1, a1 := 1, a2 := tail.s9 } (base + 0x190#32 - helperBase base)
  let returned := helperReturned 0x190#32 caller helperFinal
  have switched : sync (helperBase base) { entered with mem := after } helperFinal =
      sync base { background with mem := after } returned := by
    rw [syncWithMem]
    exact helperReturnedSync base (helperBase base) 0x190#32 { background with mem := after } caller
      helperFinal (returnTarget base _ _)
  have sp : (helperView caller 0).sp = Empty.frameBase initial.sp := regs.sp
  -- Outside the helper's static footprint at the scratch capacity, the
  -- failed scan left memory as it was at the call.
  have keptByHelper (byte : Nat)
      (outside : ¬ DeleteExtra.HelperFootprint (Empty.frameBase initial.sp) helperCall scratch
        initial.a5.toNat byte) : after[byte]? = memory[byte]? := by
    obtain ⟨frameOutside, scanOutside⟩ := outsideOfHelperFootprint outside
    rw [← enteredMemory]
    exact unchanged byte (sp ▸ frameOutside) scanOutside
  have codeKept (byte : Nat) (first : base.toNat ≤ byte)
      (last : byte < base.toNat + 4 * InsertTable.instructions.length) : after[byte]? = original.mem[byte]? :=
    (keptByHelper byte (input.codeApartAll (Nat.le_refl _) byte first last)).trans
      (premises.writesAwayFromCode byte first last)
  have savedKept (byte : Nat) (first : initial.sp.toNat - 28 ≤ byte) (last : byte < initial.sp.toNat) :
      after[byte]? = (Empty.pushed original.mem initial)[byte]? :=
    (keptByHelper byte (input.savedApartAll (Nat.le_refl _) byte first last)).trans
      (premises.writesAwayFromSaved byte first last)
  have resumed := resume premises.frame after codeKept savedKept returned rfl regs.sp
  have full : ¬ returned.a0 = 0#32 := by
    change ¬ (1 : Word) = 0#32
    decide
  rw [if_neg full] at resumed
  let last := Empty.restore initial { returned with pc := 0x1a4, a0 := 1 } (ret - base)
  let final := sync base { background with mem := after } last
  have finalMemory : final.mem = after := syncMem (base := base) (frame := { background with mem := after }) last
  have fits := layout.stack.fits
  refine ⟨final, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · rw [runAdd, runAdd, toCall, Option.bind_some]
    change (Riscfree.RV32.run (HelperRun.fullCount helperCall initial.a5.toNat) entered).bind
      (Riscfree.RV32.run 11) = _
    rw [ran, Option.bind_some, switched]
    exact resumed
  · exact Empty.returnPc (base := base) { background with mem := after } last rfl
  · exact readReg_succ.mp (syncRead (base := base) (frame := { background with mem := after }) last
      (index := 10) (by decide))
  · exact Empty.restoreRegistersCalls premises.frame.entry after
      { returned with pc := 0x1a4, a0 := 1 } (ret - base) regs.saved
  · intro byte inHeader
    rw [finalMemory]
    have apart := layout.apart
    have frameOutside : HelperFrame.OutsideFrame (Empty.frameBase initial.sp) byte :=
      OuterHelper.stackDisjointHelper fits (apart.headerStack byte inHeader)
    have scanOutside : ¬ DeleteExtra.Footprint helperCall scratch initial.a5.toNat byte := by
      intro touched
      rcases touched with cache | keys | slots
      · exact apart.headerCache byte inHeader cache
      · obtain ⟨low, high⟩ := keys
        exact apart.headerStack byte inHeader
          (input.keysInStack (call := helperCall) (Nat.le_trans (Nat.le_add_right _ 4) low) (by omega))
      · apply apart.headerScratch byte inHeader
        change initial.a4.toNat + 4 * 0 ≤ byte ∧ byte < initial.a4.toNat + 4 * initial.a5.toNat at slots
        change initial.a4.toNat ≤ byte ∧ byte < initial.a4.toNat + 4 * initial.a5.toNat
        omega
    rw [← enteredMemory] at *
    refine (unchanged byte (sp ▸ frameOutside) scanOutside).trans ?_
    rw [enteredMemory]
    exact premises.keptByte byte (apart.headerCache byte inHeader)
      (fun endpoint => apart.headerMap byte inHeader (premises.endContained layout endpoint))
      (stackDisjointOuter fits (apart.headerStack byte inHeader))
  · intro byte outside
    obtain ⟨noHelper, prefixKept⟩ := premises.keptOutside layout input (Nat.le_refl _) byte outside
    rw [finalMemory]
    exact (keptByHelper byte noHelper).trans prefixKept

end Riscfree.RangeInsert.Bounded.EntryExtension
