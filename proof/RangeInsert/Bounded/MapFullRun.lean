import RangeInsert.Bounded.EntryFresh

/-! The FULL result from sorted-map insertion skips the deletion helper
at either return site and goes straight to the restored outer return. -/

namespace Riscfree.RangeInsert.Bounded.EntryFresh

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable)
open Empty (Snapshot frameBase pushed restore)
open EntryEmpty (Frame)
open Nonempty (Call insertView insertReturned)

private theorem insertInside : ∀ index ∈ tracked SortedMap.Insert.Snapshot, index ∈ tracked Snapshot := by
  decide

theorem Calling.insertEntry {base : Word} {frame : Machine} {initial caller : Snapshot}
    {call : Call} (arrived : Calling base initial call caller) :
    sync base frame caller =
      sync (mapInsertBase base) (sync base frame caller) { insertView caller with pc := 0 } := by
  have target : base + caller.pc = mapInsertBase base + 0#32 := by
    rw [arrived.pc, BitVec.add_zero]
    rfl
  exact (syncInside (frame := frame) base (mapInsertBase base) caller caller (insertView caller)
    insertInside (fun index _ => by fin_cases index <;> rfl) target).symm

theorem insertReturnedSync (base pc : Word) (frame : Machine) (caller : Snapshot)
    (state : SortedMap.Insert.Snapshot) (target : base + pc = mapInsertBase base + state.pc) :
    sync (mapInsertBase base) (sync base frame caller) state = sync base frame (insertReturned pc caller state) :=
  syncInside base (mapInsertBase base) caller (insertReturned pc caller state)
    state insertInside (fun index _ => by fin_cases index <;> rfl) target

/-- Premises at the two call sites. The callee footprint is the 32 bytes
below the already reserved outer frame. -/
structure FullCall (base ret : Word) (original : Machine) (initial caller : Snapshot)
    (call : Call) (capacity : Word) : Prop where
  outer : Frame base ret original initial
  calling : Calling base initial call caller
  fresh : call.path = .fresh
  full : call.length = capacity
  sorted : SortedMap.Sorted (SortedMap.entriesOf call.old call.length.toNat)
  ordered : ∀ index < call.length.toNat, (call.old index).key.toNat ≤ (call.old index).value.toNat
  callee : let entered := sync base { original with mem := pushed original.mem initial } caller
    SortedMap.Insert.Environment (mapInsertBase base) (base + insertReturn call) entered
  header : let entered := sync base { original with mem := pushed original.mem initial } caller
    RawVec.Insert.Header entered (call.freshInsert capacity).vector
  stack : let entered := sync base { original with mem := pushed original.mem initial } caller
    SortedMap.Insert.Stack (mapInsertBase base) entered (call.freshInsert capacity) caller.sp
  keys : let entered := sync base { original with mem := pushed original.mem initial } caller
    0 < call.length.toNat → SortedMap.Search.Keys entered (call.freshInsert capacity).search
  codeOutside : ∀ byte, base.toNat ≤ byte → byte < base.toNat + 4 * InsertTable.instructions.length →
    byte < caller.sp.toNat - 32 ∨ caller.sp.toNat ≤ byte

def afterCallee (original : Machine) (initial caller : Snapshot) : ByteMemory :=
  SortedMap.Insert.pushed (pushed original.mem initial) caller.sp (insertView caller)

set_option maxHeartbeats 1000000 in
theorem FullCall.run {base ret : Word} {original : Machine} {initial caller : Snapshot}
    {call : Call} {capacity : Word} (premises : FullCall base ret original initial caller call capacity) :
    ∃ returned : Snapshot,
      Riscfree.RV32.run ((call.freshInsert capacity).count + 13)
          (sync base { original with mem := pushed original.mem initial } caller) =
        some (sync base { original with mem := afterCallee original initial caller }
          (restore initial { returned with a0 := 1, a1 := 1 } (ret - base))) ∧
      returned.s6 = initial.s6 ∧ returned.s7 = initial.s7 ∧ returned.s8 = initial.s8 ∧
      returned.s9 = initial.s9 ∧ returned.s10 = initial.s10 ∧
      ∀ byte, (byte < initial.sp.toNat - 80 ∨ initial.sp.toNat ≤ byte) →
        (afterCallee original initial caller)[byte]? = original.mem[byte]? := by
  let before := { original with mem := pushed original.mem initial }
  let entered := sync base before caller
  let memory := afterCallee original initial caller
  let background := { original with mem := memory }
  let retSite := base + insertReturn call
  obtain ⟨state, ran, pc, status, _, sp, _, _, _, _⟩ :=
    Call.freshFullRun premises.fresh premises.full premises.sorted premises.ordered
      premises.calling.insertEntry premises.calling.header premises.calling.start premises.calling.stop
      premises.callee premises.header premises.stack premises.keys
  let returned := insertReturned (insertReturn call) caller state
  have rebase : base + returned.pc = mapInsertBase base + state.pc := by
    change retSite = mapInsertBase base + state.pc
    rw [pc, BitVec.add_comm (mapInsertBase base), BitVec.sub_add_cancel]
  have switched := insertReturnedSync base (insertReturn call) background caller state rebase
  have entryMemory : entered.mem = pushed original.mem initial :=
    syncMem (base := base) (frame := before) caller
  have called : Riscfree.RV32.run (call.freshInsert capacity).count entered =
      some (sync base background returned) := by
    rw [ran, entryMemory]
    change some (sync (mapInsertBase base) { sync base before caller with mem := memory } state) = _
    rw [syncWithMem]
    exact congrArg some switched
  have keptCallee (byte : Nat) (outside : byte < caller.sp.toNat - 32 ∨ caller.sp.toNat ≤ byte) :
      memory[byte]? = (pushed original.mem initial)[byte]? :=
    SortedMap.Insert.pushedOutside _ (insertView caller) premises.stack.fits byte outside
  have image : CodeImage InsertTable.instructions base background :=
    premises.outer.pushedImage.withMemory memory fun byte low high =>
      keptCallee byte (premises.codeOutside byte low high)
  have machine := premises.outer.mode.toMachineState.withMemory memory
  have readable : ∀ offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word),
      Readable background (frameBase initial.sp + offset) :=
    fun offset member => Nonempty.mappedTransfer (premises.outer.readable offset member) rfl
  have saved (offset value : Word) (member : offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word))
      (word : WordAt (pushed original.mem initial) (frameBase initial.sp + offset).toNat value) :
      WordAt background.mem (frameBase initial.sp + offset).toNat value := by
    have address := Empty.frameAddress premises.outer.frameFits offset (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    apply word.congr
    intro byte lower _
    apply keptCallee byte
    right
    rw [premises.calling.sp]
    have stackAddress := Empty.frameAddress premises.outer.frameFits 0#32 (by decide)
    simp only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] at stackAddress
    omega
  have restoredSp : returned.sp = frameBase initial.sp := sp.trans premises.calling.sp
  have exited := returnFull (call := call) premises.outer machine image readable saved rfl restoredSp status
  obtain ⟨s6, s7, s8, s9, s10⟩ := premises.calling.untouched
  refine ⟨returned, ?_, s6, s7, s8, s9, s10, ?_⟩
  · change Riscfree.RV32.run ((call.freshInsert capacity).count + 13) entered = _
    rw [runAdd, called, Option.bind_some]
    exact exited
  · intro byte outside

    have stackAddress := Empty.frameAddress premises.outer.frameFits 0#32 (by decide)
    simp only [BitVec.add_zero, show (0#32).toNat = 0 from rfl, Nat.add_zero] at stackAddress
    have callerAddress := congrArg BitVec.toNat premises.calling.sp
    refine (keptCallee byte ?_).trans
      (Empty.pushedOutside original.mem initial premises.outer.frameFits byte ?_)
    · rw [callerAddress, stackAddress]
      omega
    · unfold Empty.OutsideFrame
      omega

end Riscfree.RangeInsert.Bounded.EntryFresh
