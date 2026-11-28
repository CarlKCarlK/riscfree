import RangeInsert.Bounded.EntryPredecessor
import RangeInsert.CapacityStatus
import RangeInsert.Arithmetic

namespace Riscfree.RangeInsert.Bounded.EntryFresh

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Readable)
open Empty (Snapshot frameBase pushed restore)
open EntryEmpty (Frame)
open EntryPredecessor (Map toPredecessor afterSearch calling inspectPredecessor)
open Entry
open Nonempty (Arguments Call insertView insertReturned)
set_option maxHeartbeats 1500000

def mapInsertOffset : Word := 0xfffffc78
def mapInsertBase (base : Word) : Word := base + mapInsertOffset

def insertReturn (call : Call) : Word := if call.rank = 0 then 0xd0#32 else 0xa0#32

def toInsertCount (call : Call) : Nat :=
  (if call.rank = 0 then 27 else 38) + call.search.count .upper

structure Calling (base : Word) (initial : Snapshot) (call : Call) (state : Snapshot) : Prop where
  pc : state.pc = mapInsertOffset
  link : state.ra = base + insertReturn call
  sp : state.sp = frameBase initial.sp
  header : state.a0 = call.header
  start : state.a1 = call.start
  stop : state.a2 = call.stop
  cached : state.s0 = initial.a1
  savedStart : state.s2 = call.start
  savedStop : state.s1 = call.stop
  scratchCapacity : state.s3 = initial.a5
  scratchData : state.s4 = initial.a4
  untouched : state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧ state.s8 = initial.s8 ∧
    state.s9 = initial.s9 ∧ state.s10 = initial.s10

private theorem gapFlag {start stop : Word} (gap : stop.toNat + 1 < start.toNat) :
    Step.lessWord stop 0xffffffff#32 &&& Step.lessWord (stop + 1#32) start ≠ 0#32 := by
  have ⟨increment, strict⟩ := (Riscfree.RangeInsert.predecessorGap start stop).mpr gap
  have maxWord : stop.toNat < (0xffffffff#32).toNat := increment
  unfold Step.lessWord
  have strictWord : (stop + 1#32).toNat < start.toNat := strict
  rw [if_pos maxWord, if_pos strictWord]
  decide

theorem toInsert {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (frame : Frame base returnAddress original initial)
    (arguments : Arguments initial call) (map : Map base original initial.sp call)
    (nonempty : call.start.toNat ≤ call.stop.toNat) (fresh : call.path = .fresh) :
    ∃ state : Snapshot,
      run (toInsertCount call) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := pushed original.mem initial } state) ∧
      Calling base initial call state := by
  let machine := frame.mode.toMachineState
  let image := frame.pushedImage
  rcases Call.freshHasGap fresh with rankZero | ⟨found, gap⟩
  · obtain ⟨searched, ran, rank⟩ := toPredecessor frame arguments map nonempty
    let before := afterSearch (calling base initial) searched
    let after : Snapshot :=
      { before with
        pc := mapInsertOffset, ra := base + 0xd0#32, a0 := initial.a0, a1 := initial.a2, a2 := initial.a3 }
    have zero : before.a0 = 0#32 := by
      change searched.a0 = 0#32
      rw [rank, rankZero]
    refine ⟨after, ?_, rfl, ?_, rfl, arguments.header, arguments.start, arguments.stop,
      rfl, arguments.start, arguments.stop, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · rw [show toInsertCount call = (19 + call.search.count .upper) + 8 by
        simp only [toInsertCount, if_pos rankZero]; omega, runAdd, ran, Option.bind_some]
      refine runStep (step54 machine image before rfl) ?_
      rw [if_pos zero]
      let rankZeroArm : Snapshot := { before with pc := 0xb4 }
      let cleared : Snapshot := { rankZeroArm with pc := 0xb8, a1 := 0 }
      let skipBranch : Snapshot := { cleared with pc := 0xbc, a0 := initial.a0 }
      let ready : Snapshot := { skipBranch with pc := 0xc0 }
      have setup : step (sync base { original with mem := pushed original.mem initial } skipBranch) =
          some (sync base { original with mem := pushed original.mem initial } ready) := by
        have single := stepbc machine image skipBranch rfl
        have clearedWord : skipBranch.a1 = 0#32 := rfl
        rw [if_pos clearedWord] at single
        exact single
      refine runStep (stepb4 machine image rankZeroArm rfl) ?_
      refine runStep (stepb8 machine image cleared rfl) ?_
      refine runStep setup ?_
      refine runStep (stepc0 machine image _ rfl) ?_
      refine runStep (stepc4 machine image _ rfl) ?_
      refine runStep (stepc8 machine image _ rfl) ?_
      exact runStep (stepcc machine image _ rfl rfl) rfl
    · simp [after, insertReturn, rankZero]
  · obtain ⟨before, ran, facts⟩ := inspectPredecessor frame arguments map nonempty found
    let after : Snapshot :=
      { before with pc := mapInsertOffset, ra := base + 0xa0#32, a1 := before.s2, a2 := before.s1 }
    have strict : before.a4 ≠ 0#32 := by rw [facts.gap]; exact gapFlag gap
    refine ⟨after, ?_, rfl, ?_, facts.sp, facts.header, facts.start, facts.stop, facts.cached,
      facts.start, facts.stop, facts.scratchCapacity, facts.scratchData, facts.untouched.2.2.2.2⟩
    · rw [show toInsertCount call = (33 + call.search.count .upper) + 5 by
        simp only [toInsertCount, if_neg (Nat.ne_of_gt found)]; omega, runAdd, ran, Option.bind_some]
      refine runStep (step8c machine image before facts.pc) ?_
      rw [if_neg strict]
      refine runStep (step90 machine image _ rfl) ?_
      refine runStep (step94 machine image _ rfl) ?_
      refine runStep (step98 machine image _ rfl) ?_
      exact runStep (step9c machine image _ rfl rfl) rfl
    · simp [after, insertReturn, Nat.ne_of_gt found]

theorem returnFull {base ret : Word} {original background : Machine} {initial state : Snapshot}
    {call : Call}
    (frame : Frame base ret original initial)
    (machine : MachineState background) (image : CodeImage InsertTable.instructions base background)
    (readable : ∀ offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word),
      Readable background (frameBase initial.sp + offset))
    (saved : ∀ (offset value : Word), offset ∈ ([44, 40, 36, 32, 28, 24, 20] : List Word) →
      WordAt (pushed original.mem initial) (frameBase initial.sp + offset).toNat value →
      WordAt background.mem (frameBase initial.sp + offset).toNat value)
    (arrived : state.pc = insertReturn call) (lowered : state.sp = frameBase initial.sp)
    (full : state.a0 = 1#32) :
    run 13 (sync base background state) =
      some (sync base background (restore initial { state with a0 := 1, a1 := 1 } (ret - base))) := by
  have notOk : state.a0 ≠ 0#32 := by rw [full]; decide
  have beforeRestore : run 4 (sync base background state) =
      some (sync base background { state with pc := 0x1a4, a0 := 1, a1 := 1 }) := by
    by_cases rankZero : call.rank = 0
    · have pc : state.pc = 0xd0#32 := by simpa only [insertReturn, if_pos rankZero] using arrived
      refine runStep (stepd0 machine image state pc) ?_
      rw [if_neg notOk]
      refine runStep (step198 machine image _ rfl) ?_
      refine runStep (step19c machine image _ rfl) ?_
      have equal : state.a0 = (0#32 + 1#32) := full
      rw [if_pos equal]
      exact runStep (step1a0 machine image _ rfl) rfl
    · have pc : state.pc = 0xa0#32 := by simpa only [insertReturn, if_neg rankZero] using arrived
      refine runStep (stepa0 machine image state pc) ?_
      rw [if_neg notOk]
      refine runStep (stepa4 machine image _ rfl) ?_
      refine runStep (stepa8 machine image _ rfl) ?_
      have equal : state.a0 = (0#32 + 1#32) := full
      rw [if_pos equal]
      exact runStep (step1a0 machine image _ rfl) rfl
  rw [show 13 = 4 + 9 by decide, runAdd, beforeRestore, Option.bind_some]
  exact frame.epilogueFrom machine image readable saved _ rfl lowered

end Riscfree.RangeInsert.Bounded.EntryFresh
