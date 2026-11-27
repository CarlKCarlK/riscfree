import RangeInsert.Nonempty.Layout

namespace Riscfree.RangeInsert.Nonempty

open LeanRV32D RV32IM
open Riscfree.RV32
open Riscfree.RawVec (Word Writable)
open Empty (Snapshot)

structure FreshPrefix (base returnAddress : Word) (original : Machine) (initial : Snapshot) (call : Call) : Prop where
  frame : Empty.Frame base returnAddress original initial
  arguments : Arguments initial call
  map : Map base original initial.sp call
  nonempty : call.start.toNat ≤ call.stop.toNat
  fresh : call.rank = 0 ∨ (0 < call.rank ∧ call.predecessor.value.toNat + 1 < call.start.toNat)
  writable : ∀ offset ∈ ([8, 12, 16] : List Word), Writable original (Empty.frameBase initial.sp + offset)

theorem InitialLayout.freshPrefix {base returnAddress : Word} {original : Machine}
    {initial : Snapshot} {call : Call} {capacity low high : Word}
    (layout : InitialLayout base original initial call capacity low high)
    (entry : original = sync base original { initial with pc := 0 })
    (link : initial.ra = returnAddress) (mode : MachineMode original returnAddress)
    (arguments : Arguments initial call) (nonempty : call.start.toNat ≤ call.stop.toNat)
    (fresh : call.rank = 0 ∨ (0 < call.rank ∧ call.predecessor.value.toNat + 1 < call.start.toNat)) :
    FreshPrefix base returnAddress original initial call :=
  ⟨layout.outerFrame entry link mode, arguments, layout.predecessorMap, nonempty, fresh,
    layout.stack.scratchWritable⟩

def freshStored (initial : Snapshot) (memory : ByteMemory) : ByteMemory :=
  writeWords memory (scratchWrites { initial with
    sp := Empty.frameBase initial.sp, s4 := initial.a4, s3 := initial.a5 })

def insertionReturn (call : Call) : Word := if call.rank = 0 then 0xd8#32 else 0xa4#32

def insertionPrefixCount (call : Call) : Nat := (if call.rank = 0 then 30 else 41) + call.search.count .upper

structure FreshCalling (base : Word) (initial : Snapshot) (call : Call) (state : Snapshot) : Prop where
  pc : state.pc = insertOffset
  link : state.ra = base + insertionReturn call
  sp : state.sp = Empty.frameBase initial.sp
  header : state.a0 = call.header
  start : state.a1 = call.start
  stop : state.a2 = call.stop
  cache : state.s0 = initial.a1
  savedStop : state.s1 = call.stop
  savedStart : state.s2 = call.start
  saved : state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧ state.s8 = initial.s8 ∧
    state.s9 = initial.s9 ∧ state.s10 = initial.s10

private theorem gapFlag {start stop : Word} (gap : stop.toNat + 1 < start.toNat) :
    Step.lessWord stop 0xffffffff#32 &&& Step.lessWord (stop + 1#32) start ≠ 0#32 := by
  have ⟨increment, strict⟩ := (Riscfree.RangeInsert.predecessorGap start stop).mpr gap
  have maxWord : stop.toNat < (0xffffffff#32).toNat := by exact increment
  have strictWord : (stop + 1#32).toNat < start.toNat := strict
  unfold Step.lessWord
  rw [if_pos maxWord, if_pos strictWord]
  decide

private theorem FreshPrefix.setup {base returnAddress : Word} {original : Machine} {initial state : Snapshot}
    {call : Call} (premises : FreshPrefix base returnAddress original initial call)
    (sp : state.sp = Empty.frameBase initial.sp) :
    FreshSetup base original state := by
  refine ⟨sp ▸ premises.writable 8 (by decide), sp ▸ premises.writable 12 (by decide),
    sp ▸ premises.writable 16 (by decide), ?_⟩
  intro byte low high write member
  have outside := premises.frame.codeOutside byte low high
  unfold Empty.OutsideFrame at outside
  have fit := premises.frame.frameFits
  simp only [scratchWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [show (state.sp + 8#32).toNat = initial.sp.toNat - 48 + 8 by rw [sp, Empty.frameAddress fit _ (by decide)]; rfl]
    omega
  · rw [show (state.sp + 12#32).toNat = initial.sp.toNat - 48 + 12 by rw [sp, Empty.frameAddress fit _ (by decide)]; rfl]
    omega
  · rw [show (state.sp + 16#32).toNat = initial.sp.toNat - 48 + 16 by rw [sp, Empty.frameAddress fit _ (by decide)]; rfl]
    omega

set_option maxHeartbeats 1500000 in
/-- The rank-zero and strict-gap branches call the same linked map
insertion with distinct return addresses. -/
theorem FreshPrefix.toInsert {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    {call : Call} (premises : FreshPrefix base returnAddress original initial call) :
    ∃ state : Snapshot,
      run (insertionPrefixCount call) (sync base original { initial with pc := 0 }) =
        some (sync base { original with mem := (freshStored initial (Empty.pushed original.mem initial)) } state) ∧
      FreshCalling base initial call state := by
  let memory := Empty.pushed original.mem initial
  have machine := premises.frame.mode.toMachineState
  have image := premises.frame.pushedImage
  rcases premises.fresh with noPredecessor | ⟨found, gap⟩
  · obtain ⟨searched, ran, rank⟩ :=
      toPredecessor premises.frame premises.arguments premises.map premises.nonempty
    let before := afterSearch (calling base initial) searched
    let state : Snapshot := { before with pc := 0xb0#32 }
    have zero : before.a0 = 0#32 := by
      change searched.a0 = 0#32
      rw [rank, noPredecessor]
    have branch : step (sync base { original with mem := memory } before) =
        some (sync base { original with mem := memory } state) :=
      branchNoPredecessor machine image before rfl zero
    have inserted := freshSetupFirst machine image state rfl (premises.setup (state := state) rfl)
    refine ⟨insertCalling base 0xd8#32 state state.s5, ?_,
      rfl, ?_, rfl, premises.arguments.header, premises.arguments.start, premises.arguments.stop, rfl,
      premises.arguments.stop, premises.arguments.start, rfl, rfl, rfl, rfl, rfl⟩
    · rw [show insertionPrefixCount call = (19 + call.search.count .upper) + (1 + 10) by
        simp only [insertionPrefixCount, if_pos noPredecessor]; omega,
        runAdd, ran, Option.bind_some]
      exact runStep branch inserted
    · simp only [insertCalling, insertionReturn, if_pos noPredecessor]
  · obtain ⟨inspected, ran, facts⟩ :=
      inspectPredecessor premises.frame premises.arguments premises.map premises.nonempty found
    let state : Snapshot := { inspected with pc := 0x88#32 }
    have isGap : inspected.a4 ≠ 0#32 := by rw [facts.gap]; exact gapFlag gap
    have branch : step (sync base { original with mem := memory } inspected) =
        some (sync base { original with mem := memory } state) :=
      branchGap machine image inspected facts.pc isGap
    have inserted := freshSetupGap machine image state rfl (premises.setup (state := state) facts.sp)
    refine ⟨insertCalling base 0xa4#32 state state.a0, ?_,
      rfl, ?_, facts.sp, facts.header, facts.start, facts.stop, facts.cached, facts.stop, facts.start, ?_⟩
    · rw [show insertionPrefixCount call = (33 + call.search.count .upper) + (1 + 7) by
        simp only [insertionPrefixCount, if_neg (Nat.ne_of_gt found)]; omega,
        runAdd, ran, Option.bind_some]
      have same : scratchWrites state = scratchWrites { initial with
          sp := Empty.frameBase initial.sp, s4 := initial.a4, s3 := initial.a5 } := by
        simp only [scratchWrites, show state.sp = _ from facts.sp, show state.s4 = _ from facts.scratchData,
          show state.s3 = _ from facts.scratchCapacity]
      rw [freshStored, ← same]
      exact runStep branch inserted
    · simp only [insertCalling, insertionReturn, if_neg (Nat.ne_of_gt found)]
    · exact facts.untouched.2.2.2.2

end Riscfree.RangeInsert.Nonempty
