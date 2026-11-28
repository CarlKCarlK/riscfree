import RangeInsert.Empty

/-! The common OOM return at offset 0x1a0 in the bounded Rust entry point.
The fragment starts at the instruction that sets a0 to FULL. -/

namespace Riscfree.RangeInsert.OomReturn

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 Riscfree.RawVec
open Empty (Snapshot frameBase restore viewPc)

def instructions : List (Word × instruction) :=
  [ (0x00100513, .ITYPE (1, reg 0, reg 10, .ADDI))
  , (0x02c12083, .LOAD (44, reg 2, reg 1, false, 4))
  , (0x02812403, .LOAD (40, reg 2, reg 8, false, 4))
  , (0x02412483, .LOAD (36, reg 2, reg 9, false, 4))
  , (0x02012903, .LOAD (32, reg 2, reg 18, false, 4))
  , (0x01c12983, .LOAD (28, reg 2, reg 19, false, 4))
  , (0x01812a03, .LOAD (24, reg 2, reg 20, false, 4))
  , (0x01412a83, .LOAD (20, reg 2, reg 21, false, 4))
  , (0x03010113, .ITYPE (48, reg 2, reg 2, .ADDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

private theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state) :
    ∀ entry ∈ instructions, ext_decode entry.1 state = .ok entry.2 state := by
  unfold instructions
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  repeat' apply And.intro
  all_goals
    show encdec_backwards _ _ = _
    decode_word_normal_form [privilege, landingPad]

private theorem fetchDecode {base : Word} {original : Machine}
    (machine : MachineState original) (image : CodeImage instructions base original)
    (state : Snapshot) (index : Fin instructions.length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base original state) = .ok (.F_Base instructions[index.val].1) (sync base original state) ∧
      ext_decode instructions[index.val].1 (sync base original state) =
        .ok instructions[index.val].2 (sync base original state) := by
  have synced := machine.atSync base state
  obtain ⟨_, misa⟩ := synced.misa
  have member := List.getElem_mem index.isLt
  exact ⟨(image.code machine.privilege (machine.status.imp fun _ read => read.1) machine.htif
    state index pc).fetch (syncReadPC state) misa
    ((by decide : ∀ entry ∈ instructions, isRVC (entry.1.extractLsb' 0 16) = false) _ member),
    linkedWordsDecode _ synced.privilege synced.landingPad _ member⟩

def savedRegisters (initial : Snapshot) : List (Word × Word) :=
  [(44, initial.ra), (40, initial.s0), (36, initial.s1), (32, initial.s2),
    (28, initial.s3), (24, initial.s4), (20, initial.s5)]

/-- The frame holds the entry register values. Each load is justified by
the corresponding readable initialized slot. -/
structure Premises (base : Word) (original : Machine) (initial state : Snapshot) : Prop where
  machine : MachineState original
  code : CodeImage instructions base original
  entry : original = sync base original state
  pc : state.pc = 0
  sp : state.sp = frameBase initial.sp
  returnLow : initial.ra &&& 0xfffffffe#32 = initial.ra
  returnNext : initial.ra[1] = false
  readable : ∀ address ∈ (savedRegisters initial).map Prod.fst, Readable original (state.sp + address)
  contents : ∀ entry ∈ savedRegisters initial, WordAt original.mem (state.sp + entry.1).toNat entry.2

set_option maxHeartbeats 3500000 in
theorem Premises.run {base : Word} {original : Machine} {initial state : Snapshot}
    (premises : Premises base original initial state) :
    Riscfree.RV32.run 10 original =
      some (sync base original (restore initial { state with a0 := 1 } (initial.ra - base))) := by
  conv_lhs => rw [premises.entry]
  let status : Snapshot := { state with pc := 4, a0 := 1 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code state ⟨0, by decide⟩ premises.pc
  refine runStep (Step.addi fetched decoded rfl (by decide)
    (next := status) (by advance [viewPc, premises.pc])) ?_
  let after1 : Snapshot := { status with pc := 8, ra := initial.ra }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code status ⟨1, by decide⟩ rfl
  have loaded1 := Empty.load (base := base) (state := status) premises.machine
    (premises.readable 44 (by simp [savedRegisters])) (premises.contents (44, initial.ra) (by simp [savedRegisters]))
  refine runStep (Step.lw fetched decoded (syncRead _ (index := 2) (by decide))
    (loaded1 _ _) (by decide) (next := after1) (by advance [viewPc])) ?_
  let after2 : Snapshot := { after1 with pc := 12, s0 := initial.s0 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code after1 ⟨2, by decide⟩ rfl
  have loaded2 := Empty.load (base := base) (state := after1) premises.machine
    (premises.readable 40 (by simp [savedRegisters])) (premises.contents (40, initial.s0) (by simp [savedRegisters]))
  refine runStep (Step.lw fetched decoded (syncRead _ (index := 2) (by decide))
    (loaded2 _ _) (by decide) (next := after2) (by advance [viewPc])) ?_
  let after3 : Snapshot := { after2 with pc := 16, s1 := initial.s1 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code after2 ⟨3, by decide⟩ rfl
  have loaded3 := Empty.load (base := base) (state := after2) premises.machine
    (premises.readable 36 (by simp [savedRegisters])) (premises.contents (36, initial.s1) (by simp [savedRegisters]))
  refine runStep (Step.lw fetched decoded (syncRead _ (index := 2) (by decide))
    (loaded3 _ _) (by decide) (next := after3) (by advance [viewPc])) ?_
  let after4 : Snapshot := { after3 with pc := 20, s2 := initial.s2 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code after3 ⟨4, by decide⟩ rfl
  have loaded4 := Empty.load (base := base) (state := after3) premises.machine
    (premises.readable 32 (by simp [savedRegisters])) (premises.contents (32, initial.s2) (by simp [savedRegisters]))
  refine runStep (Step.lw fetched decoded (syncRead _ (index := 2) (by decide))
    (loaded4 _ _) (by decide) (next := after4) (by advance [viewPc])) ?_
  let after5 : Snapshot := { after4 with pc := 24, s3 := initial.s3 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code after4 ⟨5, by decide⟩ rfl
  have loaded5 := Empty.load (base := base) (state := after4) premises.machine
    (premises.readable 28 (by simp [savedRegisters])) (premises.contents (28, initial.s3) (by simp [savedRegisters]))
  refine runStep (Step.lw fetched decoded (syncRead _ (index := 2) (by decide))
    (loaded5 _ _) (by decide) (next := after5) (by advance [viewPc])) ?_
  let after6 : Snapshot := { after5 with pc := 28, s4 := initial.s4 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code after5 ⟨6, by decide⟩ rfl
  have loaded6 := Empty.load (base := base) (state := after5) premises.machine
    (premises.readable 24 (by simp [savedRegisters])) (premises.contents (24, initial.s4) (by simp [savedRegisters]))
  refine runStep (Step.lw fetched decoded (syncRead _ (index := 2) (by decide))
    (loaded6 _ _) (by decide) (next := after6) (by advance [viewPc])) ?_
  let after7 : Snapshot := { after6 with pc := 32, s5 := initial.s5 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code after6 ⟨7, by decide⟩ rfl
  have loaded7 := Empty.load (base := base) (state := after6) premises.machine
    (premises.readable 20 (by simp [savedRegisters])) (premises.contents (20, initial.s5) (by simp [savedRegisters]))
  refine runStep (Step.lw fetched decoded (syncRead _ (index := 2) (by decide))
    (loaded7 _ _) (by decide) (next := after7) (by advance [viewPc])) ?_
  let ready : Snapshot := { after7 with pc := 36, sp := state.sp + 48#32 }
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code after7 ⟨8, by decide⟩ rfl
  refine runStep (Step.addi fetched decoded (syncRead _ (index := 2) (by decide)) (by decide)
    (next := ready) (by advance [viewPc])) ?_
  obtain ⟨fetched, decoded⟩ := fetchDecode premises.machine premises.code ready ⟨9, by decide⟩ rfl
  have synced := premises.machine.atSync base ready
  obtain ⟨_, misa⟩ := synced.misa
  obtain ⟨_, configuration⟩ := synced.mseccfg
  refine runStep (Step.jalr (imm := 0#12) (sourceValue := initial.ra) fetched decoded
    (syncRead _ (index := 1) (by decide)) misa synced.privilege configuration ?_ ?_
    (next := { ready with pc := initial.ra - base }) (by advance [viewPc])) ?_
  · simp [premises.returnNext, BitVec.ofBool]
  · rw [BitVec.add_comm base, BitVec.sub_add_cancel,
      show (0#12).signExtend 32 = 0#32 from rfl, BitVec.add_zero, BitVec.and_comm, premises.returnLow]
  have restored : state.sp + 48#32 = initial.sp := by
    rw [premises.sp]
    exact BitVec.sub_add_cancel _ _
  simp only [ready, after7, after6, after5, after4, after3, after2, after1, status, restore]
  rw [restored]
  rfl

end Riscfree.RangeInsert.OomReturn
