import RangeInsert.Empty.Execution

namespace Riscfree.RangeInsert.Empty

open LeanRV32D RV32IM
open Riscfree.RV32 Riscfree.RawVec

set_option maxHeartbeats 2000000

private theorem trackedRegs (indices : List (Fin 32)) (value : Fin 32 → Word)
    (original : Machine) (memory : ByteMemory) :
    (writeTracked indices value { original with mem := memory }).regs =
      (writeTracked indices value original).regs := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [writeTracked, writeX, write_reg_state, ih]

private theorem frameRegisters (base returnPC : Word) (original : Machine)
    (memory : ByteMemory) (initial : Snapshot) (key : Register)
    (notPc : key ≠ Register.PC) (notNext : key ≠ Register.nextPC) :
    (sync base { original with mem := memory } { initial with pc := returnPC }).regs.get? key =
      (sync base original { initial with pc := 0 }).regs.get? key := by
  unfold sync
  rw [readUnchanged _ _ (Ne.symm notPc), readUnchanged _ _ (Ne.symm notNext),
    readUnchanged _ _ (Ne.symm notPc), readUnchanged _ _ (Ne.symm notNext)]
  exact congrArg (fun regs => regs.get? key)
    (trackedRegs (tracked Snapshot) (RegisterView.value initial) original memory)

-- The registers a returning path may leave changed: a0–a5, and on paths
-- through callees also t0, t1, a6, and a7.
private structure Outputs where
  pc : Word
  t0 : Word
  t1 : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word
  a5 : Word
  a6 : Word
  a7 : Word

private instance : RegisterView Outputs where
  tracked := [5, 6, 10, 11, 12, 13, 14, 15, 16, 17]
  pc state := state.pc
  value state index := match index.val with
    | 5 => state.t0
    | 6 => state.t1
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

/-- After the common epilogue, a state whose s6–s10 are their entry values
leaves every register except PC, nextPC, t0, t1, and a0–a7 at its entry
value. -/
theorem restoreRegistersCalls {base : Word} {original : Machine} {initial : Snapshot}
    (entry : original = sync base original { initial with pc := 0 }) (memory : ByteMemory)
    (state : Snapshot) (pc : Word)
    (kept : state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧ state.s8 = initial.s8 ∧
      state.s9 = initial.s9 ∧ state.s10 = initial.s10) :
    ∀ key ∉ [Register.PC, .nextPC, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
      (sync base { original with mem := memory } (restore initial state pc)).regs.get? key =
        original.regs.get? key := by
  intro key outside
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨notPc, notNext, t0, t1, a0, a1, a2, a3, a4, a5, a6, a7⟩ := outside
  obtain ⟨s6, s7, s8, s9, s10⟩ := kept
  let outputs : Outputs :=
    ⟨pc, state.t0, state.t1, state.a0, state.a1, state.a2, state.a3, state.a4, state.a5,
      state.a6, state.a7⟩
  -- Elaborating `syncInside` against this expected type times out, so the
  -- equation is built first and then used.
  have merged := syncInside (frame := { original with mem := memory }) base base
    { initial with pc := pc } (restore initial state pc) outputs
    (by decide) (fun index _ => by
      fin_cases index <;> first | rfl | (simp only [restore]; assumption)) rfl
  rw [← merged, syncFrame outputs key notPc notNext (by
    intro index member
    change index ∈ ([5, 6, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 32)) at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Ne.symm t0, Ne.symm t1, Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4,
      Ne.symm a5, Ne.symm a6, Ne.symm a7])]
  exact (frameRegisters base pc original memory initial key notPc notNext).trans
    (congrArg (fun state => state.regs.get? key) entry.symm)

-- The argument registers alone.
private structure Arguments where
  pc : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  a4 : Word
  a5 : Word

private instance : RegisterView Arguments where
  tracked := [10, 11, 12, 13, 14, 15]
  pc state := state.pc
  value state index := match index.val with
    | 10 => state.a0
    | 11 => state.a1
    | 12 => state.a2
    | 13 => state.a3
    | 14 => state.a4
    | 15 => state.a5
    | _ => 0
  distinct := by decide
  nonzero := by decide

/-- After the common epilogue, a state that never wrote the callee-only
registers leaves every register except PC, nextPC, and a0–a5 at its entry
value. -/
theorem restoreRegisters {base : Word} {original : Machine} {initial : Snapshot}
    (entry : original = sync base original { initial with pc := 0 }) (memory : ByteMemory)
    (state : Snapshot) (pc : Word)
    (kept : state.t0 = initial.t0 ∧ state.t1 = initial.t1 ∧ state.a6 = initial.a6 ∧
      state.a7 = initial.a7 ∧ state.s6 = initial.s6 ∧ state.s7 = initial.s7 ∧
      state.s8 = initial.s8 ∧ state.s9 = initial.s9 ∧ state.s10 = initial.s10) :
    ∀ key ∉ [Register.PC, .nextPC, .x10, .x11, .x12, .x13, .x14, .x15],
      (sync base { original with mem := memory } (restore initial state pc)).regs.get? key =
        original.regs.get? key := by
  intro key outside
  obtain ⟨t0, t1, a6, a7, s6, s7, s8, s9, s10⟩ := kept
  have same : restore initial state pc = restore initial
      { state with
        t0 := initial.t0, t1 := initial.t1, a6 := initial.a6, a7 := initial.a7,
        s6 := initial.s6, s7 := initial.s7, s8 := initial.s8, s9 := initial.s9,
        s10 := initial.s10 } pc := by
    unfold restore
    rw [t0, t1, a6, a7, s6, s7, s8, s9, s10]
  rw [same]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨notPc, notNext, a0, a1, a2, a3, a4, a5⟩ := outside
  let outputs : Arguments :=
    ⟨pc, state.a0, state.a1, state.a2, state.a3, state.a4, state.a5⟩
  have merged := syncInside (frame := { original with mem := memory }) base base
    { initial with pc := pc } (restore initial
      { state with
        t0 := initial.t0, t1 := initial.t1, a6 := initial.a6, a7 := initial.a7,
        s6 := initial.s6, s7 := initial.s7, s8 := initial.s8, s9 := initial.s9,
        s10 := initial.s10 } pc) outputs
    (by decide) (fun index _ => by fin_cases index <;> rfl) rfl
  rw [← merged, syncFrame outputs key notPc notNext (by
    intro index member
    change index ∈ ([10, 11, 12, 13, 14, 15] : List (Fin 32)) at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Ne.symm a0, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5])]
  exact (frameRegisters base pc original memory initial key notPc notNext).trans
    (congrArg (fun state => state.regs.get? key) entry.symm)

theorem returnPc {base returnAddress : Word} (frame : Machine) (state : Snapshot)
    (atReturn : state.pc = returnAddress - base) :
    (sync base frame state).regs.get? Register.PC = some returnAddress := by
  have target : base + (returnAddress - base) = returnAddress := by
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have read := syncReadPC (base := base) (frame := frame) state
  rw [viewPc, atReturn, target] at read
  exact readReg_succ.mp read

/-- An empty input returns in 19 instructions. Every register except PC and
nextPC is preserved, including the stack pointer. Only the 48-byte stack
frame can be modified. -/
theorem Premises.run {base returnAddress : Word} {original : Machine} {initial : Snapshot}
    (premises : Premises base returnAddress original initial) :
    ∃ final, Riscfree.RV32.run 19 original = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (∀ key : Register, key ≠ Register.PC → key ≠ Register.nextPC →
        final.regs.get? key = original.regs.get? key) ∧
      ∀ byte, OutsideFrame initial.sp byte → final.mem[byte]? = original.mem[byte]? := by
  let final := sync base { original with mem := pushed original.mem initial }
    { initial with pc := returnAddress - base }
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (Riscfree.RV32.run 19) premises.entry).trans (runEmpty premises)
  · have read := syncReadPC (base := base)
      (frame := { original with mem := pushed original.mem initial })
      { initial with pc := returnAddress - base }
    apply readReg_succ.mp
    change Sail.readReg Register.PC final = .ok returnAddress final
    have target : base + (returnAddress - base) = returnAddress := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    exact target ▸ read
  · intro key notPc notNext
    exact (frameRegisters base _ original _ initial key notPc notNext).trans
      (congrArg (fun state => state.regs.get? key) premises.entry.symm)
  · intro byte outside
    exact pushedOutside original.mem initial premises.frameFits byte outside

end Riscfree.RangeInsert.Empty
