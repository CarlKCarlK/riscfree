import PopcountSpec
import Riscfree.Elf
import Riscfree.RV32.Decode
import Riscfree.RV32.Platform

/-!
# Linked RV32 popcount: SWAR

`popcount128_swar` counts each word with masks, a subtraction, additions and
a multiply by `0x01010101`. The per-word identity is proved in the kernel by
splitting the word into nibbles: every SWAR step either acts on each nibble
separately or moves whole nibbles without a carry, and the 16 nibble values
are checked exhaustively. Sail decodes the linked instructions, and Pico FV's
equivalence theorems give their effects on the registers. The ELF check uses
the same words as the Sail decoder.
-/

namespace Riscfree

namespace PopcountSwar

open LeanRV32D LeanRV32D.Functions RV32IM
open Riscfree.RV32 hiding Platform

/-! ## Per-word SWAR identity -/

section Identity

-- The arithmetic of one loop iteration with the masks the setup loads.
def swar (word : Word) : Word :=
  let pairs := word - ((word >>> (1 : Nat)) &&& 0x55555555#32)
  let nibbles := ((pairs >>> (2 : Nat)) &&& 0x33333333#32) + (pairs &&& 0x33333333#32)
  let bytes := (nibbles + (nibbles >>> (4 : Nat))) &&& 0x0f0f0f0f#32
  (bytes * 0x01010101#32) >>> (24 : Nat)

-- The eight nibbles of a word, most significant first.
def join (x : Nat → BitVec 4) : Word :=
  x 7 ++ x 6 ++ x 5 ++ x 4 ++ x 3 ++ x 2 ++ x 1 ++ x 0

theorem appendNat (x : BitVec m) (y : BitVec n) : (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem toNatJoin (x : Nat → BitVec 4) : (join x).toNat =
    (x 0).toNat + 16 * (x 1).toNat + 256 * (x 2).toNat + 4096 * (x 3).toNat +
    65536 * (x 4).toNat + 1048576 * (x 5).toNat + 16777216 * (x 6).toNat + 268435456 * (x 7).toNat := by
  simp only [join, appendNat]
  omega

def nibble (word : Word) (index : Nat) : BitVec 4 := word.extractLsb' (4 * index) 4

-- shorthand for the bounds omega needs
theorem bounds (x : Nat → BitVec 4) : ∀ index, (x index).toNat < 16 := fun index => (x index).isLt

theorem splitNibbles (word : Word) : word = join (nibble word) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNatJoin]
  have := word.isLt
  simp [nibble, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega


theorem andJoin (x y : Nat → BitVec 4) : join x &&& join y = join (fun index => x index &&& y index) := by
  simp only [join]
  rw [BitVec.and_append (w := 28) (v := 4), BitVec.and_append (w := 24) (v := 4),
    BitVec.and_append (w := 20) (v := 4), BitVec.and_append (w := 16) (v := 4),
    BitVec.and_append (w := 12) (v := 4), BitVec.and_append (w := 8) (v := 4),
    BitVec.and_append (w := 4) (v := 4)]

-- A masked right shift equals shifting the correspondingly shifted mask.
theorem shiftMask (word mask : Word) (shift : Nat) :
    (word >>> shift) &&& mask = (word &&& (mask <<< shift)) >>> shift := by
  ext index bound
  simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  by_cases inside : shift + index < 32
  · simp [BitVec.getLsbD_eq_getElem, inside, bound, show ¬ shift + index < shift by omega]
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ shift + index)]

theorem shiftJoin1 (x : Nat → BitVec 4) (even : ∀ index, (x index).toNat % 2 = 0) :
    join x >>> 1 = join (fun index => x index >>> 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, toNatJoin, Nat.shiftRight_eq_div_pow]
  have := bounds x 0; have := bounds x 1; have := bounds x 2; have := bounds x 3
  have := bounds x 4; have := bounds x 5; have := bounds x 6; have := bounds x 7
  have := even 0; have := even 1; have := even 2; have := even 3
  have := even 4; have := even 5; have := even 6; have := even 7
  omega

theorem shiftJoin2 (x : Nat → BitVec 4) (even : ∀ index, (x index).toNat % 4 = 0) :
    join x >>> 2 = join (fun index => x index >>> 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, toNatJoin, Nat.shiftRight_eq_div_pow]
  have := bounds x 0; have := bounds x 1; have := bounds x 2; have := bounds x 3
  have := bounds x 4; have := bounds x 5; have := bounds x 6; have := bounds x 7
  have := even 0; have := even 1; have := even 2; have := even 3
  have := even 4; have := even 5; have := even 6; have := even 7
  omega

theorem shiftJoin4 (x : Nat → BitVec 4) :
    join x >>> 4 = join (fun index => if index < 7 then x (index + 1) else 0#4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, toNatJoin, Nat.shiftRight_eq_div_pow]
  have := bounds x 0; have := bounds x 1; have := bounds x 2; have := bounds x 3
  have := bounds x 4; have := bounds x 5; have := bounds x 6; have := bounds x 7
  simp
  omega

theorem addJoin (x y : Nat → BitVec 4) (fits : ∀ index, (x index).toNat + (y index).toNat < 16) :
    join x + join y = join (fun index => x index + y index) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, toNatJoin]
  have := fits 0; have := fits 1; have := fits 2; have := fits 3
  have := fits 4; have := fits 5; have := fits 6; have := fits 7
  omega

theorem subJoin (x y : Nat → BitVec 4) (fits : ∀ index, (y index).toNat ≤ (x index).toNat) :
    join x - join y = join (fun index => x index - y index) := by
  have each (index : Nat) : (x index - y index).toNat = (x index).toNat - (y index).toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (fits index))
  have whole : (join y).toNat ≤ (join x).toNat := by
    rw [toNatJoin, toNatJoin]
    have := fits 0; have := fits 1; have := fits 2; have := fits 3
    have := fits 4; have := fits 5; have := fits 6; have := fits 7
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr whole), toNatJoin, toNatJoin, toNatJoin]
  simp only [each]
  have := fits 0; have := fits 1; have := fits 2; have := fits 3
  have := fits 4; have := fits 5; have := fits 6; have := fits 7
  omega

-- The four-bit version of the first two SWAR steps.
def pairs4 (value : BitVec 4) : BitVec 4 := value - ((value &&& 0xa#4) >>> 1)
def halves4 (value : BitVec 4) : BitVec 4 := ((value &&& 0xc#4) >>> 2) + (value &&& 0x3#4)

theorem evenHigh : ∀ value : BitVec 4, (value &&& 0xa#4).toNat % 2 = 0 := by decide
theorem highBelow : ∀ value : BitVec 4, ((value &&& 0xa#4) >>> 1).toNat ≤ value.toNat := by decide
theorem evenUpper : ∀ value : BitVec 4, (value &&& 0xc#4).toNat % 4 = 0 := by decide
theorem halvesFit : ∀ value : BitVec 4,
    ((value &&& 0xc#4) >>> 2).toNat + (value &&& 0x3#4).toNat < 16 := by decide
theorem countBound : ∀ value : BitVec 4, (halves4 (pairs4 value)).toNat ≤ 4 := by decide
theorem countCpop : ∀ value : BitVec 4, (halves4 (pairs4 value)).toNat = value.cpop.toNat := by decide
theorem keepLow : ∀ value : BitVec 4, value &&& 0xf#4 = value := by decide

theorem mask1 : 0x55555555#32 <<< 1 = join (fun _ => 0xa#4) := by
  apply BitVec.eq_of_toNat_eq; simp [toNatJoin]
theorem mask2 : 0x33333333#32 <<< 2 = join (fun _ => 0xc#4) := by
  apply BitVec.eq_of_toNat_eq; simp [toNatJoin]
theorem mask2Low : 0x33333333#32 = join (fun _ => 0x3#4) := by
  apply BitVec.eq_of_toNat_eq; simp [toNatJoin]
theorem mask4 : 0x0f0f0f0f#32 = join (fun index => if index % 2 = 0 then 0xf#4 else 0#4) := by
  apply BitVec.eq_of_toNat_eq; simp [toNatJoin]

theorem pairsJoin (x : Nat → BitVec 4) :
    join x - ((join x >>> 1) &&& 0x55555555#32) = join (fun index => pairs4 (x index)) := by
  rw [shiftMask, mask1, andJoin, shiftJoin1 _ (fun index => evenHigh (x index)),
    subJoin _ _ (fun index => highBelow (x index))]
  rfl

theorem countJoin (x : Nat → BitVec 4) :
    ((join x >>> 2) &&& 0x33333333#32) + (join x &&& 0x33333333#32) =
      join (fun index => halves4 (x index)) := by
  rw [shiftMask, mask2, andJoin, shiftJoin2 _ (fun index => evenUpper (x index)), mask2Low,
    andJoin, addJoin _ _ (fun index => halvesFit (x index))]
  rfl

-- Multiplying by 0x01010101 accumulates the byte counts into the top byte.
theorem byteSum (c0 c1 c2 c3 c4 c5 c6 c7 : Nat)
    (b0 : c0 ≤ 4) (b1 : c1 ≤ 4) (b2 : c2 ≤ 4) (b3 : c3 ≤ 4)
    (b4 : c4 ≤ 4) (b5 : c5 ≤ 4) (b6 : c6 ≤ 4) (b7 : c7 ≤ 4) :
    (c0 + c1 + 256 * (c2 + c3) + 65536 * (c4 + c5) + 16777216 * (c6 + c7)) * 16843009 %
        4294967296 / 16777216 = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by
  have expand : (c0 + c1 + 256 * (c2 + c3) + 65536 * (c4 + c5) + 16777216 * (c6 + c7)) * 16843009 =
      ((c0 + c1) + 256 * (c0 + c1 + c2 + c3) + 65536 * (c0 + c1 + c2 + c3 + c4 + c5) +
        16777216 * (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)) +
      4294967296 * ((c2 + c3) + 257 * (c4 + c5) + 65793 * (c6 + c7)) := by
    omega
  rw [expand, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

theorem topByte (value : Word) :
    ((value * 0x01010101#32) >>> 24).toNat = value.toNat * 16843009 % 4294967296 / 16777216 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rfl

theorem reduceJoin (n : Nat → BitVec 4) (bound : ∀ index, (n index).toNat ≤ 4) :
    ((((join n + (join n >>> 4)) &&& 0x0f0f0f0f#32) * 0x01010101#32) >>> 24).toNat =
      (n 0).toNat + (n 1).toNat + (n 2).toNat + (n 3).toNat +
        (n 4).toNat + (n 5).toNat + (n 6).toNat + (n 7).toNat := by
  rw [shiftJoin4, addJoin, mask4, andJoin]
  · rw [topByte, toNatJoin]
    simp [keepLow, BitVec.toNat_add]
    have := bound 0; have := bound 1; have := bound 2; have := bound 3
    have := bound 4; have := bound 5; have := bound 6; have := bound 7
    rw [Nat.mod_eq_of_lt (show (n 0).toNat + (n 1).toNat < 16 by omega),
      Nat.mod_eq_of_lt (show (n 2).toNat + (n 3).toNat < 16 by omega),
      Nat.mod_eq_of_lt (show (n 4).toNat + (n 5).toNat < 16 by omega),
      Nat.mod_eq_of_lt (show (n 6).toNat + (n 7).toNat < 16 by omega)]
    exact byteSum _ _ _ _ _ _ _ _ (bound 0) (bound 1) (bound 2) (bound 3)
      (bound 4) (bound 5) (bound 6) (bound 7)
  · intro index
    have := bound index
    split
    · have := bound (index + 1)
      omega
    · simp
      omega

theorem swarCpop (word : Word) : (swar word).toNat = word.cpop.toNat := by
  rw [splitNibbles word]
  simp only [swar, pairsJoin, countJoin]
  rw [reduceJoin (fun index => halves4 (pairs4 (nibble word index))) (fun index => countBound _)]
  simp only [countCpop, join, BitVec.toNat_cpop_append]
  omega


#print axioms swarCpop

end Identity

/-! ## Sail decoding of the linked instruction words -/

section SailDecode

-- Each word is a little-endian instruction from the linked popcount128_swar symbol.
-- The right column records the Sail AST we expect its decoder to return.
-- `zext.b a0, a1` is the `andi a0, a1, 255` encoding.
def instructions : List (BitVec 32 × instruction) :=
  [ (0x00000593, .ITYPE (0, reg 0, reg 11, .ADDI))
  , (0x55555637, .UTYPE (0x55555, reg 12, .LUI))
  , (0x01050813, .ITYPE (16, reg 10, reg 16, .ADDI))
  , (0x33333737, .UTYPE (0x33333, reg 14, .LUI))
  , (0x55560893, .ITYPE (0x555, reg 12, reg 17, .ADDI))
  , (0x33370713, .ITYPE (0x333, reg 14, reg 14, .ADDI))
  , (0x0f0f17b7, .UTYPE (0x0f0f1, reg 15, .LUI))
  , (0x01010637, .UTYPE (0x01010, reg 12, .LUI))
  , (0xf0f78293, .ITYPE (0xf0f, reg 15, reg 5, .ADDI))
  , (0x10160613, .ITYPE (0x101, reg 12, reg 12, .ADDI))
  , (0x00052783, .LOAD (0, reg 10, reg 15, false, 4))
  , (0x00450513, .ITYPE (4, reg 10, reg 10, .ADDI))
  , (0x0017d693, .SHIFTIOP (1, reg 15, reg 13, .SRLI))
  , (0x0116f6b3, .RTYPE (reg 17, reg 13, reg 13, .AND))
  , (0x40d787b3, .RTYPE (reg 13, reg 15, reg 15, .SUB))
  , (0x0027d693, .SHIFTIOP (2, reg 15, reg 13, .SRLI))
  , (0x00e7f7b3, .RTYPE (reg 14, reg 15, reg 15, .AND))
  , (0x00e6f6b3, .RTYPE (reg 14, reg 13, reg 13, .AND))
  , (0x00f686b3, .RTYPE (reg 15, reg 13, reg 13, .ADD))
  , (0x0046d793, .SHIFTIOP (4, reg 13, reg 15, .SRLI))
  , (0x00f686b3, .RTYPE (reg 15, reg 13, reg 13, .ADD))
  , (0x0056f6b3, .RTYPE (reg 5, reg 13, reg 13, .AND))
  , (0x02c686b3, .MUL (reg 12, reg 13, reg 13,
      { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed }))
  , (0x0186d693, .SHIFTIOP (24, reg 13, reg 13, .SRLI))
  , (0x00d585b3, .RTYPE (reg 13, reg 11, reg 11, .ADD))
  , (0xfd0512e3, .BTYPE (0x1fc4, reg 16, reg 10, .BNE))
  , (0x0ff5f513, .ITYPE (0xff, reg 11, reg 10, .ANDI))
  , (0x00008067, .JALR (0, reg 1, reg 0))
  ]

-- Sail decodes MUL only when misa.M is set (this hart model has no separate Zmmul).
set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem linkedWordsDecode (state : Machine)
    (privilege : Sail.readReg Register.cur_privilege state = .ok .Machine state)
    (landingPad : get_xLPE .Machine state = .ok false state)
    {misa : RegisterType Register.misa}
    (misaRead : Sail.readReg Register.misa state = .ok misa state)
    (multiply : _get_Misa_M misa = 1#1) :
    ∀ entry ∈ instructions, ext_decode entry.1 state = .ok entry.2 state := by
  decode_table instructions [privilege, landingPad, misaRead, multiply]

#print axioms linkedWordsDecode

end SailDecode


/-! ## Proof snapshots and the Sail register frame -/

section SailState

-- A proof snapshot records the relative PC and the nine registers the routine
-- updates: a0–a7 and t0. Byte memory and all other registers stay in the Sail frame.
structure Snapshot where
  pc : Word := 0
  a0 : Word
  a1 : Word := 0
  a2 : Word := 0
  a3 : Word := 0
  a4 : Word := 0
  a5 : Word := 0
  a6 : Word := 0
  a7 : Word := 0
  t0 : Word := 0

instance : RegisterView Snapshot where
  tracked := [5, 10, 11, 12, 13, 14, 15, 16, 17]
  pc state := state.pc
  value state index :=
    match index.val with
    | 5 => state.t0
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

@[simp] theorem viewPc (state : Snapshot) : RegisterView.pc state = state.pc := rfl

end SailState


/-! ## Code mapping, RAM, and processor assumptions -/

section SailPlatform

-- The shared platform premises, plus the M extension that Sail's MUL decoder requires.
structure Platform (base : Word) (frame : Machine) (input returnAddress : Word) (memory : Memory) :
    Prop where
  common : RV32.Platform Snapshot instructions base frame (inputAddresses input) returnAddress memory
  multiply : ∃ value, Sail.readReg Register.misa frame = .ok value frame ∧ _get_Misa_M value = 1#1

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}

-- Select the actual Sail decoding before considering the effect of the instruction.
theorem fetchAndDecode (platform : Platform base frame input returnAddress memory)
    (state : Snapshot) (index : Fin instructions.length)
    (pc : state.pc = BitVec.ofNat 32 (index.val * 4)) :
    fetch () (sync base frame state) =
        .ok (.F_Base instructions[index.val].1) (sync base frame state) ∧
      ext_decode instructions[index.val].1 (sync base frame state) =
        .ok instructions[index.val].2 (sync base frame state) := by
  obtain ⟨misa, misaRead, multiply⟩ := platform.multiply
  refine platform.common.fetchAndDecode (fun state => ?_) (by decide) state index pc
  exact linkedWordsDecode _ (platform.common.privilegeAt state) (platform.common.landingPadAt state)
    (RV32.Platform.systemRead state (by decide) (by decide) (by decide) misaRead) multiply

end SailPlatform


/-! ## Effects of the linked instructions -/

section SailInstructions

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}
variable (platform : Platform base frame input returnAddress memory)
include platform

private theorem clearTotal (state : Snapshot) (atPC : state.pc = 0#32) :
    step (sync base frame state) = some (sync base frame { state with pc := 4, a1 := 0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨0, by decide⟩ atPC
  exact Step.addi fetched decoded rfl (by decide) (by advance [viewPc, atPC])

private theorem loadPairsHigh (state : Snapshot) (atPC : state.pc = 4#32) :
    step (sync base frame state) = some (sync base frame { state with pc := 8, a2 := 0x55555000 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨1, by decide⟩ atPC
  exact Step.lui fetched decoded (by decide) (by advance [viewPc, atPC])

private theorem saveEnd (state : Snapshot) (atPC : state.pc = 8#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 12, a6 := state.a0 + 16 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨2, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem loadNibblesHigh (state : Snapshot) (atPC : state.pc = 12#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 16, a4 := 0x33333000 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨3, by decide⟩ atPC
  exact Step.lui fetched decoded (by decide) (by advance [viewPc, atPC])

private theorem completePairsMask (state : Snapshot) (atPC : state.pc = 16#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 20, a7 := state.a2 + 0x555 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨4, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem completeNibblesMask (state : Snapshot) (atPC : state.pc = 20#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 24, a4 := state.a4 + 0x333 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨5, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem loadBytesHigh (state : Snapshot) (atPC : state.pc = 24#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 28, a5 := 0x0f0f1000 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨6, by decide⟩ atPC
  exact Step.lui fetched decoded (by decide) (by advance [viewPc, atPC])

private theorem loadMultiplierHigh (state : Snapshot) (atPC : state.pc = 28#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 32, a2 := 0x01010000 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨7, by decide⟩ atPC
  exact Step.lui fetched decoded (by decide) (by advance [viewPc, atPC])

private theorem completeBytesMask (state : Snapshot) (atPC : state.pc = 32#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 36, t0 := state.a5 + 0xffffff0f }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨8, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem completeMultiplier (state : Snapshot) (atPC : state.pc = 36#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 40, a2 := state.a2 + 0x101 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨9, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem loadWord (state : Snapshot) (atPC : state.pc = 40#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 44, a5 := memory state.a0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨10, by decide⟩ atPC
  exact platform.common.lw fetched decoded (syncRead state (by decide)) inRam (BitVec.add_zero _)
    (by decide) (by advance [viewPc, atPC])

private theorem advancePointer (state : Snapshot) (atPC : state.pc = 44#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 48, a0 := state.a0 + 4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨11, by decide⟩ atPC
  exact Step.addi fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem alignPairs (state : Snapshot) (atPC : state.pc = 48#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 52, a3 := state.a5 >>> (1 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨12, by decide⟩ atPC
  exact Step.srli fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem isolatePairHighs (state : Snapshot) (atPC : state.pc = 52#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 56, a3 := state.a3 &&& state.a7 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨13, by decide⟩ atPC
  exact Step.and fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem countPairs (state : Snapshot) (atPC : state.pc = 56#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 60, a5 := state.a5 - state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨14, by decide⟩ atPC
  exact Step.sub fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem alignNibbles (state : Snapshot) (atPC : state.pc = 60#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 64, a3 := state.a5 >>> (2 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨15, by decide⟩ atPC
  exact Step.srli fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem keepLowerPairs (state : Snapshot) (atPC : state.pc = 64#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 68, a5 := state.a5 &&& state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨16, by decide⟩ atPC
  exact Step.and fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem keepUpperPairs (state : Snapshot) (atPC : state.pc = 68#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 72, a3 := state.a3 &&& state.a4 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨17, by decide⟩ atPC
  exact Step.and fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem countNibbles (state : Snapshot) (atPC : state.pc = 72#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 76, a3 := state.a3 + state.a5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨18, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem alignBytes (state : Snapshot) (atPC : state.pc = 76#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 80, a5 := state.a3 >>> (4 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨19, by decide⟩ atPC
  exact Step.srli fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem sumNibbles (state : Snapshot) (atPC : state.pc = 80#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 84, a3 := state.a3 + state.a5 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨20, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem keepByteCounts (state : Snapshot) (atPC : state.pc = 84#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 88, a3 := state.a3 &&& state.t0 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨21, by decide⟩ atPC
  exact Step.and fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem sumBytes (state : Snapshot) (atPC : state.pc = 88#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 92, a3 := state.a3 * state.a2 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨22, by decide⟩ atPC
  exact Step.mul fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem extractCount (state : Snapshot) (atPC : state.pc = 92#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 96, a3 := state.a3 >>> (24 : Nat) }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨23, by decide⟩ atPC
  exact Step.srli fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem addCount (state : Snapshot) (atPC : state.pc = 96#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 100, a1 := state.a1 + state.a3 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨24, by decide⟩ atPC
  exact Step.add fetched decoded (syncRead state (by decide)) (syncRead state (by decide)) (by decide)
    (by advance [viewPc, atPC])

private theorem branchOnEnd (state : Snapshot) (atPC : state.pc = 100#32) :
    step (sync base frame state) = some (sync base frame
      { state with pc := if state.a0 = state.a6 then 104#32 else 40#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨25, by decide⟩ atPC
  exact platform.common.bne fetched decoded (syncRead state (by decide)) (syncRead state (by decide))
    (by rw [viewPc, atPC]; decide) (by advance [viewPc, atPC])

private theorem returnByte (state : Snapshot) (atPC : state.pc = 104#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := 108, a0 := state.a1 &&& 255#32 }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨26, by decide⟩ atPC
  exact Step.andi fetched decoded (syncRead state (by decide)) (by decide) (by advance [viewPc, atPC])

private theorem returnToCaller (state : Snapshot) (atPC : state.pc = 108#32) :
    step (sync base frame state) =
      some (sync base frame { state with pc := returnAddress - base }) := by
  obtain ⟨fetched, decoded⟩ := fetchAndDecode platform state ⟨27, by decide⟩ atPC
  exact platform.common.ret fetched decoded (by decide) (by advance [viewPc])

end SailInstructions


/-! ## Setup, loop body, and exit -/

section SailRun

variable {base input returnAddress : Word} {frame : Machine} {memory : Memory}

-- The setup loads the masks and the end pointer and clears the total. Each
-- mask is written as its `lui` and `addi` parts; `setupMasks` evaluates them.
def setupResult (state : Snapshot) : Snapshot :=
  { state with pc := 40, a1 := 0, a2 := 0x01010000 + 0x101, a4 := 0x33333000 + 0x333,
               a5 := 0x0f0f1000, a6 := state.a0 + 16, a7 := 0x55555000 + 0x555,
               t0 := 0x0f0f1000 + 0xffffff0f }

theorem setupMasks (state : Snapshot) :
    (setupResult state).a7 = 0x55555555 ∧ (setupResult state).a4 = 0x33333333 ∧
      (setupResult state).t0 = 0x0f0f0f0f ∧ (setupResult state).a2 = 0x01010101 :=
  ⟨rfl, rfl, rfl, rfl⟩

-- One iteration counts the word at a0 and adds the count to a1.
def wordResult (memory : Memory) (state : Snapshot) : Snapshot :=
  let word := memory state.a0
  let pairs := word - ((word >>> (1 : Nat)) &&& state.a7)
  let nibbles := ((pairs >>> (2 : Nat)) &&& state.a4) + (pairs &&& state.a4)
  let shifted := nibbles >>> (4 : Nat)
  let count := (((nibbles + shifted) &&& state.t0) * state.a2) >>> (24 : Nat)
  { state with pc := if state.a0 + 4 = state.a6 then 104#32 else 40#32
               a0 := state.a0 + 4, a1 := state.a1 + count, a3 := count, a5 := shifted }

variable (platform : Platform base frame input returnAddress memory)
include platform

private theorem setup (state : Snapshot) (atPC : state.pc = 0#32) :
    RV32.run 10 (sync base frame state) = some (sync base frame (setupResult state)) := by
  refine runStep (clearTotal platform state atPC) ?_
  refine runStep (loadPairsHigh platform _ rfl) ?_
  refine runStep (saveEnd platform _ rfl) ?_
  refine runStep (loadNibblesHigh platform _ rfl) ?_
  refine runStep (completePairsMask platform _ rfl) ?_
  refine runStep (completeNibblesMask platform _ rfl) ?_
  refine runStep (loadBytesHigh platform _ rfl) ?_
  refine runStep (loadMultiplierHigh platform _ rfl) ?_
  refine runStep (completeBytesMask platform _ rfl) ?_
  refine runStep (completeMultiplier platform _ rfl) ?_
  rfl

private theorem oneWord (state : Snapshot) (atPC : state.pc = 40#32)
    (inRam : state.a0 ∈ inputAddresses input) :
    RV32.run 16 (sync base frame state) = some (sync base frame (wordResult memory state)) := by
  refine runStep (loadWord platform state atPC inRam) ?_
  refine runStep (advancePointer platform _ rfl) ?_
  refine runStep (alignPairs platform _ rfl) ?_
  refine runStep (isolatePairHighs platform _ rfl) ?_
  refine runStep (countPairs platform _ rfl) ?_
  refine runStep (alignNibbles platform _ rfl) ?_
  refine runStep (keepLowerPairs platform _ rfl) ?_
  refine runStep (keepUpperPairs platform _ rfl) ?_
  refine runStep (countNibbles platform _ rfl) ?_
  refine runStep (alignBytes platform _ rfl) ?_
  refine runStep (sumNibbles platform _ rfl) ?_
  refine runStep (keepByteCounts platform _ rfl) ?_
  refine runStep (sumBytes platform _ rfl) ?_
  refine runStep (extractCount platform _ rfl) ?_
  refine runStep (addCount platform _ rfl) ?_
  refine runStep (branchOnEnd platform _ rfl) ?_
  rfl

private theorem finish (state : Snapshot) (atPC : state.pc = 104#32) :
    RV32.run 2 (sync base frame state) = some (sync base frame
      { state with pc := returnAddress - base, a0 := state.a1 &&& 255#32 }) := by
  refine runStep (returnByte platform state atPC) ?_
  refine runStep (returnToCaller platform _ rfl) ?_
  rfl

end SailRun


/-! ## Correctness of the linked Sail execution -/

section Correctness

-- With the setup masks, one iteration adds the SWAR count of the word.
theorem wordCount (memory : Memory) (state : Snapshot)
    (pairsMask : state.a7 = 0x55555555) (nibblesMask : state.a4 = 0x33333333)
    (bytesMask : state.t0 = 0x0f0f0f0f) (multiplier : state.a2 = 0x01010101) :
    (wordResult memory state).a1 = state.a1 + swar (memory state.a0) := by
  simp only [wordResult]
  rw [pairsMask, nibblesMask, bytesMask, multiplier]
  rfl

-- Four word counts of at most 32 fit in the returned byte.
theorem byteTotal (first second third fourth : Word)
    (firstBound : first.toNat ≤ 32) (secondBound : second.toNat ≤ 32)
    (thirdBound : third.toNat ≤ 32) (fourthBound : fourth.toNat ≤ 32) :
    ((0#32 + first + second + third + fourth) &&& 255#32).toNat =
      first.toNat + second.toNat + third.toNat + fourth.toNat := by
  rw [BitVec.toNat_and, show (255#32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_add, BitVec.toNat_zero]
  omega

-- The four input words agree with the bytes in Sail memory. Only a0–a7, t0,
-- and the two PC entries change.
theorem popcount128SwarSailCorrect (base : Word) (machine : Machine) (initial : Snapshot)
    (memory : Memory) (returnAddress : Word)
    (entry : machine = sync base machine { initial with pc := 0 })
    (platform : Platform base machine initial.a0 returnAddress memory) :
    ∃ final, RV32.run 76 machine = some final ∧
      final.regs.get? Register.PC = some returnAddress ∧
      (final.regs.get? Register.x10).map BitVec.toNat =
        some (inputBits memory initial.a0).cpop.toNat ∧
      final.mem = machine.mem ∧
      ∀ register ∉ [Register.PC, .nextPC, .x5, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
        final.regs.get? register = machine.regs.get? register := by
  let seed := setupResult { initial with pc := 0 }
  let first := wordResult memory seed
  let second := wordResult memory first
  let third := wordResult memory second
  let fourth := wordResult memory third
  let last := { fourth with pc := returnAddress - base, a0 := fourth.a1 &&& 255#32 }
  have setupStep := setup platform { initial with pc := 0 } rfl
  have firstStep := oneWord platform seed rfl (by simp [seed, setupResult, inputAddresses])
  have secondStep := oneWord platform first
    (by simp [first, seed, setupResult, wordResult])
    (by simp [first, seed, setupResult, wordResult, inputAddresses])
  have thirdStep := oneWord platform second
    (by simp [second, first, seed, setupResult, wordResult, BitVec.add_assoc])
    (by simp [second, first, seed, setupResult, wordResult, inputAddresses])
  have fourthStep := oneWord platform third
    (by simp [third, second, first, seed, setupResult, wordResult, BitVec.add_assoc])
    (by simp [third, second, first, seed, setupResult, wordResult, inputAddresses])
  have returned := finish platform fourth
    (by simp [fourth, third, second, first, seed, setupResult, wordResult, BitVec.add_assoc])
  refine ⟨sync base machine last, ?_, ?_, ?_, syncMem _, ?_⟩
  · refine (congrArg (RV32.run 76) entry).trans ?_
    rw [show 76 = 10 + (16 + (16 + (16 + (16 + 2)))) by decide,
      RV32.runAdd, setupStep, Option.bind_some, RV32.runAdd, firstStep, Option.bind_some,
      RV32.runAdd, secondStep, Option.bind_some, RV32.runAdd, thirdStep, Option.bind_some,
      RV32.runAdd, fourthStep, Option.bind_some, returned]
  · have pcRead := syncReadPC (base := base) (frame := machine) last
    have pc : base + last.pc = returnAddress := by
      change base + (returnAddress - base) = returnAddress
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    rw [viewPc, pc] at pcRead
    exact readReg_succ.mp pcRead
  · have read : Sail.readReg Register.x10 (sync base machine last) =
        .ok last.a0 (sync base machine last) := syncRead last (index := 10) (by decide)
    rw [readReg_succ.mp read, Option.map_some]
    have counts : fourth.a1 = 0#32 + swar (memory initial.a0) + swar (memory (initial.a0 + 4)) +
        swar (memory (initial.a0 + 4 + 4)) + swar (memory (initial.a0 + 4 + 4 + 4)) := by
      rw [wordCount memory third rfl rfl rfl rfl, wordCount memory second rfl rfl rfl rfl,
        wordCount memory first rfl rfl rfl rfl, wordCount memory seed (setupMasks _).1 (setupMasks _).2.1 (setupMasks _).2.2.1
        (setupMasks _).2.2.2]
      rfl
    have bound (word : Word) : (swar word).toNat ≤ 32 := by
      rw [swarCpop]
      exact BitVec.toNat_cpop_le word
    change some ((fourth.a1 &&& 255#32).toNat) = _
    rw [counts, byteTotal _ _ _ _ (bound _) (bound _) (bound _) (bound _),
      swarCpop, swarCpop, swarCpop, swarCpop]
    simp only [inputBits, BitVec.toNat_cpop_append]
    congr 1
    omega
  · intro register outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨pc, next, x5, x10, x11, x12, x13, x14, x15, x16, x17⟩ := outside
    refine syncFrame last register pc next ?_
    intro index member
    change index ∈ ([5, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 32)) at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ne.symm x5
    · exact Ne.symm x10
    · exact Ne.symm x11
    · exact Ne.symm x12
    · exact Ne.symm x13
    · exact Ne.symm x14
    · exact Ne.symm x15
    · exact Ne.symm x16
    · exact Ne.symm x17

#print axioms popcount128SwarSailCorrect

end Correctness


/-! ## ELF byte verification -/

def verifyElf (path : String) : IO Unit :=
  Riscfree.verifyElf path "popcount128_swar" (instructions.map Prod.fst)

end PopcountSwar

end Riscfree
