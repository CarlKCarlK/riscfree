import RangeInsert.Nonempty.Extension
import RangeInsert.Nonempty.Contained.Nonvacuity

/-! A concrete caller extends the range 4..=9 with 10..=11. The
machine runs through the linked call with the updated cache and temporary
deletion header. -/

namespace Riscfree.RangeInsert.Nonempty.Extension.Nonvacuity

open LeanRV32D RV32IM
open Riscfree.RV32 Riscfree.RawVec
open Contained.Nonvacuity (base sp image modelCall contents initial machine ranges modelFrameMap)

private def call : Call := modelCall 3 ranges 10 11

private theorem modeled : Model.Modeled image (contents call) (machine call) :=
  Model.syncModeled _ base _

private theorem cacheWord (address : Nat) (value : Word)
    (low : 0x2500 ≤ address) (high : address + 4 ≤ 0x2508) (aligned : address % 4 = 0)
    (chosen : image.word (address / 4) = some value) :
    WordAt (machine call).mem address value := by
  rw [modeled.mem]
  have word := wordMemoryWord (Model.keys image (contents call))
    (Model.contents image (contents call)) address aligned (by
      intro byte inside
      simp only [Model.keys, image, List.mem_append, List.mem_range'_1]
      omega)
  rw [Model.contents, chosen, Option.getD_some] at word
  exact word

theorem adjacent :
    ExtensionPrefix base Model.returnTo (machine call) (initial call) call 15 0 := by
  obtain ⟨frame, map⟩ := modelFrameMap (length := 3) (old := ranges) (start := 10) (stop := 11)
    (by decide)
  refine ⟨frame, ⟨rfl, rfl, rfl⟩, map, by decide, by decide, by decide, by decide,
    by decide, ?_, cacheWord 0x2500 15 (by decide) (by decide) (by decide) (by decide),
    cacheWord 0x2504 0 (by decide) (by decide) (by decide) (by decide),
    Model.readable modeled (by decide) (by decide), Model.readable modeled (by decide) (by decide),
    Model.writable modeled (by decide) (by decide), Model.writable modeled (by decide) (by decide),
    Model.writable modeled (by decide) (by decide), ?_, ?_, ?_⟩
  · intro byte _ high
    change byte < 0x2500 + 8 at high
    exact Or.inl (show byte < 0x2800 - 48 by omega)
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact Model.writable modeled (by decide) (by decide)
  · intro byte _ high
    change byte < 0x1208 + 4 * 109 at high
    change (byte < 0x2500 ∨ 0x2500 + 8 ≤ byte) ∧ (byte < 0x4000 + 4 ∨ 0x4000 + 8 ≤ byte)
    omega
  · intro byte low _
    change 0x4000 ≤ byte at low
    exact Or.inr (show 0x2500 + 8 ≤ byte by omega)

theorem adjacentReachesHelper :
    ∃ state : Empty.Snapshot,
      run (58 + call.search.count .upper) (machine call) =
        some (sync base { (machine call) with mem := (extensionStored (initial call) call 15 0
          (Empty.pushed (machine call).mem (initial call))) } state) ∧
      ExtensionCalling base (initial call) call state := by
  obtain ⟨state, reached, arguments⟩ := adjacent.toHelper
  have initialRun := congrArg (run (58 + call.search.count .upper)) adjacent.frame.entry
  exact ⟨state, initialRun.trans reached, arguments⟩

end Riscfree.RangeInsert.Nonempty.Extension.Nonvacuity
