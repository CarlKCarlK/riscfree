<!-- TODO0 consider deleting this spec once the work below is implemented and released. -->

# Plan: from RawVec to RangeSetBlaze

The processor infrastructure is now strong enough to build on: Sail fetch
derived from `CodeImage`, machine-checked nonvacuity, axiom-path checks, and a
verified calling shim (see `docs/rawvec-assurance.md`). The next work returns
to data structures. Do not improve the processor infrastructure unless an
application below needs it. When one does, add the general lemma under
`proof/Riscfree/RV32/` rather than a workaround in the application.

## 1. Insertion into `RawVec<Pair>`

Status: proved (`proof/RawVec/PairInsert.lean`); the cost is recorded in
`docs/rawvec-pair-cost.md`. The board run of the extended demo is pending.

Verify `raw_vec_pair_insert`, the same generic `RawVec<T>::insert` in
`research/vec-ffi/linked/raw_vec.rs` with `T = Pair` (two `u32` words, 8 bytes).
The research report predicts the differences: `<< 3` instead of `<< 2` and one
extra load/store pair per moved element.

- Link it into the ESP32-C3 demo the way `raw_vec_u32_insert` is linked, and
  extend the board test and `just prove`'s ELF check to it.
- Follow the `AGENTS.md` rule: add a nonvacuity file covering all five paths.
- Reuse the u32 proof as far as practical. Where the u32 proof hard-codes the
  element size, factor out the size-independent parts (`Call`, the header
  checks, the copy-loop invariant, `unchanged`, the nonvacuity model) so that
  both proofs instantiate them.

**Measure the cost.** This item tests whether the workflow is practical. Record
in the commit message or a short note in `docs/`:

- the new lines of proof specific to the pair routine, the lines reused or
  generalized from the u32 proof, and any new `proof/Riscfree/` lemmas;
- elaboration time and peak memory for the new modules;
- what still had to be written by hand per instruction or per routine, and
  what could become generic (for example generated step lemmas).

## 2. Vector removal

Verify a bounded `remove` (shift the suffix left, decrement the length, return
the removed element or a status). Reuse whatever item 1 generalized, and record
the same cost measurements.

## 3. Minimal ordered map with linear search

Implement and verify the smallest ordered-map operations that RangeSetBlaze's
insertion needs, over the bounded pair vector, using linear search: lower-bound
lookup, insert, and remove. Keys are strictly increasing and unique. Keep the
`OrderedMap` experiment in range-set-blaze-vibe-validation as a test oracle,
not as the machine-code interface (see `research/vec-ffi/REPORT.md`).

## 4. Connect to the RangeSetBlaze insertion algorithm

Connect these operations to RangeSetBlaze's actual insertion algorithm
(`internal_add2` and `delete_extra`) and to its existing abstract Lean proof.
`research/vec-ffi/REPORT.md` already lists what bounded storage forces:
capacity exhaustion before the deletion pass, failure that leaves the
collection unchanged, and the byte-size and overflow premises.

## Deferred infrastructure

Do these only when an application above needs them:

- Give the popcount proofs a machine-mode corollary through
  `Platform.ofCodeImage`, with nonvacuity.
- Prove the converse of `Environment.ofMachine` (inverting Sail's `mem_read`),
  so the machine-mode theorem provably covers every case the original covers.
- Cover the shim's final `ret` to a halfword-aligned caller. This needs a Sail
  configuration with Zca and, in turn, a verified compressed caller.
- Make the shim proof independent of link layout. The shims are now linked
  next to the routines, so only a change to the shims or routines moves the
  `auipc`/`jalr` words and `routineOffset`. A proof parameterized by the
  offset would remove even that update.
- Prove the pair routine's calling shim, ideally by making `Shim.lean`
  generic over the routine it calls.
