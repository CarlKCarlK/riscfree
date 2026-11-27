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
`docs/rawvec-pair-cost.md`. The extended demo passed on the board on
November 26, 2026 (`research/vec-ffi/README.md`).

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

Status: proved for `u32` and `Pair` (`proof/RawVec/U32Remove.lean`,
`proof/RawVec/PairRemove.lean`) on the shared layer `proof/RawVec/Remove.lean`,
with nonvacuity on every path, and passed on the board and under a scratch copy
of the QEMU harness. The routine returns a status, not the removed element.
The cost is recorded in `docs/rawvec-remove-cost.md`.

- When the QEMU harness (branch `emulator-research`) reaches `main`, add
  `src/cases/raw_vec_remove.rs` to it, calling the two routines directly.

## 3. Minimal ordered map with linear search

Status: both bounds, insertion, and removal have Sail proofs and concrete
nonvacuity witnesses on the `sorted-map` branch. See
[the sorted-map proof and cost notes](../docs/sorted-map.md).

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
  generic over the routine it calls. The two removal shims would follow from
  the same generic proof.
- Share the call record, `Header`, and slot arithmetic between
  `RawVec/Insert.lean` and `RawVec/Remove.lean` (about 60 duplicated lines).
  This would change the insertion theorems' statements, so do it together with
  an update of `Compatibility.lean`.

## Deferred build-time work

Measured on the 32-thread development machine with everything built:
`just prove` took about 78 s before the removal proofs (axiom audit 18 s,
`axiom-paths` 47 s, linked-byte checks 8 s) and about 110 s with them. A clean build of the project's proofs takes about
1,116 s, of which `DecoderNormalForm` takes 949 s.

- Split each future routine's step lemmas into several independent modules
  that Lake can elaborate in parallel, as a convention for new routines. Today
  `RawVec/PairInsert/Instructions.lean` takes 75 s, and every edit to it or to
  a module it imports pays that cost. Leave the existing proofs as they are
  unless they are edited heavily.
- Speed up `just axiom-paths` (47 s), now the largest part of `just prove`.
- Remove `--reference` from `scripts/AxiomAudit.lean` once the module-by-module
  selection has agreed with it through a few more proof additions.
- Consider a separate fast `just check` for proof development if `just prove`
  becomes slow again.
- Speed up the decoder normal form (949 s). It runs only on rare rebuilds.

### Compositional stack-space bounds

- Prove the maximum additional stack space required by each verified machine-code routine, as a constant or a function of its inputs.
- Compose stack-space bounds across ordinary calls, sequential calls, and tail calls without reproving callees.
- Prove that execution never accesses stack memory outside the permitted region and restores the stack pointer on return.
- Establish a sufficient stack-space bound for the complete RangeSetBlaze insertion algorithm.
- Prefer statically proved bounds over runtime stack-overflow checks. Document insufficient stack space as outside the correctness theorem's premises.

The current sorted-map removal routine requires 16 additional bytes, independent of map size.