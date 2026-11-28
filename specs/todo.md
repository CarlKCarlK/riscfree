<!-- TODO0 consider deleting this spec once the work below is implemented and released. -->

# Medium article: Before publication

The goal is a technical Medium article, not an academic research paper
or a comprehensive verification framework.

This checklist governs project priorities across development sessions.

## Phase 1: Establish and merge the verified baseline

- [x] Strengthen the header-preservation postcondition (H1). The writable header region is now only the length word, and `InsertionPremises.run` states that the data pointer and capacity are preserved.
- [x] Correct the documented dependency revision.
- [x] Document that the conservative scratch-capacity premise (M1) is sufficient but not necessary. Strengthening the theorem is deferred to the OOM work.
- [x] Resolve remaining merge-blocking review findings. The review listed H1, the dependency revision, and M1 as merge-blocking.
- [x] Pass full proof build, kernel replay, and axiom audit. On merged `main` (November 27, 2026): `just prove` passed, and `just kernel-check` replayed all 102 modules.
- [x] Merge `production-api` and repin riscfree. It fast-forwarded the dependency's `main` to `09f0d01`, the revision riscfree already pinned, so no repin was needed.
- [x] Obtain approval and merge `range-insert`.

## Phase 2: Additional verification

- [ ] Return OOM status and prove failure semantics.
- [ ] Prove that discarding the set after OOM is safe.
- [ ] Verify zero production overhead from `Infallible`.
- [ ] Prove correctness over a sequence of successful insertions.
- [ ] Connect cardinality to `ncard`.
- [ ] Prove compositional stack-space bounds, including the complete range-insertion routine.
- [ ] Prove the firmware shim. Do this after the OOM work, since the calling convention or return-value handling may change.
- [ ] Add a negative test for `checkCalls`.

## Phase 3: Testing and reproducibility

- [ ] Pass ESP32-C3 hardware tests on the final implementation. The pre-OOM baseline passed on November 27, 2026, including `Range insertion PASS`; rerun after the OOM changes.
- [ ] Integrate with the QEMU harness.
- [x] Pin the Rust toolchain. `rust-toolchain.toml` pins rustc 1.100.0, which built the verified binaries; `just prove` passed with it on November 27, 2026.
- [ ] Run `just prove` in CI. On a fresh checkout, `just prove` fails because `scripts/check_proof_sources.py` runs before `lake build` has fetched the range-set-blaze-vibe-validation dependency. Fix this ordering when adding CI.
- [ ] Add Lean 4.28 to the mathematical repository's CI matrix.

## Infrastructure

- [ ] Speed up proof builds and axiom audits where there is low-hanging fruit.

Improve reusable proof infrastructure only as needed by the approved work.

## Article preparation

- [ ] Measure machine-code size and instruction counts.
- [ ] Report provable maximum stack usage.
- [ ] Summarize proof reuse and development costs.
- [ ] Describe AI successes, failures, and human interventions.
- [ ] Document trusted assumptions and verification limitations.
- [ ] Provide reproducible build and verification commands.

## Scope and workflow rules

- This section governs priorities and supersedes conflicting requirements elsewhere in this document.
- Complete Phase 1 before undertaking Phase 2.
- Do not expand the project without approval.
- Existing TODO items outside this list are deferred until after publication.
- In particular, defer arbitrary-backend correctness, range removal, and general-purpose proof automation.
- Preserve the existing bounded-backend OOM specification: no rollback, transactional semantics, or preliminary capacity checks.
- Mark items complete only after verifying their completion.
- Record significant results, measurements, and lessons as the work progresses, rather than reconstructing them during article preparation.
- Keep this checklist current across agents and development sessions.
- This is a project-wide plan, not an assignment to complete in a single session.


- [ ] Cover all legitimate collection and scratch capacities, including
      zero, and prove that OOM is never returned spuriously.
- [ ] Establish the validity of all memory accesses, including reads,
      on both successful and failed executions.

---

# Detailed specifications, project history, and deferred work

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
nonvacuity witnesses, merged into `main`. See
[the sorted-map proof and cost notes](../docs/sorted-map.md).

Implement and verify the smallest ordered-map operations that RangeSetBlaze's
insertion needs, over the bounded pair vector, using linear search: lower-bound
lookup, insert, and remove. Keys are strictly increasing and unique. Keep the
`OrderedMap` experiment in range-set-blaze-vibe-validation as a test oracle,
not as the machine-code interface (see `research/vec-ffi/REPORT.md`).

## 4. Connect to the RangeSetBlaze insertion algorithm

Status: proved and merged into `main` on November 27, 2026. See
`docs/range-insert.md`. `InsertionPremises.run` in
`proof/RangeInsert/Theorem.lean` covers the empty, contained, extension, and
fresh paths. It gives the exact instruction count, the ABI return, and
preservation of registers and memory outside the writable regions. It also
proves that the stored map and cache represent the production model
`internalAddProduction`, whose result is the union with its cardinality
cached. Nonvacuity witnesses exercise every successful branch.

Connect these operations to RangeSetBlaze's actual insertion algorithm
(`internal_add2` and `delete_extra`) and to its existing abstract Lean proof.
`research/vec-ffi/REPORT.md` already lists what bounded storage forces:
capacity exhaustion before the deletion pass, failure that leaves the
collection unchanged, and the byte-size and overflow premises.

The ESP32-C3 firmware test passed on the board on November 27, 2026,
including `Range insertion PASS`. The firmware shim's formal proof remains
open (Phase 2, after the OOM work).

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
The range-insertion helper's nested calls use at most 112 bytes for the uncompressed routines.

### Backend-independent algorithm correctness

- Specify the mathematical contracts of the collection traits, including ordered lookup, lazy traversal, insertion, removal, and capacity exhaustion.
- Prove that the shared RangeSetBlaze insertion algorithm is correct for any backend satisfying these contracts.
- Establish that the verified bounded sorted-map backend satisfies the contracts.
- Investigate how to establish that the production `BTreeMap` and `Vec` backend satisfies the same contracts.
- Distinguish backend-independent algorithm correctness from the machine-code correctness of a particular compiled instantiation.

Explore whether this approach generalizes to other existing Rust algorithms through the substitution of simpler, verification-friendly collection backends.

### range-set-blaze-vibe-validation

- Leave its `python` branch alone for now. Later, review whether its work should be merged. It is another example of the value of having a single mathematical proof library serving multiple implementations.
- Add a second Lean version (4.28, which riscfree pins) to its CI matrix, so that future mathematical improvements cannot inadvertently break riscfree compatibility.

### Proof automation

- Consider incorporating a generalized version of the instruction-lemma generator into riscfree. It currently lives in `~/deldir/riscfree-range-insert/generate_delete_extra_steps.py`. Generating 111 instruction proofs with only one systematic correction is strong evidence that this machinery could be reusable. The generated proofs still pass through Lean's kernel, so we need not trust the generator for logical correctness, but we still inspect what its theorems state.
- Automate proofs of conventional function prologues and epilogues. Compiler-generated stack management is highly mechanical. Ideally, a future riscfree tool could recognize these instruction sequences and automatically generate their frame contracts and proofs. This would complement the instruction-lemma generator.

### Bounded-backend failure

- [ ] **Return OOM status from the bounded range-insertion backend.** After completing the current machine-code proof, change the generic collection interface to propagate allocation failures via `Result`, preferably with an associated error type. The production `BTreeMap`/`Vec` backend uses `Infallible` and retains its existing allocation-failure behavior. The bounded RISC-V backend returns an OOM status instead of trapping when either the map or the deletion-key buffer runs out of capacity.
  - On success, retain the existing correctness guarantees.
  - On OOM, guarantee memory safety, stack restoration, and preservation of unrelated memory. The caller must discard the set; its contents, canonical representation, and cached cardinality need not remain valid.
  - Do not introduce rollback, transactional semantics, or preliminary capacity checks.
  - Verify that monomorphization and inlining eliminate the OOM return paths in production, with no runtime overhead.
  - Update the machine-code proofs and tests to cover both successful execution and OOM returns.

Consider tracking all 31 writable integer registers in a common snapshot structure for future projects, provided doing so doesn't substantially increase Lean's elaboration costs.

OOM Spec addition:
- Cover all valid map and scratch-buffer capacities, including zero.
- Remove sufficient-capacity premises from the top-level theorem.
- Prove that insertion succeeds whenever the actual intermediate
  storage requirements are met and returns OOM otherwise.
- Do not permit spurious OOM returns.
