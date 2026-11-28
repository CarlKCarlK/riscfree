# Agent Guidance for riscfree

These rules add to the shared preferences in `~/.codex/AGENTS.md` and win where
they are more specific.

## Branches

- Work on `main`. Create or switch to another branch only when given
  permission.
- This is a fast-moving preliminary project: commit and push to `main` without
  asking once a change is complete and its self-review and checks pass.

## README credits

- Keep the Credits section of `README.md` up to date. When the project starts
  using a library, tool, model, or another project's technique or design,
  credit it there with a link and a short note on what riscfree uses it for.
  Remove a credit only when the project stops using it.

## Conditional theorems

- Every conditional correctness theorem needs a machine-checked nonvacuity
  result next to it. Bundle the theorem's premises, prove that the bundle
  invokes the theorem, and exhibit concrete states that satisfy the bundle on
  each execution path. Check the result with the kernel. See
  `proof/RawVec/Nonvacuity.lean` and `docs/rawvec-assurance.md`.
- When a theorem's statement changes, update its nonvacuity proof in the same
  change.

## Compressed instructions

- Prefer uncompressed RISC-V instructions (`riscv32im` rather than
  `riscv32imc`) throughout the verified code and, where practical, its callers.
  The pinned Sail model needs four-byte-aligned return addresses, which
  uncompressed callers always provide. The verified routines and the QEMU
  harness in `emulator/` are built this way.
- Investigate whether compressed instructions can be disabled before
  introducing additional calling shims.
- Document any exceptions and their effect on the formal guarantees, as
  `docs/rawvec-assurance.md` does for the ESP32-C3 shims.

## Verification rules

- **Legitimate states.** Cover all legitimate inputs and states.
  Do not strengthen preconditions merely to simplify proofs.

- **Resource exhaustion.** Cover all valid collection and scratch
  capacities, including zero. Succeed when sufficient resources exist;
  otherwise, return the specified error. Do not permit spurious OOM.

- **Memory safety.** Prove the validity of all reads and writes,
  not just preservation of unrelated memory. Cover failure paths
  as well as successful paths.

- **Repeated calls.** Successful operations must reestablish all
  invariants needed for subsequent calls, including allocation metadata.
  Prove that operation theorems compose.

- **Failure states.** Specify which invariants and operations remain
  valid after failure. If the caller must discard an object, prove
  that discarding it is safe.

- **Stack space.** Prefer statically proved, compositional stack-space
  bounds over runtime stack-overflow checks.

- **Specification review.** Review what each theorem states, not merely
  whether Lean accepts its proof. Look for unnecessarily restrictive
  premises, missing postconditions, and vacuous guarantees.

- **Pin the toolchain; verify the bytes.** Pin compiler versions
  and compilation settings to make machine code reproducible.
  Independently check that the linked machine code matches the proof.
