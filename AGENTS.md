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
