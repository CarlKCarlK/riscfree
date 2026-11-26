# What the RawVec insertion proof establishes

This note records what `rawVecU32InsertSailCorrect` (in
[proof/RawVec.lean](../proof/RawVec.lean)) depends on: its axioms and the
premises it assumes. It also lists what is still trusted.

## Axioms

`just prove` runs two axiom checks. `scripts/AxiomAudit.lean` accepts only an
allow-list for every declaration under `proof/`. `just axiom-paths` runs
`scripts/AxiomPaths.lean`, which explains each axiom the RawVec theorem reaches
and fails if the instructions the routine executes reach any axiom outside the
expected seven.

The theorem depends on 72 axioms. Its *statement* already reaches all 72,
through `run`, `step`, and Sail's `execute`. The proof therefore adds no axiom
beyond what the definitions it talks about already mention.

The 72 axioms fall into three groups.

### Lean's standard axioms (3)

`propext`, `Quot.sound`, and `Classical.choice` come from Lean's core
library and Mathlib lemmas. Every Mathlib-based development depends on them.

### Sail stubs that only other instructions reach (65)

The search is repeated with Sail's instruction dispatcher
`LeanRV32D.Functions.execute` blocked. It starts from the statement plus the
executors of the seven instruction formats the routine uses: `LOAD`, `STORE`,
`BTYPE`, `ITYPE`, `RTYPE`, `SHIFTIOP`, and `JALR`. That search no longer
reaches 65 of the 69 Sail stubs. They are:

- the 63 floating-point functions (`riscv_f16Add`, ..., `riscv_ui64ToF64`).
  Only the F, D, and Zfh executors call them.
- `cancel_reservation`, reached through `execute_STORECON` (`sc.w`), and
  `get_16_random_bits`, reached through the `seed` CSR read.

The other 6 of the 75 stubs in `LeanRV32D.RiscvExtras`, including
`plat_term_read` and `valid_reservation`, are not reached at all.

These dependencies are incidental to how Sail is written. `step` calls
`execute`, a single `match` over every instruction, so the definition of
`step` mentions every executor. Sail's Lean backend declares the external C
functions of the reference simulator, such as the SoftFloat library, with
`axiom`.

### Sail stubs on the executed path (4)

| Stub | Reached through | Why it does not affect this routine |
| --- | --- | --- |
| `load_reservation` | `execute_LOAD` → `vmem_read_addr` | Called only when the `res` flag is set (`lr.w`). Every `lw` passes `res = false`. |
| `match_reservation` | `execute_STORE` → `vmem_write_addr` | Called only for a store-conditional (`res && ...`). Every `sw` passes `res = false`. |
| `plat_term_write` | `execute_STORE` → `checked_mem_write` → `mmio_write` → `htif_store` | Writes a character to the host terminal when a store hits HTIF's `tohost`. The platform premise `htif_tohost_base = none` makes every store go to RAM. |
| `sys_enable_experimental_extensions` | `execute_BTYPE` → `jump_to` → `currentlyEnabled` → `hartSupports` | `hartSupports` is one `match` over all extensions. Only the experimental Zibi and Zvabd cases read the stub. `jump_to` asks about Zca, and only for a target with bit 1 set. Every target in this routine has bit 1 clear. |

### Meaning

None of these axioms is an assumption about the routine's correctness. Each
Sail stub is an opaque constant of a nonempty type, and the audit checks
that type is nonempty. A proof cannot inspect such a constant's value, so the
same proof term proves the theorem for every interpretation of every stub.
The theorem is therefore as strong as it would be with any concrete
floating-point library, reservation set, terminal, or experimental-extension
setting.

What the stubs *do* affect is the meaning of `step` on instructions this
routine never runs. Those instructions are outside the theorem.

## Nonvacuity

A conditional theorem whose premises can never hold together proves nothing.
[proof/RawVec/Nonvacuity.lean](../proof/RawVec/Nonvacuity.lean) shows the
premises of `rawVecU32InsertSailCorrect` can all hold at once.

- `Hypotheses` lists the theorem's premises in order. `Hypotheses.run`
  feeds them to the theorem, so the bundle cannot omit one.
- `modelHypotheses` builds a concrete machine and proves every premise for
  any index, value, capacity, and element contents, provided the length is at
  most 1000. The machine is in machine mode with `MPRV` clear, landing pads and
  HTIF disabled, `misa` = RV32IM, and one readable, writable, executable PMA
  region covering the address space. Memory holds the 30 linked instruction
  words at `0x1000`, the header at `0x3000`, and the elements at `0x4000`.
  The return address is `0x2000`.
- Five theorems instantiate the model, one per execution path:
  `appendSatisfiable` (14 instructions), `shiftSatisfiable` (inserting before
  two elements, 30 instructions), `invalidLengthSatisfiable` (5),
  `invalidIndexSatisfiable` (6), and `fullSatisfiable` (7). Each also proves the
  path's condition, status, and instruction count by `decide`. The matching
  `appendRuns`, ..., `fullRuns` apply the theorem to the model and conclude
  that the concrete machine returns to `0x2000` with the expected status.

The `Environment` premise quantifies over every memory that agrees on the
code bytes. The model meets it through `Environment.ofMachine`. That lemma
derives the instruction fetch from Sail's semantics (see
`proof/Riscfree/RV32/Fetch.lean`), so the model never assumes a fetch result.
The `entry` premise, `original = sync base original ...`, holds because
synchronizing a synchronized state again changes nothing (`syncSync`).

`lake build` checks these proofs, and `leanchecker` replays them through Lean's
kernel (`just kernel-check`). They use no axioms beyond the theorem's own.

## Remaining trusted base

The later sections of this note add to this list as the guarantee is
extended.

- Lean's kernel and the three standard axioms.
- The Sail RISC-V model as the specification of the processor, its
  translation to Lean by Sail's Lean backend, and the pinned configuration
  (no PMP entries, CLINT disabled, compressed instructions disabled).
- `Riscfree.RV32.step` and `run`: one uninterrupted Sail instruction per
  step, with no interrupt delivery or counters.
- GNU binutils (`nm`, `objdump`) locating the routine's bytes in the ELF
  for the linked-byte check.
