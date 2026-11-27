# What verifying `RawVec<Pair>` insertion cost

`raw_vec_pair_insert` is the second instance of the generic Rust
`RawVec<T>::insert` to be verified against Sail, after `raw_vec_u32_insert`.
This note measures what the second routine cost on top of the first, to judge
whether verifying more routines this way is practical.

## What the routine changed

The research report predicted `<< 3` addressing and one extra load and store per
moved element. Both hold. The compiler also chose different registers: the
length moved from `a3` to `a4`, the loop counter to `a6`, and the moved pair
passes through `a7` and `t0` with `t1` holding the next pointer. The routine
has 33 instructions (u32: 30). Append takes 15 instructions (u32: 14), and
inserting before `m > 0` elements takes `19 + 8m` (u32: `18 + 6m`). So the
per-instruction lemmas and their composition could not be reused unchanged.
What could be reused is everything that does not depend on the code.

## Lines of proof

Code lines exclude blank lines and comments.

| Part | Files | Code lines |
| --- | --- | ---: |
| Pair-specific | `PairInsert/Instructions.lean`, `PairInsert.lean`, `PairInsert/Nonvacuity.lean` | 1,026 |
| … of which also appear verbatim in the u32 files | | 708 (69%) |
| Shared, new | `Access.lean`, `Insert.lean`, `Model.lean` | 650 |
| New general lemmas under `proof/Riscfree/RV32/` | `WordAt.congr` (Store), `runCountdown` (Execution) | 23 |
| u32 files after the refactoring | `RawVec.lean` 624 → 421, `Instructions.lean` 448 → 360, `Nonvacuity.lean` 427 → 300 | −418 |
| One-time audit of the refactoring | `Compatibility.lean` | 222 |

The 650 shared lines replace 418 u32 lines. The other 232 lines generalize
them: the `Element` class with `Word` and `Pair` instances, slot arithmetic for
any element size, and a nonvacuity model for any code layout and element type.

The shared part covers what the plan asked to share:

- `Insert.Call`: the call's inputs, `valid`, `status`, `result`, slot
  addresses, and `unchanged`.
- `Insert.Header` and `Insert.Buffer`: the premises.
- `Insert.Progress`: the copy-loop invariant, with `initialProgress`,
  `Progress.source`, `Progress.copy`, and `finalWords`.
- `EnvironmentFor` and its machine-mode derivation, and `Platform.loadWord` /
  `storeWord`.
- `RawVec/Model.lean`: the nonvacuity machine, `Header` and `Buffer` on it,
  and code images placed by a table of words.
- `runCountdown`: induction over a countdown loop.

`Compatibility.lean` restates the four original u32 theorems (routine,
machine mode, and both shim theorems) verbatim against verbatim copies of the
original definitions, and derives each from the current theorem. So the
refactoring added no premise to them and weakened no conclusion. The u32 and
pair theorems reach the same 72 axioms, and `just axiom-paths` confirms that
each routine's executed instructions reach only the expected seven.

## Elaboration time and memory

`lake env lean` on each module, on this machine. Every module first loads the
Sail model, which accounts for about 5 s and 6.8 GB.

| Module | Time | Peak memory |
| --- | ---: | ---: |
| `RawVec.Access` | 5.4 s | 6.9 GB |
| `RawVec.Insert` | 5.7 s | 6.9 GB |
| `RawVec.Model` | 6.3 s | 7.0 GB |
| `RawVec.Compatibility` | 5.5 s | 6.9 GB |
| `RawVec.PairInsert.Instructions` | 76.7 s | 7.8 GB |
| `RawVec.PairInsert` | 5.6 s | 6.9 GB |
| `RawVec.PairInsert.Nonvacuity` | 5.4 s | 6.9 GB |
| `RawVec.Instructions` (u32, for comparison) | 69.0 s | 7.6 GB |
| `RawVec` (u32, includes `#print axioms`) | 15.4 s | 7.3 GB |

Nearly all the time goes into the 33 step lemmas, which unfold Sail's fetch,
decode, and execute. The routine-level proof, the shared layer, and the
nonvacuity proof each take about a second beyond the import.

## Kernel replay

`just kernel-check` replays every module's declarations through Lean's kernel
(`scripts/KernelCheck.lean`). Times are wall clock during a run with 16
parallel jobs, so they include contention:

| Module | Replay time |
| --- | ---: |
| `RawVec.PairInsert.Instructions` | 52.6 s |
| `RawVec.Instructions` (u32) | 48.7 s |
| `RawVec.PairInsert` | 6.9 s |
| `RawVec.PairInsert.Nonvacuity` | 6.9 s |
| `RawVec.Access`, `Insert`, `Model`, `Compatibility` | 6.6–8.0 s each |

All 31 modules replay without error. The whole check took 6 min 46 s one module
at a time and 2 min 48 s with 16 jobs (the default). The slowest single
module bounds that time, so more jobs or more machines would not shorten it
much.

### Memory

Each replay process reports a peak resident set (RSS) of 6.3–6.9 GB. Adding
those up suggests 16 jobs need over 100 GB. In fact the machine's physical
memory in use rose from 5 GB idle to a peak of 21 GB, and at least 40 GB of its
62 GB stayed available throughout.

The sum overestimates because most of each process's RSS is the Sail model's
`.olean` files. Lean maps them into memory read-only. Those pages belong to the
operating system's page cache, and every process that maps the same file
shares one physical copy, yet each process's RSS counts all of them. Only the
memory each replay allocates itself, roughly 1 GB per job here, is private.

## What still had to be written by hand

Per instruction (33 lemmas, about 330 lines, mechanical): each step lemma is
determined by its table entry and PC. A load needs a `Readable` and a
`WordAt` premise, a store a `Writable` premise and the stored memory, a branch
its condition, and everything else only the snapshot update. The lemmas were
adapted by hand from the u32 ones. Two pitfalls cost time: a store with a
nonzero offset must bind `Step.sw` with `have` before `exact`, or elaboration
times out, and a premise whose type is an `Element.Mapped` instance needs an
explicit ascription before `.1` and `.2` project from it. The table entries
were also written by hand from the disassembly, then checked by the decode
proof and by `just prove` against the linked bytes.

Per routine (about 320 distinct lines): the register snapshot, and the
composition of step lemmas into the header checks (`dispatch`), the loop setup,
one loop iteration (`oneCopy`), and the final stores (`finish`). Only `oneCopy`
and `finish` needed real thought: which register holds which address, and how
the two word stores of a pair make up one element store. The rest, including
the loop induction, the main theorems, the register-frame proof, and the
nonvacuity instance, are the u32 text with register names and counts
changed.

Candidates to generate or make generic next:

- The step lemmas, from the instruction table. Their shape follows the opcode.
- The decode-table entries, from the linked words. The decoder already
  computes them.
- `dispatch` and the main theorem's register-frame proof. Both follow the
  control flow and the snapshot's tracked registers, so a generic lemma or a
  tactic that chains step lemmas along a path would remove most per-routine
  composition.

## Outside the proof

- **Link layout.** Adding the pair routine moved the demo's code, so the
  verified u32 shim's `call` offset changed from 0xd60 to 0x1560. `build.rs`
  now assembles the shims into their own object and links it directly before
  the routines, so the offset (now 0xbc) depends only on those two objects.
  The shim table, `routineOffset`, and the shim's nonvacuity model were
  updated once.
- **Pair shim.** The demo calls the pair routine through a copy of the u32
  shim, which is not proved.
- **Kernel replay.** `leanchecker RawVec` replays every module whose name
  starts with `RawVec`, all in one process. Each module there builds its own
  environment, so with the new modules it ran out of memory.
  `scripts/KernelCheck.lean` replays exactly one module per process with
  `leanchecker`'s own replay function, and `just kernel-check` runs those
  processes in parallel.
- **Board test.** `just run-raw-vec` exercises both routines. The board run
  of this build is still to be done.
