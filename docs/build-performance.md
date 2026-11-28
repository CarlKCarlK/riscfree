# Build and check times

This note records the November 27, 2026 build-speed work: three low-cost
changes to the proof build and its checks, measured before and after on the
32-thread development machine (62 GiB of memory, WSL 2). The verification
guarantees are unchanged: the same modules are built and replayed, the same
axiom-path checks run with the same flags, and a wrong decoding still fails
the build.

## Results

| Step | Before | After |
| --- | ---: | ---: |
| `just axiom-paths` (14 checks) | 267.4 s | 24.8 s |
| `lake build` after a change to `Riscfree.RV32.Decode` | 448.8 s | 285.9 s |
| `RangeInsert.DeleteTable` elaboration (in that build) | 324 s | 162 s |
| `RangeInsert.InsertTable` elaboration (in that build) | 284 s | 132 s |
| `just kernel-check` (16 jobs) | 236.1 s | 212.8 s |
| `just prove`, everything built | not measured | 92.8 s |

The `just prove` run that would have given the earlier figure was interrupted;
its axiom-path step alone took the 267.4 s above. The `lake build` rows rebuild everything that imports `Riscfree.RV32.Decode`
but not the decoder normal form, which only a change to
`Riscfree.RV32.DecoderNormalForm` or its imports rebuilds.

## The three changes

### One axiom-path process

`just axiom-paths` used to start one `lake env lean --run
scripts/AxiomPaths.lean` per checked module, 14 in all, each taking about
19 s. `scripts/AxiomPaths.lean` now takes several `--module` checks, imports
every named module once, and runs each check with exactly its old theorems,
`--block`, `--root`, and `--expect` arguments.

Combining the processes alone brought the time to 159 s, because most of each
check was not the import but the dependency searches through the same Sail
definitions. The script now caches each constant's direct uses for the whole
run. The cache depends only on the shared environment, so the searches return
what they did before: apart from the command lines, the new report is
identical to the old one, line by line.

Each check still fails on its own terms. A theorem must be in its check's
module's import closure, as when that module alone was imported. The script
runs every check, then fails if any failed. Removing an expected axiom, naming
a theorem from a module the check does not import, and naming an unknown
theorem each made the run fail, as did malformed arguments.

### Decoding without the kernel pre-check

`decodeByNormalForm` asked the kernel whether the decoder's normal form reduces
to the expected instruction, then added that same reduction as an auxiliary
theorem, which the kernel checks again. The first check lets `decode_word`
fall back to `simp`, because a failure inside the auxiliary theorem is reported
only after the tactic has finished.

`decode_word_normal_form` and `decode_table_normal_form` have no fallback, so
they now skip the first check. A wrong expected instruction is still an error,
now the kernel's rejection of the auxiliary theorem at the same tactic. Lean
then keeps the rejected auxiliary theorem as an axiom so that elaboration can
continue, but the build has already failed. The axiom audit would reject that
axiom in any case. `decode_word` keeps the pre-check and its fallback; the
popcount proofs, which use it, build in the same time as before.

### Longest replays first

`just kernel-check` started its replays alphabetically, so the three longest,
the decoder normal form, `RangeInsert.DeleteTable`, and
`RangeInsert.InsertTable`, started late. They now start first. The other
modules follow alphabetically, and each module still replays exactly once.

Editing a table of step lemmas, such as
`proof/RawVec/PairInsert/Instructions.lean`, now costs 110.3 s of rebuilding.
There is no earlier measurement from this session to compare it with.

## Kernel replay at other job counts

With the longest replays first:

| Jobs | Time | Peak memory in use | Above idle | Swapping |
| ---: | ---: | ---: | ---: | --- |
| 12 | 216.7 s | 25.3 GiB | 13.7 GiB | 88 KiB in, none out |
| 16 | 212.8 s | 28.4 GiB | 16.9 GiB | 124 KiB in, none out |
| 24 | 227.4 s | 35.2 GiB | 23.7 GiB | 268 KiB in, none out |
| 32 | 246.2 s | 42.8 GiB | 31.2 GiB | 108 KiB in, none out |

Memory in use is `MemTotal - MemAvailable`, sampled twice a second, with
11.5 GiB in use before each run. Swapping is the total of `vmstat`'s `si` and
`so` columns. All runs replayed all 102 modules without error.

The decoder normal form's replay sets the floor: 209 s at 16 jobs. More jobs
slow it down (242 s at 32) without shortening anything else that matters, so
16 stays the default.

## Deferred until after publication

- Split `RangeInsert.DeleteTable` and `RangeInsert.InsertTable` into modules
  that Lake can elaborate in parallel.
- Restructure the decoder normal form, the longest single build step and the
  floor on kernel replay.
