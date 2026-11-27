# What verifying `RawVec<T>` removal cost

`raw_vec_u32_remove` and `raw_vec_pair_remove` are the two instances of one
generic Rust `RawVec<T>::remove`
([raw_vec_remove.rs](../research/vec-ffi/linked/raw_vec_remove.rs)). They are
the third and fourth RawVec routines verified against Sail, after the two
insertion routines. This note records what they cost on top of insertion, in
the same terms as [rawvec-pair-cost.md](rawvec-pair-cost.md).

## The routine

The interface is `remove(vec, index) -> status`. It returns 0 after removing
the element, 2 if `index >= length`, which includes every index of an empty
vector, and 3 if `length > capacity`. The length is checked first. Neither
rejection writes memory. The removed element is not returned, because the
caller owns the buffer and can read `data[index]` first. Returning it would
add a third written location and its separation premises to every theorem.

At `opt-level=1` the compiler turned the loop into a pointer walk with no
calls and no stack frame. The two instances differ only in the shift (2 or 3),
the pointer step (4 or 8), and one extra load and store for the pair's second
word. Unlike the two insertion routines, they use identical registers
(`a0`–`a4`, plus `a5` for the pair).

| Path | `u32` | `Pair` |
| --- | ---: | ---: |
| Invalid length | 5 | 5 |
| Invalid index (including empty) | 6 | 6 |
| Remove the last element | 9 | 9 |
| Remove before `m > 0` elements | `15 + 4m` | `15 + 6m` |
| Static instructions | 23 | 25 |

## Lines of proof

Code lines exclude blank lines and comments. "Verbatim" counts lines that
also occur, after trimming, in the files named. Short lines such as `omega`
or `intro byte outside` count, so the figure measures copying, not
understanding.

| Part | Files | Code lines | Verbatim |
| --- | --- | ---: | ---: |
| Shared, new | `Remove.lean` | 219 | 128 (58%) from `Insert.lean` |
| `u32` instance | `U32Remove/Instructions.lean`, `U32Remove.lean`, `U32Remove/Nonvacuity.lean` | 768 (280 + 347 + 141) | 484 (63%) from the insertion files |
| `Pair` instance | `PairRemove/Instructions.lean`, `PairRemove.lean`, `PairRemove/Nonvacuity.lean` | 825 (306 + 377 + 142) | 666 (80%) from the `u32` removal files |
| Model generalization | `Model.lean` | 207 → 259 | |
| Insertion nonvacuity call sites | `Nonvacuity.lean`, `PairInsert/Nonvacuity.lean` | 17 lines changed | |
| New general lemmas under `proof/Riscfree/RV32/` | | 0 | |

So the first removal routine cost about 1,000 lines, 219 of them shared, and
the second about 160 lines that are not copied from the first.

Reused without change:

- `Access.lean`: `Readable`, `Writable`, `EnvironmentFor`,
  `Environment.ofMachine`, `Platform.loadWord`, `Platform.storeWord`, and
  `pcReadReturned`.
- `Insert.lean`: the `Element` class with its `Word` and `Pair` instances, the
  element frame lemmas (`wordStoreElement`, `elementStoreWord`,
  `elementStoreElement`), `outsideCode`, `storeKeepsCode`, `elementKeepsCode`,
  `ofWordNat`, and `counterPrev`.
- `proof/Riscfree/RV32/`: every step lemma used (`Step.lw`, `Step.sw`,
  `Step.addi`, `Step.add`, `Step.slli`, `Step.bgeu`, `Platform.bne`,
  `Platform.ret`), the `advance` tactic, `decode_table_normal_form`,
  `runCountdown`, `runStep`, `runAdd`, and `syncFrame`.
- `Model.lean`: the model machine, `tableImage`, and `modelMode`, after the
  generalization below.

Written new in `Remove.lean`: the call record, `valid`, `status`, `result`,
`unchanged`, `Header`, `Buffer`, slot arithmetic, the forward copy-loop
invariant `Progress` with `copy` and `source`, and `finalWords`. About 60 of
its lines (the call record, `Header`, and slot arithmetic) duplicate insertion's
almost exactly. Sharing them would change the insertion theorems' statements,
so it is left as a recorded follow-up (`specs/todo.md`). Two lemmas are new in
kind. `slotShift` computes an element address modulo `2 ^ 32` with no bound.
`slotReached` shows the loop's pointer meets the end pointer exactly at the
length, even when `data + size * length` is `2 ^ 32` and the end pointer wraps
to 0.

The model was generalized from insertion calls to a `Contents` record
(length, capacity, elements), with `Contents.ofInsert` and
`Contents.ofRemove`. The per-element facts that were inline in insertion's
`modelBuffer` became `modelElement`, `elementReadable`, and
`elementWritable`, which both buffers use. Insertion's `modelBuffer` lost a
premise (`valid`) that no step used.

## Elaboration time and memory

`lake env lean` on each module, one at a time. Loading the Sail model accounts
for about 5 s and 6.8 GB of each.

| Module | Time | Peak memory |
| --- | ---: | ---: |
| `RawVec.Remove` | 8.9 s | 6.9 GB |
| `RawVec.Model` | 7.4 s | 7.0 GB |
| `RawVec.U32Remove.Instructions` | 65.4 s | 7.7 GB |
| `RawVec.U32Remove` | 5.9 s | 6.9 GB |
| `RawVec.U32Remove.Nonvacuity` | 5.8 s | 6.9 GB |
| `RawVec.PairRemove.Instructions` | 61.8 s | 7.5 GB |
| `RawVec.PairRemove` | 5.5 s | 6.9 GB |
| `RawVec.PairRemove.Nonvacuity` | 5.2 s | 6.9 GB |
| `RawVec.PairInsert.Instructions` (for comparison, same run) | 79.8 s | 7.8 GB |

As with insertion, nearly all the time goes into the 48 step lemmas. In an
earlier, quieter run the two `Instructions` modules took 54 s and 65 s, so
these times vary by about 20% with machine load.

## Kernel replay

`just kernel-check` (16 jobs) replayed all 38 modules without error in
3 min 14 s of wall-clock time. The QEMU and board runs overlapped it, so the
times include contention. The new modules took 41 s (`U32Remove.Instructions`),
57 s (`PairRemove.Instructions`), and 7–17 s each for the rest.

## Assurance checks

- `scripts/check_proof_sources.py`: 38 files, no forbidden shortcuts.
- `scripts/AxiomAudit.lean`: 2,697 declarations use the same 72 axioms as
  before (Lean's 3 and 69 Sail stubs with nonempty types). The allow-list did
  not change.
- `just axiom-paths`: both removal theorems reach 72 axioms from their
  statements, and their executed instructions reach exactly the expected 7.
- `just prove`: the linked bytes of both removal routines match the tables
  that Sail decodes, and the verified insertion shim still calls
  `raw_vec_u32_insert` 188 (0xbc) bytes ahead.

## Difficulties

How much went wrong, as a measure of what a third operation would cost:

- **Step lemmas: none.** All 48 step lemmas and both decode tables
  elaborated on the first attempt. The u32 lemmas were adapted from the
  insertion lemmas by opcode, and the pair lemmas from the u32 removal
  lemmas.
- **The pair instance: none.** The routine proof and nonvacuity module were
  derived from the u32 ones by substitution (counts, PCs, shift, the snapshot's
  `a5`) plus a new `oneCopy`. Both elaborated on the first attempt.
- **The u32 routine proof: three rounds.** A header-offset `rw` needed the
  intermediate `have` that the insertion proofs use. The dispatch must split
  on the path before chaining steps, because the step count depends on it.
  `runCountdown` states its counter as `0 + remaining`.
- **`Remove.lean`: one kernel failure.** `omega` on
  `(length + 0xffffffff) % 2 ^ 32` produced a term too deep for the kernel
  ("deep recursion detected"). Reusing insertion's `counterPrev`, which the
  kernel checks by computation, fixed it.
- **The model: five rounds.** Coercions from both call types to `Contents`
  did not fire, because the expected type `Contents ?α` still had a
  metavariable. Explicit `Contents.ofInsert` calls replaced them.
- **Link layout.** `rustc` orders function sections alphabetically, so
  `raw_vec_pair_remove` would have landed between the verified shim and
  `raw_vec_u32_insert` and moved the shim's call offset. Compiling removal into
  its own object, linked after the insertion routines, avoided that, and
  `just prove` checks it.

## What could be generated

Recorded, not built:

- **Step lemmas from the instruction table.** All 48 followed one template per
  opcode: a load needs `Readable` and `WordAt` premises, a store a `Writable`
  premise and the stored memory, a branch its condition with both targets
  computed from the table, and the rest only the snapshot update. Every one
  elaborated on the first attempt, which suggests the template is complete for
  these seven formats.
- **Decode-table entries from the linked words.** `decode_table_normal_form`
  already checks them, and here every entry was right the first time, so a
  generator only needs to print what the decoder computes.
- **Per-routine composition.** The two removal proofs differ in about 160
  lines: constants (PCs, the body length, the shift) and the loop body.
  `dispatch`, `setupLoop`, `finish`, `success`, the loop induction, the main
  theorems, and the register-frame proof could be one proof over a record of
  those constants plus a per-element `oneCopy`. That record would also cover
  the two insertion proofs, whose structure is the same with different
  registers.
- **Nonvacuity modules.** 88% of the pair removal module is the u32 one. A
  module per routine needs only the table length, the element type, and the
  witnesses.

## Tests

`src/cases/raw_vec_remove.rs` is one generic test case, written for both
element types. It takes the routine as a function pointer, so the ESP32-C3
demo passes the calling shims and a harness without compressed instructions
can pass the routines. Its seven calls reach every path, including an empty
vector, and it checks the guard elements on both sides of the buffer and the
vacated slots' stale values. `Pair` elements are `(k, 10k)`, so a routine that
moved only keys would fail.

- **ESP32-C3 (revision v0.4), November 26, 2026:** all four RawVec checks
  passed, including the pair insertion demo, which had not been run on the
  board before. The output is in `research/vec-ffi/README.md`.
- **QEMU 6.2:** a scratch copy of the `emulator-research` branch's harness,
  outside the repository, ran the same case file against both routines
  linked directly, and both passed. The byte check confirmed those routines
  match the recorded words. Adding the case to the harness itself is left
  until that branch merges (`specs/todo.md`).
