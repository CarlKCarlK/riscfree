# RangeSetBlaze range insertion experiment

One Rust algorithm runs over the production collections, `BTreeMap` and
`Vec`, and over the bounded sorted map and RawVec. The extracted operations
are `internal_add_baseline`, `internal_add2`, and `delete_extra` from
RangeSetBlaze revision `6ae67451`. [Production Rust source](https://github.com/CarlKCarlK/range-set-blaze/blob/6ae67451fc57f7b0c91692ff17c4d53b284dbec7/src/set.rs)

## Collection operations and mathematical correspondence

| Operation | Production collections | Bounded collections |
| --- | --- | --- |
| Mutable predecessor at or before the new start | `range_mut(..=key).next_back()` | Verified upper bound, then borrow the preceding slot |
| Lazy mutable suffix from the selected start | `range_mut(key..)` | Verified lower bound, then a live-suffix slice iterator |
| Insert a new range | `BTreeMap::insert` | Verified sorted-map insertion |
| Collect a deletion key | `Vec::push` | Verified word insertion at the scratch RawVec's length |
| Remove a collected key | `BTreeMap::remove` | Verified sorted-map removal |

The scan holds a mutable reference to the selected range's end, lazily
walks successors with the original end as the adjacency limit, subtracts
each accepted successor's cardinality, and appends its key to the temporary
buffer. The loop stops at the first gap. It then adds the extension length,
updates the selected end, and removes the collected keys in order after the
map borrow ends. The fresh path adds the incoming inclusive length
after the deletion pass. The extension path adds the predecessor's
extension length before that pass. The explicit loop implements the
production `map_while(...).collect()` stopping and append order.

The mathematical proofs come from range-set-blaze-vibe-validation, a
pinned Lake dependency (commit `09f0d01d` on its `main`), so riscfree
keeps no copy of them. That commit exposes the fresh and extension branches of the
production model (`internalAddProduction_fresh` and
`internalAddProduction_extension`), which `Theorem.lean` uses. The
library is in the `RangeSetBlazeValidation` namespace, because Sail also
declares a top-level `IntRange`. Its sources build with both its own Lean 4.33.1 and
riscfree's Lean 4.28.0-rc1, without separate copies. riscfree requires it
after Pico FV, so Pico FV's Mathlib and Sail revisions are the ones
resolved. The source check, axiom audit, and kernel replay include the
dependency modules that riscfree imports (`RangeSetBlaze.Basic` and
`RangeSetBlaze.AlgoC`). The production fixed-end model also lives
there, in `AlgoC.lean`. Algo C's `internalAddCLen` uses a growing
adjacency limit. The fixed-end correspondence proves that
after a successor grows the end, canonical spacing puts the rest of the
suffix beyond the growing end as well. Therefore the two scans test and
accept the same successors and thread the same cached lengths.
`internalAddProduction_correct` proves union and cached cardinality for
the abstract production model. Its result is a canonical list by
construction. `Arithmetic.lean` proves the unsigned endpoint comparisons
and widened inclusive width, including an inclusive length of `2^32`.
It also establishes the exact two-word addition and subtraction identities
used in the RV32I bookkeeping.
[Mathematical proof](https://github.com/CarlKCarlK/range-set-blaze-vibe-validation/blob/09f0d01d148f2c18e86fe55ff543c8851a177842/RangeSetBlaze/AlgoC.lean)

## Storage and machine costs

Let `n` be the original number of ranges and `k` the number of collected
successors. Successful insertion requires capacity `n+1` on the fresh
path and `n` on the other paths. The deletion buffer needs at least
`k` slots. Otherwise the bounded routine returns `FULL`, with no
preliminary capacity check or rollback. Scratch exhaustion can occur
after writes to the map or cached length, so the caller must discard the
set after `FULL`. `RangeInsert.Bounded` proves both outcomes (see
[Phase 2 bounded execution theorem](#phase-2-bounded-execution-theorem)).

With linear sorted-map search and shifting, the fresh or extension path
takes `O((k+1)(n+1))` instructions. Each deletion performs a new linear
search and shifts a suffix, so the worst case is quadratic. The forward
iterator itself takes `O(k+1)` steps. Appending a key takes constant time.
The contained case uses only the predecessor search, and the empty input
needs no search.

With rustc 1.100.0, the trapping version's linked entry had 109
instruction words and its deletion helper 117. The bounded version has 116
and 120, with the same 48-byte frames. The following QEMU counts, taken on
the trapping version, (`-singlestep -d exec,nochain`) include calls through the
whole stack, starting at the first instruction of `range_insert_u32` and
ending at its return. They are execution measurements for the shared test
inputs. Sail independently proves the empty-input count.

| Shared case | Executed instructions |
| --- | ---: |
| Empty input range | 19 |
| Empty map, singleton | 174 |
| Strictly contained | 55 |
| Equal-start contained | 55 |
| Extends predecessor by adjacency | 145 |
| Fresh insertion absorbs first stored range | 313 |
| Fresh insertion before all ranges | 199 |
| Fresh insertion after all ranges | 204 |
| Fresh insertion adjacent to a successor | 364 |
| Predecessor extension absorbs two successors | 393 |
| Entire u32 domain into empty map | 173 |
| Entire u32 domain by extending a predecessor | 248 |
| Contained at u32::MAX | 55 |

From the emitted prologues and call graph, reserve 112 bytes below the
uncompressed caller's stack pointer. The entry and deletion helper each
reserve 48 bytes. While both are on the stack the deepest callee,
`sorted_map_remove`, reserves another 16. The 32-byte sorted-map
insertion frame is on the fresh path before entering the helper.
The searches and RawVec callees use no additional stack. The compressed
ESP32-C3 caller uses a 16-byte uncompressed shim so the routine sees a
word-aligned return address. With that shim the caller needs 128 bytes.
These call-tree figures are from the linked disassembly. A firmware build
with `-C target-feature=-c` still has `EF_RISCV_RVC` set when built with the
current ESP32-C3 target and prebuilt Rust libraries. The machine theorem
begins at the uncompressed routine's entry.

For the empty-input path, `RangeInsert.Empty.Premises.run` proves that 19
instructions reach the aligned return address, preserve all registers
except the program counters, and leave memory unchanged outside the
48-byte frame. The concrete witness in `Empty/Nonvacuity.lean` satisfies
the mapping and stack premises and applies the theorem.

For a nonempty input whose end is already covered by its predecessor,
`RangeInsert.Nonempty.ContainedPremises.run` proves that exactly
`44 + c` instructions reach the return address, where `c` is the
verified upper-bound search's count (`7 + 5r` when the scan stops at
rank `r`, or `6 + 5n` when it passes all `n` entries). The run preserves
every register except PC, nextPC, and a0–a5, including the stack pointer
and the callee-saved registers. It leaves every byte outside the 48-byte
frame unchanged, so the map and the cached length are untouched. The
shared prefix (`Nonempty/Predecessor.lean`) covers the prologue, the
nonempty branch, the argument moves, and the call to
`sorted_map_upper_bound`. It composes `sortedMapSearchSailRun` at the
linked offset `-0x208` rather than re-proving the search. The path
premises are a positive rank, a nonnull data pointer, and a predecessor
end at or after the input end. The strict-gap test is proved false from
these premises, including when the predecessor ends at `u32::MAX`.

`Nonempty/Correspondence.lean` connects this path to the abstract model.
When the live entries, read in order, are a canonical set's ranges
(`Represents`), the upper-bound rank selects the same predecessor as the
model's `takeWhile`/`getLast?` split. `containedModel` then shows that
`internalAddProduction` returns the set and the cached count unchanged,
and `containedCorrect` shows that this is the union with the input and
the cardinality. `Contained/Nonvacuity.lean` builds concrete machines for
a strictly contained input (56 instructions), an input that starts at its
predecessor's start (61), and a one-entry map whose range ends at
`u32::MAX` (55). The 55-instruction count matches the QEMU measurement
for the shared one-entry cases. The kernel applies the run theorem to all
three, and `Represents` and `containedModel` hold for the same maps.

## Proof size and measurements

The abstract proof uses about 2,090 lines of Lean from the mathematical
dependency. The production-model work added there covers the fixed-end
correspondence, the covered branch, the finite-domain cardinality bound,
and concrete cases. riscfree keeps the machine arithmetic and the
machine-to-model correspondence. The two linked
tables have about 300 lines. The linked proof
reuses the existing decoder normal form, register snapshots, memory and
stack lemmas, and the RawVec model machine. The decoder cache was copied
into the worktree and the normal form was reused.

The mathematical modules built in 4.6 seconds with a peak RSS of about
2.0 GiB on this machine. Independent kernel replay took about 2–3 seconds
per mathematical module. The table builds took 233 seconds for the entry
and 269 seconds for the deletion helper. Peak RSS for that build was about
7.9 GiB with the existing decoder cached. The empty-path execution, frame,
and witness modules each elaborated in about 4–7 seconds. Peak RSS for
the build was about 6.9 GiB. The contained path adds about 1,000 lines in
five modules (steps, shared prefix, run, model correspondence, and
witnesses). Each elaborated in about 4–8 seconds, reusing the cached entry
decode table, the search theorem, and the empty path's frame lemmas.

## Checks and remaining scope

- `just test-range-insert-host` exercises the production adapter over
  16,384 small-domain cases and the endpoint extremes.
- `just emulate-raw-vec` runs all shared cases under QEMU, including
  `FULL` returns at zero capacity, a full map whose final set would fit,
  both resources short, scratch exhaustion on each modifying path (also
  after one successful append), and an exact fit. Every case checks that
  the header's data pointer and capacity are unchanged and the length is
  within capacity. `just test-range-insert-exhaustion` runs these cases.
- `just build-raw-vec` checks the ESP32-C3 ELF. After flashing with
  `just run-raw-vec`, the firmware should print `Range insertion PASS`.
  The physical ESP32-C3 run passed on November 27, 2026, printing
  `Range insertion PASS`. That run goes through the compressed caller's
  firmware shim, whose formal proof is still pending.
- The ELF checks compare both bounded range insertion symbols with
  `Bounded/InsertTable.lean` and `Bounded/DeleteTable.lean`, including trap
  bytes, their eight call sites, the existing collection callees, and the firmware
  shim. The negative fixtures modify an instruction byte, a linked call
  immediate, and a shim byte.

`RangeInsert.DeleteExtra.Premises.run` proves the linked deletion helper
from entry to return. It reuses the proved lower bound, word append, and
sorted-map removal routines. The scan and removal invariants relate the
cursor to the initialized deletion-key prefix and the live map entries.
The result records the final live entries, cache words, scratch prefix,
restored stack pointer and saved registers, and a memory footprint covering
the selected end, shifted entries, mutable headers, scratch, and the two
helper stack frames. The premises require enough scratch capacity for every
accepted successor. They also keep the cache, temporary header, and
initialized scratch prefix outside the removal writes.

The helper's exact cost is the entry count (40 or 41 plus lower-bound
search), 42 or 44 instructions per accepted successor, 1 or 3 for the
scan exit, 1 or 14 for the extension test and stores, and 14 for return.
The removal phase adds 2 instructions for an empty key list or 4 plus
the sum of 8 instructions and the verified sorted-map removal cost per
key. Concrete machine witnesses exercise a gap without deletions, growth
followed by a gap, growth followed by end of map, and a maximum endpoint
with two deletions.

The outer predecessor-extension path shares the checked positive-rank
prefix with the covered path. The checked run to the helper call takes
58 instructions plus upper-bound search. The helper's lower bound
selects the predecessor whose end the caller extended. A separate
checked run from the helper's return takes 10 instructions through the
common epilogue. A concrete machine extends `4..=9` with `10..=11` and
checks the prefix through the helper call.

The common initial layout names the linked code images, map allocation,
scratch allocation, cached cardinality, stack space, and disjoint regions.
It derives the caller-prefix assumptions for extension and fresh
insertion. A concrete machine with all nine linked images witnesses
adjacent extension and both fresh cases. The two fresh prefixes reach
the sorted-map insertion call after 30 or 41 instructions plus
upper-bound search.

The helper's entry, scan, and removal premises can be derived from the
same layout populated with the helper's input words. The helper code,
cache, and shifted entries stay within their separate allocations. The
nested stack geometry uses at most 112 bytes for the uncompressed
routines. For a map with `n` entries and `k` accepted successors, the
helper's instruction count is at most `83 + 5n + k(102 + 11n)`.

The predecessor-extension theorem runs the linked caller and helper
through the ABI return in exactly 68 instructions plus upper-bound
search and the helper count. It derives the helper's input from the
actual stores, preserves the ABI's saved registers, and preserves memory
outside the declared writable regions. The adjacent-range machine
returns `4..=16` and `20..=23` with cached cardinality 17 in 276
instructions.

The fresh theorem composes sorted-map insertion, the helper, and the
final cache addition. It uses a spare map slot before deletions. The
entry point takes 30 or 41 instructions plus upper-bound search to call
sorted insertion, eight instructions from that call's return to the
helper, and 20 after the helper returns. The two concrete fresh machines
return in 215 and 364 instructions with the expected map and count.

`RangeInsert.Nonempty.Premises.run` covers empty, contained, extension,
and both fresh paths through one entry theorem. It gives the exact
instruction count, returned ABI state, live entries and cache words,
and preservation outside the declared writable regions. Concrete
machines exercise every branch of this theorem.

`RangeInsert.Nonempty.InsertionPremises.run` in `Theorem.lean` connects
that result to the production model on every path. Its premises are the
entry machine and layout, a map that represents a canonical set, an
accurate cached count, a spare map slot for fresh insertion, and one
deletion-buffer word per map entry. Sortedness, nonoverlap, and the exact
helper scratch counts are derived from these premises. The writable
regions are the 112-byte stack area, the two cache words, the scratch
allocation, the map allocation, and only the length word of the map
header. The conclusion states that the header's data pointer and capacity
words are unchanged. It adds three facts to the machine facts. The live
entries are the ranges of `internalAddProduction`, and the cache words
hold its cached count. That result is the union of the set and the input,
and its count is its cardinality. `Layout/Nonvacuity.lean` satisfies these
premises for every input range on a concrete machine holding `4..=9`,
`12..=16`, and `20..=23` with cache 15. It also shows inputs that reach
each successful branch and applies the theorem.

The deletion-buffer premise is sufficient but not necessary. The machine
uses one scratch word per accepted successor on the path that runs. That
is at most the number of entries after the selected range on the
extension and fresh paths, and none on the empty and contained paths.
A caller that sizes the buffer from the current map length satisfies the
premise. A smaller buffer that would still succeed is outside this
theorem. `RangeInsert.Nonempty.Premises.run` in `Correct.lean` takes the
exact path-specific counts (`freshScratch` and `extensionScratch`) for
the machine facts. `Call.resultRepresents` and
`internalAddProduction_correct` do not depend on scratch. A tighter
premise for `InsertionPremises.run` is deferred.

## Phase 2 capacity model

`RangeInsert.Capacity` defines the demand of each insertion path. Empty
and contained inputs need no new slots. Extension needs one scratch word
per accepted successor. Fresh insertion also needs one transient map
slot, even if subsequent deletions would make the result fit in the
original capacity. The model computes the fresh scratch demand using
the pure vector insertion result, which is independent of the actual
map capacity.

The capacity classification reuses `Call.path` and
`DeleteExtra.Call.acceptCount`. The success case is equivalent to the
path-specific storage premises of the existing execution proof.
Concrete model examples cover zero capacity, exact fit, scratch one
word short, and map failure taking precedence when both are short.
The module elaborated in 5.98 s with a peak RSS of about 6.5 GiB using
the baseline build artifacts. `RangeInsert.Bounded` proves the bounded
binary against this model.

`RangeInsert.CapacityStatus` composes the existing sorted-map and RawVec
runs with the status checks needed by range insertion. A full fresh
insert modifies only the callee stack frame. A full scratch append
returns in seven instructions with memory unchanged, and it needs only
the scratch header. The nonvacuity witnesses reuse the collection model
machines and exercise zero and positive capacities, including both
nonempty map search exits. Elaboration took 4.61 s for the status module
and 4.91 s for its witnesses. Independent kernel replay of the three
Phase 2 modules took 11.07 s.

`RangeInsert.OomReturn` checks the common outer OOM epilogue of the
candidate binary. It reads seven initialized save slots, puts `FULL`
in `a0`, and restores the outer frame and return address in ten
instructions. It changes no memory. All 40 bytes at entry offset
`0x1a0` agree in the QEMU and firmware ELFs. The concrete witness starts
with different values in the registers being restored. Elaboration
took 22.63 s for the epilogue and 5.41 s for the witness. Independent
kernel replay took 21.47 s. The bounded execution proof reaches the same
instructions through the full entry table (`Bounded/Entry.lean`), so this
standalone fragment is not on that theorem's path.

The baseline success theorem now invokes `MapStorage.metadataKept`
through `InitialLayout.metadataKept`. The same lemma can recover the
data pointer and capacity on a failure path once that path establishes
the write footprint. It does not depend on the final length or on
canonical ranges. The success theorem's statement and witness
statements were unchanged. Kernel replay of the theorem and its
layout witness took 9.10 s.

## Phase 2 bounded execution theorem

`RangeInsert.Bounded` proves the bounded linked binary, in which both
allocating operations propagate `Result` and the entry point returns `OK`
(0) or `FULL` (1) in `a0`. `Bounded.Unified.Premises.run` has no
spare-slot or scratch-capacity premise. For every map and scratch capacity
that the initial layout allows, including zero, it proves:

- termination after the exact count of the path and outcome that run;
- return at the link register with the stack pointer and every register
  outside the caller-saved list restored;
- no change to any byte outside the declared writable regions (the
  112-byte stack area, the two cache words, the scratch allocation, the map
  allocation, and the map header's length word);
- `a0 = OK` exactly when `Call.capacityOutcome` is `success`, so `FULL`
  is never returned spuriously;
- on `OK`, the live entries and cache hold the trapping version's verified
  result for that path;
- on `FULL`, the header's length word is at most its capacity.

`Bounded.Unified.InsertionPremises.run` adds that the header's data
pointer and capacity are unchanged on every outcome and, on `OK`, that the
result represents `internalAddProduction`: the union of the set and the
input, with its cardinality cached. With the data pointer, capacity, and a
length within capacity, the caller can release the allocation after
`FULL`. The set's entries and cached count are not otherwise specified.

| Path and outcome | Bounded instructions | Trapping version |
| --- | --- | --- |
| Empty | 21 | 19 |
| Contained | 46 + upper-bound search | 44 + search |
| Extension, OK or `FULL` | 58 + search + helper + 11 | 68 + search + helper |
| Fresh, map full | 27 (no predecessor) or 38 (gap) + search + sorted insertion + 13 | traps |
| Fresh, OK | to helper + helper + 22 | to helper + helper + 20 |
| Fresh, scratch `FULL` | to helper + failed scan + 11 | traps |

The helper's failed scan processes exactly the scratch capacity's worth of
accepted successors, then returns `FULL` from the first append that does
not fit. Its unchanged-memory guarantee covers every byte outside the
helper's frame and scan footprint.

### Reuse and changes

The trapping version's machine-independent definitions and results are
reused unchanged: the deletion-helper model, the scan and removal
invariants, the production-model correspondence (`Call.resultRepresents`),
the path selector, the collection proofs, and the capacity model. The
bounded result is the trapping version's `Call.result` with the bounded
count, so the representation theorem transfers without change. The new
work is step lemmas for both new tables, the changed register allocation
of the helper's scan, both `FULL` paths through the helper and the caller,
the fresh path's scratch header written after insertion instead of
before, and the composition. The scan's loop head now carries the cursor
in `a0` and the cache's low word in `a2`, so the old fixed-PC lemmas were
regenerated at the new offsets.

The trapping version's execution proofs (`Correct.lean`, `Theorem.lean`,
`Nonempty/Extension/Run.lean`, `Nonempty/Fresh/Run.lean`, and their
witnesses) still check against the recorded trapping tables in
`InsertTable.lean` and `DeleteTable.lean`. They no longer describe a built
binary. Retiring them means splitting the shared definitions out of about
45 modules, which is left as a separate change.

### Nonvacuity and checks

`Bounded/Nonvacuity.lean` builds one concrete machine with every linked
bounded image. The helper is 12 bytes longer, so the entry point starts at
`0x15e0` and every shared routine keeps its address. `allOutcomes`
satisfies the bundled premises and selects the stated path and outcome
for the empty, contained, and extension paths, both causes of fresh
insertion, extension and fresh insertion with zero scratch (`FULL`), and
fresh insertion into a full map (`FULL`). `modelRuns` applies the theorem.

The bounded theorem reaches exactly the trapping theorem's 71 axioms: the
Sail model's external declarations, `Classical.choice`, and `Quot.sound`.
Kernel replay of the 24 new execution modules took 89 s. The two tables,
their step lemmas, and the empty path replayed in 263 s.

### Production overhead

For the extracted `u32` production adapter, optimized x86-64 assembly with
`Infallible` has the same instructions, call targets, and stack use as the
trapping version on Rust 1.89 and 1.100.0, after renaming generic
symbols. Only panic source locations differ. The production adapter binds
the infallible result with `let Ok(()) = ...`, which Rust 1.89 accepts.
