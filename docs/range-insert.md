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
pinned Lake dependency (commit `d7837025` on its `main`),
so riscfree keeps no copy of them. That revision puts the library in the
`RangeSetBlazeValidation` namespace, because Sail also declares a
top-level `IntRange`. Its sources build with both its own Lean 4.33.1 and
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
[Mathematical proof](https://github.com/CarlKCarlK/range-set-blaze-vibe-validation/blob/d7837025ca5ed1ec74f35768ea12d97014dad249/RangeSetBlaze/AlgoC.lean)

## Storage and machine costs

Let `n` be the original number of ranges and `k` the number of collected
successors. Successful insertion requires capacity `n+1` on the fresh
path and `n` on the other paths. The deletion buffer needs at least
`k` slots. Both exhaustion cases trap in QEMU. Scratch exhaustion can
occur after writes to the map or cached length. These are executable
observations. The exhaustion paths have no Sail termination theorem.

With linear sorted-map search and shifting, the fresh or extension path
takes `O((k+1)(n+1))` instructions. Each deletion performs a new linear
search and shifts a suffix, so the worst case is quadratic. The forward
iterator itself takes `O(k+1)` steps. Appending a key takes constant time.
The contained case uses only the predecessor search, and the empty input
needs no search.

With rustc 1.100.0, the linked entry has 109 instruction words and the
linked deletion helper has 117. The following QEMU counts (`-singlestep -d exec,nochain`) include calls through the
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
- `just emulate-raw-vec` runs all shared cases under QEMU.
  `just test-range-insert-exhaustion` verifies the two expected traps.
- `just build-raw-vec` checks the ESP32-C3 ELF. After flashing with
  `just run-raw-vec`, the firmware should print `Range insertion PASS`.
  A physical run is pending.
- The ELF checks cover both range insertion symbols, including trap bytes,
  their eight call sites, the existing collection callees, and the firmware
  shim. The negative fixtures modify an instruction byte, a linked call
  immediate, and a shim byte.

The contained path is proved. The main remaining proof obligation is to
compose the fresh-insertion and predecessor-extension paths with the
verified collection theorems, reusing the shared prefix. This starts in `delete_extra` with a loop invariant relating the concrete
cursor, accumulated endpoint, two-word cache, and initialized scratch
prefix. That invariant can transfer to a deletion loop that reads the
scratch keys in order and composes the sorted-map removal theorem. The
temporary map can contain touching or overlapping ranges, while its keys
remain strictly increasing for each collection call. The outer proof then
composes upper-bound and map insertion with this helper and connects the
returned entries and count to the abstract union theorem.
Exact dynamic instruction formulas and composed memory, register, and
stack guarantees for those two paths remain open.
