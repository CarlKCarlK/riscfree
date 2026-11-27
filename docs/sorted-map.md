# Sorted-map backend for RangeSetBlaze

The backend stores strictly increasing, unique `u32` keys and `u32` values
in the live prefix of a caller-provided `RawVec<Pair>`. Its four C ABI entry
points use a common linear scan and the existing vector update routines.

## Collection interface

RangeSetBlaze's baseline insertion uses a mutable predecessor at or before the
new start, followed by a lazy forward traversal from the selected range's start.
The traversal holds on to the first value so it can extend that range and
collects deletion keys in a temporary vector. It releases the traversal before
deleting those keys. A standalone insertion adds a new start and then uses the
same deletion pass. Both paths maintain a cached set cardinality.
[RangeSetBlaze implementation](https://github.com/CarlKCarlK/range-set-blaze/blob/main/src/set.rs)

| Operation needed by RangeSetBlaze | BTreeMap expression | Bounded map operation |
| --- | --- | --- |
| Mutable predecessor inclusive | `range_mut(..=key).next_back()` | `upper_bound(key)`, then use the preceding slot if any |
| Lazy mutable suffix | `range_mut(key..)` | `lower_bound(key)`, then advance through live slots |
| Insert a start | `insert(key, value)` | `sorted_map_insert` |
| Delete a collected key | `remove(&key)` | `sorted_map_remove` |

A future adapter can yield a shared reference to each key and an exclusive
reference to its value. The underlying slice can split the first entry from
the rest so the algorithm can retain its value reference across the scan.
A bounded vector can collect keys during the traversal. The existing
`OrderedMap` experiment's cloned suffix is suitable as an oracle. The
production algorithm needs to be able to stop before the end of the suffix.
`internalAddCLen` establishes set union and cached cardinality at the mathematical
algorithm layer. Range insertion through the adapter is the next task.
[Ordered-map experiment](https://github.com/CarlKCarlK/range-set-blaze-vibe-validation/tree/main/rust-tests)
[Mathematical insertion and cardinality proofs](https://github.com/CarlKCarlK/range-set-blaze-vibe-validation/blob/main/RangeSetBlaze/AlgoC.lean)

## Contracts and costs

- Both bounds return ranks in a sorted map and preserve memory. They return
  zero for an empty map without reading its data pointer.
- Insertion replaces an equal key's value even at capacity. It returns
  `FULL` for a new key at capacity and `INVALID_LENGTH` for a malformed
  length. Both failures preserve the map.
- Removal returns `ABSENT` for a missing key and `INVALID_LENGTH` for a
  malformed length. A successful removal leaves the vacated slot outside the
  map's live prefix.
- The list specification proves that insertion and erasure preserve strictly
  increasing keys. The update theorems connect the live contents to that
  specification, including all key/value pairs after a replacement.
- The two updates restore the stack pointer, return address, and callee-saved
  registers. Their proofs account for the stack stores and the exact writes
  to the map. The callers supply mapped RAM, aligned addresses, and the
  separation required by the proof's memory premises.

If a RangeSetBlaze insertion absorbs `k` successors, the baseline uses at most
one predecessor lookup, one insertion, one suffix traversal and `k` removals.
That count follows the algorithm and is independent of the map backend.
The machine costs below apply to this particular linear-scan backend.
Let `S` be the lower-bound instruction count and `V` the count of the
corresponding RawVec callee for the same arguments.

| Path | Exact instructions |
| --- | --- |
| Either bound on empty input | 4 |
| Either bound stopping at position `p` in a nonempty map | `7 + 5p` |
| Either bound exhausting a nonempty map of length `n` | `6 + 5n` |
| Insert with invalid length | 18 |
| Replace at a matching position | `32 + S` |
| Insert at the end, or reject because full at the end | `27 + S + V` |
| Insert before another key, or reject because full at that point | `32 + S + V` |
| Remove with invalid length | 16 |
| Remove an absent key when the search exhausts, including an empty map | `21 + S` |
| Remove an absent key when the search stops at a different key | `26 + S` |
| Remove a matching key | `28 + S + V` |

The proof checks the exact instruction count and composes the search and
vector theorems at their actual linked addresses. `just prove` compares all
four instruction sequences in both ELFs, checks the update routines' call
targets, and exercises corrupted copies. The QEMU caller uses uncompressed
instructions. The ESP32-C3 demo uses assembly wrappers to supply the
word-aligned return addresses required by this Sail model. The sorted-map
wrappers are exercised by the hardware harness and remain outside these
theorems.

## ESP32-C3 test

All six cases passed on the physical ESP32-C3. The demo reported successful
insertion and removal for both `RawVec<u32>` and `RawVec<Pair>`, followed
by `SortedMap search PASS` and `SortedMap update PASS`.

Run `just run-raw-vec` from the repository root with the board connected.
Its `build-raw-vec` prerequisite checks the linked firmware's RawVec bytes
and runs the Lean ELF checker on all four sorted-map routines, including
the call targets of insertion and removal. Flashing starts after those
checks pass.

## Verification effort

The bounds share a single scan model and correctness proof, parameterized
by strict versus inclusive comparison. Insertion and removal reuse that
search theorem, the respective vector-shifting theorem, the Sail decoder,
the instruction rules, and the RawVec model machine. New work covers
link-register and stack handling, the search result's use in deciding the
update path, the writes for an equal-key replacement, and the connection
from pointwise buffer results to the independent list specification.

The instruction files are the main cost of adding another compiled routine.
Most per-instruction lemmas follow existing statement patterns. Branch
targets, register assignments, relocation offsets, and the transfer of memory
premises across calls still require close review. A future generator could
emit the repetitive step statements from checked instruction tables. The
composition and the mathematical correspondence still need separate proofs.


The new `proof/SortedMap` modules contain about 4,700 lines, including the
specification, linked opcode tables, per-instruction lemmas, composition,
and nonvacuity witnesses. The branch builds on the shared Sail and RawVec
proof modules. With the decoder and existing dependencies cached, measured
module elaboration on the development machine was:

| Lean module | Elaboration |
| --- | ---: |
| `SortedMap.Insert.Table` (44 linked words) | 99 s |
| `SortedMap.Insert.Instructions` | 7.9 s |
| `SortedMap.Insert` | 7.9 s |
| `SortedMap.Insert.Nonvacuity` | 4.3 s |
| `SortedMap.Remove` | 6.4 s |
| `SortedMap.Remove.Nonvacuity` | 4.6 s |

Peak reported RSS was about 7.4 GiB for the linked insertion table build and
6.6–6.8 GiB for the composition and witness builds. These measurements include
the memory-mapped Sail imports. Keeping the insertion table separate lets
edits to instruction effects or to the composition reuse its decode proof.
