# Bounded Rust vectors and ordered maps for machine-code verification

This report records a November 26, 2026 experiment with Rust 1.100.0, LLVM
23.1.5, `heapless` 0.9.3, and the `riscv32im-unknown-none-elf` target. The
target's ELF attribute is `rv32i2p1_m2p0_zmmul1p0`: compressed instructions are
not enabled. All decoded instructions are four bytes.

The complete Rust source is in [src/lib.rs](src/lib.rs). The generated compiler
assembly (`*.s`), relocatable machine code (`*.o`), decoded bytes
(`*.disassembly.txt`), and ELF attributes (`*.attributes.txt`) are in
[generated](generated). [scripts/build-rv32.sh](scripts/build-rv32.sh)
reproduces them at optimization levels `1`, `3`, `s`, and `z`.

## Recommendation

Verify the custom `#[repr(C)]` runtime-capacity vector first, using
`custom_u32_push` and `custom_u32_insert_loop` at `opt-level=1`.

This is the best first proof target because:

- its `{data, length, capacity}` header is an explicit, stable 12-byte RV32 C
  ABI rather than an opaque Rust layout or fat pointer;
- one routine works for every runtime capacity;
- the insertion loop has no external calls, panic paths, compiler-outlined
  helpers, or hidden control flow;
- capacity exhaustion, an invalid `length > capacity` header, and an invalid
  index have explicit status values;
- the four-byte and eight-byte versions have the same control-flow graph, with
  the pair version adding one load and one store per moved element;
- the exact dynamic instruction count is a small affine function of the
  number of shifted elements.

After the custom vector proof establishes the memory model and calling
convention, `heapless::Vec` remains worth adopting where Rust owns the object
and a compile-time capacity is acceptable. Its push machine code is excellent.
It is not the best first C-ABI proof boundary because its layout is not stable,
each capacity is a distinct type, and `VecView` communicates capacity through
Rust fat-pointer metadata.

## Compared source interfaces

The custom representation is intentionally small:

```rust
#[repr(C)]
pub struct U32Vec {
    pub data: *mut u32,
    pub length: u32,
    pub capacity: u32,
}

#[repr(C)]
pub struct PairVec {
    pub data: *mut Pair,
    pub length: u32,
    pub capacity: u32,
}
```

The `heapless` C wrappers instead accept opaque storage. C obtains the size and
alignment from Rust and initializes it through Rust before calling push or
insert. The experiment uses `Vec<T, 16, u32>` so the length field has the same
width as the custom header.

Both alternatives return these status values:

| Value | Meaning |
| ---: | --- |
| 0 | Success. |
| 1 | Capacity is full; no mutation. |
| 2 | Insertion index is greater than length; no mutation. |
| 3 | Custom header has `length > capacity`; no mutation. |

The `heapless` wrapper checks the index before calling `Vec::insert`, converting
what would otherwise be a panic into status 2. A normally initialized
`heapless::Vec` maintains `length <= capacity` internally, so it has no status
3 counterpart.

## Memory representation and FFI

### `heapless::Vec`

In `heapless` 0.9.3, `Vec<T, N, LenT>` aliases a `VecInner` containing a length
and inline `[MaybeUninit<T>; N]` storage. With `LenT = u32` and capacity 16,
the RV32 experiment reports:

| Element | Object size | Alignment | Observed data offset |
| --- | ---: | ---: | ---: |
| `u32` | 68 bytes | 4 bytes | 4 bytes |
| `Pair` | 132 bytes | 4 bytes | 4 bytes |

These observations are not a C layout guarantee: neither `VecInner` nor its
storage has `#[repr(C)]`, its fields are private, and a future release may
change them. Opaque storage plus Rust size/alignment/initialization functions
is workable, but the verified interface must treat the concrete crate version
and layout as part of the artifact.

Capacity `N` is a const generic. The generated fixed-vector push and insertion
compare against literal 16, so changing `N` can change machine code and needs a
new linked-byte check even when the proof can be parameterized at a higher
level.

### `heapless::VecView`

`VecView<T, LenT>` erases the const generic by replacing the inline array type
with an unsized `[MaybeUninit<T>]`. It is useful inside Rust, but it is not an
owned vector and can exist only behind a fat pointer. In the exported Rust-ABI
experiment, RV32 passes:

```text
a0 = address of VecInner length and inline data
a1 = slice metadata / runtime capacity
a2 = insertion index
a3 = inserted u32
```

This is visible in `heapless_view_u32_insert_rust_abi`: the full check compares
the loaded length with `a1`. Rust does not promise that fat-pointer layout as a
C ABI. A C wrapper must therefore use a concrete `Vec<T, N>` and recreate a
view on the Rust side, which makes its external capacity static again.

### Custom header

Both custom headers are exactly 12 bytes and four-byte aligned on RV32. The
backing allocation is separate, so the same routine accepts every capacity.
The unsafe FFI contract requires an exclusive header and a writable, aligned
allocation of `capacity` elements. Such an allocation also establishes the
pointer-offset and address-overflow preconditions required by Rust. The code
checks `length <= capacity`; successful insertion additionally establishes
`index <= length < capacity`, so `length + 1` cannot overflow `u32`.

These are source-level safety arguments only. The future machine-code proof
must state and prove alignment, allocation extent, non-aliasing, address
non-wraparound, preservation outside the shifted range and header, and the
calling-convention obligations.

## Generated-code comparison

### Static instruction counts

Counts below are exported-symbol sizes divided by four. At levels `1` and `3`,
the relevant `heapless` operations inline into the wrapper; insertion still
calls `memmove`. The explicit loops have no calls at any tested level.

| Routine | `1` | `3` | `s` | `z` |
| --- | ---: | ---: | ---: | ---: |
| `heapless_u32_push` | 11 | 13 | 13 | 6 + callees |
| `custom_u32_push` | 18 | 18 | 18 | 18 |
| `heapless_pair_push` | 12 | 14 | 14 | 14 |
| `custom_pair_push` | 19 | 19 | 19 | 19 |
| `heapless_u32_insert` | 37 | 38 | 12 + 52-instruction callee | 10 + callees |
| `custom_u32_insert` (`memmove`) | 40 | 40 | 38 | 38 |
| `custom_u32_insert_loop` | 29 | 29 | 30 | 30 |
| `heapless_pair_insert` | 41 | 42 | 20 + 61-instruction callee | 20 + callees |
| `custom_pair_insert` (`memmove`) | 44 | 44 | 42 | 42 |
| `custom_pair_insert_loop` | 32 | 32 | 33 | 33 |
| runtime-capacity `VecView<u32>::insert` | 39 | 36 | 12 + 51-instruction callee | 10 + callees |

The `s` build does not inline the fixed `heapless` insertion. Its library
callee retains the formatted panic branch for `index > length`, even though
the wrapper has already excluded it. The `z` build adds several
`OUTLINED_FUNCTION_*` calls. Both choices enlarge the proof graph despite their
size-oriented names. Level `1` is the cleanest tested output; level `3` is a
close second.

### Dynamic instruction counts at `opt-level=1`

Push counts include return:

| Routine | Success | Full | Invalid header |
| --- | ---: | ---: | ---: |
| `heapless_u32_push` | 11 | 6 | Not representable through the API |
| `heapless_pair_push` | 12 | 6 | Not representable through the API |
| `custom_u32_push` | 14 | 6 | 5 |
| `custom_pair_push` | 15 | 6 | 5 |

For explicit-loop insertion, let `m = length - index` on a successful call:

| Routine | `m = 0` | `m > 0` | Bad index | Full | Invalid header |
| --- | ---: | ---: | ---: | ---: | ---: |
| `custom_u32_insert_loop` | 15 | `16 + 7m` | 6 | 7 | 5 |
| `custom_pair_insert_loop` | 16 | `17 + 9m` | 6 | 7 | 5 |

The pair loop's two additional instructions per moved element are the second
word load and store. This regular correspondence should let most proof
infrastructure be shared while keeping separate linked routines and theorems.

No straightforward self-contained count exists for the `memmove` variants:
each successful insertion executes a call even when zero bytes move, and the
linked `memmove` implementation determines both its proof obligations and its
variable-input instruction count.

### Representative machine code

The promising `u32` loop at level `1` has one backwards branch and no call.
The machine-code word is shown before each decoded instruction:

```text
2c: 02d5f263  bgeu a1, a3, 0x50
30: 00269713  slli a4, a3, 0x2
34: 00052783  lw   a5, 0x0(a0)
38: 00e787b3  add  a5, a5, a4
3c: ffc7a803  lw   a6, -0x4(a5)
40: fff68693  addi a3, a3, -0x1
44: 0107a023  sw   a6, 0x0(a5)
48: ffc70713  addi a4, a4, -0x4
4c: fed5e4e3  bltu a1, a3, 0x34
```

The `heapless` level-1 push is also attractive and fully self-contained:

```text
00: 00052603  lw    a2, 0x0(a0)
04: 00f00693  li    a3, 0xf
08: 00c6ec63  bltu  a3, a2, 0x20
0c: 00261693  slli  a3, a2, 0x2
10: 00d506b3  add   a3, a0, a3
14: 00160713  addi  a4, a2, 0x1
18: 00e52023  sw    a4, 0x0(a0)
1c: 00b6a223  sw    a1, 0x4(a3)
20: 01063513  sltiu a0, a2, 0x10
24: 00154513  xori  a0, a0, 0x1
28: 00008067  ret
```

See [generated/release-1.disassembly.txt](generated/release-1.disassembly.txt)
for every byte and relocation and [generated/release-1.s](generated/release-1.s)
for compiler assembly.

## Capacity and RangeSetBlaze algorithm order

Runtime capacity does not materially complicate the custom machine code. It
adds a header load and comparison to push and insertion, but it avoids one
routine per capacity. Element width is similarly regular: address scaling
changes from `<< 2` to `<< 3`, and pair movement adds one load/store pair.

Bounded storage exposes resource assumptions omitted by the mathematical list
model:

- `delete_extra` may collect a data-dependent number of deletion keys, so its
  key vector must either have capacity for the maximum map population or
  return an explicit exhaustion result.
- `internal_add2` inserts the new range before running `delete_extra`. If the
  map is already at capacity, insertion can fail even when the later deletion
  pass would make the final map fit. Preserving the production algorithm means
  not deleting first; callers must provide a spare slot or accept this failure.
- Failure must leave the collection unchanged. Push and vector insertion do;
  a later whole-algorithm interface must decide how to propagate exhaustion
  without changing lazy iteration, cardinality-arithmetic order, or the
  subsequent deletion pass.
- Capacity in elements is insufficient as a memory premise by itself. The
  proof needs byte-size multiplication, allocation bounds, alignment, and
  pointer-addition non-overflow for four- and eight-byte elements.

The existing `OrderedMap` experiment in range-set-blaze-vibe-validation was
reviewed first. Its `VecOrderedMap` correctly captures strictly increasing
unique keys and its differential tests are valuable, but methods such as
`successors_ge` clone an entire suffix into an allocating `Vec`. That contract
intentionally abstracts iterator laziness and cost, so it should remain an
oracle rather than become the production machine-code interface. A bounded
interface should expose a lower-bound index/cursor and borrowed forward
iteration, then collect exactly the deletion prefix into the bounded key
vector before the unchanged deletion pass.

## Existing library survey

### Worth adopting or studying

- [`heapless`](https://github.com/rust-embedded/heapless) 0.9.3 is maintained,
  `no_std`, allocation-free, and already supplies the required vector
  operations. It is the best existing vector library when fixed compile-time
  capacity and Rust-owned layout are acceptable. The project credits Jorge
  Aparicio, Per Lindgren, and Emil Fresk as authors.
- [`x39-sACN`](https://crates.io/crates/x39-sacn) 0.2.1 contains a
  `SortedVecMap<K, V, N>` implemented as a sorted `heapless::Vec` with binary
  search, ascending iteration, fixed capacity, and no allocation. It closely
  matches the desired map shape and is useful prior art. It is part of a much
  larger networking crate, uses const-generic capacity, and does not provide
  the specialized lazy cursor/deletion interface needed here, so adopting the
  entire crate solely for this internal type is not recommended.

### Not direct fits

- `heapless::LinearMap` and `heapless::IndexMap` are not key-sorted maps;
  iteration order is not the required strictly increasing key order.
- [`vecset`](https://github.com/youknowone/vecset-rs) has a current `no_std`,
  zero-dependency sorted `VecMap`, and
  [`sorted_vector_map`](https://crates.io/crates/sorted_vector_map) supplies a
  fuller sorted-vector map API. Both use allocating `Vec`, not caller-provided
  bounded storage, so neither solves the verified C-ABI storage problem.
- `small_sorted_set`, `vec_collections`, and similar `SmallVec` designs may
  spill to an allocator. That fallback is incompatible with the no-allocator
  requirement and complicates resource-exhaustion semantics.

The most practical map direction is therefore a thin project-specific sorted
map layer over the verified runtime vector primitives, informed by
`VecOrderedMap` and `x39-sACN`, rather than a complete new general-purpose map.
It should not be implemented until the required cursor and failure contract is
settled.

## Limits of this experiment

- The object files are relocatable, not linked firmware. Calls to `memmove`
  deliberately remain relocations; the explicit-loop recommendation avoids
  that dependency. Final verification must use bytes from the actual linked
  image as riscfree already does.
- Clang 14 accepted the C header for `riscv32-unknown-none-elf`, and its static
  assertions confirmed the 8-byte pair and 12-byte headers. This was a
  freestanding syntax/type/layout check, not a linked mixed-language test.
- The host tests cover representative shifts and failure statuses; they are
  not exhaustive or property tests.
- No Lean proof, production RangeSetBlaze refactor, complete ordered map, or
  firmware integration was attempted.
