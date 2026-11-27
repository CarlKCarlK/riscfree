# What the RawVec proofs establish

This note records what `rawVecU32InsertSailCorrect` (in
[proof/RawVec.lean](../proof/RawVec.lean)) depends on: its axioms and the
premises it assumes. It also lists what is still trusted. Later sections cover
the pair routine and the two removal routines, which follow the same pattern.

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

`lake build` checks these proofs, and `just kernel-check` replays them through
Lean's kernel with `leanchecker`'s replay function. They use no axioms beyond
the theorem's own.

## The platform premise

`rawVecU32InsertSailCorrect` takes `Environment`, which assumes a `Platform`
for every memory that agrees with the original on the 120 code bytes.
`Platform.code` assumes the result of Sail's instruction fetch at each
instruction.

`rawVecU32InsertSailCorrectInMachineMode` derives that premise. It takes
two facts about the original machine:

- `MachineMode`: machine mode, readable `misa`, `mseccfg`, and `mstatus`
  with `MPRV` clear, landing pads disabled, HTIF disabled, and a word-aligned
  return address in `ra`. Every one of these fields is also a field of
  `Platform`.
- `CodeImage`: the code fits in the address space and is word-aligned, the 30
  words sit little-endian in memory at the code base, and for each halfword
  Sail's `matching_pma` finds a region marked executable.

[proof/Riscfree/RV32/Fetch.lean](../proof/Riscfree/RV32/Fetch.lean) proves
what Sail's `fetch` does from these facts. Machine mode and `mstatus` are
enough for the address translation, because `effectivePrivilege` ignores
`MPRV` for fetches and machine mode uses Bare translation. Each halfword read
then needs the matching PMA region to be executable, HTIF off, and the two
bytes in memory. The pinned configuration has no PMP entries and its CLINT is
disabled, so neither affects the read. `CodeImage.withMemory` shows the image
survives any memory that keeps the code bytes, and `Buffer.awayFromCode`
already makes every write miss the code. So the old "for every memory"
premise follows (`Environment.ofMachine`).

The original theorem is unchanged. `rawVecU32InsertSailCorrectInMachineMode`
is a corollary of it. `Nonvacuity.lean` shows that its premises hold on the
model for all five paths (`machineAppendRuns`, ...).

The converse is not proved: that every `Environment` gives a `CodeImage`.
It would need an inversion of Sail's `mem_read`. So the new theorem is not
formally shown to cover every situation the old one covers. Both theorems
remain, and for real hardware the new premises are the natural ones to check.

`Platform.ofCodeImage` builds a `Platform` the same way for any routine, so the
popcount proofs could drop their code-mapping premise too. They have not been
changed.

## The pair routine

`rawVecPairInsertSailCorrect` and `rawVecPairInsertSailCorrectInMachineMode`
(in [proof/RawVec/PairInsert.lean](../proof/RawVec/PairInsert.lean)) make the
same claims for `raw_vec_pair_insert`. They reach the same 72 axioms, and
`just axiom-paths` checks the first one's executed path against the same
seven expected axioms. Their premises are the same generic `Header` and
`Buffer` structures from [proof/RawVec/Insert.lean](../proof/RawVec/Insert.lean),
instantiated for eight-byte elements: both words of each shifted pair must be
readable, both words of each written slot writable, and each slot's eight
bytes must miss the header and the routine's 132 code bytes.
[proof/RawVec/PairInsert/Nonvacuity.lean](../proof/RawVec/PairInsert/Nonvacuity.lean)
shows the premises of both theorems hold on the five paths (15, 35, 5, 6, and
7 instructions).

The `u32` theorems now instantiate the same generic definitions.
[proof/RawVec/Compatibility.lean](../proof/RawVec/Compatibility.lean) keeps the
original `u32` definitions and statements verbatim and derives each original
theorem, including both shim theorems, from the current one. So the
refactoring added no premise and weakened no conclusion.

The demo calls the pair routine through `call_raw_vec_pair_insert`, a copy of
the `u32` shim. That shim is not proved.

## The removal routines

`rawVecU32RemoveSailCorrect` and `rawVecPairRemoveSailCorrect`, each with an
`InMachineMode` form (in [proof/RawVec/U32Remove.lean](../proof/RawVec/U32Remove.lean)
and [proof/RawVec/PairRemove.lean](../proof/RawVec/PairRemove.lean)), verify the
two instances of `RawVec<T>::remove`. They reach the same 72 axioms as the
insertion theorems, and `just axiom-paths` checks each one's executed path
against the same seven expected axioms. The routines use the same seven
instruction formats as insertion, so the table above applies unchanged.

The specification, premises, and loop invariant are in
[proof/RawVec/Remove.lean](../proof/RawVec/Remove.lean). `Remove.Header` is the
same as insertion's. `Remove.Buffer` differs because removal touches a
different footprint:

- The elements after the removed one must be readable, and the slots from the
  index up to the new length writable. No permission is required for the
  removed slot's own read, for the vacated last slot, or for spare capacity.
- Only the written slots must miss the header and the code. A successful call
  therefore needs one slot fewer than insertion, and none of the capacity.
- The elements must fit in the address space up to the old length:
  `data + size * length <= 2 ^ 32`. The loop ends when its pointer equals the
  end pointer `data + size * length`. When that sum is exactly `2 ^ 32` the end
  pointer wraps to 0, and `Remove.slotReached` shows that no earlier pointer
  equals it, so the bound is not stronger than the code needs.

The conclusion is pointwise, like insertion's: each slot below the new length
holds `result`, the old sequence without the removed element, and
`unchanged` allows only the length word and the slots from the index to the
new length to change. The vacated last slot keeps its old element.

[proof/RawVec/U32Remove/Nonvacuity.lean](../proof/RawVec/U32Remove/Nonvacuity.lean)
and [proof/RawVec/PairRemove/Nonvacuity.lean](../proof/RawVec/PairRemove/Nonvacuity.lean)
show the premises of both theorems hold on the routine's four paths: shift
(removing index 1 of 4, 23 and 27 instructions), last (9), invalid length (5),
and invalid index (6). A fifth witness, an empty vector, takes the
invalid-index path. They use the shared model in
[proof/RawVec/Model.lean](../proof/RawVec/Model.lean), now stated over the
vector's contents so that insertion and removal calls both instantiate it.

The demo calls the removal routines through `call_raw_vec_u32_remove` and
`call_raw_vec_pair_remove` in
[examples/raw_vec_remove_call.S](../examples/raw_vec_remove_call.S), copies of
the insertion shim. These shims are not proved.

## Calling shim

The Rust demo calls `call_raw_vec_u32_insert`, the seven-instruction shim in
[examples/raw_vec_call.S](../examples/raw_vec_call.S), rather than the
routine itself. [proof/RawVec/Shim.lean](../proof/RawVec/Shim.lean) proves the
shim and the routine together.

### What is checked

- The table holds the shim's seven linked words. `call raw_vec_u32_insert`
  assembles to `auipc ra, 0x0` and `jalr ra, 0xb4(ra)`. Their immediates
  depend on where the linker puts the two functions. `build.rs` assembles the
  shims into their own object and links it directly before the routines'
  object, so only those two objects determine the offset. `just prove` compares the
  shim's 28 bytes and the routine's 120 bytes with the tables. It also checks
  that the routine starts exactly `routineOffset` (0xbc) bytes after the shim.
  If a change to the shims or routines moves either function, the check fails, and the table
  and `routineOffset` must be updated together.
- The shim's steps use the same `Fetch.lean` derivation as the routine, so
  neither code image is assumed to be fetchable. `ShimEnvironment` requires
  machine mode and the two code images in executable memory.
- The routine theorem is applied to the state the shim reaches after `jalr`.
  `syncInside` re-expresses that state in the routine's snapshot form, and it
  converts the routine's end state back afterward. `rawVecU32InsertSailRun`
  exposes the end state in that form. It is the proof's former internal
  statement, so `rawVecU32InsertSailCorrect` is unchanged.

### What the theorems say

`callRawVecU32InsertSailAtReturn` holds for any caller. After
`call.count + 6` instructions, the shim stands at its `ret`. `a0` holds the
routine's status, and `ra` holds the caller's return address. Every register
other than the PC, `nextPC`, and `a0`–`a7` has its original value; in
particular `ra` and `sp` are restored. Memory is the routine's result applied
to the original memory with `ra` stored at `sp - 4`.

`callRawVecU32InsertSailCorrect` adds the `ret` for a caller whose return
address is word-aligned. After `call.count + 7` instructions, the PC is the
caller's return address, with the same register and memory guarantees.

### Premises beyond the routine's

`ShimLayout` adds what the shim needs:

- The saved-`ra` word at `sp - 4` is readable, writable, and aligned. It is
  disjoint from the header, from every element slot up to the length, and from
  both code images.
- The routine's writes (the length word and the shifted slots) miss the shim's
  code, so the shim's last three instructions are still there to run.

The header and buffer premises are the routine's, stated for the original
machine. The proof transfers them across the shim's stack store.
`ShimHypotheses` in `Nonvacuity.lean` bundles every premise. The model places
the shim at `0xf44`, the routine at `0x1000`, and `sp` at `0x5000`, and
`shimAppendRuns`, ..., `shimFullRuns` apply the full theorem on each of the
five paths.

### Why the last `ret` is not always covered

The pinned Sail configuration sets `hartSupports Ext_Zca` to `false`.
`jump_to` therefore raises a fetch-address-misaligned exception for any
target with bit 1 set, whatever `misa.C` says. The Rust caller is compiled for
`riscv32imc`, so its return address can have bit 1 set. The ESP32-C3 implements
the C extension and returns there correctly. In the linked demo, the five calls
return to `0x42013afe`, `0x42013b10`, `0x42013b22`, `0x42013b34`, and
`0x42013b76`. Three of them have bit 1 set. For those three, the final `ret` is
the only instruction outside the formal guarantee. Covering it would need a Sail
configuration with Zca, which in turn means verifying the compressed caller.

## Remaining trusted base

The later sections of this note add to this list as the guarantee is
extended.

- Lean's kernel and the three standard axioms.
- The Sail RISC-V model as the specification of the processor, its
  translation to Lean by Sail's Lean backend, and the pinned configuration
  (no PMP entries, CLINT disabled, compressed instructions disabled).
- `Riscfree.RV32.step` and `run`: one uninterrupted Sail instruction per
  step, with no interrupt delivery or counters.
- GNU binutils (`nm`, `objdump`) locating the routine's and the shim's bytes
  in the ELF for the linked-byte check.

About the Rust caller, the following remain trusted:

- **Calling convention.** The caller passes the header pointer, index, and
  value in `a0`–`a2`, and its return address in `ra`. It enters the shim
  with `jal`/`jalr`, and that instruction itself is not modeled. The caller
  expects only `a0` as a result. It treats `a0`–`a7` as clobbered, which the
  RISC-V ABI allows and the theorems confirm.
- **The final `ret`** when the return address has bit 1 set (see above).
- **Memory facts.** The `Header`, `Buffer`, and `ShimLayout` premises:
  readable and writable PMA regions, the initialized elements, and the
  separation of the header, buffer, stack slot, and code. In the demo, Rust's
  types and the `unsafe` block's safety comment establish these, and the proof
  does not check them.
- **No concurrent access.** Nothing else reads or writes the header, buffer,
  or stack slot during the call. No interrupt or exception arrives: the demo
  disables the watchdogs and runs without interrupts, and `step` does not
  model their delivery.
- **The machine state at entry.** Machine mode, `MPRV` clear, landing pads and
  HTIF disabled. The ESP32-C3 has no HTIF. The model's HTIF and landing-pad
  settings stand for hardware that does not implement those features.
