import Popcount
import PopcountSwar
import RawVec.Shim
import RawVec.PairInsert
import Riscfree.Elf

/-!
# Linked-byte checks

Run after `lake build` and after building the ELF files. Sail's `LeanRV32D`
declares a top-level `main`, so this file cannot be run with `lean --run`.
Instead, append an `#eval` of `linkedBytes` with `<check>`, `<ELF path>` pairs
and pass the result to Lean on standard input, as `just prove` does:

```bash
{ cat scripts/LinkedBytes.lean; echo '#eval linkedBytes ["popcount", "x.elf"]'; } \
  | lake env lean --stdin
```

A failed check throws, so Lean exits with an error.

Each check compares the raw bytes of a linked routine with the instruction
words of the table its proof decodes (see `proof/Riscfree/Elf.lean`):

* `popcount`, `popcount-swar`: the two popcount routines.
* `raw-vec`: `raw_vec_u32_insert` and `raw_vec_pair_insert`.
* `raw-vec-shim`: the u32 calling shim, and that its `call` reaches the
  routine exactly `routineOffset` bytes ahead.
* `uncompressed`: the file has no compressed instructions, as the QEMU harness
  requires.

Prefixing a check with `reject-` makes it a negative test: the check must fail,
and with the message of a byte mismatch or of a set `EF_RISCV_RVC` flag, so a
missing or unreadable file does not count. `scripts/corrupt_elf.py` writes the
corrupted copies that `just prove` passes this way.

Checking the linked executable is separate from proving the instruction
sequence correct, so these checks live here rather than in the proof modules.
Editing them therefore rebuilds no proof. Importing the proof modules once
lets every check run in one Lean process.
-/

open Riscfree

def checkRawVecShim (path : String) : IO Unit := do
  let routine ← verifyElfSymbol path "raw_vec_u32_insert" (RawVec.instructions.map Prod.fst)
  let shim ← verifyElfSymbol path "call_raw_vec_u32_insert" (RawVec.shimInstructions.map Prod.fst)
  unless routine == shim + RawVec.routineOffset.toNat do
    throw (IO.userError s!"raw_vec_u32_insert is {routine - shim} bytes after the shim, but the \
      proof's call reaches {RawVec.routineOffset.toNat}")
  IO.println s!"call_raw_vec_u32_insert: calls raw_vec_u32_insert {RawVec.routineOffset.toNat} bytes ahead"

def runCheck : String → String → IO Unit
  | "popcount", path => verifyElf path "popcount128" (Popcount.instructions.map Prod.fst)
  | "popcount-swar", path =>
    verifyElf path "popcount128_swar" (PopcountSwar.instructions.map Prod.fst)
  | "raw-vec", path => do
    verifyElf path "raw_vec_u32_insert" (RawVec.instructions.map Prod.fst)
    verifyElf path "raw_vec_pair_insert" (RawVec.PairInsert.instructions.map Prod.fst)
  | "raw-vec-shim", path => checkRawVecShim path
  | "uncompressed", path => verifyUncompressed path
  | check, _ => throw (IO.userError s!"unknown linked-byte check {check}")

-- The failure messages that show a negative test failed for the intended reason.
def rejectionReasons : List String :=
  ["bytes differ from the Lean proof", "EF_RISCV_RVC is set"]

def expectRejection (check path : String) : IO Unit := do
  let failure ← try
      runCheck check path
      pure none
    catch error => pure (some (toString error))
  let some message := failure
    | throw (IO.userError s!"{path}: {check} accepted a corrupted file")
  unless rejectionReasons.any fun reason => (message.splitOn reason).length > 1 do
    throw (IO.userError s!"{path}: {check} failed for an unexpected reason: {message}")
  IO.println s!"{path}: rejected as expected ({message})"

def linkedBytes (args : List String) : IO Unit := do
  let rec run : List String → IO Unit
    | [] => pure ()
    | check :: path :: rest => do
      match check.dropPrefix? "reject-" with
      | some negative => expectRejection negative.toString path
      | none => runCheck check path
      run rest
    | [check] => throw (IO.userError s!"linked-byte check {check} needs an ELF path")
  if args.isEmpty then
    throw (IO.userError "linkedBytes needs at least one <check>, <ELF path> pair")
  run args
