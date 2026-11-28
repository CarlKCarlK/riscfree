import Popcount
import PopcountSwar
import RawVec.Shim
import RawVec.PairInsert
import RawVec.U32Remove
import RawVec.PairRemove
import SortedMap.Search.Instructions
import SortedMap.Remove.Instructions
import SortedMap.Insert.Table
import Riscfree.Elf
import RangeInsert.Bounded.InsertTable
import RangeInsert.Bounded.DeleteTable

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
* `raw-vec`: `raw_vec_u32_insert`, `raw_vec_pair_insert`, `raw_vec_u32_remove`,
  and `raw_vec_pair_remove`.
* `sorted-map`: both searches, insertion, removal, and the update routines’ call targets.
* `range-insert`: both range insertion symbols and their call targets.
* `range-insert-shim`: the firmware's word-aligned calling shim and its target.
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

/-- Resolve an uncompressed Rust call pair through the signed immediates in
the checked table. The symbol comparison is independent of disassembly. -/
def checkCall (caller callee : Nat) (target : String)
    (instructions : List (BitVec 32 × instruction)) (index : Nat) : IO Unit := do
  let some (_, .UTYPE (high, link, .AUIPC)) := instructions[index]?
    | throw (IO.userError "Expected auipc in range insertion call")
  let some (_, .JALR (low, source, destination)) := instructions[index + 1]?
    | throw (IO.userError "Expected jalr in range insertion call")
  unless link == RV32.reg 1 && source == link && destination == link do
    throw (IO.userError "Expected range insertion call to link through ra")
  let address := (BitVec.ofNat 32 (caller + 4 * index) +
    ((high.signExtend 32) <<< 12) + low.signExtend 32) &&& 0xfffffffe
  unless address.toNat == callee do
    throw (IO.userError s!"Range insertion call target differs from the symbol {target}")

def checkCalls (caller : Nat) (instructions : List (BitVec 32 × instruction))
    (targets : List (Nat × Nat × String)) : IO Unit := do
  let sites := instructions.zipIdx.filterMap fun ((_, operation), index) =>
    match operation with
    | .JAL (_, destination) | .JALR (_, _, destination) =>
      if destination == RV32.reg 0 then none else some index
    | _ => none
  unless sites == targets.map (fun (index, _, _) => index + 1) do
    throw (IO.userError "Linked range insertion calls differ from the expected sites")
  for (index, address, symbol) in targets do
    checkCall caller address symbol instructions index

def checkRangeInsert (path : String) : IO Unit := do
  let insertWords := RangeInsert.Bounded.InsertTable.instructions
  let deleteWords := RangeInsert.Bounded.DeleteTable.instructions
  let insert ← verifyElfSymbol path RangeInsert.Bounded.InsertTable.symbol (insertWords.map Prod.fst)
  let delete ← verifyElfSymbol path RangeInsert.Bounded.DeleteTable.symbol (deleteWords.map Prod.fst)
  let upper ← verifyElfSymbol path "sorted_map_upper_bound" (SortedMap.Search.upperInstructions.map Prod.fst)
  let lower ← verifyElfSymbol path "sorted_map_lower_bound" (SortedMap.Search.lowerInstructions.map Prod.fst)
  let mapInsert ← verifyElfSymbol path "sorted_map_insert" (SortedMap.Insert.instructions.map Prod.fst)
  let mapRemove ← verifyElfSymbol path "sorted_map_remove" (SortedMap.Remove.instructions.map Prod.fst)
  let push ← verifyElfSymbol path "raw_vec_u32_insert" (RawVec.instructions.map Prod.fst)
  checkCalls insert insertWords [
    (19, upper, "sorted_map_upper_bound"), (38, mapInsert, "sorted_map_insert"),
    (50, mapInsert, "sorted_map_insert"), (61, delete, "delete_extra"),
    (98, delete, "delete_extra")]
  checkCalls delete deleteWords [
    (19, lower, "sorted_map_lower_bound"), (64, push, "raw_vec_u32_insert"),
    (106, mapRemove, "sorted_map_remove")]
  IO.println "Range insertion: all eight linked call targets checked"

def checkRangeInsertShim (path : String) : IO Unit := do
  let insert ← verifyElfSymbol path RangeInsert.Bounded.InsertTable.symbol
    (RangeInsert.Bounded.InsertTable.instructions.map Prod.fst)
  let shim ← verifyElfSymbol path "call_range_insert_u32"
    [0xff010113, 0x00112623, 0x00000097, 0xe28080e7, 0x00c12083, 0x01010113, 0x00008067]
  unless shim == insert + 0x1d0 do
    throw (IO.userError "Range insertion call target differs in the firmware shim")

def runCheck : String → String → IO Unit
  | "popcount", path => verifyElf path "popcount128" (Popcount.instructions.map Prod.fst)
  | "popcount-swar", path =>
    verifyElf path "popcount128_swar" (PopcountSwar.instructions.map Prod.fst)
  | "raw-vec", path => do
    verifyElf path "raw_vec_u32_insert" (RawVec.instructions.map Prod.fst)
    verifyElf path "raw_vec_pair_insert" (RawVec.PairInsert.instructions.map Prod.fst)
    verifyElf path "raw_vec_u32_remove" (RawVec.U32Remove.instructions.map Prod.fst)
    verifyElf path "raw_vec_pair_remove" (RawVec.PairRemove.instructions.map Prod.fst)
  | "sorted-map", path => do
    let lower ← verifyElfSymbol path "sorted_map_lower_bound" (SortedMap.Search.lowerInstructions.map Prod.fst)
    verifyElf path "sorted_map_upper_bound" (SortedMap.Search.upperInstructions.map Prod.fst)
    let insert ← verifyElfSymbol path "sorted_map_insert" (SortedMap.Insert.instructions.map Prod.fst)
    let vectorInsert ← verifyElfSymbol path "raw_vec_pair_insert" (RawVec.PairInsert.instructions.map Prod.fst)
    unless insert + SortedMap.Insert.searchOffset.toNat == lower &&
        insert + SortedMap.Insert.vectorOffset.toNat == vectorInsert + 2 ^ 32 do
      throw (IO.userError "sorted_map_insert call targets differ from the Lean proof")
    let remove ← verifyElfSymbol path "sorted_map_remove" (SortedMap.Remove.instructions.map Prod.fst)
    let vector ← verifyElfSymbol path "raw_vec_pair_remove" (RawVec.PairRemove.instructions.map Prod.fst)
    unless remove + SortedMap.Remove.searchOffset.toNat == lower + 2 ^ 32 &&
        remove + SortedMap.Remove.vectorOffset.toNat == vector + 2 ^ 32 do
      throw (IO.userError "sorted_map_remove call targets differ from the Lean proof")
  | "range-insert", path => checkRangeInsert path
  | "range-insert-shim", path => checkRangeInsertShim path
  | "raw-vec-shim", path => checkRawVecShim path
  | "uncompressed", path => verifyUncompressed path
  | check, _ => throw (IO.userError s!"unknown linked-byte check {check}")

-- The failure messages that show a negative test failed for the intended reason.
def rejectionReasons : List String :=
  ["bytes differ from the Lean proof", "Range insertion call target differs", "EF_RISCV_RVC is set"]

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
