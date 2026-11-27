import Lean

/-!
# Axiom audit

Run after `lake build`:

```bash
lake env lean --run scripts/AxiomAudit.lean
lake env lean --run scripts/AxiomAudit.lean --reference  # also cross-check the selection
lake env lean --run scripts/AxiomAudit.lean RangeSetBlaze.Basic  # also audit dependency modules
```

The audit imports every module under `proof/` from its built `.olean`, so a
proof file missing from the `lakefile.toml` globs fails here instead of going
unchecked. Further module names on the command line, such as the mathematical
dependency's modules that `scripts/check_proof_sources.py --dependency-modules`
lists, are audited the same way. It collects the axioms that the kernel recorded for every
declaration in those modules and fails unless each one is

* one of Lean's three standard axioms, or
* one of the Sail RISC-V extern stubs listed in `sailExterns`, declared in
  `LeanRV32D.RiscvExtras`, whose type is nonempty.

The Sail stubs are uninterpreted functions for the floating-point library,
reservations, the terminal, and the entropy source. Sail's Lean backend
declares them with `axiom`, and they reach every theorem about `step` because
Sail's `execute` mentions every instruction. An axiom whose type is nonempty
is conservative: any proof that uses it remains a proof with the constant
replaced by a variable and then instantiated with an inhabitant. A
proposition-valued axiom usually has no `Nonempty` instance, so a new
assumption of that kind fails the type check as well as the list.

`sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and `Lean.trustCompiler`
are rejected with an explanation, because they mean `sorry`, `native_decide`,
`bv_decide`, or compiled code entered the proof.
-/

open Lean Meta

def proofDir : System.FilePath := "proof"

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module that declares the accepted Sail extern stubs. -/
def sailExternModule : Name := `LeanRV32D.RiscvExtras

/-- The Sail extern stubs the current proofs reach. Extend this list only when
a new proof reaches another stub of `LeanRV32D.RiscvExtras`; the audit still
checks that each added stub has a nonempty type. -/
def sailExterns : List Name :=
  [`cancel_reservation, `get_16_random_bits, `load_reservation, `match_reservation,
   `plat_term_write, `sys_enable_experimental_extensions,
   `riscv_f16Add, `riscv_f16Div, `riscv_f16Eq, `riscv_f16Le, `riscv_f16Le_quiet,
   `riscv_f16Lt, `riscv_f16Lt_quiet, `riscv_f16Mul, `riscv_f16MulAdd, `riscv_f16Sqrt,
   `riscv_f16Sub, `riscv_f16ToF32, `riscv_f16ToF64, `riscv_f16ToI32, `riscv_f16ToUi32,
   `riscv_f16roundToInt,
   `riscv_f32Add, `riscv_f32Div, `riscv_f32Eq, `riscv_f32Le, `riscv_f32Le_quiet,
   `riscv_f32Lt, `riscv_f32Lt_quiet, `riscv_f32Mul, `riscv_f32MulAdd, `riscv_f32Sqrt,
   `riscv_f32Sub, `riscv_f32ToBF16, `riscv_f32ToF16, `riscv_f32ToF64, `riscv_f32ToI32,
   `riscv_f32ToI64, `riscv_f32ToUi32, `riscv_f32ToUi64, `riscv_f32roundToInt,
   `riscv_f64Add, `riscv_f64Div, `riscv_f64Eq, `riscv_f64Le, `riscv_f64Le_quiet,
   `riscv_f64Lt, `riscv_f64Lt_quiet, `riscv_f64Mul, `riscv_f64MulAdd, `riscv_f64Sqrt,
   `riscv_f64Sub, `riscv_f64ToF16, `riscv_f64ToF32, `riscv_f64ToI32, `riscv_f64ToI64,
   `riscv_f64ToUi32, `riscv_f64ToUi64, `riscv_f64roundToInt,
   `riscv_i32ToF16, `riscv_i32ToF32, `riscv_i32ToF64, `riscv_i64ToF32, `riscv_i64ToF64,
   `riscv_ui32ToF16, `riscv_ui32ToF32, `riscv_ui32ToF64, `riscv_ui64ToF32, `riscv_ui64ToF64]

/-- Axioms that mean a proof shortcut, with the shortcut each one indicates. -/
def shortcutAxioms : List (Name × String) :=
  [(``sorryAx, "`sorry` or an elaboration error"),
   (``Lean.ofReduceBool, "`native_decide`, `decide +native`, or `bv_decide`"),
   (``Lean.ofReduceNat, "native evaluation of a natural-number term"),
   (``Lean.trustCompiler, "trust in the compiled code of `native_decide` or `bv_decide`")]

/-- The declarations of the audited modules, read from each module's own
constant table.

This selects the same set as `referenceDeclarations`. When `importModules`
loads module `i`, it records each name of `moduleData[i].constNames` as
belonging to module `i`, which is what `getModuleIdxFor?` returns, and it
rejects a name that two modules declare. So the constants that belong to an
audited module are exactly the names in the audited modules' `constNames`.
The module-index filter below keeps that true even if a future Lean records
a name in a table without owning it. `--reference` checks the equality. -/
def auditedDeclarations (env : Environment) (moduleSet : NameSet) : List Name :=
  (env.header.moduleNames.zip env.header.moduleData).toList.flatMap fun (module, data) =>
    if moduleSet.contains module then
      data.constNames.toList.filter fun name =>
        (env.getModuleIdxFor? name).any (env.header.moduleNames[·.toNat]! == module)
    else []

-- TODO Remove `referenceDeclarations` and `--reference` once the module-by-module
-- selection has agreed with it through a few more proof additions.
/-- The original selection: scan every constant in the environment, including
all of Mathlib and Sail, and keep those whose module is audited. It takes
about 150 s, against well under a second for `auditedDeclarations`. -/
def referenceDeclarations (env : Environment) (moduleSet : NameSet) : List Name :=
  env.constants.toList.filterMap fun (name, _) => do
    let index ← env.getModuleIdxFor? name
    guard (moduleSet.contains env.header.moduleNames[index.toNat]!)
    pure name

def sorted (names : List Name) : List Name :=
  (names.toArray.qsort Name.lt).toList

/-- One pass with a shared `visited` set gives every axiom the declarations use,
and records the first declaration that reaches each one. Thread the state
through a `for` loop: under `lean --run`, `forM` in `CollectAxioms.M` took
minutes instead of seconds. -/
def collectAll (env : Environment) (declarations : List Name) :
    CollectAxioms.State × NameMap Name := Id.run do
  let mut state : CollectAxioms.State := {}
  let mut firstUser : NameMap Name := {}
  for user in declarations do
    let known := state.axioms.size
    state := (((CollectAxioms.collect user).run env).run state).2
    for name in state.axioms.extract known do
      firstUser := firstUser.insert name user
  (state, firstUser)

/-- An accepted Sail stub must come from `sailExternModule` and have a nonempty type. -/
def checkSailExtern (env : Environment) (name : Name) : MetaM (Array String) := do
  let some (.axiomInfo info) := env.find? name
    | return #[s!"{name} is listed as a Sail extern stub but is not an axiom"]
  let module := (env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!)
  unless module == some sailExternModule do
    return #[s!"{name} comes from {module}, not {sailExternModule}"]
  let isNonempty ← forallTelescope info.type fun _ body => do
    let level ← getLevel body
    return (← synthInstance? (mkApp (mkConst ``Nonempty [level]) body)).isSome
  if isNonempty then
    return #[]
  return #[s!"{name} : {info.type} has no Nonempty instance, so it may not be conservative"]

/-- Check the axioms of the audited declarations. With `referenceAxioms`, also
require that the reference selection reached exactly the same axioms. -/
def audit (env : Environment) (modules : Array Name) (audited : List Name)
    (referenceAxioms : Option (Array Name)) : IO UInt32 := do
  let (state, firstUser) := collectAll env audited
  let mut failures : Array String := #[]
  if let some referenceAxioms := referenceAxioms then
    unless sorted state.axioms.toList == sorted referenceAxioms.toList do
      failures := failures.push "the two selections reach different axioms"
  let allowed := standardAxioms ++ sailExterns
  let unexpected := state.axioms.filter (!allowed.contains ·)
  for name in unexpected do
    -- A shortcut usually appears directly in the proof that took it.
    let direct := audited.filter fun user =>
      (env.find? user).any fun info =>
        info.type.getUsedConstants.contains name ||
          (info.value? (allowOpaque := true)).any (·.getUsedConstants.contains name)
    let users := if direct.isEmpty then (firstUser.find? name).toList else direct
    let reason := match shortcutAxioms.lookup name with
      | some shortcut => s!" ({shortcut})"
      | none => ""
    failures := failures.push
      s!"unexpected axiom {name}{reason}, used by {users.take 5}{if users.length > 5 then " ..." else ""}"
  -- One `MetaM` session shares the instance cache across the stubs.
  let context : Core.Context := { fileName := "<axiom audit>", fileMap := default }
  let check := (sailExterns.filter state.axioms.contains).toArray.flatMapM (checkSailExtern env)
  let (sailFailures, _) ← (check.run' {} {}).toIO context { env }
  failures := failures ++ sailFailures
  if failures.isEmpty then
    let sailCount := (state.axioms.filter sailExterns.contains).size
    IO.println s!"axiom audit: OK: {audited.length} declarations in {modules.size} modules use \
      {state.axioms.size} axioms: Lean's {state.axioms.size - sailCount} standard axioms and \
      {sailCount} Sail extern stubs with nonempty types."
    return 0
  for failure in failures do
    IO.eprintln s!"axiom audit: {failure}"
  return 1

def main (args : List String) : IO UInt32 := do
  let reference := args.contains "--reference"
  let extra := (args.filter (· != "--reference")).map String.toName
  if extra.any (·.isAnonymous) then
    IO.eprintln "usage: AxiomAudit.lean [--reference] [module ...]"
    return 2
  let modules := ((← proofModules) ++ extra.toArray).qsort Name.lt
  if modules.isEmpty then
    IO.eprintln s!"axiom audit: no Lean files under {proofDir}"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let moduleSet := modules.foldl NameSet.insert {}
  let audited := auditedDeclarations env moduleSet
  if reference then
    let expected := referenceDeclarations env moduleSet
    unless sorted audited == sorted expected do
      IO.eprintln s!"axiom audit: the module-by-module selection chose {audited.length} \
        declarations, but the whole-environment scan chose {expected.length}"
      return 1
    let referenceAxioms := (collectAll env expected).1.axioms
    IO.println s!"axiom audit: reference scan agrees on all {audited.length} declarations"
    return (← audit env modules audited (some referenceAxioms))
  audit env modules audited none
where
  /-- Module names for every `.lean` file under `proofDir`, sorted. -/
  proofModules : IO (Array Name) := do
    let files ← proofDir.walkDir
    let modules := files.filterMap fun file => do
      guard (file.extension == some "lean")
      let relative ← (file.withExtension "").toString.dropPrefix? (proofDir.toString ++ "/")
      pure (relative.toString.splitOn "/" |>.foldl Name.str .anonymous)
    pure (modules.qsort Name.lt)
