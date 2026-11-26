import Lean

/-!
# Axiom audit

Run after `lake build`:

```bash
lake env lean --run scripts/AxiomAudit.lean
```

The audit imports every module under `proof/` from its built `.olean`, so a
proof file missing from the `lakefile.toml` globs fails here instead of going
unchecked. It collects the axioms that the kernel recorded for every
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

def main : IO UInt32 := do
  let modules ← proofModules
  if modules.isEmpty then
    IO.eprintln s!"axiom audit: no Lean files under {proofDir}"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let moduleSet := modules.foldl NameSet.insert {}
  let audited := env.constants.toList.filterMap fun (name, _) => do
    let index ← env.getModuleIdxFor? name
    guard (moduleSet.contains env.header.moduleNames[index.toNat]!)
    pure name
  -- One pass with a shared `visited` set gives every axiom the audited code uses,
  -- and records the first audited declaration that reaches each one. Thread the
  -- state through a `for` loop: under `lean --run`, `forM` in `CollectAxioms.M`
  -- took minutes instead of seconds.
  let mut state : CollectAxioms.State := {}
  let mut firstUser : NameMap Name := {}
  for user in audited do
    let known := state.axioms.size
    state := (((CollectAxioms.collect user).run env).run state).2
    for name in state.axioms.extract known do
      firstUser := firstUser.insert name user
  let allowed := standardAxioms ++ sailExterns
  let unexpected := state.axioms.filter (!allowed.contains ·)
  let mut failures : Array String := #[]
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
where
  /-- Module names for every `.lean` file under `proofDir`, sorted. -/
  proofModules : IO (Array Name) := do
    let files ← proofDir.walkDir
    let modules := files.filterMap fun file => do
      guard (file.extension == some "lean")
      let relative ← (file.withExtension "").toString.dropPrefix? (proofDir.toString ++ "/")
      pure (relative.toString.splitOn "/" |>.foldl Name.str .anonymous)
    pure (modules.qsort Name.lt)
  /-- An accepted Sail stub must come from `sailExternModule` and have a nonempty type. -/
  checkSailExtern (env : Environment) (name : Name) : MetaM (Array String) := do
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
