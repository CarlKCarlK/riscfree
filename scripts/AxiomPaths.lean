import Lean

/-!
# Axiom dependency paths

Run after `lake build`. Each check starts with `--module`, names the module
whose imports must contain its theorems, and lists the theorems to explain:

```bash
lake env lean --run scripts/AxiomPaths.lean --module RawVec Riscfree.RawVec.rawVecU32InsertSailCorrect
```

A check may also add `--block <constant>` (repeatable) to list the axioms the
statement still reaches when the search may not enter those constants.
Blocking Sail's instruction dispatcher `LeanRV32D.Functions.execute` and
naming the executors of the instructions the routine runs with
`--root <constant>` separates axioms on the routine's execution path from
those that only another instruction's semantics mentions. Add
`--expect <axiom>` (repeatable) to fail unless that restricted search reaches
exactly the listed axioms, so a change that puts a new axiom on the routine's
path is noticed.

Give several checks, each with its own `--module`, theorems, and flags, to run
them in one process. Importing the environment takes most of the running
time, so the script imports every named module once and then runs each check
with only its own flags. A constant's definition, and therefore every search
below, does not depend on which other modules are imported. A check fails if
one of its theorems is not in its module's import closure, so it accepts the
same theorems as when that module alone is imported. The script runs every
check and fails if any of them failed.

For each theorem, the report lists every axiom the kernel would need to check
it and, for each axiom:

* whether the theorem's *statement* already reaches it (through the
  definitions the statement mentions, such as `run` and Sail's `execute`), or
  only its *proof* does, and
* one shortest chain of constants from the theorem to the axiom.

An axiom reached by the statement is part of what the statement means. An
axiom reached only by the proof is an extra assumption the proof made. This
script only reports; `scripts/AxiomAudit.lean` enforces the allowed list.
-/

open Lean

/-- One `--module` group of the command line. -/
structure Check where
  module : Name
  theorems : List Name
  blocked : List Name
  roots : List Name
  expected : List Name

/-- Constants directly mentioned by a declaration's type and, for definitions,
theorems, and opaque constants, its value. -/
def directUses (env : Environment) (name : Name) (includeValue : Bool := true) : Array Name :=
  match env.find? name with
  | none => #[]
  | some info =>
    let fromType := info.type.getUsedConstants
    let fromValue := if includeValue then
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      else #[]
    -- Inductive types reach their constructors, and constructors and recursors
    -- reach their inductive type, so follow those links as the kernel does.
    let structural : Array Name := match info with
      | .inductInfo value => value.ctors.toArray
      | .ctorInfo value => #[value.induct]
      | .recInfo value => value.all.toArray
      | _ => #[]
    fromType ++ fromValue ++ structural

/-- The `directUses` of every constant searched so far. Every check reads the same
environment, so an entry stays valid for the whole run. Without it, each check
recomputes the uses of the same Sail definitions, which is most of the running
time. -/
abbrev UsesCache := Std.HashMap Name (Array Name)

/-- Breadth-first search from `roots`, recording each reached constant's parent.
The search does not enter the constants in `blocked`. -/
def reach (env : Environment) (cache : UsesCache) (roots : Array Name) (blocked : List Name := []) :
    (NameMap Name × Array Name) × UsesCache := Id.run do
  let mut cache := cache
  let mut parent : NameMap Name := {}
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  let mut queue := roots
  for root in roots do
    seen := seen.insert root
  let mut head := 0
  while head < queue.size do
    let current := queue[head]!
    head := head + 1
    order := order.push current
    let uses ← match cache[current]? with
      | some uses => pure uses
      | none => do
        let uses := directUses env current
        cache := cache.insert current uses
        pure uses
    for next in uses do
      unless seen.contains next || blocked.contains next do
        seen := seen.insert next
        parent := parent.insert next current
        queue := queue.push next
  return ((parent, order), cache)

def chain (parent : NameMap Name) (target : Name) : List Name := Id.run do
  let mut path := [target]
  let mut current := target
  for _ in [0:10000] do
    match parent.find? current with
    | some previous =>
      path := previous :: path
      current := previous
    | none => break
  return path

def isAxiom (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.axiomInfo _) => true
  | _ => false

/-- `module` and every module it imports, directly or indirectly. -/
def importClosure (env : Environment) (module : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [module]
  while true do
    match stack with
    | [] => break
    | current :: rest =>
      stack := rest
      if seen.contains current then
        continue
      seen := seen.insert current
      if let some index := env.getModuleIdx? current then
        for imported in env.header.moduleData[index.toNat]!.imports do
          stack := imported.module :: stack
  return seen

/-- Print the report for one check. Returns `false` if it failed. -/
def runCheck (env : Environment) (cacheRef : IO.Ref UsesCache) (check : Check) : IO Bool := do
  -- Take the cache out of the reference while searching, so that it stays unshared
  -- and `reach` updates it in place.
  let reachCached (roots : Array Name) (blocked : List Name := []) := do
    let (result, cache) := reach env (← cacheRef.swap {}) roots blocked
    cacheRef.set cache
    return result
  let closure := importClosure env check.module
  let mut passed := true
  for theoremName in check.theorems do
    let some info := env.find? theoremName
      | IO.eprintln s!"unknown declaration {theoremName}"; return false
    let some moduleIndex := env.getModuleIdxFor? theoremName
      | IO.eprintln s!"{theoremName} is not from an imported module"; return false
    let definingModule := env.header.moduleNames[moduleIndex.toNat]!
    unless closure.contains definingModule do
      IO.eprintln s!"{theoremName} is from {definingModule}, which {check.module} does not import"
      return false
    -- The statement's closure follows the statement's constants through their
    -- full definitions; the theorem's own proof term is excluded.
    let (_, statementOrder) ← reachCached info.type.getUsedConstants
    let statementAxioms := statementOrder.filter (isAxiom env)
    let (parent, order) ← reachCached #[theoremName]
    let axioms := order.filter (isAxiom env)
    IO.println s!"{theoremName}: {axioms.size} axioms, {statementAxioms.size} reached from the statement"
    for axiomName in axioms do
      let origin := if statementAxioms.contains axiomName then "statement" else "proof only"
      let path := chain parent axiomName
      IO.println s!"  {axiomName} [{origin}]"
      IO.println s!"    {" → ".intercalate (path.map toString)}"
    unless check.blocked.isEmpty do
      let roots := info.type.getUsedConstants ++ check.roots.toArray
      let (blockedParent, blockedOrder) ← reachCached roots check.blocked
      let remaining := blockedOrder.filter (isAxiom env)
      IO.println s!"  with {check.blocked} blocked and extra roots {check.roots}: {remaining.size} axioms"
      for axiomName in remaining do
        IO.println s!"    {axiomName}: {" → ".intercalate ((chain blockedParent axiomName).map toString)}"
      unless check.expected.isEmpty do
        let unexpected := remaining.filter (!check.expected.contains ·)
        let missing := check.expected.filter (!remaining.contains ·)
        if unexpected.isEmpty && missing.isEmpty then
          IO.println s!"  OK: the restricted search reaches exactly the {check.expected.length} expected axioms"
        else
          IO.eprintln s!"  FAIL: unexpected {unexpected.toList}, missing {missing}"
          passed := false
  return passed

/-- Sort one check's arguments into theorems, `--block`, `--root`, and `--expect` names. -/
def splitFlags : List String → List Name → List Name → List Name → List Name →
    List Name × List Name × List Name × List Name
  | "--block" :: name :: rest, theorems, blocked, roots, expected =>
    splitFlags rest theorems (blocked ++ [name.toName]) roots expected
  | "--root" :: name :: rest, theorems, blocked, roots, expected =>
    splitFlags rest theorems blocked (roots ++ [name.toName]) expected
  | "--expect" :: name :: rest, theorems, blocked, roots, expected =>
    splitFlags rest theorems blocked roots (expected ++ [name.toName])
  | name :: rest, theorems, blocked, roots, expected =>
    splitFlags rest (theorems ++ [name.toName]) blocked roots expected
  | [], theorems, blocked, roots, expected => (theorems, blocked, roots, expected)

/-- Split the arguments into checks. Returns `none` for an empty list, for
arguments before the first `--module`, and for a check without theorems. -/
partial def parseChecks : List String → Option (List Check)
  | "--module" :: module :: rest =>
    let (own, others) := rest.span (· != "--module")
    let (theorems, blocked, roots, expected) := splitFlags own [] [] [] []
    if theorems.isEmpty then none
    else
      let check := { module := module.toName, theorems, blocked, roots, expected }
      if others.isEmpty then some [check]
      else (parseChecks others).map (check :: ·)
  | _ => none

def main (arguments : List String) : IO UInt32 := do
  let some checks := parseChecks arguments
    | IO.eprintln "usage: AxiomPaths (--module <module> <theorem>... [--block <constant>]... \
      [--root <constant>]... [--expect <axiom>]...)..."
      return 2
  initSearchPath (← findSysroot)
  let imports := checks.toArray.map fun check => ({ module := check.module } : Import)
  let env ← importModules imports {} (loadExts := true)
  let cacheRef ← IO.mkRef ({} : UsesCache)
  let mut failures := 0
  for check in checks do
    IO.println s!"module {check.module}"
    unless ← runCheck env cacheRef check do
      failures := failures + 1
  if failures > 0 then
    IO.eprintln s!"FAIL: {failures} of {checks.length} axiom-path checks failed"
    return 1
  IO.println s!"OK: all {checks.length} axiom-path checks passed"
  return 0
