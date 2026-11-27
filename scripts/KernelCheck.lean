import Lean.CoreM
import Lean.Replay
import LeanChecker.Replay

/-!
# Kernel replay, one module at a time

Run after `lake build`:

```bash
lake env lean --run scripts/KernelCheck.lean RawVec RawVec.Insert ...
```

`leanchecker M` replays every module whose name starts with `M`, all at once
and each with its own imported environment. `RawVec` is a prefix of every
`RawVec.*` module, so `leanchecker RawVec` loads all of them together and runs
out of memory. This script replays exactly the named modules, one after
another: each module's new declarations go through Lean's kernel into the
environment of its imports.

`replayFromImports` is `leanchecker`'s own function (`src/lean/LeanChecker.lean`
in the Lean 4.28.0-rc1 toolchain), copied because that module also defines
`main`. Keep it in step with the pinned toolchain.
-/

open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay' newConstants
  env'.freeRegions

unsafe def main (modules : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  for module in modules do
    IO.println s!"replaying {module}"
    replayFromImports module.toName
  return 0
