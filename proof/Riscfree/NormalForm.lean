import Lean

/-!
# Kernel-checked normal forms of definitions

```lean
normal_form name (x : X) (h : P x) : term x
  expanding [f] unfolding Namespace using [lemma₁, …]
```

runs `simp` once on `term x`, with the hypotheses `h` as rewrite rules, and adds
two declarations with `addDecl`, so the kernel checks both:

* `def name (x : X) := <normal form of term x>`, whose parameters are the
  binders that are not propositions. The normal form must not mention a
  hypothesis.
* `theorem name.eq (x : X) (h : P x) : term x = name x`.

A concrete instance such as `term a = v` then needs no further `simp`: rewrite
with `name.eq` and let the kernel reduce `name a` along the branch that `a`
selects. riscfree uses this for the Sail decoder (`Riscfree.RV32.DecoderNormalForm`).

The constants in `expanding` are unfolded once by delta expansion before `simp`
runs. This handles definitions too large for Lean to generate equation lemmas
for. `simp` also unfolds every definition under `Namespace` reachable from them
that the kernel evaluates poorly or that `simp` must see through: recursive
definitions (well-founded recursion does not reduce well in the kernel) and
nullary configuration constants. Definitions that a hypothesis rewrites are left
alone, so the hypothesis can apply. Everything else stays folded for the kernel
to evaluate on concrete arguments.

The idea of partially evaluating the Sail decoder once comes from
ship-your-interpreter by Basis Research; this is an independent implementation.
-/

namespace Riscfree

open Lean Meta Elab Command Term

/-- The definitions under `namespacePrefix` reachable from `roots` that `simp`
should unfold: recursive definitions and nullary constants. Definitions in
`keep`, the heads that hypotheses rewrite, are never unfolded. The search continues through
definitions that are not unfolded, so their callees are found too. -/
def reachableUnfolds (roots : Array Name) (namespacePrefix : Name) (keep : NameSet) :
    MetaM (Array Name) := do
  let mut visited : NameSet := {}
  let mut chosen : Array Name := #[]
  let mut stack := roots
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if visited.contains name then
      continue
    visited := visited.insert name
    let some (.defnInfo info) := (← getEnv).find? name | continue
    let isRoot := roots.contains name
    unless isRoot || namespacePrefix.isPrefixOf name do
      continue
    if keep.contains name || (← isInstance name) then
      continue
    let unfold := !isRoot && (!info.type.isForall || (← isRecursiveDefinition name))
    if unfold then
      chosen := chosen.push name
    for used in info.value.getUsedConstants do
      unless visited.contains used do
        stack := stack.push used
  return chosen

syntax (name := normalFormCommand) "normal_form " ident bracketedBinder* " : " term
  " expanding " "[" ident,* "]" " unfolding " ident " using " "[" ident,* "]" : command

@[command_elab normalFormCommand] def elabNormalForm : CommandElab := fun stx => do
  let `(normal_form $name:ident $binders:bracketedBinder* : $body:term
      expanding [$expansions,*] unfolding $namespacePrefix using [$rules,*]) := stx
    | throwUnsupportedSyntax
  let declName := (← getCurrNamespace) ++ name.getId
  -- The Sail decoder nests thousands of branches; the default depth is too small.
  liftTermElabM <| withTheReader Core.Context (fun context => { context with maxRecDepth := 1000000 }) do
  Term.elabBinders binders fun locals => do
    let lhs ← instantiateMVars (← Term.elabTermAndSynthesize body none)
    let expansionNames ← expansions.getElems.mapM fun ident =>
      realizeGlobalConstNoOverloadWithInfo ident
    let expanded ← deltaExpand lhs (expansionNames.contains ·)
    let mut theorems : SimpTheorems := {}
    let mut keep : NameSet := {}
    for fact in locals do
      let factType ← inferType fact
      if ← isProp factType then
        theorems ← theorems.add (.fvar fact.fvarId!) #[] fact
        if let some (_, left, _) := factType.eq? then
          if let .const head _ := left.getAppFn then
            keep := keep.insert head
    for rule in rules.getElems do
      let constant ← realizeGlobalConstNoOverloadWithInfo rule
      theorems ← match ← getConstInfo constant with
        | .thmInfo _ => theorems.addConst constant
        | _ => theorems.addDeclToUnfold constant
    for constant in ← reachableUnfolds expansionNames namespacePrefix.getId keep do
      theorems ← theorems.addDeclToUnfold constant
    let context ← Simp.mkContext (config := { maxSteps := 50000000 })
      (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
    -- Only branch pruning; other simprocs would try to evaluate the symbolic arguments.
    let mut simprocs : Simprocs := {}
    simprocs ← simprocs.add ``reduceIte (post := false)
    simprocs ← simprocs.add ``reduceDIte (post := false)
    let (result, _) ← Meta.simp expanded context (simprocs := #[simprocs])
    let normal ← instantiateMVars result.expr
    let parameters ← locals.filterM fun binder => return !(← isProp (← inferType binder))
    let normalValue ← instantiateMVars (← mkLambdaFVars parameters normal)
    if normalValue.hasFVar || normalValue.hasMVar then
      throwError "normal_form: the normal form still mentions a hypothesis:{indentExpr normal}"
    let normalType ← instantiateMVars (← inferType normalValue)
    let levels := (collectLevelParams (collectLevelParams {} normalValue) normalType).params.toList
    addDecl <| Declaration.defnDecl
      { name := declName, levelParams := levels, type := normalType, value := normalValue,
        hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    let application := mkAppN (mkConst declName (levels.map mkLevelParam)) parameters
    let proof ← instantiateMVars (← result.getProof)
    let equation ← mkEq lhs application
    let statement ← instantiateMVars (← mkForallFVars locals equation)
    let proof ← instantiateMVars (← mkLambdaFVars locals (← mkExpectedTypeHint proof equation))
    if proof.hasMVar then
      throwError "normal_form: the simp proof has unassigned metavariables"
    addDecl <| Declaration.thmDecl
      { name := declName ++ `eq, levelParams := levels, type := statement, value := proof }

end Riscfree
