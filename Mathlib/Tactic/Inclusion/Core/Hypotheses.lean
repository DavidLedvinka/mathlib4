/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Inclusion

/-!
# Inclusion hypotheses

**TODO (NOT FOR CODEX)**
-/

@[expose] public meta section

open Lean Meta Elab Term

namespace Inclusion

/-- Infer the type of `h` and run every matching hypothesis extension, restoring the previous state
when an extension fails. -/
def runHypothesisExts (h : Expr) : HypothesisM Unit := do
  let type ← instantiateMVars (← inferType h)
  let exts := hypothesisExt.getState (← getEnv)
  let matchedExts ← exts.getSortedMatch (← read).enabledFamilies type (·.priority)
  for ext in matchedExts do
    if !exts.erased.contains ext.name then
      let saved ← saveState
      try
        ext.derive h type
        recordExtraModUseFromDecl (isMeta := true) ext.name
        trace[Tactic.inclusion] "{ext.name} processed {type}"
      catch err =>
        trace[Tactic.inclusion] "Failed to apply {ext.name} to {type} : {err.toMessageData}"
        restoreState saved

/-- Construct the inclusion hypothesis `iExpr.expr ∈ Univ.univ` using the `Univ` instance for
`iExpr.iType`. -/
def mkUniversalHyp (iExpr : IExpr) : MetaM ExprInclusionFunction := do
  let univ ← iExpr.iType.synthUniv
  return ⟨#[], #[], iExpr.iType, ← iExpr.iType.mkUniv univ, ← iExpr.mkMemUniv univ⟩

/-- Combine the inclusion hypothesis for each `iExpr` into one inclusion hypothesis. -/
def combineHyps (iExprs : Array IExpr) : HypothesisM (Array ExprInclusionFunction) := do
  let state ← get
  iExprs.mapM fun iExpr => do
    let { expr, iType } := iExpr
    let hyps := state.inclusions[expr]?.getD #[]
    if hyps.isEmpty then
      return ← mkUniversalHyp iExpr
    let (params, argIndices) := mergeInclusionParams (hyps.map (·.params))
    withInclusionParams params fun paramVars => do
      let firstHyp := hyps[0]!
      let firstArgs := argIndices[0]!.map fun i => paramVars[i]!
      let mut set := (mkAppN firstHyp.inclusion firstArgs).headBeta
      let mut proofBody := (mkAppN firstHyp.proof firstArgs).headBeta
      if hyps.size > 1 then
        let refiner ← iType.synthRefine
        for h : i in [1:hyps.size] do
          let hyp := hyps[i]
          let args := argIndices[i]!.map fun j => paramVars[j]!
          let nextSet := (mkAppN hyp.inclusion args).headBeta
          let nextProof := (mkAppN hyp.proof args).headBeta
          set ← iType.mkRefine refiner set nextSet
          proofBody ← mkAppM ``Refine.mem_refine #[proofBody, nextProof]
      let inclusion ← mkLambdaFVars paramVars set
      let proof ← mkLambdaFVars paramVars proofBody
      return ⟨params, #[], iType, inclusion, proof⟩

/-- Make inclusion hypothesis from the local context for each inclusion variable in `fn`. -/
def mkHyps (fn : ExprInclusionFunction) (enabledParams : NameSet)
    (enabledFamilies : NameSet := {}) :
    MetaM (Array ExprInclusionFunction) := do
  if fn.iExprs.isEmpty then
    return #[]
  HypothesisM.run (iExprsArray := fn.iExprs) (enabledParams := enabledParams)
      (enabledFamilies := enabledFamilies) do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        let h := ldecl.toExpr
        runHypothesisExts h
    combineHyps fn.iExprs

end Inclusion
