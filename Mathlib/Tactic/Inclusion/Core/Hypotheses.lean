/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Lean.Meta.Basic
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
    let saved ← saveState
    try
      ext.derive h type
      recordExtraModUseFromDecl (isMeta := true) ext.declName
      trace[Tactic.inclusion] "[{ext.family}] {ext.userName} processed {type}"
    catch err =>
      trace[Tactic.inclusion]
        "Failed to apply [{ext.family}] {ext.userName} to {type} : {err.toMessageData}"
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
    (enabledFamilies : Array Name := #[]) :
    MetaM (Array ExprInclusionFunction) := do
  if fn.iExprs.isEmpty then
    return #[]
  HypothesisM.run (iExprsArray := fn.iExprs) (enabledParams := enabledParams)
      (enabledFamilies := enabledFamilies) do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        runHypothesisExts ldecl.toExpr
    combineHyps fn.iExprs

/-- Check that two inclusion types are definitionally equal, including their chosen `ToSet`
instances. -/
def ensureOutputType (actual expected : IType) : MetaM Unit := do
  -- The represented element types must agree, for example both must be `Real`.
  unless ← pureIsDefEq actual.elemType expected.elemType do
    -- Report the component that differs instead of a generic type mismatch.
    throwError "Inclusion function has expression type {actual.elemType}, expected \
      {expected.elemType}"
  -- The computational set types must agree, for example both must be `Interval Dyadic`.
  unless ← pureIsDefEq actual.setType expected.setType do
    -- A hypothesis using a different backend cannot be substituted into the main function.
    throwError "Inclusion function has set type {actual.setType}, expected {expected.setType}"
  -- Even equal element and set types may be interpreted by definitionally different `ToSet`s.
  unless ← pureIsDefEq actual.toSetInst expected.toSetInst do
    -- Require the same interpretation so that the two membership propositions agree.
    throwError "Inclusion function uses an unexpected `ToSet` instance"

def ExprInclusionFunction.closeWithHyps (fn : ExprInclusionFunction)
    (hyps : Array ExprInclusionFunction) : MetaM ExprInclusionFunction := do
  -- Each free inclusion expression in `fn` must have one corresponding inclusion hypothesis.
  unless fn.iExprs.size = hyps.size do
    throwError "Internal error: the inclusion function and its hypotheses have different lengths"
  -- A function with no inclusion variables is already closed, so preserve it unchanged.
  if fn.iExprs.isEmpty then
    return fn
  -- Form one deduplicated parameter list for `fn` followed by all the hypothesis functions.
  -- `argIndices[j]` records where the parameters of the `j`th input occur in this merged list.
  let (params, argIndices) :=
    mergeInclusionParams (#[fn.params] ++ hyps.map (·.params))
  -- Introduce one `Nat` free variable for each merged parameter while constructing the new terms.
  withInclusionParams params fun paramVars => do
    -- Recover the parameter arguments expected by the original inclusion function, in its order.
    let fnParamArgs := argIndices[0]!.map fun i => paramVars[i]!
    -- Specialize the computational function at those parameters, leaving only its set arguments.
    let inclusionFn := (mkAppN fn.inclusion fnParamArgs).headBeta
    -- Specialize its correctness proof similarly, leaving its sets and membership proofs.
    let proofFn := (mkAppN fn.proof fnParamArgs).headBeta
    -- Collect the closed set computed for each inclusion expression.
    let mut sets := Array.emptyWithCapacity hyps.size
    -- Collect the accompanying proofs that the inclusion expressions belong to those sets.
    let mut proofs := Array.emptyWithCapacity hyps.size
    -- Process hypotheses in exactly the order of `fn.iExprs`.
    for _h : i in [:hyps.size] do
      -- The `i`th hypothesis is intended to close the `i`th inclusion expression.
      let hyp := hyps[i]
      -- Read the element type, set type, and `ToSet` instance expected at this position.
      let expected := fn.iExprs[i]!
      -- Reject a hypothesis whose represented set cannot be passed to `fn` at this position.
      ensureOutputType hyp.outputType expected.iType
      -- Select the merged parameter variables required by this particular hypothesis function.
      let hypParamArgs := argIndices[i + 1]!.map fun j => paramVars[j]!
      -- Since `hyp` is closed, specializing its parameters produces its final represented set.
      sets := sets.push ((mkAppN hyp.inclusion hypParamArgs).headBeta)
      -- Specializing its proof produces `expected.expr ∈` that represented set.
      proofs := proofs.push ((mkAppN hyp.proof hypParamArgs).headBeta)
    -- Substitute all computed sets into the original inclusion function.
    let inclusionBody := mkAppN inclusionFn sets
    -- Abstract the merged parameters to recover a reusable closed computational function.
    let inclusion ← mkLambdaFVars paramVars inclusionBody
    -- Supply the same sets and then their membership proofs to the original correctness theorem.
    let proofBody := mkAppN proofFn (sets ++ proofs)
    -- Abstract the merged parameters from the resulting correctness proof too.
    let proof ← mkLambdaFVars paramVars proofBody
    -- Every inclusion variable has now been discharged, hence the empty `iExprs` field.
    return ⟨params, #[], fn.outputType, inclusion, proof⟩

def toClosedInclusionFunction (goal : Expr) (enabledParams : NameSet)
    (enabledFamilies : Array Name) : MetaM ExprInclusionFunction := do
  let fn ← toExprInclusionFunction goal enabledParams enabledFamilies
  fn.closeWithHyps (← mkHyps fn enabledParams enabledFamilies)

end Inclusion
