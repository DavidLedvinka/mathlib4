/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Elab

/-!
# API for `inclusion` extensions

This file defines helpers for safely interacting with the `InclusionM` and `HypothesisM` monads
when constructing extensions for the `inclusion` tactic.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- Return the expression variable associated with the registered parameter `name` when that
parameter is enabled. The variable is created on its first use and reused thereafter. -/
def getParam? (name : Name) : InclusionM (Option Expr) := do
  -- Reuse the parameter variable if an earlier extension already requested it.
  if let some exprVar := (← get).usedParams.find? name then
    return some exprVar
  let some param := (inclusionParamExt.getState (← getEnv)).find? name
    | throwError "Unknown inclusion parameter '{name}'"
  -- A parameter is available when it has a default or the tactic invocation supplied its value.
  unless param.defaultValue.isSome || (← read).enabledParams.contains name do
    return none
  let ctx ← read
  let exprVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances (mkConst ``Nat) .syntheticOpaque
  modify fun state => { state with usedParams := state.usedParams.insert name exprVar }
  return some exprVar

/-- Create and register an inclusion variable for `e`, represented using `setType` and `toSetInst`
and optionally mapped over `cover`. Its set and membership-proof variables are synthetic opaque
metavariables in the initial local context of the current `InclusionM` computation. -/
def mkIVar (e setType toSetInst : Expr) (cover : Option Expr := none) : InclusionM IVar := do
  -- Inclusion variables are deliberately created in the fixed initial context of `InclusionM`.
  let ctx ← read
  -- Reject an expression depending on a binder introduced temporarily by a recursive extension.
  unless ← MetavarContext.isWellFormed ctx.localContext e do
    throwError "Cannot create an inclusion variable for {e} because it depends on variables \
      introduced while constructing the inclusion function"
  -- Record the element type that will appear in the resulting membership proposition.
  let eType ← inferType e
  -- The type itself must also remain meaningful after the current temporary context is closed.
  unless ← MetavarContext.isWellFormed ctx.localContext eType do
    throwError "Cannot create an inclusion variable for {e} because its type depends on variables \
      introduced while constructing the inclusion function"
  -- The computational set type must be available in the same initial context.
  unless ← MetavarContext.isWellFormed ctx.localContext setType do
    throwError "Cannot use set type {setType} for {e} because it depends on variables introduced \
      while constructing the inclusion function"
  -- The interpretation of represented sets must not capture a temporary local declaration either.
  unless ← MetavarContext.isWellFormed ctx.localContext toSetInst do
    throwError "Cannot use the `ToSet` instance for {e} because it depends on variables introduced \
      while constructing the inclusion function"
  -- Bundle the element type, represented-set type, `ToSet` instance, and original expression.
  let iExpr : IExpr := ⟨⟨eType, setType, toSetInst⟩, e⟩
  -- Create the placeholder represented set that extensions use while constructing the body.
  let setVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances setType .syntheticOpaque
  -- Its accompanying proof has type `e ∈ setVar` under the selected `ToSet` instance.
  let hypType ← iExpr.mkMem setVar
  -- Create the placeholder proof used in the soundness body.
  let hypVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances hypType .syntheticOpaque
  -- Attach any cover selected by the extension to the new inclusion variable.
  let iVar := { iExpr, setVar, hypVar, cover }
  -- Cache the variable by its associated expression so repeated occurrences share it.
  modify fun state => { state with iVars := state.iVars.insert iVar.expr iVar }
  -- Return it so the requesting extension can use its set and proof placeholders immediately.
  return iVar

/-- Find the canonical goal inclusion variable definitionally equal to `e`. Exact expression
matching is attempted first and does not invoke the elaborator. -/
def requestedIVar? (e : Expr) : HypothesisM (Option IExpr) := do
  -- Hypothesis processing uses the fixed collection of variables requested by the goal body.
  let ctx ← read
  -- Exact `ExprMap` lookup handles the overwhelmingly common case without unification.
  if let some iVar := ctx.iVarsMap[e]? then
    return some iVar.iExpr
  -- Fall back to definitional equality when the hypothesis uses a reducibly different expression.
  for iVar in ctx.iVars do
    if ← pureIsDefEq e iVar.expr then
      return some iVar.iExpr
  -- Hypotheses about expressions not requested by the goal are irrelevant.
  return none

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

/-- Construct an inclusion body for a hypothesis endpoint, sharing parameter variables with the
goal computation. -/
def mkHypInclusionBody (e : Expr) (expected : IType) : HypothesisM ExprInclusionBody := do
  -- Read the fixed hypothesis context inherited from the enclosing goal computation.
  let ctx ← read
  -- Seed the nested inclusion computation with every parameter variable used so far.
  let initialState : InclusionM.State := { usedParams := (← get).usedParams }
  -- Reconstruct the `InclusionM` context using the same root locals, enabled parameters, and
  -- extension families as hypothesis processing.
  let inclusionContext : InclusionM.Context :=
    { localContext := ctx.localContext
      localInstances := ctx.localInstances
      enabledParams := ctx.enabledParams
      families := ctx.families }
  -- Recursively construct the endpoint's inclusion body and retain the resulting inclusion state.
  let (body, inclusionState) ←
    (mkExprInclusionBody e).runWith inclusionContext initialState
  -- Read the represented-set type and interpretation actually produced by the endpoint body.
  let iType ← body.inferIType e
  -- A hypothesis endpoint must close without introducing further unknown inclusion expressions.
  unless inclusionState.iVars.isEmpty do
    throwError "The inclusion function for {e} depends on inclusion variables"
  -- Ensure that its resulting set can be used as a hypothesis for the requested expression.
  ensureOutputType iType expected
  -- Recover the synthetic opaque parameter variables in the stable `NameMap` order.
  let (_, paramVars) := inclusionState.usedParams.toArray.unzip
  -- Abstract those known placeholders to test whether the computational body is otherwise closed.
  let inclusion ← mkLambdaFVars paramVars body.inclusionBody (binderInfoForMVars := .default)
  -- Any remaining free variable would escape from the eventual closed inclusion function.
  if inclusion.hasFVar then
    throwError "The computational inclusion function for {e} contains a free variable"
  -- Any remaining metavariable would leave the computational result under-specified.
  if inclusion.hasMVar then
    throwError "The computational inclusion function for {e} contains a metavariable"
  -- Propagate newly used parameters so the goal and every hypothesis share one parameter list.
  modify fun state => { state with usedParams := inclusionState.usedParams }
  -- Keep the unabstracted body; the shared parameters are abstracted once when all hypotheses
  -- close.
  return body

/-- Validate and add an inclusion hypothesis body for a requested inclusion expression. -/
def addInclusionHyp (iExpr : IExpr) (body : ExprInclusionBody) : HypothesisM Unit := do
  -- Reject candidates whose element type, represented-set type, or `ToSet` instance is unsuitable.
  ensureOutputType (← body.inferIType iExpr.expr) iExpr.iType
  -- Append the candidate to the array associated with the canonical requested expression.
  modify fun state => { state with inclusions := state.inclusions.alter iExpr.expr fun
    -- Preserve earlier candidates because they will later be combined with `Refine`.
    | some hyps => hyps.push body
    -- Create the candidate array when this is the first useful hypothesis for the expression.
    | none => #[body] }

/-- The generic hypothesis extension that uses a closed `ToSet` membership hypothesis directly as
an inclusion hypothesis. -/
@[hypothesisExt core | _ ∈ _]
meta def directMembershipHyp : HypothesisExt where
  derive h type := do
    -- Recognize a proposition `expr ∈ set` whose membership comes from a `ToSet` instance.
    let some (expr, set, _) := toSetMem? type | failure
    -- The represented set must remain valid after leaving the local hypothesis declaration.
    if set.hasFVar || set.hasMVar then
      trace[Tactic.inclusion] "Ignoring non-closed direct hypothesis {type}"
      failure
    -- Ignore membership hypotheses for expressions the goal did not turn into inclusion variables.
    let some iExpr ← requestedIVar? expr | return
    -- The original hypothesis itself proves the resulting one-candidate inclusion body.
    addInclusionHyp iExpr ⟨set, h⟩

end Inclusion
