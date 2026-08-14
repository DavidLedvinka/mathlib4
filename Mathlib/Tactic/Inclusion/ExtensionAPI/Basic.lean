/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.CheckElab

/-!
# Basic API for `inclusion` extensions

This file defines helpers for safely interacting with the `InclusionM` and `HypothesisM` monads
when constructing extensions for the `inclusion` tactic.
-/

public meta section

open Lean Meta

namespace Inclusion

private def mkParamVar (name : Name) (context : InclusionM.Context) : MetaM Expr := do
  let some param := (inclusionParamExt.getState (← getEnv)).find? name
    | throwError "Unknown inclusion parameter '{name}'"
  unless param.defaultValue.isSome || context.enabledParams.contains name do
    throwError "No value was supplied for inclusion parameter '{name}'"
  mkFreshExprMVarAt context.localContext context.localInstances
    (mkConst ``Nat) .syntheticOpaque

section InclusionM

def getParam (name : Name) : InclusionM Expr := do
  if let some exprVar := (← get).usedParams.find? name then
    return exprVar
  let paramVar ← mkParamVar name (← read)
  modify fun state => { state with usedParams := state.usedParams.insert name paramVar }
  return paramVar

private def checkIVarWellFormed (localContext : LocalContext) (iExpr : IExpr) : MetaM Unit := do
  let ⟨type, e⟩ := iExpr
  unless ← MetavarContext.isWellFormed localContext e do
    throwError "Cannot create an inclusion variable for {e} because it depends on variables \
      introduced while constructing the inclusion function"
  unless ← MetavarContext.isWellFormed localContext type.elemType do
    throwError "Cannot create an inclusion variable for {e} because its type depends on \
      variables introduced while constructing the inclusion function"
  unless ← MetavarContext.isWellFormed localContext type.setType do
    throwError "Cannot use set type {type.setType} for {e} because it depends on \
      variables introduced while constructing the inclusion function"
  unless ← MetavarContext.isWellFormed localContext type.toSetInst do
    throwError "Cannot use the `ToSet` instance for {e} because it depends on variables \
      introduced while constructing the inclusion function"

/-- Create and register an inclusion variable for `iExpr`. -/
def mkIVar (iExpr : IExpr) (cover : Option Expr := none) : InclusionM IVar := do
  let ctx ← read
  checkIVarWellFormed ctx.localContext iExpr
  let setVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances iExpr.iType.setType .syntheticOpaque
  let hypType ← iExpr.mkMem setVar
  let hypVar ← mkFreshExprMVarAt ctx.localContext ctx.localInstances hypType .syntheticOpaque
  let iVar := { iExpr, setVar, hypVar, cover }
  modify fun state => { state with iVars := state.iVars.insert iVar.expr iVar }
  return iVar

/-- Construct an inclusion extension that treats matching expressions as inclusion variables.
`mkSetType` chooses the computational set type from the inferred element type, and `mkCover` may
attach a cover to the resulting inclusion variable. -/
def mkIVarExt (mkSetType : Expr → InclusionM Expr)
    (mkCover : IExpr → InclusionM (Option Expr) := fun _ ↦ pure none)
    (priority : Nat := eval_prio low) (name : Name := by exact decl_name%) : InclusionExt where
  declName := name
  userName := name
  priority := priority
  derive e := do
    let elemType ← inferType e
    let setType ← mkSetType elemType
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[setType, elemType])
    let iExpr : IExpr := ⟨⟨elemType, setType, toSetInst⟩, e⟩
    return (← mkIVar iExpr (← mkCover iExpr)).toExprInclusionBody

/-- Construct an inclusion extension for a nondependent inclusion variable with fixed element and
represented-set types. -/
def mkNDIVarExt (elemType : Expr) (setType : MetaM Expr)
    (mkCover : IExpr → InclusionM (Option Expr) := fun _ ↦ pure none)
    (priority : Nat := eval_prio low) (name : Name := by exact decl_name%) : InclusionExt :=
  mkIVarExt
    (fun actualType => do
      unless ← isDefEq actualType elemType do failure
      liftM setType)
    mkCover (priority := priority) (name := name)

structure InclusionHypothesisArg where
  exprIdx : Nat
  setIdx : Nat
  proofIdx : Nat
  deriving Inhabited, ToExpr

structure ParamArg where
  name : Name
  idx : Nat
  deriving Inhabited, ToExpr

def deriveInclusionOp (theoremName : Name) (hypArgs : Array InclusionHypothesisArg)
    (paramArgs : Array ParamArg) (e : Expr) : InclusionM ExprInclusionBody := do
  let theoremExpr ← mkConstWithFreshMVarLevels theoremName
  let (args, binderInfos, conclusion) ← forallMetaTelescopeReducing (← inferType theoremExpr)
  let some (expr, inclusionBody, _) := toSetMem? conclusion | failure
  unless ← isDefEq expr e do failure
  for ⟨name, idx⟩ in paramArgs do
    unless ← isDefEq args[idx]! (← getParam name) do failure
  for ⟨exprIdx, setIdx, proofIdx⟩ in hypArgs do
    let arg ← instantiateMVars args[exprIdx]!
    let body ← mkExprInclusionBody arg
    unless ← isDefEq args[setIdx]! body.inclusionBody do failure
    unless ← isDefEq args[proofIdx]! body.proofBody do failure
  for h : i in [:args.size] do
    let argId := args[i].mvarId!
    unless ← argId.isAssigned do
      if binderInfos[i]!.isInstImplicit then
        argId.assign (← synthInstance (← argId.getType))
      else
        throwError "Could not infer theorem argument '{(← argId.getDecl).userName}' in inclusion \
          extension generated from '{theoremName}'"
  return ⟨← instantiateMVars inclusionBody, ← instantiateMVars (mkAppN theoremExpr args)⟩

end InclusionM

section HypothesisM

/-- Return the shared expression variable for the enabled inclusion parameter `name`. -/
def HypothesisM.getParam (name : Name) : HypothesisM Expr := do
  if let some paramVar := (← get).usedParams.find? name then
    return paramVar
  let paramVar ← mkParamVar name (← read).toContext
  modify fun state => { state with usedParams := state.usedParams.insert name paramVar }
  return paramVar

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

/-- Apply the hypothesis extension generated from `theoremName` to hypothesis `h`. -/
def deriveHypothesisOp (theoremName : Name) (sourceIdx : Nat)
    (hypArgs : Array InclusionHypothesisArg) (paramArgs : Array ParamArg)
    (h type : Expr) : HypothesisM Unit := do
  let theoremExpr ← mkConstWithFreshMVarLevels theoremName
  let (args, binderInfos, conclusion) ← forallMetaTelescopeReducing (← inferType theoremExpr)
  let sourceId := args[sourceIdx]!.mvarId!
  unless ← isDefEq (← sourceId.getType) type do failure
  sourceId.assign h
  let some (outputExpr, outputSet, outputToSetInst) := toSetMem? conclusion | failure
  let outputExpr ← instantiateMVars outputExpr
  let some iExpr ← requestedIVar? outputExpr | return
  for ⟨name, idx⟩ in paramArgs do
    unless ← isDefEq args[idx]! (← HypothesisM.getParam name) do failure
  unless ← isDefEq (← inferType outputExpr) iExpr.iType.elemType do failure
  unless ← isDefEq (← inferType outputSet) iExpr.iType.setType do failure
  unless ← isDefEq outputToSetInst iExpr.iType.toSetInst do failure
  for ⟨exprIdx, setIdx, proofIdx⟩ in hypArgs do
    let inputExpr ← instantiateMVars args[exprIdx]!
    let inputSet ← instantiateMVars args[setIdx]!
    let proofType ← instantiateMVars (← args[proofIdx]!.mvarId!.getType)
    let some (_, _, inputToSetInst) := toSetMem? proofType | failure
    let expected : IType :=
      ⟨← inferType inputExpr, ← inferType inputSet, inputToSetInst⟩
    let body ← mkHypInclusionBody inputExpr expected
    unless ← isDefEq args[setIdx]! body.inclusionBody do failure
    unless ← isDefEq args[proofIdx]! body.proofBody do failure
  for h : i in [:args.size] do
    let argId := args[i].mvarId!
    unless ← argId.isAssigned do
      if binderInfos[i]!.isInstImplicit then
        argId.assign (← synthInstance (← argId.getType))
      else
        throwError "Could not infer theorem argument '{(← argId.getDecl).userName}' in hypothesis \
          extension generated from '{theoremName}'"
  let body :=
    { inclusionBody := ← instantiateMVars outputSet
      proofBody := ← instantiateMVars (mkAppN theoremExpr args) }
  addInclusionHyp iExpr body

end HypothesisM

end Inclusion
