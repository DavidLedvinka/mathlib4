/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Elab

/-!
# Basic API for `inclusion` extensions

This file defines helpers for safely interacting with the `InclusionM` and `HypothesisM` monads
when constructing extensions for the `inclusion` tactic.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- Return the value of parameter `name`, if it was supplied or has a default. -/
def InclusionM.getParam? (name : Name) : InclusionM (Option Expr) := do
  let some decl := (inclusionParamExt.getState (← getEnv)).find? name
    | throwError "Unknown inclusion parameter `{name}`"
  if let some value := (← read).paramSettings.find? name then
    return some value
  return decl.defaultValue?

/-- Return the value of parameter `name`. -/
def InclusionM.getParam (name : Name) : InclusionM Expr := do
  let some value ← InclusionM.getParam? name
    | throwError "No value was supplied for inclusion parameter `{name}`"
  return value

/-- Return the value of parameter `name`, if it was supplied or has a default. -/
def HypothesisM.getParam? (name : Name) : HypothesisM (Option Expr) := do
  let some decl := (inclusionParamExt.getState (← getEnv)).find? name
    | throwError "Unknown inclusion parameter `{name}`"
  if let some value := (← read).paramSettings.find? name then
    return some value
  return decl.defaultValue?

/-- Return the value of parameter `name`, or report that it was not supplied. -/
def HypothesisM.getParam (name : Name) : HypothesisM Expr := do
  let some value ← HypothesisM.getParam? name
    | throwError "No value was supplied for inclusion parameter `{name}`"
  return value

/-- Check that `iExpr` and its hypothesis representation are well formed in `localContext`. -/
private def checkIVarWellFormed (localContext : LocalContext) (iExpr : IExpr)
    (hypType : HypothesisType) : MetaM Unit := do
  let ⟨iType, e⟩ := iExpr
  unless ← MetavarContext.isWellFormed localContext e do
    throwError "Cannot create an inclusion variable for {e} because it depends on variables \
      introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext iType.elemType do
    throwError "Cannot create an inclusion variable for {e} because its type depends on \
      variables introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext iType.setType do
    throwError "Cannot use set type {iType.setType} for {e} because it depends on \
      variables introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext iType.toSetInst do
    throwError "Cannot use the `ToSet` instance for {e} because it depends on variables \
      introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext hypType.iType.elemType do
    throwError "Cannot use the hypothesis element type for {e} because it depends on variables \
      introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext hypType.iType.setType do
    throwError "Cannot use hypothesis set type {hypType.iType.setType} for {e} because it depends \
      on variables introduced while constructing the inclusion"
  unless ← isDefEq hypType.iType.elemType iType.elemType do
    throwError "The hypothesis representation for {e} has an unexpected element type"
  unless ← MetavarContext.isWellFormed localContext hypType.iType.toSetInst do
    throwError "Cannot use the hypothesis `ToSet` instance for {e} because it depends on variables \
      introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext hypType.accumulator do
    throwError "Cannot use the hypothesis accumulator for {e} because it depends on variables \
      introduced while constructing the inclusion"
  let expectedType ← mkAppOptM ``HypothesisAccumulator
    #[hypType.iType.setType, iType.setType, iType.elemType, hypType.iType.toSetInst,
      iType.toSetInst]
  unless ← isDefEq (← inferType hypType.accumulator) expectedType do
    throwError "The hypothesis accumulator for {e} has an unexpected type"

/-- Create and register an inclusion variable for `iExpr`, accumulating its hypotheses according
to `hypType`. -/
def mkIVar (iExpr : IExpr) (hypType : HypothesisType) (cover : Option Expr := none) :
    InclusionM IVar := do
  let ctx ← read
  if ctx.noIVars then
    throwError "Cannot create an inclusion variable for {iExpr.expr} since `noIVars` is set to true"
  checkIVarWellFormed ctx.localContext iExpr hypType
  let setVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances iExpr.iType.setType .syntheticOpaque
  let hypVarType ← iExpr.mkMem setVar
  let hypVar ← mkFreshExprMVarAt ctx.localContext ctx.localInstances hypVarType .syntheticOpaque
  let iVar := { iExpr, hypType, setVar, hypVar, cover }
  modify fun state => { state with iVars := state.iVars.insert iVar.expr iVar }
  return iVar

/-- Construct an inclusion extension for making non dependently typed inclusion variables with
main inclusion type `iType` and the hypothesis representation constructed by `mkHypType iExpr`. -/
def mkNDIVarExt (iType : IType) (mkHypType : IExpr → InclusionM HypothesisType)
    (mkCover : InclusionM (Option Expr) := pure none)
    (priority : Nat := eval_prio low) (name : Name := by exact decl_name%) : InclusionExt where
  declName := name
  userName := name
  priority := priority
  derive e := do
    let eType ← inferType e
    unless ← isDefEq eType iType.elemType do failure
    let iExpr : IExpr := ⟨iType, e⟩
    return (← mkIVar iExpr (← mkHypType iExpr) (← mkCover)).toExprInclusionBody

/-- Return the inclusion variable registered for `e`, if there is one. -/
def findIVar? (e : Expr) : HypothesisM (Option IVar) := do
  return (← read).iVarsMap[e]?

private def IType.isDefEq (type expectedType : IType) : MetaM Bool := do
  unless ← pureIsDefEq type.elemType expectedType.elemType do return false
  unless ← pureIsDefEq type.setType expectedType.setType do return false
  pureIsDefEq type.toSetInst expectedType.toSetInst

/-- Construct a closed inclusion body for an expression argument of a hypothesis rule. -/
def mkHypExprInclusionBody (e : Expr) : HypothesisM ExprInclusionBody := do
  let ctx ← read
  let inclusionContext := { ctx.toContext with noIVars := true }
  let (body, inclusionState) ← (mkExprInclusionBody e).runWith inclusionContext
  unless inclusionState.iVars.isEmpty do
    throwError "The inclusion for {e} depends on inclusion variables"
  if body.inclusionBody.hasFVar then
    throwError "The inclusion hypothesis generated from {e} contains a free variable"
  if body.inclusionBody.hasMVar then
    throwError "The inclusion hypothesis generated from {e} contains a metavariable"
  return body

/-- Add the inclusion hypothesis `body` for `iVar`, converting it from the main representation to
the accumulator representation when necessary. -/
def addInclusionHyp (iVar : IVar) (body : ExprInclusionBody) : HypothesisM Unit := do
  let hypIExpr := iVar.hypIExpr
  let bodyType ← body.inferIType hypIExpr.expr
  let body ← if ← bodyType.isDefEq hypIExpr.iType then
    pure body
  else if ← bodyType.isDefEq iVar.type then
    iVar.accumulateMainHypBody body
  else
    throwError "Inclusion hypothesis for {iVar.expr} has set type {bodyType.setType}, expected \
      {hypIExpr.iType.setType} or {iVar.type.setType}"
  let state ← get
  let body ← match state.inclusions[iVar.expr]? with
    | some accumulated => iVar.combineHypBodies accumulated body
    | none => pure body
  set { state with inclusions := state.inclusions.insert iVar.expr body }

end Inclusion
