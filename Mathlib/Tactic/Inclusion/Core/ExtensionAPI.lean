/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core

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
  if let some exprVar := (← get).usedParams.find? name then
    return some exprVar
  let some param := (inclusionParamExt.getState (← getEnv)).find? name
    | throwError "Unknown inclusion parameter '{name}'"
  let enabled := param.enabledByDefault || (← read).enabledParams.contains name
  unless enabled do return none
  let ctx ← read
  let exprVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances (mkConst ``Nat) .syntheticOpaque
  modify fun state => { state with usedParams := state.usedParams.insert name exprVar }
  return some exprVar

/-- Create and register an inclusion variable for `e`, represented using `setType` and `toSetInst`
and optionally mapped over `cover`. Its set and membership-proof variables are synthetic opaque
metavariables in the initial local context of the current `InclusionM` computation. -/
def mkIVar (e setType toSetInst : Expr) (cover : Option Expr := none) : InclusionM IVar := do
  let ctx ← read
  unless ← MetavarContext.isWellFormed ctx.localContext e do
    throwError "Cannot create an inclusion variable for {e} because it depends on variables \
      introduced while constructing the inclusion function"
  let eType ← inferType e
  unless ← MetavarContext.isWellFormed ctx.localContext eType do
    throwError "Cannot create an inclusion variable for {e} because its type depends on variables \
      introduced while constructing the inclusion function"
  unless ← MetavarContext.isWellFormed ctx.localContext setType do
    throwError "Cannot use set type {setType} for {e} because it depends on variables introduced \
      while constructing the inclusion function"
  unless ← MetavarContext.isWellFormed ctx.localContext toSetInst do
    throwError "Cannot use the `ToSet` instance for {e} because it depends on variables introduced \
      while constructing the inclusion function"
  let iExpr : IExpr := ⟨⟨eType, setType, toSetInst⟩, e⟩
  let setVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances setType .syntheticOpaque
  let hypType ← iExpr.mkMem setVar
  let hypVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances hypType .syntheticOpaque
  let iVar := { iExpr, setVar, hypVar, cover }
  modify fun state => { state with iVars := state.iVars.insert iVar.expr iVar }
  return iVar

/-- Construct a closed inclusion function for `e` with the expected output type. -/
def toClosedExprInclusionFunction (e : Expr) (expected : IType)
    (enabledParams : NameSet := {}) (enabledFamilies : NameSet := {}) :
    MetaM ExprInclusionFunction := do
  let fn ← toExprInclusionFunction e (enabledParams := enabledParams)
    (enabledFamilies := enabledFamilies)
  unless fn.iExprs.isEmpty do
    throwError "The inclusion function for {e} depends on inclusion variables"
  if fn.inclusion.hasFVar then
    throwError "The computational inclusion function for {e} contains a free variable"
  if fn.inclusion.hasMVar then
    throwError "The computational inclusion function for {e} contains a metavariable"
  ensureOutputType fn.outputType expected
  return fn

/-- An inclusion hypothesis for one of the inclusion variables requested by the target
computation. -/
structure InclusionHypResult where
  expr : Expr
  hyp : ExprInclusionFunction

/-- Find the canonical target inclusion variable definitionally equal to `e`. Exact expression
matching is attempted first and does not invoke the elaborator. -/
def requestedIVar? (e : Expr) : HypothesisM (Option IExpr) := do
  let ctx ← read
  if let some iExpr := ctx.iExprsMap[e]? then
    return some iExpr
  for requested in ctx.iExprsArray do
    if ← isDefEqWithoutAssignment e requested.expr then
      return some requested
  return none

/-- If `result.expr` is a requested inclusion expression, validate and add `result.hyp` to its
candidate inclusion hypotheses. Otherwise, do nothing. -/
def addInclusionHypResult (result : InclusionHypResult) : HypothesisM Unit := do
  let some iExpr ← requestedIVar? result.expr | return
  unless result.hyp.iExprs.isEmpty do
    throwError "An inclusion hypothesis for {result.expr} contains inclusion variables"
  ensureOutputType result.hyp.outputType iExpr.iType
  modify fun state => { state with inclusions := state.inclusions.alter iExpr.expr fun
    | some hyps => hyps.push result.hyp
    | none => #[result.hyp] }

/-- Construct a closed inclusion function for a hypothesis endpoint. -/
def mkHypInclusionFunction (e : Expr)
    (expected : IType) : HypothesisM ExprInclusionFunction := do
  let ctx ← read
  toClosedExprInclusionFunction e expected (enabledParams := ctx.enabledParams)
    (enabledFamilies := ctx.enabledFamilies)

/-- The generic hypothesis extension that uses a closed `ToSet` membership hypothesis directly as
an inclusion hypothesis. -/
@[hypothesisExt _ ∈ _]
meta def directMembershipHyp : HypothesisExt where
  family := `core
  derive h type := do
    let some (expr, set, toSetInst) := toSetMem? type | failure
    if set.hasFVar || set.hasMVar then
      trace[Tactic.inclusion] "Ignoring non-closed direct hypothesis {type}"
      failure
    let iType : IType := ⟨← inferType expr, ← inferType set, toSetInst⟩
    addInclusionHypResult ⟨expr, ⟨#[], #[], iType, set, h⟩⟩

end Inclusion
