/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Expr
public meta import Mathlib.Tactic.Inclusion.Core.Extensions
public meta import Mathlib.Lean.Meta.Basic

/-!
# Constructing inclusions

This file defines the recursive construction of inclusion bodies from inclusion extensions and
closes them using inclusion hypotheses from the local context.
-/

public meta section

open Lean Meta Elab Term

namespace Inclusion

initialize registerTraceClass `Tactic.inclusion

/-- Construct an `ExprInclusionBody` for `e`. -/
def mkExprInclusionBody (e : Expr) : InclusionM ExprInclusionBody := do
  if let some iVar := (← get).iVars[e]? then
    trace[Tactic.inclusion] "Reusing ivar for {e}"
    return iVar.toExprInclusionBody
  let savedState ← saveState
  let matchedExts ← getInclusionExtMatches (← read).families e
  for (family, ext) in matchedExts do
    try
      let body ← ext.derive e
      recordExtraModUseFromDecl (isMeta := true) ext.declName
      trace[Tactic.inclusion] "[{family}] {ext.userName} applied to {e}"
      return body
    catch err =>
      trace[Tactic.inclusion]
        "Failed to apply [{family}] {ext.userName} to {e} : {err.toMessageData}"
      restoreState savedState
  throwError "No inclusion extension applies to {e}"

/-- Check that `body.proofBody` is a proof of `e ∈ body.inclusionBody` and infer its `IType`. -/
def ExprInclusionBody.inferIType (body : ExprInclusionBody) (e : Expr) : MetaM IType := do
  let proofBodyType ← inferType body.proofBody
  let invalidProof := m!"{proofBodyType} is not a proof of `{e} ∈ {body.inclusionBody}`"
  let some (e', s, toSetInst) := toSetMem? proofBodyType | throwError invalidProof
  unless ← isDefEq e' e do throwError invalidProof
  unless ← isDefEq s body.inclusionBody do throwError invalidProof
  return ⟨← inferType e, ← inferType body.inclusionBody, toSetInst⟩

/-- Run hypothesis extensions on hypothesis `h`. -/
def runHypothesisExts (h : Expr) : HypothesisM Unit := do
  let type ← instantiateMVars (← inferType h)
  let matchedExts ← getHypothesisExtMatches (← read).families type
  for (family, ext) in matchedExts do
    let saved ← saveState
    try
      ext.derive h type
      recordExtraModUseFromDecl (isMeta := true) ext.declName
      trace[Tactic.inclusion] "[{family}] {ext.userName} processed {type}"
    catch err =>
      trace[Tactic.inclusion]
        "Failed to apply [{family}] {ext.userName} to {type} : {err.toMessageData}"
      restoreState saved

/-- Run hypothesis extensions on all declarations in the local context. -/
def collectHyps : HypothesisM Unit := do
  let context ← read
  if context.iVars.isEmpty then
    return ()
  for ldecl in context.localContext do
    unless ldecl.isImplementationDetail do
      runHypothesisExts ldecl.toExpr

/-- Construct the universal inclusion body for `iExpr`. -/
def mkUniversalHypBody (iExpr : IExpr) : MetaM ExprInclusionBody := do
  let univ ← iExpr.iType.synthUniv
  return ⟨← iExpr.iType.mkUniv univ, ← iExpr.mkMemUniv univ⟩

/-- Combine the candidate hypothesis bodies for `iExpr` using `Refine`, or use its universal
inclusion when there are no candidates. -/
def combineHypBodies (iExpr : IExpr) (bodies : Array ExprInclusionBody) :
    MetaM ExprInclusionBody := do
  if bodies.isEmpty then
    return ← mkUniversalHypBody iExpr
  let first := bodies[0]!
  if bodies.size = 1 then
    return first
  let refiner ← iExpr.iType.synthRefine
  let mut set := first.inclusionBody
  let mut proof := first.proofBody
  for h : i in [1:bodies.size] do
    let next := bodies[i]
    set ← iExpr.iType.mkRefine refiner set next.inclusionBody
    proof ← mkAppM ``Refine.mem_refine #[proof, next.proofBody]
  return ⟨set, proof⟩

/-- Collect inclusion hypotheses and close `body` over its inclusion variables, covers, and shared
parameters. -/
def mkExprInclusion (output : IExpr) (body : ExprInclusionBody) : HypothesisM ExprInclusion := do
  collectHyps
  let context ← read
  let state ← get
  let coarsen? ← match context.iVars.any (·.cover.isSome) with
    | true => some <$> output.iType.synthCoarsen
    | false => pure none
  let body ← context.iVars.foldrM (init := body) fun iVar body => do
    let hypBody ← combineHypBodies iVar.iExpr (state.inclusions[iVar.expr]?.getD #[])
    let inclusion ← mkLambdaFVars #[iVar.setVar] body.inclusionBody
      (binderInfoForMVars := .default)
    let proof ← mkLambdaFVars #[iVar.setVar, iVar.hypVar] body.proofBody
      (binderInfoForMVars := .default)
    match iVar.cover with
    | none =>
      let inclusionBody := mkApp inclusion hypBody.inclusionBody
      let proofBody := mkAppN proof #[hypBody.inclusionBody, hypBody.proofBody]
      return { inclusionBody, proofBody }
    | some cover =>
      let coarsen := coarsen?.get!
      let inclusionBody ← iVar.mkCoverMap output.iType hypBody.inclusionBody cover coarsen inclusion
      let proofBody ← iVar.mkCoverMapProof output hypBody cover coarsen inclusion proof
      return { inclusionBody, proofBody }
  let (params, paramVars) := state.usedParams.toArray.unzip
  let inclusion ← mkLambdaFVars paramVars body.inclusionBody (binderInfoForMVars := .default)
  let proof ← mkLambdaFVars paramVars body.proofBody (binderInfoForMVars := .default)
  return ⟨params, output.iType, inclusion, proof⟩

/-- Construct an `ExprInclusion` for `e`. -/
def toExprInclusion (e : Expr) : InclusionM ExprInclusion := do
  let body ← mkExprInclusionBody e
  let iType ← body.inferIType e
  HypothesisM.run <| mkExprInclusion ⟨iType, e⟩ body

end Inclusion
