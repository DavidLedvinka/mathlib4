/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Expr
public meta import Mathlib.Tactic.Inclusion.Core.Extensions

/-!
# Constructing inclusion functions

This file defines `toExprInclusionFunction` for constructing an inclusion function for an
input expression by recursively applying inclusion extensions.
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
  let exts := inclusionExt.getState (← getEnv)
  let matchedExts ← exts.getSortedMatch (← read).enabledFamilies e (·.priority)
  for ext in matchedExts do
    try
      let body ← ext.derive e
      recordExtraModUseFromDecl (isMeta := true) ext.declName
      trace[Tactic.inclusion] "[{ext.family}] {ext.userName} applied to {e}"
      return body
    catch err =>
      trace[Tactic.inclusion]
        "Failed to apply [{ext.family}] {ext.userName} to {e} : {err.toMessageData}"
      restoreState savedState
  throwError "No inclusion extension applies to {e}"

/-- Apply the covers of `iVars` to an inclusion body. -/
private def mkCoveredExprInclusionBody (output : IExpr)
    (body : ExprInclusionBody) (iVars : Array IVar) : MetaM ExprInclusionBody := do
  unless iVars.any (·.cover.isSome) do
    return body
  let coarsen ← output.iType.synthCoarsen
  iVars.foldrM (init := body) fun iVar body ↦ do
    let some cover := iVar.cover | return body
    let inclusion ← mkLambdaFVars #[iVar.setVar] body.inclusionBody
      (binderInfoForMVars := .default)
    let proof ← mkLambdaFVars #[iVar.setVar, iVar.hypVar] body.proofBody
      (binderInfoForMVars := .default)
    let inclusionBody ← iVar.mkCoverMap output.iType cover coarsen inclusion
    let proofBody ← iVar.mkCoverMapProof output cover coarsen inclusion proof
    return { inclusionBody, proofBody }

/-- Given an `ExprInclusionBody` for `e`, make its associated `ExprInclusionFunction`. -/
private def mkExprInclusionFunction (e : Expr) (body : ExprInclusionBody) :
    InclusionM ExprInclusionFunction := do
  let state ← get
  let iVars := state.iVars.valuesArray
  let (params, paramVars) := state.usedParams.toArray.unzip
  let (iExprs, setVars, hypVars) :=
    (iVars.map (·.iExpr), iVars.map (·.setVar), iVars.map (·.hypVar))
  let proofBodyType ← inferType body.proofBody
  let invalidProof := m!"{proofBodyType} is not a proof of `{e} ∈ {body.inclusionBody}`"
  let some (e', s, toSetInst) := toSetMem? proofBodyType | throwError invalidProof
  unless ← isDefEq e' e do throwError invalidProof
  unless ← isDefEq s body.inclusionBody do throwError invalidProof
  let output : IExpr := ⟨⟨← inferType e, ← inferType body.inclusionBody, toSetInst⟩, e⟩
  let coveredBody ← mkCoveredExprInclusionBody output body iVars
  let inclusion ← mkLambdaFVars (paramVars ++ setVars) coveredBody.inclusionBody
    (binderInfoForMVars := .default)
  let proof ← mkLambdaFVars (paramVars ++ setVars ++ hypVars) coveredBody.proofBody
    (binderInfoForMVars := .default)
  return ⟨params, iExprs, output.iType, inclusion, proof⟩

/-- Construct an `ExprInclusionFunction` for `e`. -/
def toExprInclusionFunction (e : Expr)
    (enabledParams : NameSet := {}) (enabledFamilies : Array Name := #[]) :
    MetaM ExprInclusionFunction :=
  InclusionM.run (enabledParams := enabledParams) (enabledFamilies := enabledFamilies) do
    let body ← mkExprInclusionBody e
    mkExprInclusionFunction e body

end Inclusion
