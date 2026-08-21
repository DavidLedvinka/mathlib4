/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Core.ToSet
public meta import Mathlib.Tactic.Inclusion.Core.Types

/-!
# Expr helpers for the `inclusion` tactic

This file defines helpers for matching or building certain expressions that are used in the
core of the `inclusion` tactic.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- If `e` is an `Expr` of the form `x ∈ s` using a `ToSet` instance, return
`some (x, s, toSetInst)`. -/
def toSetMem? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (``Membership.mem, #[_, _, membershipInst, s, x]) := e.getAppFnArgs | none
  let (``instMembershipOfToSet, #[_, _, toSetInst]) := membershipInst.getAppFnArgs | none
  return (x, s, toSetInst)

/-- Given expressions `x : xType`, `s : setType`, and `toSetInst : ToSet setType xType`, create
the expression `x ∈ s`. -/
def mkToSetMem (xType setType x s toSetInst : Expr) : MetaM Expr := do
  let membershipInst ← mkAppOptM ``instMembershipOfToSet #[setType, xType, toSetInst]
  mkAppOptM ``Membership.mem #[xType, setType, membershipInst, s, x]

/-- Given `iExpr : IExpr` and `set : iExpr.iType.setType`, create the expression
`iExpr.expr ∈ set`. -/
def IExpr.mkMem (iExpr : IExpr) (set : Expr) : MetaM Expr :=
  mkToSetMem iExpr.iType.elemType iExpr.iType.setType iExpr.expr set iExpr.iType.toSetInst

/-- Construct the initial accumulated hypothesis body for `iVar`. -/
def IVar.mkEmptyHypBody (iVar : IVar) : MetaM ExprInclusionBody := do
  let inclusionBody ← mkAppM ``HypothesisAccumulator.empty #[iVar.hypType.accumulator]
  let proofBody ← mkAppM ``HypothesisAccumulator.mem_empty
    #[iVar.hypType.accumulator, iVar.expr]
  return { inclusionBody, proofBody }

/-- Combine two accumulated hypothesis bodies for `iVar`. -/
def IVar.combineHypBodies (iVar : IVar) (left right : ExprInclusionBody) :
    MetaM ExprInclusionBody := do
  let inclusionBody ← mkAppM ``HypothesisAccumulator.combine
    #[iVar.hypType.accumulator, left.inclusionBody, right.inclusionBody]
  let proofBody ← mkAppM ``HypothesisAccumulator.mem_combine
    #[iVar.hypType.accumulator, left.proofBody, right.proofBody]
  return { inclusionBody, proofBody }

/-- Convert a hypothesis body in the main representation of `iVar` to its accumulator
representation. -/
def IVar.accumulateMainHypBody (iVar : IVar) (body : ExprInclusionBody) :
    MetaM ExprInclusionBody := do
  let inclusionBody ← mkAppM ``HypothesisAccumulator.ofMain
    #[iVar.hypType.accumulator, body.inclusionBody]
  let proofBody ← mkAppM ``HypothesisAccumulator.mem_ofMain
    #[iVar.hypType.accumulator, body.proofBody]
  return { inclusionBody, proofBody }

/-- Convert an accumulated hypothesis body for `iVar` to its main representation. -/
def IVar.finishHypBody (iVar : IVar) (body : ExprInclusionBody) :
    MetaM ExprInclusionBody := do
  let result ← mkAppM ``HypothesisAccumulator.toMain?
    #[iVar.hypType.accumulator, body.inclusionBody]
  let result' ← whnf result
  let (``Option.some, #[_, inclusionBody]) := result'.getAppFnArgs
    | throwError "The hypotheses for {iVar.expr} do not determine an inclusion in \
        {iVar.type.setType}"
  let proofBody ← mkAppM ``HypothesisAccumulator.mem_toMain
    #[iVar.hypType.accumulator, body.proofBody, ← mkEqRefl result]
  return { inclusionBody, proofBody }

/-- Given

· `source : iVar.type.setType`,
· `outputType : IType`,
· `cover : Cover iVar.type.setType iVar.type.elemType`,
· `coarsen : Coarsen outputType.setType outputType.elemType`, and
· `inclusion : iVar.type.setType → outputType.setType`,

create the expression `cover.coverMap source inclusion : outputType.setType`. -/
def IVar.mkCoverMap (iVar : IVar) (outputType : IType)
    (source cover coarsen inclusion : Expr) : MetaM Expr :=
  mkAppOptM ``Cover.coverMap
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      outputType.setType, outputType.elemType, outputType.toSetInst, coarsen,
      source, inclusion]

/-- Given

· a source inclusion body for `iVar`,
· `output : IExpr`,
· `cover : Cover iVar.type.setType iVar.type.elemType`,
· `coarsen : Coarsen output.iType.setType output.iType.elemType`,
· `inclusion : iVar.type.setType → output.iType.setType`, and
· `proof : ∀ s, iVar.expr ∈ s → output.expr ∈ inclusion s`,

create a proof of `output.expr ∈ cover.coverMap source.inclusionBody inclusion`. -/
def IVar.mkCoverMapProof (iVar : IVar) (output : IExpr)
    (source : ExprInclusionBody) (cover coarsen inclusion proof : Expr) : MetaM Expr := do
  let outputLevel ← getDecLevel output.iType.setType
  let setLevel ← getDecLevel iVar.type.setType
  let elemLevel ← getDecLevel iVar.type.elemType
  return mkAppN (mkConst ``Cover.mem_coverMap [outputLevel, setLevel, elemLevel])
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      output.iType.setType, output.iType.elemType, output.iType.toSetInst, coarsen,
      source.inclusionBody, inclusion, iVar.expr, output.expr, source.proofBody, proof]

/-- Given `iType : IType`, synthesize an expression of type
`Coarsen iType.setType iType.elemType`. -/
def IType.synthCoarsen (iType : IType) : MetaM Expr := do
  let type ← mkAppOptM ``Coarsen #[iType.setType, iType.elemType, iType.toSetInst]
  try synthInstance type catch _ =>
    throwError "No `Coarsen` instance is registered for {iType.setType}"

/-- Given an expression `b : IntervalBool`, create the expression proving `b = b`. -/
def mkIntervalBoolRefl (b : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``IntervalBool) b

/-- Given an `ExprInclusion` `inc` for `goal`, and a proof
`inclusionProof : inc.inclusion = IntervalBool.true` create a proof of `goal`. -/
def ExprInclusion.mkGoalProof (inc : ExprInclusion) (goal inclusionProof : Expr) : Expr :=
  mkAppN (mkConst ``true_of_mem_intervalBool_eq_true)
    #[goal, inc.inclusion, inc.proof, inclusionProof]

end Inclusion
