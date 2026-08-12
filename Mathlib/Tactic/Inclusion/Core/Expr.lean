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

/-- Given `iVar : IVar`, an inclusion set `source`, and expressions for a cover, coarsener, and
inclusion function, create the corresponding application of `Cover.coverMap`. -/
def IVar.mkCoverMap (iVar : IVar) (outputType : IType)
    (source cover coarsen inclusion : Expr) : MetaM Expr :=
  mkAppOptM ``Cover.coverMap
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      outputType.setType, outputType.elemType, outputType.toSetInst, coarsen,
      source, inclusion]

/-- Given `iVar : IVar`, `output : IExpr`, a source inclusion body, and expressions for a cover,
coarsener, inclusion function, and its pointwise inclusion proof, create an application of
`Cover.mem_coverMap`. -/
def IVar.mkCoverMapProof (iVar : IVar) (output : IExpr)
    (source : ExprInclusionBody) (cover coarsen inclusion proof : Expr) : MetaM Expr :=
  mkAppOptM ``Cover.mem_coverMap
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      output.iType.setType, output.iType.elemType, output.iType.toSetInst, coarsen,
      source.inclusionBody, inclusion, iVar.expr, output.expr, source.proofBody, proof]

/-- Given `iType : IType`, synthesize an expression of type
`Coarsen iType.setType iType.elemType`. -/
def IType.synthCoarsen (iType : IType) : MetaM Expr := do
  let type ← mkAppOptM ``Coarsen #[iType.setType, iType.elemType, iType.toSetInst]
  try synthInstance type catch _ =>
    throwError "No `Coarsen` instance is registered for {iType.setType}"

/-- Given `iType : IType`, `refiner : Refine iType.setType iType.elemType`, and expressions
`left right : iType.setType`, create the expression `refiner.refine left right`. -/
def IType.mkRefine (iType : IType) (refiner left right : Expr) : MetaM Expr :=
  mkAppOptM ``Refine.refine #[iType.setType, iType.elemType, iType.toSetInst, refiner, left, right]

/-- Given `iType : IType`, synthesize an expression of type
`Refine iType.setType iType.elemType`. -/
def IType.synthRefine (iType : IType) : MetaM Expr := do
  let type ← mkAppOptM ``Refine #[iType.setType, iType.elemType, iType.toSetInst]
  try synthInstance type catch _ =>
    throwError "No `Refine` instance is registered for {iType.setType}"

/-- Given `iType : IType` and `univ : Univ iType.setType iType.elemType`, create the
expression for `Univ.univ`. -/
def IType.mkUniv (iType : IType) (univ : Expr) : MetaM Expr :=
  mkAppOptM ``Univ.univ #[iType.setType, iType.elemType, iType.toSetInst, univ]

/-- Given `iExpr : IExpr` and `univ : Univ iExpr.iType.setType iExpr.iType.elemType`, create the
expression for the proof of `iExpr.expr ∈ Univ.univ`. -/
def IExpr.mkMemUniv (iExpr : IExpr) (univ : Expr) : MetaM Expr :=
  mkAppOptM ``Univ.mem_univ
    #[iExpr.iType.setType, iExpr.iType.elemType, iExpr.iType.toSetInst, univ, iExpr.expr]

/-- Given `iType : IType`, synthesize an expression of type `Univ iType.setType iType.elemType`. -/
def IType.synthUniv (iType : IType) : MetaM Expr := do
  let type ← mkAppOptM ``Univ #[iType.setType, iType.elemType, iType.toSetInst]
  try synthInstance type catch _ =>
    throwError "No `Univ` instance is registered for {iType.setType}"

/-- Given an expression `b : IntervalBool`, create the expression proving `b = b`. -/
def mkIntervalBoolRefl (b : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``IntervalBool) b

/-- Given an inclusion function `fn` for `goal`, expressions for its parameters and result, and a
proof that the result is `IntervalBool.true`, create an expression proving `goal`. -/
def ExprInclusion.mkGoalProof (fn : ExprInclusion) (goal : Expr)
    (paramExprs : Array Expr) (inclusionExpr inclusionProof : Expr) : Expr :=
  mkAppN (mkConst ``true_of_mem_intervalBool_eq_true)
    #[goal, inclusionExpr, mkAppN fn.proof paramExprs, inclusionProof]

end Inclusion
