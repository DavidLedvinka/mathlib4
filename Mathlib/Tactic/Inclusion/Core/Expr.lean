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

/-- Given `iVar : IVar` and expressions `cover : Cover iVar.type.setType iVar.type.elemType`,
`coarsen : Coarsen outputType.setType outputType.elemType`, and
`inclusion : iVar.type.setType → outputType.setType`, create the corresponding application of
`Cover.coverMap`. -/
def IVar.mkCoverMap (iVar : IVar) (outputType : IType)
    (cover coarsen inclusion : Expr) : MetaM Expr :=
  mkAppOptM ``Cover.coverMap
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      outputType.setType, outputType.elemType, outputType.toSetInst, coarsen,
      iVar.setVar, inclusion]

/-- Given `iVar : IVar`, `output : IExpr`, and expressions for a cover, coarsener, inclusion
function, and the corresponding pointwise inclusion proof, create an application of
`Cover.mem_coverMap`. -/
def IVar.mkCoverMapProof (iVar : IVar) (output : IExpr)
    (cover coarsen inclusion proof : Expr) : MetaM Expr :=
  mkAppOptM ``Cover.mem_coverMap
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      output.iType.setType, output.iType.elemType, output.iType.toSetInst, coarsen,
      iVar.setVar, inclusion, iVar.expr, output.expr, iVar.hypVar, proof]

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

/-- Given an inclusion function `fn` for `goal`, expressions for its parameters and result, and a
proof that the result is `IntervalBool.true`, create an expression proving `goal`. -/
def ExprInclusionFunction.mkGoalProof (fn : ExprInclusionFunction) (goal : Expr)
    (paramExprs : Array Expr) (inclusionExpr inclusionProof : Expr) : Expr :=
  mkAppN (mkConst ``true_of_mem_intervalBool_eq_true)
    #[goal, inclusionExpr, mkAppN fn.proof paramExprs, inclusionProof]

/-- Introduce an array of `Nat` free variables for each param in `params` into the local context
and pass the resulting array to `k`. -/
def withInclusionParams {α : Type} [Inhabited α] (params : Array Name)
    (k : Array Expr → MetaM α) : MetaM α :=
  withLocalDeclsDND (params.map fun name => (name, mkConst ``Nat)) k

/-- **TODO (NOT FOR CODEX)** -/
def mergeInclusionParams (paramArrays : Array (Array Name)) :
    Array Name × Array (Array Nat) := Id.run do
  let mut params := #[]
  let mut positions : NameMap Nat := {}
  let mut argIndices := Array.emptyWithCapacity paramArrays.size
  for inputParams in paramArrays do
    let mut indices := Array.emptyWithCapacity inputParams.size
    for param in inputParams do
      let i ← match positions.find? param with
        | some i => pure i
        | none => do
          let i := params.size
          params := params.push param
          positions := positions.insert param i
          pure i
      indices := indices.push i
    argIndices := argIndices.push indices
  return (params, argIndices)

end Inclusion
