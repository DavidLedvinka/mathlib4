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

/-- Given `iexpr : IExpr` and `set : iexpr.iVarType.setType`, create the expression
`iexpr.expr ∈ set`. -/
def IExpr.mkMem (iexpr : IExpr) (set : Expr) : MetaM Expr :=
  mkToSetMem iexpr.iVarType.elemType iexpr.iVarType.setType iexpr.expr set iexpr.iVarType.toSetInst

/-- Given expressions `coverCheck : CoverCheck iVarType.setType iVarType.elemType`,
`set : iVarType.setType`, and `predicate : iVarType.setType → IntervalBool`,
create the expression `CoverCheck.check coverCheck set predicate`. -/
def mkCoverCheck (iVarType : IType) (set coverCheck predicate : Expr) : MetaM Expr :=
  mkAppOptM ``CoverCheck.check
    #[iVarType.setType, iVarType.elemType, iVarType.toSetInst, coverCheck, set, predicate]

end Inclusion
