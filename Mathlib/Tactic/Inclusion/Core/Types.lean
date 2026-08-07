/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Lean.Meta.Basic

/-!
# Datatypes for the `inclusion` tactic

This file defines several datatypes (and some basic API) that are used throughout the core of the
`inclusion` tactic.

-/

public meta section

open Lean Meta

namespace Inclusion

/-- An `IType` is a structure that holds the types of an inclusion expression `x ∈ s`, where
the type of `x` is `elemType`, the type of `s` is `setType` and the `ToSet setType elemType`
instance used is `toSetInst`. -/
structure IType where
  /-- The element type of an inclusion expression -/
  elemType : Expr
  /-- The set type of an inclusion expression. -/
  setType : Expr
  /-- The `ToSet setType elemType` instance of an inclusion expression. -/
  toSetInst : Expr

structure IExpr where
  iVarType : IType
  expr : Expr

/-- An `IVar` is a structure that holds the data of a "free inclusion variable" associated to an
inclusion expression `iexpr`. This includes a pair of variables `setVar`, `hypVar` (which are
sometimes free variables but often synthetic opaque metavariables), where `setVar` is a variable for
an inclusion set and `hypVar` is a (variable) proof of `iexpr.expr ∈ setVar`. -/
structure IVar where
  /-- The inclusion expression represented by the inclusion variable. -/
  iexpr : IExpr
  /-- The inclusion set variable. -/
  setVar : Expr
  /-- The variable `hypVar : iexpr.expr ∈ setVar`. -/
  hypVar : Expr
  /-- An expression of type `CoverCheck iVar.type.setType iVar.type.elemType`. This specifies how an
  inclusion predicate of the `IVar` should be computationally checked (in particular whether it
  should be checked on a cover to reduce the "dependency effect"). -/
  coverCheck : Expr

/-- The `IType` of an `IVar` -/
def IVar.type (iVar : IVar) : IType := iVar.iexpr.iVarType

/-- The associated expression of an `IVar`. -/
def IVar.expr (iVar : IVar) : Expr := iVar.iexpr.expr

/-- An `ExprInclusionFunction` is a structure associated with an expression `e`, that specifies
a function for computing the inclusion of `e` in some set and the proof that this computation
is correct. -/
structure ExprInclusionFunction where
  /-- The array of inclusion parameters used in the inclusion function. -/
  params : Array Name
  /-- The array of inclusion expressions that are substituted for inclusion variables in the
  inclusion function. -/
  iexprs : Array IExpr
  /-- The types of the inclusion result. -/
  outputType : IType
  /-- The expression of the inclusion function of type `ℕ → ... → ℕ → Iα₀ → ... → Iαₙ → Iβ`, with
  one `ℕ` argument for each inclusion parameter and one `Iαᵢ` argument for each inclusion
  variable. -/
  inclusion : Expr
  /-- A proof of
  `∀ n₀ ... nₖ s₀ ... sₘ, iexprs[0].expr ∈ s₀ → ... → iexprs[m].expr ∈ sₘ →`
  `e ∈ inclusion n₀ ... nₖ s₀ ... sₘ`, where `e` is the represented expression. -/
  proof : Expr

/-- An `ExprInclusionBody` is an intermediate structure used in the process of building the
`ExprInclusionFunction` associated to an expression `e`. It contains an `inclusionBody` and
`proofBody` which contain the (possibly partially completed) body of the `inclusion` and `proof`
expressions of the `ExprInclusionFunction` respectively. -/
structure ExprInclusionBody where
  /-- The (possibly partially completed) body of the inclusion function. -/
  inclusionBody : Expr
  /-- The (possibly partially completed) proof of `e ∈ inclusionBody`. -/
  proofBody : Expr

/-- Convert an `IVar` to an `ExprInclusionBody` -/
def IVar.toExprInclusionBody (iVar : IVar) : ExprInclusionBody := ⟨iVar.setVar, iVar.hypVar⟩

/-- An `InclusionParam` is a structure that holds the data of an adjustable `ℕ` typed
inclusion parameter used by the `inclusion` tactic. -/
structure InclusionParam where
  /-- The name of the inclusion parameter. -/
  name : Name
  /-- The expression of the inclusion parameter. -/
  exprVar : Expr

end Inclusion
