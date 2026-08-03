module

public import Mathlib.Tactic.Inclusion.Core.ToSet

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace IntervalArithmetic

/-- If `e` is an `Expr` of the form `x ∈ s` using a `ToSet` instance, return
`some (x, s, toSetInst)`. -/
def toSetHyp? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (``Membership.mem, #[_, _, membershipInst, s, x]) := e.getAppFnArgs | none
  let (``instMembershipOfToSet, #[_, _, toSetInst]) := membershipInst.getAppFnArgs | none
  return (x, s, toSetInst)

/-- Create the `Membership` instance induced by `toSetInst`. -/
def mkMembershipOfToSet (xType setType toSetInst : Expr) : MetaM Expr :=
  mkAppOptM ``instMembershipOfToSet #[setType, xType, toSetInst]

/-- Create an expression of the form `x ∈ s` using `toSetInst`. -/
def mkToSetMem (xType setType x s toSetInst : Expr) : MetaM Expr := do
  let membershipInst ← mkMembershipOfToSet xType setType toSetInst
  mkAppOptM ``Membership.mem #[xType, setType, membershipInst, s, x]

/-- Create a right-associated product from `exprs`, using `PUnit.unit` if `exprs` is empty. -/
def mkProdsExpr (exprs : Array Expr) : MetaM Expr := do
  let result ← exprs.foldrM (init := none) fun expr result => do
    let some prods := result | return some expr
    return some (← mkAppM ``Prod.mk #[expr, prods])
  return result.getD (mkConst ``PUnit.unit [1])

/-- Create a right-associated conjunction from `hyps`, using `True.intro` if `hyps` is empty. -/
def mkProdsHyp (hyps : Array Expr) : MetaM Expr := do
  let result ← hyps.foldrM (init := none) fun hyp result => do
    let some prods := result | return some hyp
    return some (← mkAppM ``And.intro #[hyp, prods])
  return result.getD (mkConst ``True.intro)

end IntervalArithmetic
