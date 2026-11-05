/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Basic
public import Mathlib.Tactic.Inclusion.Extension.Function

/-!
# API for function inclusion extensions

`mkFunctionExt` lifts a family's chosen inclusion type to nondependent functions. Lambdas are
processed under their binders; other functions become atomic inclusion variables. Applications
are lifted only when they depend on a newly introduced binder, so an ordinary expression such
as `f 0` keeps its scalar inclusion variable and its scalar hypotheses.

The hypothesis helpers reuse the registered scalar rules under binders. Computations may contain
those binders, but must be closed once they are abstracted. Neither inclusion variables nor
variables from the original local context may escape into a hypothesis computation.

For example, `fun i => f i + x` uses a function inclusion variable for `f` and a scalar one for
`x`. A hypothesis `∀ i, f i ≤ (i : ℝ) + 1` supplies an index-dependent upper bound; a hypothesis
`f 0 ≤ 1` supplies a bound only at `0`. Restrictions such as `∀ i, i < 3 → f i ≤ 1` become
piecewise bounds, universal where the restriction is false. For scalar applications, specialization
matches applications already requested by the tactic; it does not solve equations for indices.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- Lift `iType` to pointwise inclusions of functions with domain `domain`. -/
def IType.function (iType : IType) (domain : Expr) : MetaM IType := do
  let toSetInst ← mkAppOptM ``instToSetFun
    #[domain, iType.elemType, iType.setType, iType.toSetInst]
  return ⟨← mkArrow domain iType.elemType, ← mkArrow domain iType.setType, toSetInst⟩

/-- Recognize the pointwise function representation, returning its domain and range inclusion
type. Other representations of functions, such as a specialized matrix enclosure, are untouched. -/
def IType.function? (iType : IType) : Option (Expr × IType) := do
  let_expr instToSetFun domain elemType setType toSetInst := iType.toSetInst | none
  return (domain, ⟨elemType, setType, toSetInst⟩)

private partial def functionIType (range : IType) (type : Expr) : MetaM IType := do
  if ← pureIsDefEq type range.elemType then return range
  let .forallE _ domain body _ ← whnf type | failure
  if body.hasLooseBVars || (← isProp domain) then failure
  return ← (← functionIType range body).function domain

/-- Derive an application of a pointwise inclusion to a computational index. This is only used
under binders: expressions well formed in the original context retain their scalar treatment. -/
def deriveFunctionApplication (e : Expr) : InclusionM ExprInclusionBody := do
  let ctx ← read
  if ← MetavarContext.isWellFormed ctx.localContext e then failure
  let .app f i := e | failure
  if i.hasMVar || (i.find? fun e => e.isFVar && ctx.localContext.contains e.fvarId!).isSome then
    throwError "The function index {i} contains metavariables or variables from the original \
      context"
  let body ← mkExprInclusionBody f
  return ⟨mkApp body.inclusionBody i, ← mkAppM ``apply_mem #[body.proofBody, i]⟩

/-- Construct a low-priority extension for nondependent functions valued in `range`.
Explicit lambdas recurse on their bodies; other functions are atomic. The priority should remain
below that of extensions for particular operations or specialized function representations. -/
def mkFunctionExt (family : Name) (range : IType)
    (priority : Nat := eval_prio low) (name : Name := by exact decl_name%) : InclusionExt where
  family := family
  declName := name
  priority := priority
  derive e := do
    let type ← whnf (← inferType e)
    unless type.isForall do failure
    let iType ← functionIType range type
    if e.isHeadBetaTarget then
      return ← mkExprInclusionBody e.headBeta
    if let .letE _ _ value body _ := e then
      return ← mkExprInclusionBody (body.instantiate1 value)
    if let .lam name domain body bi := e then
      withLocalDecl name bi domain fun i => do
        let body ← mkExprInclusionBody (body.instantiate1 i)
        let inclusionBody ← mkLambdaFVars #[i] body.inclusionBody
        let proof ← mkLambdaFVars #[i] body.proofBody
        return ⟨inclusionBody, ← mkAppM ``fun_mem #[proof]⟩
    else if ← MetavarContext.isWellFormed (← read).localContext e then
      return (← mkIVar ⟨iType, e⟩).toExprInclusionBody
    else
      deriveFunctionApplication e

/-- Use a universally quantified hypothesis to bound a requested function pointwise. -/
def deriveForallFunctionHyp (iExpr : IExpr) (h : Expr) : HypothesisM Unit := do
  let some (domain, range) := iExpr.iType.function? | failure
  let .forallE name hypDomain _ bi ← whnf (← inferType h) | failure
  unless ← pureIsDefEq domain hypDomain do return
  withLocalDecl name bi domain fun i => do
    let request : IExpr := ⟨range, mkApp iExpr.expr i⟩
    let bodies ← deriveHypBodies request (mkApp h i) #[i]
    if bodies.isEmpty then return
    let body ← combineHypBodies request bodies
    let inclusionBody ← mkLambdaFVars #[i] body.inclusionBody
    checkHypInclusionClosed inclusionBody
    let proof ← mkLambdaFVars #[i] body.proofBody
    addInclusionHyp iExpr ⟨inclusionBody, ← mkAppM ``fun_mem #[proof]⟩

/-- Specialize a quantified hypothesis only at indices already present in a requested
application. This does not search for arbitrary witnesses or discharge side conditions. -/
def deriveSpecializedHyp (iExpr : IExpr) (h : Expr) : HypothesisM Unit :=
  withNewMCtxDepth do
    let e := iExpr.expr
    unless e.isApp do return
    let (args, _, conclusion) ← forallMetaTelescopeReducing (← inferType h)
    let (_, candidates) ← StateT.run (s := #[]) <| conclusion.forEach fun candidate => do
      if !candidate.hasLooseBVars && candidate.getAppFn == e.getAppFn &&
          candidate.getAppNumArgs == e.getAppNumArgs then
        modify fun es => es.push candidate
    for candidate in candidates do
      let saved ← saveState
      try
        let bodies ← withoutModifyingMCtx do
          unless ← isDefEq candidate e do failure
          let mut indices := #[]
          for arg in args do
            let value ← instantiateMVars arg
            if value.hasMVar then break
            indices := indices.push value
          if indices.isEmpty then failure
          let bodies ← deriveHypBodies iExpr (mkAppN h indices)
          bodies.mapM fun body => do
            return ⟨← instantiateMVars body.inclusionBody, ← instantiateMVars body.proofBody⟩
        for body in bodies do addInclusionHyp iExpr body
      catch _ => restoreState saved

/-- Turn a conditional bound into a piecewise inclusion, universal where the condition fails.
The condition and its decision procedure must satisfy the same closure requirement as a bound. -/
def deriveConditionalHyp (iExpr : IExpr) (h : Expr) : HypothesisM Unit := do
  let .forallE name condition _ bi ← whnf (← inferType h) | failure
  unless ← isProp condition do failure
  checkHypInclusionClosed condition
  let inst ← synthInstance (mkApp (mkConst ``Decidable) condition)
  checkHypInclusionClosed inst
  withLocalDecl name bi condition fun hp => do
    let bodies ← deriveHypBodies iExpr (mkApp h hp) #[hp]
    if bodies.isEmpty then return
    let body ← combineHypBodies iExpr bodies
    let proof ← mkLambdaFVars #[hp] body.proofBody
    let proofBody ← mkAppOptM ``mem_dite_univ
      #[iExpr.iType.elemType, iExpr.iType.setType, iExpr.iType.toSetInst, none,
        condition, inst, iExpr.expr, ← mkLambdaFVars #[hp] body.inclusionBody, proof]
    let some (_, inclusionBody, _) := toSetMem? (← inferType proofBody) | failure
    checkHypInclusionClosed inclusionBody
    addInclusionHyp iExpr ⟨inclusionBody, proofBody⟩

/-- Use bounds for particular applications of a requested function. Each gives a pointwise
inclusion equal to `Univ.univ` away from that index, using decidable equality on the domain. -/
def deriveFunctionPointHyp (iExpr : IExpr) (h : Expr) : HypothesisM Unit := do
  let some (_, range) := iExpr.iType.function? | failure
  let type ← instantiateMVars (← inferType h)
  let (_, indices) ← StateT.run (s := #[]) <| type.forEach fun e => do
    if let .app f i := e then
      if f == iExpr.expr && !i.hasLooseBVars && !(← get).contains i then
        modify fun indices => indices.push i
  for i in indices do
    let saved ← saveState
    try
      checkHypInclusionClosed i
      let request : IExpr := ⟨range, mkApp iExpr.expr i⟩
      let bodies ← deriveHypBodies request h
      if bodies.isEmpty then continue
      let body ← combineHypBodies request bodies
      let proofBody ← mkAppM ``mem_update_univ #[body.proofBody]
      let some (_, inclusionBody, _) := toSetMem? (← inferType proofBody) | failure
      checkHypInclusionClosed inclusionBody
      addInclusionHyp iExpr ⟨inclusionBody, proofBody⟩
    catch err =>
      trace[Tactic.inclusion] "Could not use point bound at {i}: {err.toMessageData}"
      restoreState saved

end Inclusion
