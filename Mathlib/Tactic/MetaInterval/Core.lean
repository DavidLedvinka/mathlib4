module

public meta import Mathlib.Tactic.MetaInterval.Expr
public meta import Mathlib.Tactic.MetaInterval.Dyadic
public meta import Mathlib.Tactic.MetaInterval.Certificate
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Data.Real.Basic

set_option linter.style.header false

@[expose] public meta section

open Lean Meta Elab Tactic Qq

namespace IntervalArithmetic

structure IntervalM.State where
  cache : ExprMap (IntervalCertificate × Interval Dyadic) := {}
  deriving Inhabited

abbrev IntervalM := StateT IntervalM.State MetaM

/-- Temporarily we only extract the first appearance of `x ∈ (i.map Dyadic.toReal).toSet`. -/
def mkIntervalHyp (x : Expr) : IntervalM Unit := do
  if (← get).cache.contains x then
    return
  let lctx ← getLCtx
  for ldecl in lctx do
    let t ← instantiateMVars ldecl.type
    if let some (e, iExpr, f) := intervalHyp? t then
      if e == x && (← isDefEq f (mkConst ``Dyadic.toReal)) then
        let i ← unsafe (evalExpr (Interval Dyadic) q(Interval Dyadic) iExpr)
        modify fun s => { s with cache := s.cache.insert e (⟨e, iExpr, ldecl.toExpr⟩, i) }
        return
  throwError "No interval hypothesis found for {x}"

def CertificateGenerator.toIntervalCertificate (gen : CertificateGenerator) (e : Expr) :
    IntervalM (IntervalCertificate × Interval Dyadic) := do
  for i in gen.iVarExprs do
    mkIntervalHyp i
  let cache := (← get).cache
  let certs := gen.iVarExprs.map fun i => (cache.get! i).1
  let intervals := gen.iVarExprs.map fun i => (cache.get! i).2
  match gen.fn with
  | .pureCert fn => do
    let params ← gen.params.mapM fun param => do
      let some value ← liftM <| getNatValue? param
        | throwError "Interval parameter {param} is not a natural-number literal"
      return value
    let intervalExpr := mkAppN fn.intervalExpr (gen.params ++ certs.map (·.intervalExpr))
    let interval := fn.intervalComp params intervals
    let proof := mkAppN fn.proof
      (gen.params ++ gen.iVarExprs ++ certs.map (·.intervalExpr) ++ certs.map (·.proof))
    return (⟨e, intervalExpr, proof⟩, interval)
  | .metaCert fn =>
    fn gen.params gen.iVarExprs (certs.map (·.intervalExpr)) (certs.map (·.proof)) intervals

/-- Temporarily we only handle `le` goals on `ℝ` with a `Dyadic` backend. -/
def intervalCore (g : MVarId) : IntervalM Expr := do
  let t ← whnfR (← g.getType)
  match t.le? with
  | some ⟨t, a, b⟩ => do
    if ← isDefEq t (mkConst ``Real) then
      let (lcert, linterval) ← (← toCertificateGenerator a).toIntervalCertificate a
      let (rcert, rinterval) ← (← toCertificateGenerator b).toIntervalCertificate b
      unless linterval.le rinterval do
        throwError "The computed intervals do not verify the requested inequality"
      let le ← mkDecideProof (← mkAppM ``Interval.le #[lcert.intervalExpr, rcert.intervalExpr])
      mkAppM ``Interval.le_of_le #[mkConst ``Monotone.dyadicToReal, lcert.proof, rcert.proof, le]
    else
      throwError "{t} must be type ℝ (for now)"
  | none => throwError "Not a valid interval goal"

def intervalTactic : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let prf ← (intervalCore g).run' {}
  g.assign prf
  replaceMainGoal []

elab "meta_interval" : tactic => intervalTactic

end IntervalArithmetic
