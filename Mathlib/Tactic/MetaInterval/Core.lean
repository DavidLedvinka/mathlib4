module

public import Mathlib.Tactic.MetaInterval.Expr
public import Mathlib.Tactic.MetaInterval.Dyadic
public import Mathlib.Tactic.MetaInterval.Certificate
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Data.Real.Basic

set_option linter.style.header false

open Lean Meta Elab Tactic

namespace IntervalArithmetic

structure State where
  cache : ExprMap IntervalCertificate := {}
  deriving Inhabited

abbrev IntervalM := StateT State MetaM

/-- Temporarily we only extract the first appearance of `x ∈ i.toSet.map Dyadic.toReal` -/
def mkIntervalHyp (x : FVarId) : IntervalM Unit := do
  let lctx ← getLCtx
  for ldecl in lctx do
    let t ← instantiateMVars ldecl.type
    if let some (e, iExpr, _) := intervalHyp? t then
      if e == .fvar x then
        let i ← unsafe (evalExpr (Interval Dyadic) (← mkAppM ``Interval #[mkConst ``Dyadic]) iExpr)
        modify fun s => { s with cache := s.cache.insert e ⟨i, iExpr, ldecl.toExpr⟩}

def CertificateGenerator.toIntervalCertificate (gen : CertificateGenerator) :
    IntervalM IntervalCertificate := do
  for i in gen.ivarSet do
    mkIntervalHyp i
  let cache := (← get).cache
  let fvars := gen.fvarSet.toArray
  let ivars := gen.ivarSet.toArray
  let hyps := (fun i ↦ cache.get! (.fvar i)) <$> ivars
  gen.certGen fvars ivars hyps

/-- Temporarily we only handle `le` goals on `ℝ` with a `Dyadic` backend. -/
def intervalCore (g : MVarId) : IntervalM Expr := do
  let t ← whnfR (← g.getType)
  match t.le? with
  | some ⟨t, a, b⟩ => do
    if ← isDefEq t (mkConst ``Real) then
      let lcert ← (← toCertificateGenerator a).toIntervalCertificate
      let rcert ← (← toCertificateGenerator b).toIntervalCertificate
      unless lcert.interval.le rcert.interval do
        throwError m!"Inequality not verified: TODO"
      let le ← mkDecideProof (← mkAppM ``Interval.le #[lcert.intervalExpr, rcert.intervalExpr])
      mkAppM ``Interval.le_of_le #[mkConst ``Monotone.dyadicToReal, lcert.proof, rcert.proof, le]
    else
      throwError "{t} must be type ℝ (for now)"
  | none => throwError "Not a valid interval goal"

def intervalTactic : TacticM Unit := do
  let g ← getMainGoal
  let prf ← (intervalCore g).run' {}
  g.assign prf
  replaceMainGoal []

end IntervalArithmetic
