module

public meta import Mathlib.Tactic.MetaInterval.Expr
public meta import Mathlib.Tactic.MetaInterval.Dyadic
public meta import Mathlib.Tactic.MetaInterval.Certificate
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Data.Real.Basic

set_option linter.style.header false

@[expose] public meta section

open Lean Meta Elab Tactic

namespace IntervalArithmetic

/-- Temporarily we only extract the first appearance of `x ∈ (i.map Dyadic.toReal).toSet`. -/
def mkIntervalHyp (x : Expr) : IntervalM Unit := do
  let lctx ← getLCtx
  for ldecl in lctx do
    let t ← instantiateMVars ldecl.type
    if let some (e, iExpr, _) := intervalHyp? t then
      if e == x then
        let type ← mkAppM ``Interval #[mkConst ``Dyadic]
        let i ← unsafe (evalExpr (Interval Dyadic) type iExpr)
        modify fun s => { s with cache := s.cache.insert e ⟨i, iExpr, ldecl.toExpr⟩}
  throwError "No interval hypothesis found for {x}"

def CertificateGenerator.toIntervalCertificate (gen : CertificateGenerator) :
    IntervalM IntervalCertificate := do
  for i in gen.ivars.keys do
    mkIntervalHyp i
  let cache := (← get).cache
  let certs := (fun i ↦ (i, cache.get! i)) <$> gen.ivars.keysArray
  gen.certGen certs

/-- Temporarily we only handle `le` goals on `ℝ` with a `Dyadic` backend. -/
def intervalCore (g : MVarId) : IntervalM Expr := do
  let t ← whnfR (← g.getType)
  match t.le? with
  | some ⟨t, a, b⟩ => do
    if ← isDefEq t (mkConst ``Real) then
      let lcert ← (← toCertificateGenerator a).toIntervalCertificate
      let rcert ← (← toCertificateGenerator b).toIntervalCertificate
      unless lcert.interval.le rcert.interval do
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
