module

public import Mathlib.Tactic.MetaInterval.Extensions
public meta import Mathlib.Tactic.MetaInterval.Extensions

set_option linter.style.header false

@[expose] public section

open Lean Meta
open IntervalArithmetic

namespace IntervalArithmetic.MetaInterval.Tests

def unitInterval : Interval Dyadic := ⟨1, 2⟩

def positiveInterval : Interval Dyadic := ⟨3, 4⟩

def negativeInterval : Interval Dyadic := ⟨some (-4), some (-2)⟩

def zeroInterval : Interval Dyadic := ⟨some (-1), 1⟩

/-! Test-only extensions for meta certificates and locally bound free variables. -/

def metaValue : ℝ := 1

theorem metaValue_mem :
    metaValue ∈ ((MetaInterval.ofNat 1).map Dyadic.toReal).toSet := by
  simpa [metaValue] using MetaInterval.ofNat_mem 1

meta def metaValueCertificate : IntervalM (IntervalCertificate × Interval Dyadic) := do
  let intervalExpr ← mkAppM ``MetaInterval.ofNat #[mkNatLit 1]
  return (⟨mkConst ``metaValue, intervalExpr, mkConst ``metaValue_mem⟩, MetaInterval.ofNat 1)

@[intervalExt metaValue]
meta def evalMetaValue : IntervalExt where
  eval e := do
    unless e.isConstOf ``metaValue do failure
    return .metaBody ⟨mkConst ``metaValueCertificate⟩

theorem natCast_mem (n : ℕ) :
    (n : ℝ) ∈ ((MetaInterval.ofNat n).map Dyadic.toReal).toSet := by
  constructor
  · exact WithBot.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast]
  · exact WithTop.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast]

def indexedValue (i : ℕ) : ℝ := i

theorem indexedValue_mem (i : ℕ) :
    indexedValue i ∈ ((MetaInterval.ofNat i).map Dyadic.toReal).toSet := by
  simpa [indexedValue] using natCast_mem i

def unregisteredIndexedValue (i : ℕ) : ℝ := i

@[intervalExt indexedValue _]
meta def evalIndexedValue : IntervalExt where
  eval e := do
    let (``indexedValue, #[i]) := e.getAppFnArgs | failure
    let some id := i.fvarId? | failure
    modify fun state => { state with fvars := state.fvars.insert id }
    let intervalBody ← mkAppM ``MetaInterval.ofNat #[i]
    let proofBody ← mkAppM ``indexedValue_mem #[i]
    return .pureBody ⟨intervalBody, intervalBody, proofBody⟩

def natPow (x : Interval Dyadic) : ℕ → Interval Dyadic
  | 0 => MetaInterval.ofNat 1
  | n + 1 => MetaInterval.mul (natPow x n) x

theorem natPow_mem {r : ℝ} {x : Interval Dyadic}
    (h : r ∈ (x.map Dyadic.toReal).toSet) (n : ℕ) :
    r ^ n ∈ ((natPow x n).map Dyadic.toReal).toSet := by
  induction n with
  | zero =>
      simpa [natPow] using MetaInterval.ofNat_mem 1
  | succ n ih =>
      rw [pow_succ]
      exact MetaInterval.mul_mem ih h

@[intervalExt _ ^ _]
meta def evalNatPow : IntervalExt where
  eval e := do
    let (``HPow.hPow, #[α, β, γ, _, x, n]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Real) do failure
    unless ← isDefEq β (mkConst ``Nat) do failure
    unless ← isDefEq γ (mkConst ``Real) do failure
    let .pureBody body ← mkCertificateBody x
      | throwError "The test natural-power extension only supports a pure base"
    let nFVars := (collectFVars {} n).fvarSet
    modify fun state => { state with fvars := state.fvars.union nFVars }
    let intervalExprBody ← mkAppM ``natPow #[body.intervalExprBody, n]
    let intervalCompBody ← mkAppM ``natPow #[body.intervalCompBody, n]
    let intervalProofBody ← mkAppM ``natPow_mem #[body.intervalProofBody, n]
    return .pureBody ⟨intervalExprBody, intervalCompBody, intervalProofBody⟩

@[intervalExt Finset.sum (Finset.range _) _]
meta def evalRangeSum : IntervalExt where
  eval e := do
    let (``Finset.sum, #[α, β, _, s, f]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Nat) do failure
    unless ← isDefEq β (mkConst ``Real) do failure
    let (``Finset.range, #[n]) := s.getAppFnArgs | failure
    lambdaTelescope f fun xs summand => do
      let #[i] := xs | failure
      modify fun state => { state with fvars := state.fvars.insert i.fvarId! }
      let .pureBody body ← mkCertificateBody summand
        | throwError "The test range-sum extension only supports pure summands"
      let intervalCompFn ← mkLambdaFVars #[i] body.intervalCompBody
      let proofFn ← mkLambdaFVars #[i] body.intervalProofBody
      let intervalProofBody ← mkAppM ``sumRangeIntervals_mem #[n, proofFn]
      let some (_, intervalExprBody, _) := intervalHyp? (← inferType intervalProofBody)
        | throwError "The range-sum proof is not an interval-containment proof"
      modify fun state =>
        { state with fvars := Std.TreeSet.erase state.fvars i.fvarId! }
      let intervalCompBody ← mkAppM ``sumRangeIntervals #[n, intervalCompFn]
      return .pureBody ⟨intervalExprBody, intervalCompBody, intervalProofBody⟩

example : metaValue ≤ 2 := by
  meta_interval

example : ∑ i ∈ Finset.range 3, indexedValue i + 1 ≤ 6 := by
  meta_interval

example {x : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet) : x ^ 3 ≤ 8 := by
  meta_interval

example {x : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet) :
    (∑ i ∈ Finset.range 3, x ^ (i + 1)) ≤ 14 := by
  meta_interval

example : (∫ x in (0 : ℝ)..1, x * x) ≤ 1 / 2 := by
  meta_interval

example : 0 ≤ ∫ x in (0 : ℝ)..1, x * x := by
  meta_interval

example {y : ℝ} (hy : y ∈ (unitInterval.map Dyadic.toReal).toSet) :
    (∫ x in (0 : ℝ)..1, x * y) ≤ 5 / 4 := by
  meta_interval

example : (1 : ℝ) + 2 ≤ 4 := by
  meta_interval

example : (1 : ℝ) / 3 ≤ 334 / 1000 := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (positiveInterval.map Dyadic.toReal).toSet) : x + y ≤ 6 := by
  meta_interval

example {x : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet) : x + x ≤ 4 := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (positiveInterval.map Dyadic.toReal).toSet) : x - y ≤ -1 := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (positiveInterval.map Dyadic.toReal).toSet) : x * y ≤ 8 := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (negativeInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (unitInterval.map Dyadic.toReal).toSet) : x * y ≤ -2 := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (unitInterval.map Dyadic.toReal).toSet) : x / y ≤ 2 := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (negativeInterval.map Dyadic.toReal).toSet) : x / y ≤ -(1 / 4) := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (positiveInterval.map Dyadic.toReal).toSet) :
    (x + 1) * (y - 2) / 2 ≤ 5 := by
  meta_interval

example {x : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet) : -x ≤ -1 := by
  meta_interval

def unsupportedValue (x : ℝ) : ℝ := x

example {x : ℝ} (hx : unsupportedValue x ∈ (unitInterval.map Dyadic.toReal).toSet) :
    unsupportedValue x + 1 ≤ 3 := by
  meta_interval

example (_x : ℝ) : True := by
  fail_if_success
    have : _x ≤ 1 := by
      meta_interval
  trivial

example {x y : ℝ} (_hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (_hy : y ∈ (zeroInterval.map Dyadic.toReal).toSet) : True := by
  fail_if_success
    have : x / y ≤ 10 := by
      meta_interval
  trivial

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let e ← mkAppM ``HAdd.hAdd #[x, x]
    let gen ← toCertificateGenerator e
    unless gen.iVarExprs.size == 1 do
      throwError "Expected repeated expressions to share one interval variable"
    match gen.fn with
    | .pureCert _ => pure ()
    | .metaCert _ =>
      throwError "Expected a composition of pure extensions to remain pure"

run_meta
  let succeeded ← try
    discard <| CertificateGeneratorM.run do
      withLocalDeclD `i (mkConst ``Nat) fun i => do
        let e ← mkAppM ``unregisteredIndexedValue #[i]
        modify fun state => { state with fvars := state.fvars.insert i.fvarId! }
        mkCertificateBody e
    pure true
  catch _ =>
    pure false
  if succeeded then
    throwError "A binder-dependent expression must not be used as an interval variable"

end IntervalArithmetic.MetaInterval.Tests
