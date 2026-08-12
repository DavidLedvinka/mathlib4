module

public import Mathlib.Tactic.Inclusion.Experimental.LargeExtensions
public meta import Mathlib.Tactic.Inclusion.Experimental.LargeExtensions

set_option linter.style.header false

@[expose] public section

set_option warn.sorry false

open Lean Meta
open MeasureTheory
open scoped BigOperators

namespace Inclusion.Experimental.HighPrecision

def inv (prec : ℕ) (x : Interval Dyadic) : Interval Dyadic :=
  match x.lb, x.ub with
  | some l, some u =>
      if 0 < l ∨ u < 0 then
        ⟨some (Large.divDown prec 1 u), some (Large.divUp prec 1 l)⟩
      else
        Interval.univ Dyadic
  | _, _ => Interval.univ Dyadic

theorem inv_mem {r : ℝ} {x : Interval Dyadic} (prec : ℕ) (hrx : r ∈ x) :
    1 / r ∈ inv prec x := by
  sorry

def div (prec : ℕ) (x y : Interval Dyadic) : Interval Dyadic :=
  match x.lb, x.ub, y.lb, y.ub with
  | some xl, some xu, some yl, some yu =>
      if 0 < yl then
        if 0 ≤ xl then
          ⟨some (Large.divDown prec xl yu), some (Large.divUp prec xu yl)⟩
        else if xu ≤ 0 then
          ⟨some (Large.divDown prec xl yl), some (Large.divUp prec xu yu)⟩
        else
          ⟨some (Large.divDown prec xl yl), some (Large.divUp prec xu yl)⟩
      else if yu < 0 then
        if 0 ≤ xl then
          ⟨some (Large.divDown prec xu yu), some (Large.divUp prec xl yl)⟩
        else if xu ≤ 0 then
          ⟨some (Large.divDown prec xu yl), some (Large.divUp prec xl yu)⟩
        else
          ⟨some (Large.divDown prec xu yu), some (Large.divUp prec xl yu)⟩
      else
        Interval.univ Dyadic
  | _, _, _, _ => Interval.univ Dyadic

theorem div_mem {r s : ℝ} {x y : Interval Dyadic} (prec : ℕ)
    (hrx : r ∈ x) (hsy : s ∈ y) : r / s ∈ div prec x y := by
  sorry

def zpow (prec : ℕ) (x : Interval Dyadic) : ℤ → Interval Dyadic
  | .ofNat n => Large.pow x n
  | .negSucc n => inv prec (Large.pow x (n + 1))

theorem zpow_mem {r : ℝ} {x : Interval Dyadic} (prec : ℕ) (hrx : r ∈ x) (n : ℤ) :
    r ^ n ∈ zpow prec x n := by
  sorry

def absInterval (x : Interval Dyadic) : Interval Dyadic :=
  match x.lb, x.ub with
  | some l, some u =>
      if 0 ≤ l then
        x
      else if u ≤ 0 then
        ⟨some (-u), some (-l)⟩
      else
        ⟨some 0, some (max (-l) u)⟩
  | _, _ => ⟨some 0, ⊤⟩

theorem abs_mem {r : ℝ} {x : Interval Dyadic} (hrx : r ∈ x) :
    |r| ∈ absInterval x := by
  sorry

def ramanujanNumerator (k : ℕ) : ℕ :=
  (4 * k).factorial * (1103 + 26390 * k)

def ramanujanDenominator (k : ℕ) : ℕ :=
  k.factorial ^ 4 * 396 ^ (4 * k)

noncomputable def ramanujanSummand (k : ℕ) : ℝ :=
  (ramanujanNumerator k : ℝ) / ramanujanDenominator k

def ramanujanSummandInterval (prec k : ℕ) : Interval Dyadic :=
  let numerator : Dyadic := ramanujanNumerator k
  let denominator := ramanujanDenominator k
  ⟨some (Large.divNatDown prec numerator denominator),
    some (Large.divNatUp prec numerator denominator)⟩

theorem ramanujanSummand_mem (prec k : ℕ) :
    ramanujanSummand k ∈ ramanujanSummandInterval prec k := by
  sorry

theorem natCast_mem (n : ℕ) : (n : ℝ) ∈ Large.ofNat n := by
  sorry

def gaussianTerms (prec : ℕ) : ℕ :=
  prec / 5 + 8

def gaussianBoundsAux (prec : ℕ) :
    ℕ → ℕ → ℕ → Bool → Dyadic → Dyadic → Dyadic × Dyadic
  | 0, n, factorial, positive, lo, hi =>
      let nextHi := Large.divNatUp prec 1 (factorial * (2 * n + 1))
      if positive then (lo, hi + nextHi) else (lo - nextHi, hi)
  | fuel + 1, n, factorial, positive, lo, hi =>
      let denominator := factorial * (2 * n + 1)
      let termLo := Large.divNatDown prec 1 denominator
      let termHi := Large.divNatUp prec 1 denominator
      let lo' := if positive then lo + termLo else lo - termHi
      let hi' := if positive then hi + termHi else hi - termLo
      gaussianBoundsAux prec fuel (n + 1) (factorial * (n + 1)) (!positive) lo' hi'

def gaussianIntegralInterval (prec : ℕ) : Interval Dyadic :=
  let bounds := gaussianBoundsAux prec (gaussianTerms prec) 0 1 true 0 0
  ⟨some bounds.1, some bounds.2⟩

noncomputable def gaussianIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (-(x ^ 2))

theorem gaussianIntegral_mem (prec : ℕ) :
    gaussianIntegral ∈ gaussianIntegralInterval prec := by
  sorry

@[inclusionExt real.dyadic | _ / _]
meta def evalDiv : InclusionExt where
  priority := 0
  derive e := do
    let (a, b) ← Inclusion.realBinaryArgs e
    let left ← mkExprInclusionBody a
    let right ← mkExprInclusionBody b
    let prec ← Large.precisionExpr
    return ⟨← mkAppM ``div #[prec, left.inclusionBody, right.inclusionBody],
      ← mkAppM ``div_mem #[prec, left.proofBody, right.proofBody]⟩

@[inclusionExt real.dyadic | _ ^ (_ : ℤ)]
meta def evalZPow : InclusionExt where
  priority := 0
  derive e := do
    let (``HPow.hPow, #[α, β, γ, _, x, n]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Real) do failure
    unless ← isDefEq β (mkConst ``Int) do failure
    unless ← isDefEq γ (mkConst ``Real) do failure
    let body ← mkExprInclusionBody x
    let prec ← Large.precisionExpr
    return ⟨← mkAppM ``zpow #[prec, body.inclusionBody, n],
      ← mkAppM ``zpow_mem #[prec, body.proofBody, n]⟩

@[inclusionExt real.dyadic | |(_ : ℝ)|]
meta def evalAbs : InclusionExt where
  derive e := do
    let body ← mkExprInclusionBody (← Inclusion.realUnaryArg e)
    return ⟨← mkAppM ``absInterval #[body.inclusionBody],
      ← mkAppM ``abs_mem #[body.proofBody]⟩

@[inclusionExt real.dyadic | ramanujanSummand _]
meta def evalRamanujanSummand : InclusionExt where
  derive e := do
    let (``ramanujanSummand, #[k]) := e.getAppFnArgs | failure
    let prec ← Large.precisionExpr
    return ⟨← mkAppM ``ramanujanSummandInterval #[prec, k],
      ← mkAppM ``ramanujanSummand_mem #[prec, k]⟩

@[inclusionExt real.dyadic | Nat.cast _]
meta def evalNatCast : InclusionExt where
  priority := 0
  derive e := do
    let (``Nat.cast, #[α, _, n]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Real) do failure
    return ⟨← mkAppM ``Large.ofNat #[n], ← mkAppM ``natCast_mem #[n]⟩

@[inclusionExt real.dyadic | Finset.sum (Finset.range _) _]
meta def evalRangeSum : InclusionExt where
  derive e := do
    let (``Finset.sum, #[α, β, _, s, f]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Nat) do failure
    unless ← isDefEq β (mkConst ``Real) do failure
    let (``Finset.range, #[n]) := s.getAppFnArgs | failure
    lambdaTelescope f fun xs summand => do
      let #[i] := xs | failure
      let body ← mkExprInclusionBody summand
      let intervalFn ← mkLambdaFVars #[i] body.inclusionBody
      let proofFn ← mkLambdaFVars #[i] body.proofBody
      return ⟨← mkAppM ``Inclusion.sumRangeIntervals #[n, intervalFn],
        ← mkAppM ``Inclusion.sumRangeIntervals_mem #[n, proofFn]⟩

@[inclusionExt real.dyadic | gaussianIntegral]
meta def evalGaussianIntegral : InclusionExt where
  derive e := do
    unless e.isConstOf ``gaussianIntegral do failure
    let prec ← Large.precisionExpr
    return ⟨← mkAppM ``gaussianIntegralInterval #[prec],
      ← mkAppM ``gaussianIntegral_mem #[prec]⟩

@[inclusionExt real.dyadic | intervalIntegral (_ : ℝ → ℝ) _ _ volume]
meta def evalGaussianIntegralExpr : InclusionExt where
  priority := 0
  derive e := do
    unless ← isDefEq e (mkConst ``gaussianIntegral) do failure
    let prec ← Large.precisionExpr
    return ⟨← mkAppM ``gaussianIntegralInterval #[prec],
      ← mkAppM ``gaussianIntegral_mem #[prec]⟩

end Inclusion.Experimental.HighPrecision
