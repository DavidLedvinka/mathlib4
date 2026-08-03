module

public import Mathlib.Tactic.Inclusion.Experimental.LargeExtensions
public meta import Mathlib.Tactic.Inclusion.Experimental.LargeExtensions

set_option linter.style.header false

@[expose] public section

set_option warn.sorry false

open Lean Meta

namespace IntervalArithmetic.Inclusion.Experimental.RocqBenchmark

/-- Number of alternating-series terms used by the benchmark-only trigonometric evaluator. -/
def trigTerms (prec : ℕ) : ℕ := prec / 8 + 7

/-- Directed evaluation of an alternating sine/cosine series at a nonnegative dyadic point. -/
def trigTaylorBoundsAux (prec : ℕ) (ulp xSq : Dyadic) :
    ℕ → ℕ → Bool → Dyadic → Dyadic → Dyadic → Dyadic → Dyadic × Dyadic
  | 0, _degree, positive, _termLo, termHi, sumLo, sumHi =>
      if positive then (sumLo, sumHi + termHi) else (sumLo - termHi, sumHi)
  | fuel + 1, degree, positive, termLo, termHi, sumLo, sumHi =>
      let sumLo' := if positive then sumLo + termLo else sumLo - termHi
      let sumHi' := if positive then sumHi + termHi else sumHi - termLo
      let denominator := (degree + 1) * (degree + 2)
      let nextLo := Large.divNatDown prec (termLo * xSq) denominator
      let nextHi := Large.divNatUp prec (termHi * xSq) denominator
      if nextHi ≤ ulp then
        if !positive then (sumLo', sumHi' + nextHi) else (sumLo' - nextHi, sumHi')
      else
        trigTaylorBoundsAux prec ulp xSq fuel (degree + 2) (!positive) nextLo nextHi sumLo' sumHi'

def sinTaylorBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  trigTaylorBoundsAux prec (Dyadic.ofIntWithPrec 1 prec) (x * x)
    (trigTerms prec) 1 true x x 0 0

def cosTaylorBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  trigTaylorBoundsAux prec (Dyadic.ofIntWithPrec 1 prec) (x * x)
    (trigTerms prec) 0 true 1 1 0 0

/- These are downward 40-bit alternating-Taylor polynomials on `[0, π / 4]`. Their truncation,
coefficient-rounding, and final-rounding errors fit inside the returned two-ulp envelopes. -/
def sinPolynomialBounds30 (x : Dyadic) : Dyadic × Dyadic :=
  let z := x * x
  let lo := Dyadic.ofIntWithPrec (-27546) 40
  let lo := Dyadic.ofIntWithPrec 3029959 40 + z * lo
  let lo := Dyadic.ofIntWithPrec (-218157070) 40 + z * lo
  let lo := Dyadic.ofIntWithPrec 9162596898 40 + z * lo
  let lo := Dyadic.ofIntWithPrec (-183251937963) 40 + z * lo
  let lo := Dyadic.ofIntWithPrec 1099511627776 40 + z * lo
  let lo := Large.roundDown 30 (x * lo)
  (lo, lo + Dyadic.ofIntWithPrec 2 30)

def cosPolynomialBounds30 (x : Dyadic) : Dyadic × Dyadic :=
  let z := x * x
  let lo := Dyadic.ofIntWithPrec (-302996) 40
  let lo := Dyadic.ofIntWithPrec 27269633 40 + z * lo
  let lo := Dyadic.ofIntWithPrec (-1527099484) 40 + z * lo
  let lo := Dyadic.ofIntWithPrec 45812984490 40 + z * lo
  let lo := Dyadic.ofIntWithPrec (-549755813888) 40 + z * lo
  let lo := Dyadic.ofIntWithPrec 1099511627776 40 + z * lo
  let lo := Large.roundDown 30 lo
  (lo, lo + Dyadic.ofIntWithPrec 2 30)

def sinSeriesBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  if prec = 30 then sinPolynomialBounds30 x else sinTaylorBounds prec x

def cosSeriesBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  if prec = 30 then cosPolynomialBounds30 x else cosTaylorBounds prec x

def halfPiLower : Dyadic := Dyadic.ofIntWithPrec 1686629713 30

def halfPiUpper : Dyadic := Dyadic.ofIntWithPrec 1686629714 30

def halfPiError : Dyadic := Dyadic.ofIntWithPrec 1 30

def quarterPiLower : Dyadic := Dyadic.ofIntWithPrec 843314856 30

def quarterPiUpper : Dyadic := Dyadic.ofIntWithPrec 843314857 30

def sinFirstQuadrantBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  if x ≤ quarterPiLower then
    sinSeriesBounds prec x
  else if quarterPiUpper ≤ x then
    let bounds := cosSeriesBounds prec (halfPiUpper - x)
    (bounds.1, bounds.2 + halfPiError)
  else
    sinSeriesBounds prec x

def cosFirstQuadrantBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  if x ≤ quarterPiLower then
    cosSeriesBounds prec x
  else if quarterPiUpper ≤ x then
    let bounds := sinSeriesBounds prec (halfPiUpper - x)
    (bounds.1 - halfPiError, bounds.2)
  else
    cosSeriesBounds prec x

def sinPointBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  if x ≤ halfPiLower then
    sinFirstQuadrantBounds prec x
  else if halfPiUpper ≤ x then
    let bounds := cosFirstQuadrantBounds prec (x - halfPiUpper)
    (bounds.1 - halfPiError, bounds.2)
  else
    (1 - halfPiError, 1)

def cosPointBounds (prec : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  if x ≤ halfPiLower then
    cosFirstQuadrantBounds prec x
  else if halfPiUpper ≤ x then
    let bounds := sinFirstQuadrantBounds prec (x - halfPiUpper)
    (-bounds.2 - halfPiError, -bounds.1)
  else
    (-halfPiError, halfPiError)

/-- A benchmark-only sine inclusion optimized for inputs in `[0, 3]`. -/
def sin (prec : ℕ) (x : Interval Dyadic) : Interval Dyadic :=
  match x.lb, x.ub with
  | some l, some u =>
      if 0 ≤ l ∧ u ≤ 3 then
        let lBounds := sinPointBounds prec l
        let uBounds := sinPointBounds prec u
        let lower := max (-1) (min lBounds.1 uBounds.1)
        let upper :=
          if u ≤ halfPiLower then min 1 uBounds.2
          else if halfPiUpper ≤ l then min 1 lBounds.2
          else 1
        ⟨some lower, some upper⟩
      else
        ⟨some (-1), some 1⟩
  | _, _ => ⟨some (-1), some 1⟩

/-- A benchmark-only cosine inclusion optimized for inputs in `[0, 3]`. -/
def cos (prec : ℕ) (x : Interval Dyadic) : Interval Dyadic :=
  match x.lb, x.ub with
  | some l, some u =>
      if 0 ≤ l ∧ u ≤ 3 then
        let lBounds := cosPointBounds prec l
        let uBounds := cosPointBounds prec u
        ⟨some (max (-1) uBounds.1), some (min 1 lBounds.2)⟩
      else
        ⟨some (-1), some 1⟩
  | _, _ => ⟨some (-1), some 1⟩

theorem sin_mem {r : ℝ} {x : Interval Dyadic} (prec : ℕ) (hrx : r ∈ x) :
    Real.sin r ∈ sin prec x := by
  sorry

theorem cos_mem {r : ℝ} {x : Interval Dyadic} (prec : ℕ) (hrx : r ∈ x) :
    Real.cos r ∈ cos prec x := by
  sorry

@[inclusionExt Real.sin _]
meta def evalSin : InclusionExt where
  eval e := do
    let body ← mkExprInclusionBody (← realUnaryArg e)
    let prec ← Large.precisionExpr
    return ⟨← mkAppM ``sin #[prec, body.inclusionBody],
      ← mkAppM ``sin_mem #[prec, body.proofBody]⟩

@[inclusionExt Real.cos _]
meta def evalCos : InclusionExt where
  eval e := do
    let body ← mkExprInclusionBody (← realUnaryArg e)
    let prec ← Large.precisionExpr
    return ⟨← mkAppM ``cos #[prec, body.inclusionBody],
      ← mkAppM ``cos_mem #[prec, body.proofBody]⟩

end IntervalArithmetic.Inclusion.Experimental.RocqBenchmark
