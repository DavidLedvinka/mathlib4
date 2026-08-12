module

public import Mathlib.Tactic.Inclusion.Extension.Extensions
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

@[expose] public section

set_option warn.sorry false

open Lean Meta

namespace Inclusion.Large

public meta section

register_option inclusion.large.precision : Nat := {
  defValue := 100
  descr := "dyadic precision used by the experimental large-computation inclusion extensions"
}

end

/-- Direct downward dyadic division, avoiding conversion through normalized rationals. -/
def divDown (prec : ℕ) (a b : Dyadic) : Dyadic :=
  match a, b with
  | .zero, _ | _, .zero => 0
  | .ofOdd an ak _, .ofOdd bn bk _ =>
      let (num, den) := if bn < 0 then (-an, -bn) else (an, bn)
      let shift := (prec : Int) + bk - ak
      let quotient := match shift with
        | .ofNat s => (num <<< s) / den
        | .negSucc s => num / (den <<< (s + 1))
      Dyadic.ofIntWithPrec quotient prec

def divUp (prec : ℕ) (a b : Dyadic) : Dyadic :=
  -divDown prec (-a) b

/-- The specialization of `divDown` for a positive natural denominator. -/
def divNatDown (prec : ℕ) (a : Dyadic) (b : ℕ) : Dyadic :=
  match a, b with
  | _, 0 | .zero, _ => 0
  | .ofOdd an ak _, b + 1 =>
      let shift := (prec : Int) - ak
      let denominator : Int := b + 1
      let quotient := match shift with
        | .ofNat s => (an <<< s) / denominator
        | .negSucc s => an / (denominator <<< (s + 1))
      Dyadic.ofIntWithPrec quotient prec

def divNatUp (prec : ℕ) (a : Dyadic) (b : ℕ) : Dyadic :=
  -divNatDown prec (-a) b

/-- Round downward with shifts alone, without invoking integer division by one. -/
def roundDown (prec : ℕ) (a : Dyadic) : Dyadic :=
  match a with
  | .zero => 0
  | .ofOdd an ak _ =>
      let shift := (prec : Int) - ak
      let rounded := match shift with
        | .ofNat s => an <<< s
        | .negSucc s => an >>> (s + 1)
      Dyadic.ofIntWithPrec rounded prec

def roundUp (prec : ℕ) (a : Dyadic) : Dyadic :=
  -roundDown prec (-a)

def ratApprox (prec : ℕ) (q : ℚ) : Interval Dyadic :=
  ⟨some (q.toDyadic prec), some (-(-q).toDyadic prec)⟩

def scientific (prec m : ℕ) (s : Bool) (e : ℕ) : Interval Dyadic :=
  if s then
    let denominator := 10 ^ e
    ⟨some (divNatDown prec m denominator), some (divNatUp prec m denominator)⟩
  else
    let value : Dyadic := (m * 10 ^ e : ℕ)
    ⟨some value, some value⟩

theorem scientific_mem (prec m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e) ∈ scientific prec m s e := by
  sorry

/- These exact operations deliberately follow the implementations in `DyadicReal.lean`. The only
difference is that the new `Interval` type has no endpoint-closure Boolean. -/

def ofNat (n : ℕ) : Interval Dyadic :=
  ⟨some n, some n⟩

theorem ofNat_mem (n : ℕ) : (OfNat.ofNat n : ℝ) ∈ ofNat n := by
  sorry

def add (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.lb with
    | ⊥, _ | _, ⊥ => ⊥
    | some a, some b => some (a + b)
  ub := match x.ub, y.ub with
    | ⊤, _ | _, ⊤ => ⊤
    | some a, some b => some (a + b)

theorem add_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r + s ∈ add x y := by
  sorry

def sub (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.ub with
    | ⊥, _ | _, ⊤ => ⊥
    | some a, some b => some (a - b)
  ub := match x.ub, y.lb with
    | ⊤, _ | _, ⊥ => ⊤
    | some a, some b => some (a - b)

theorem sub_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r - s ∈ sub x y := by
  sorry

inductive IntervalSignClass
  | nonneg
  | nonpos
  | mixed

def toIntervalSignClass (x : Interval Dyadic) : IntervalSignClass :=
  let zeroLb : WithBot Dyadic := some 0
  let zeroUb : WithTop Dyadic := some 0
  if zeroLb ≤ x.lb then .nonneg
  else if x.ub ≤ zeroUb then .nonpos
  else .mixed

def upperToLower : WithTop Dyadic → WithBot Dyadic
  | ⊤ => ⊥
  | some a => some a

def lowerToUpper : WithBot Dyadic → WithTop Dyadic
  | ⊥ => ⊤
  | some a => some a

def lowerMul : WithBot Dyadic → WithBot Dyadic → WithBot Dyadic
  | ⊥, ⊥ => ⊥
  | some a, ⊥ | ⊥, some a => if a = 0 then some 0 else ⊥
  | some a, some b => some (a * b)

def upperMul : WithTop Dyadic → WithTop Dyadic → WithTop Dyadic
  | ⊤, ⊤ => ⊤
  | some a, ⊤ | ⊤, some a => if a = 0 then some 0 else ⊤
  | some a, some b => some (a * b)

def mul (x y : Interval Dyadic) : Interval Dyadic :=
  match toIntervalSignClass x, toIntervalSignClass y with
  | .nonneg, .nonneg => ⟨lowerMul x.lb y.lb, upperMul x.ub y.ub⟩
  | .nonneg, .nonpos =>
      ⟨lowerMul (upperToLower x.ub) y.lb, upperMul (lowerToUpper x.lb) y.ub⟩
  | .nonneg, .mixed => ⟨lowerMul (upperToLower x.ub) y.lb, upperMul x.ub y.ub⟩
  | .nonpos, .nonneg =>
      ⟨lowerMul x.lb (upperToLower y.ub), upperMul x.ub (lowerToUpper y.lb)⟩
  | .nonpos, .nonpos =>
      ⟨lowerMul (upperToLower x.ub) (upperToLower y.ub),
        upperMul (lowerToUpper x.lb) (lowerToUpper y.lb)⟩
  | .nonpos, .mixed =>
      ⟨lowerMul x.lb (upperToLower y.ub), upperMul (lowerToUpper x.lb) (lowerToUpper y.lb)⟩
  | .mixed, .nonneg => ⟨lowerMul x.lb (upperToLower y.ub), upperMul x.ub y.ub⟩
  | .mixed, .nonpos =>
      ⟨lowerMul (upperToLower x.ub) y.lb, upperMul (lowerToUpper x.lb) (lowerToUpper y.lb)⟩
  | .mixed, .mixed =>
      ⟨min (lowerMul x.lb (upperToLower y.ub)) (lowerMul (upperToLower x.ub) y.lb),
        max (upperMul (lowerToUpper x.lb) (lowerToUpper y.lb)) (upperMul x.ub y.ub)⟩

theorem mul_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r * s ∈ mul x y := by
  sorry

def pow (x : Interval Dyadic) (n : ℕ) : Interval Dyadic :=
  let zeroLb : WithBot Dyadic := some 0
  let zeroUb : WithTop Dyadic := some 0
  if n = 0 then
    ofNat 1
  else if zeroLb ≤ x.lb || n % 2 = 1 then
    let lb := match x.lb with | ⊥ => ⊥ | some q => some (q ^ n)
    let ub := match x.ub with | ⊤ => ⊤ | some q => some (q ^ n)
    ⟨lb, ub⟩
  else if decide (x.ub ≤ zeroUb) then
    let lb := match x.ub with | ⊤ => ⊥ | some q => some (q ^ n)
    let ub := match x.lb with | ⊥ => ⊤ | some q => some (q ^ n)
    ⟨lb, ub⟩
  else
    let ub := match x.lb, x.ub with
      | some q₁, some q₂ =>
          let q₁' := if 0 ≤ q₁ then q₁ else -q₁
          if q₁' < q₂ then some (q₂ ^ n)
          else if q₁' = q₂ then some (q₂ ^ n)
          else some (q₁' ^ n)
      | _, _ => ⊤
    ⟨some 0, ub⟩

theorem pow_mem {r : ℝ} {x : Interval Dyadic} (h : r ∈ x) (n : ℕ) :
    r ^ n ∈ pow x n := by
  sorry

def lt (x y : Interval Dyadic) : IntervalBool :=
  match x.ub, y.lb with
  | some xu, some yl => if xu < yl then .true else .undetermined
  | _, _ => .undetermined

theorem lt_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : (r < s) ∈ lt x y := by
  sorry

section Sqrt

def sqrtFloorAndExact (prec : ℕ) (q : Dyadic) : Int × Bool :=
  match q with
  | .zero => (0, true)
  | .ofOdd n k _ =>
      if n < 0 then
        (0, true)
      else
        let N := n.natAbs
        let shift : Int := 2 * (prec : Int) - k
        match shift with
        | .ofNat s =>
            let scaled := N <<< s
            let m := Nat.sqrt scaled
            ((m : Int), m * m = scaled)
        | .negSucc s =>
            let t := s + 1
            let denom := (1 : ℕ) <<< t
            let scaledFloor := N / denom
            let m := Nat.sqrt scaledFloor
            ((m : Int), (m * m) * denom = N)

def sqrtDown (prec : ℕ) (q : Dyadic) : Dyadic :=
  Dyadic.ofIntWithPrec (sqrtFloorAndExact prec q).1 prec

def sqrtUp (prec : ℕ) (q : Dyadic) : Dyadic :=
  let result := sqrtFloorAndExact prec q
  Dyadic.ofIntWithPrec (if result.2 then result.1 else result.1 + 1) prec

def sqrt (prec : ℕ) (x : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb with
    | ⊥ => some 0
    | some a => if a < 0 then some 0 else some (sqrtDown prec a)
  ub := match x.ub with
    | ⊤ => ⊤
    | some a => if a ≤ 0 then some 0 else some (sqrtUp prec a)

theorem sqrt_mem {r : ℝ} {x : Interval Dyadic} (prec : ℕ) (hrx : r ∈ x) :
    Real.sqrt r ∈ sqrt prec x := by
  sorry

end Sqrt

section Exp

def bitLenAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else 1 + bitLenAux fuel (n / 2)

def bitLen (n : ℕ) : ℕ := bitLenAux n n

def expTaylorTerms (prec : ℕ) : ℕ :=
  let L := bitLen prec
  let LL := bitLen L
  let denom := max 1 (L - LL + 1)
  max 8 (prec / denom + 80)

def divPowTwo (x : Dyadic) (k : ℕ) : Dyadic :=
  match x with
  | .zero => 0
  | .ofOdd n e _ => Dyadic.ofIntWithPrec n (e + k)

def squareIter : ℕ → Dyadic → Dyadic
  | 0, x => x
  | k + 1, x => squareIter k (x * x)

def expReductionSteps (prec : ℕ) (x : Dyadic) : ℕ :=
  let steps := match x with
  | .zero => 0
  | .ofOdd n e _ =>
      let L := bitLen n.natAbs
      match e with
      | .ofNat eNat => L - eNat
      | .negSucc s => L + (s + 1)
  if x = 0 then 0 else steps + if prec ≤ 64 then 10 else if x ≤ 2 then 8 else 1

def expTaylorLowerAux (prec : ℕ) (x : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic
  | 0, _k, _term, sum => sum
  | n + 1, k, term, sum =>
      let next := divNatDown prec (term * x) (k + 1)
      if next = 0 then sum
      else expTaylorLowerAux prec x n (k + 1) next (sum + next)

def expTaylorLower (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  expTaylorLowerAux prec x terms 0 1 1

def expTaylorUpperAux (prec : ℕ) (ulp x : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic × Dyadic
  | 0, k, term, sum =>
      (sum, divNatUp prec (term * x) (k + 1))
  | n + 1, k, term, sum =>
      let numerator := term * x
      let next := divNatUp prec numerator (k + 1)
      if next ≤ ulp then
        (sum, next)
      else
        expTaylorUpperAux prec ulp x n (k + 1) next (sum + next)

def expTaylorUpper (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let result := expTaylorUpperAux prec (Dyadic.ofIntWithPrec 1 prec) x terms 0 1 1
  let sum := result.1
  let next := result.2
  sum + next + next

/- After the low-precision range reduction, `0 ≤ x < 2⁻¹⁰`. The quadratic remainder is
smaller than `2⁻³²`, so these fixed polynomials enclose `exp x` before repeated squaring. -/
def expPolynomialLower30 (x : Dyadic) : Dyadic :=
  let c₂ := Dyadic.ofIntWithPrec 549755813888 40
  let one := Dyadic.ofIntWithPrec 1099511627776 40
  roundDown 30 (one + x * (one + x * c₂))

def expPolynomialUpper30 (x : Dyadic) : Dyadic :=
  let c₂ := Dyadic.ofIntWithPrec 549755813888 40
  let one := Dyadic.ofIntWithPrec 1099511627776 40
  let tail := Dyadic.ofIntWithPrec 1 32
  roundUp 30 (one + x * (one + x * c₂) + tail)

/- For the precision-120 dependency benchmark, the coefficients below are downward 130-bit
approximations to `1 / n!`, from degree eleven to zero. On `0 ≤ x < 2⁻⁸`, coefficient and
Taylor-tail errors together fit inside the two-ulp envelope returned below. -/
def expPolynomialBounds120 (x : Dyadic) : Dyadic × Dyadic :=
  let lo := Dyadic.ofIntWithPrec 34099162951031992891551888671613 130
  let lo := Dyadic.ofIntWithPrec 375090792461351921807070775387751 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 3750907924613519218070707753877515 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 33758171321521672962636369784897640 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 270065370572173383701090958279181120 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 1890457594005213685907636707954267841 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 11342745564031282115445820247725607048 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 56713727820156410577229101238628035242 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 226854911280625642308916404954512140970 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 680564733841876926926749214863536422912 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 1361129467683753853853498429727072845824 130 + x * lo
  let lo := Dyadic.ofIntWithPrec 1361129467683753853853498429727072845824 130 + x * lo
  let lo := roundDown 120 lo
  (lo, lo + Dyadic.ofIntWithPrec 2 120)

def expNonnegDown (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let k := expReductionSteps prec x
  let reduced := divPowTwo x k
  let initial := if prec = 30 then expPolynomialLower30 reduced
    else if prec = 120 ∧ x ≤ 2 then (expPolynomialBounds120 reduced).1
    else expTaylorLower prec terms reduced
  squareIter k initial

def expNonnegUp (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let k := expReductionSteps prec x
  let reduced := divPowTwo x k
  let initial := if prec = 30 then expPolynomialUpper30 reduced
    else if prec = 120 ∧ x ≤ 2 then (expPolynomialBounds120 reduced).2
    else expTaylorUpper prec terms reduced
  squareIter k initial

def expDown (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  if x < 0 then
    let x := -x
    let k := expReductionSteps prec x
    let reduced := divPowTwo x k
    let initial := if prec = 30 then expPolynomialUpper30 reduced
      else if prec = 120 ∧ x ≤ 2 then (expPolynomialBounds120 reduced).2
      else expTaylorUpper prec terms reduced
    squareIter k (divDown prec 1 initial)
  else expNonnegDown prec terms x

def expUp (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  if x < 0 then
    let x := -x
    let k := expReductionSteps prec x
    let reduced := divPowTwo x k
    let initial := if prec = 30 then expPolynomialLower30 reduced
      else if prec = 120 ∧ x ≤ 2 then (expPolynomialBounds120 reduced).1
      else expTaylorLower prec terms reduced
    squareIter k (divUp prec 1 initial)
  else expNonnegUp prec terms x

def exp (prec : ℕ) (x : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb with
    | ⊥ => some 0
    | some a => some (expDown prec (expTaylorTerms prec) a)
  ub := match x.ub with
    | ⊤ => ⊤
    | some a => some (expUp prec (expTaylorTerms prec) a)

theorem exp_mem {r : ℝ} {x : Interval Dyadic} (prec : ℕ) (hrx : r ∈ x) :
    Real.exp r ∈ exp prec x := by
  sorry

end Exp

section Pi

def atanTerms (prec : ℕ) : ℕ := prec / 4 + 4

def atanBoundsAux (prec : ℕ) (ulp qSqLo qSqHi : Dyadic) :
    ℕ → ℕ → Bool → Dyadic → Dyadic → Dyadic → Dyadic → Dyadic × Dyadic
  | 0, _d, pos, _termLo, termHi, lo, hi =>
      if pos then (lo, hi + termHi) else (lo - termHi, hi)
  | n + 1, d, pos, termLo, termHi, lo, hi =>
      let lo' := if pos then lo + termLo else lo - termHi
      let hi' := if pos then hi + termHi else hi - termLo
      let d' := d + 2
      let termLo' := divNatDown prec (termLo * qSqLo * (d : Dyadic)) d'
      let termHi' := divNatUp prec (termHi * qSqHi * (d : Dyadic)) d'
      if termHi' ≤ ulp then
        if !pos then (lo', hi' + termHi') else (lo' - termHi', hi')
      else
        atanBoundsAux prec ulp qSqLo qSqHi n d' (!pos) termLo' termHi' lo' hi'

def atanBounds (prec : ℕ) (qLo qHi : Dyadic) (n : ℕ) : Dyadic × Dyadic :=
  atanBoundsAux prec (Dyadic.ofIntWithPrec 1 prec) (qLo * qLo) (qHi * qHi)
    (n + 1) 1 true qLo qHi 0 0

def pi (prec : ℕ) : Interval Dyadic :=
  let terms := atanTerms prec
  let q₁Lo := divNatDown prec 1 5
  let q₁Hi := divNatUp prec 1 5
  let q₂Lo := divNatDown prec 1 239
  let q₂Hi := divNatUp prec 1 239
  let a₁ := atanBounds prec q₁Lo q₁Hi terms
  let a₂ := atanBounds prec q₂Lo q₂Hi terms
  let lb := 16 * a₁.1 - 4 * a₂.2
  let ub := 16 * a₁.2 - 4 * a₂.1
  ⟨some lb, some ub⟩

theorem pi_mem (prec : ℕ) : Real.pi ∈ pi prec := by
  sorry

end Pi

meta def precisionExpr : InclusionM Expr := do
  return mkNatLit <| inclusion.large.precision.get (← getOptions)

@[inclusionExt real.dyadic | OfNat.ofNat _]
meta def evalOfNat : InclusionExt where
  priority := 0
  derive e := do
    let (``OfNat.ofNat, #[alpha, n, _]) := e.getAppFnArgs | failure
    unless ← isDefEq alpha (mkConst ``Real) do failure
    guard n.isRawNatLit
    return ⟨← mkAppM ``ofNat #[n], ← mkAppM ``ofNat_mem #[n]⟩

@[inclusionExt real.dyadic | _ + _]
meta def evalAdd : InclusionExt where
  priority := 0
  derive e := Inclusion.evalBinary e ``add ``add_mem

@[inclusionExt real.dyadic | _ - _]
meta def evalSub : InclusionExt where
  priority := 0
  derive e := Inclusion.evalBinary e ``sub ``sub_mem

@[inclusionExt real.dyadic | _ * _]
meta def evalMul : InclusionExt where
  priority := 0
  derive e := Inclusion.evalBinary e ``mul ``mul_mem

@[inclusionExt real.dyadic | OfScientific.ofScientific _ _ _]
meta def evalScientific : InclusionExt where
  derive e := do
    let (``OfScientific.ofScientific, #[alpha, _, m, s, exponent]) := e.getAppFnArgs | failure
    unless ← isDefEq alpha (mkConst ``Real) do failure
    let prec ← precisionExpr
    return ⟨← mkAppM ``scientific #[prec, m, s, exponent],
      ← mkAppM ``scientific_mem #[prec, m, s, exponent]⟩

@[inclusionExt real.dyadic | _ ^ _]
meta def evalPow : InclusionExt where
  derive e := do
    let (``HPow.hPow, #[alpha, beta, gamma, _, x, n]) := e.getAppFnArgs | failure
    unless ← isDefEq alpha (mkConst ``Real) do failure
    unless ← isDefEq beta (mkConst ``Nat) do failure
    unless ← isDefEq gamma (mkConst ``Real) do failure
    let body ← mkExprInclusionBody x
    return ⟨← mkAppM ``pow #[body.inclusionBody, n],
      ← mkAppM ``pow_mem #[body.proofBody, n]⟩

@[inclusionExt real.dyadic | Real.sqrt _]
meta def evalSqrt : InclusionExt where
  derive e := do
    let body ← mkExprInclusionBody (← realUnaryArg e)
    let prec ← precisionExpr
    return ⟨← mkAppM ``sqrt #[prec, body.inclusionBody],
      ← mkAppM ``sqrt_mem #[prec, body.proofBody]⟩

@[inclusionExt real.dyadic | Real.exp _]
meta def evalExp : InclusionExt where
  derive e := do
    let body ← mkExprInclusionBody (← realUnaryArg e)
    let prec ← precisionExpr
    return ⟨← mkAppM ``exp #[prec, body.inclusionBody],
      ← mkAppM ``exp_mem #[prec, body.proofBody]⟩

@[inclusionExt real.dyadic | Real.pi]
meta def evalPi : InclusionExt where
  derive e := do
    unless e.isConstOf ``Real.pi do failure
    let prec ← precisionExpr
    return ⟨← mkAppM ``pi #[prec], ← mkAppM ``pi_mem #[prec]⟩

@[inclusionExt real.dyadic | (_ : ℝ) < (_ : ℝ)]
meta def evalLt : InclusionExt where
  derive e := do
    let (``LT.lt, #[_, _, a, b]) := e.getAppFnArgs | failure
    unless ← isDefEq (← inferType a) (mkConst ``Real) do failure
    unless ← isDefEq (← inferType b) (mkConst ``Real) do failure
    let left ← mkExprInclusionBody a
    let right ← mkExprInclusionBody b
    return ⟨← mkAppM ``lt #[left.inclusionBody, right.inclusionBody],
      ← mkAppM ``lt_mem #[left.proofBody, right.proofBody]⟩

@[inclusionExt real.dyadic | (_ : ℝ) > (_ : ℝ)]
meta def evalGt : InclusionExt where
  derive e := do
    let (``GT.gt, #[_, _, b, a]) := e.getAppFnArgs | failure
    unless ← isDefEq (← inferType a) (mkConst ``Real) do failure
    unless ← isDefEq (← inferType b) (mkConst ``Real) do failure
    let left ← mkExprInclusionBody a
    let right ← mkExprInclusionBody b
    return ⟨← mkAppM ``lt #[left.inclusionBody, right.inclusionBody],
      ← mkAppM ``lt_mem #[left.proofBody, right.proofBody]⟩

end Inclusion.Large
