module

public import Mathlib.Tactic.Inclusion.Experimental.DyadicRealOperations
public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Experimental.Families
public import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

@[expose] public section

set_option warn.sorry false

open Lean Meta Set

namespace Inclusion.ComplexBall

/-- A complex number whose real and imaginary parts are dyadic. -/
structure GaussianDyadic where
  re : Dyadic
  im : Dyadic

def GaussianDyadic.toComplex (z : GaussianDyadic) : ℂ :=
  ⟨Dyadic.toReal z.re, Dyadic.toReal z.im⟩

def GaussianDyadic.zero : GaussianDyadic := ⟨0, 0⟩

def GaussianDyadic.ofNat (n : ℕ) : GaussianDyadic := ⟨n, 0⟩

def GaussianDyadic.I : GaussianDyadic := ⟨0, 1⟩

def GaussianDyadic.add (x y : GaussianDyadic) : GaussianDyadic :=
  ⟨x.re + y.re, x.im + y.im⟩

def GaussianDyadic.neg (x : GaussianDyadic) : GaussianDyadic := ⟨-x.re, -x.im⟩

def GaussianDyadic.sub (x y : GaussianDyadic) : GaussianDyadic :=
  ⟨x.re - y.re, x.im - y.im⟩

def GaussianDyadic.mul (x y : GaussianDyadic) : GaussianDyadic :=
  ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

def dyadicAbs (x : Dyadic) : Dyadic := if x < 0 then -x else x

/-- A cheap upper bound for the usual complex norm of a Gaussian dyadic. -/
def GaussianDyadic.normUpper (z : GaussianDyadic) : Dyadic :=
  dyadicAbs z.re + dyadicAbs z.im

/-- A cheap lower bound for the usual complex norm of a Gaussian dyadic. -/
def GaussianDyadic.normLower (z : GaussianDyadic) : Dyadic :=
  max (dyadicAbs z.re) (dyadicAbs z.im)

/-- A closed complex ball with a Gaussian-dyadic center. A top radius represents the whole plane. -/
structure Ball where
  center : GaussianDyadic
  radius : WithTop Dyadic

def Ball.toSet (b : Ball) : Set ℂ :=
  match b.radius with
  | ⊤ => Set.univ
  | some r => Metric.closedBall b.center.toComplex (Dyadic.toReal r)

instance : ToSet Ball ℂ := ⟨Ball.toSet⟩

def Ball.univ : Ball := ⟨GaussianDyadic.zero, ⊤⟩

instance : Univ Ball ℂ where
  univ := Ball.univ
  mem_univ x := by
    change x ∈ Ball.toSet Ball.univ
    simp [Ball.univ, Ball.toSet]

/-- Choose the smaller-radius input ball. This is a sound approximation to intersection because
every point in both balls lies in either input ball. -/
def Ball.refine (x y : Ball) : Ball := if x.radius ≤ y.radius then x else y

theorem Ball.refine_mem {z : ℂ} {x y : Ball} (hx : z ∈ x) (hy : z ∈ y) :
    z ∈ x.refine y := by
  simp only [Ball.refine]
  split <;> assumption

instance : Refine Ball ℂ where
  refine := Ball.refine
  mem_refine := Ball.refine_mem

def radiusAdd : WithTop Dyadic → WithTop Dyadic → WithTop Dyadic
  | some r, some s => some (r + s)
  | _, _ => ⊤

def Ball.ofNat (n : ℕ) : Ball := ⟨GaussianDyadic.ofNat n, 0⟩

def Ball.I : Ball := ⟨GaussianDyadic.I, 0⟩

def Ball.neg (x : Ball) : Ball := ⟨x.center.neg, x.radius⟩

def Ball.add (x y : Ball) : Ball :=
  ⟨x.center.add y.center, radiusAdd x.radius y.radius⟩

def Ball.sub (x y : Ball) : Ball :=
  ⟨x.center.sub y.center, radiusAdd x.radius y.radius⟩

def Ball.mul (x y : Ball) : Ball :=
  let radius := match x.radius, y.radius with
    | some r, some s =>
        some (x.center.normUpper * s + y.center.normUpper * r + r * s)
    | _, _ => ⊤
  ⟨x.center.mul y.center, radius⟩

def Ball.inv (x : Ball) : Ball :=
  let radius := match x.radius with
    | some r =>
        let lower := x.center.normLower - r
        if 0 < lower then some (Inclusion.upperApprox (1 / lower.toRat)) else ⊤
    | ⊤ => ⊤
  ⟨GaussianDyadic.zero, radius⟩

def Ball.div (x y : Ball) : Ball := x.mul y.inv

theorem ofNat_mem (n : ℕ) : (OfNat.ofNat n : ℂ) ∈ Ball.ofNat n := by
  sorry

theorem I_mem : Complex.I ∈ Ball.I := by
  sorry

theorem neg_mem {z : ℂ} {x : Ball} (hz : z ∈ x) : -z ∈ x.neg := by
  sorry

theorem add_mem {z w : ℂ} {x y : Ball} (hz : z ∈ x) (hw : w ∈ y) :
    z + w ∈ x.add y := by
  sorry

theorem sub_mem {z w : ℂ} {x y : Ball} (hz : z ∈ x) (hw : w ∈ y) :
    z - w ∈ x.sub y := by
  sorry

theorem mul_mem {z w : ℂ} {x y : Ball} (hz : z ∈ x) (hw : w ∈ y) :
    z * w ∈ x.mul y := by
  sorry

theorem inv_mem {z : ℂ} {x : Ball} (hz : z ∈ x) : z⁻¹ ∈ x.inv := by
  sorry

theorem div_mem {z w : ℂ} {x y : Ball} (hz : z ∈ x) (hw : w ∈ y) :
    z / w ∈ x.div y := by
  sorry

/-- Bounds the usual complex absolute value using the center's coordinate norms and the radius. -/
def Ball.absBounds (x : Ball) : Interval Dyadic :=
  match x.radius with
  | some r =>
      ⟨some (max 0 (x.center.normLower - r)), some (x.center.normUpper + r)⟩
  | ⊤ => Interval.univ Dyadic

theorem abs_mem {z : ℂ} {x : Ball} (hz : z ∈ x) : ‖z‖ ∈ x.absBounds := by
  sorry

/-- Enclose a metric closed ball whose center and radius are themselves enclosed. -/
def closedBallHull (center : Ball) (radius : Interval Dyadic) : Ball :=
  let resultRadius := match center.radius, radius.ub with
    | some centerRadius, some radiusUpper => some (centerRadius + radiusUpper)
    | _, _ => ⊤
  ⟨center.center, resultRadius⟩

theorem closedBallHull_mem {z center : ℂ} {radius : ℝ} {centerBall : Ball}
    {radiusInterval : Interval Dyadic} (hcenter : center ∈ centerBall)
    (hradius : radius ∈ radiusInterval) (hz : z ∈ Metric.closedBall center radius) :
    z ∈ closedBallHull centerBall radiusInterval := by
  sorry

meta def complexUnaryArg (e : Expr) : InclusionM Expr := do
  let .app _ a ← whnfR e | failure
  unless ← isDefEq (← inferType a) (mkConst ``Complex) do failure
  unless ← isDefEq (← inferType e) (mkConst ``Complex) do failure
  return a

meta def complexBinaryArgs (e : Expr) : InclusionM (Expr × Expr) := do
  let .app (.app _ a) b ← whnfR e | failure
  unless ← isDefEq (← inferType a) (mkConst ``Complex) do failure
  unless ← isDefEq (← inferType b) (mkConst ``Complex) do failure
  unless ← isDefEq (← inferType e) (mkConst ``Complex) do failure
  return (a, b)

meta def evalComplexUnary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let body ← mkExprInclusionBody (← complexUnaryArg e)
  return ⟨← mkAppM op #[body.inclusionBody], ← mkAppM inclusion #[body.proofBody]⟩

meta def evalComplexBinary (e : Expr) (op inclusion : Name) : InclusionM ExprInclusionBody := do
  let (a, b) ← complexBinaryArgs e
  let left ← mkExprInclusionBody a
  let right ← mkExprInclusionBody b
  return ⟨← mkAppM op #[left.inclusionBody, right.inclusionBody],
    ← mkAppM inclusion #[left.proofBody, right.proofBody]⟩

@[inclusionExt complex.ball | OfNat.ofNat _]
meta def evalOfNat : InclusionExt where
  derive e := do
    let (``OfNat.ofNat, #[α, n, _]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Complex) do failure
    guard n.isRawNatLit
    return ⟨← mkAppM ``Ball.ofNat #[n], ← mkAppM ``ofNat_mem #[n]⟩

@[inclusionExt complex.ball | Complex.I]
meta def evalI : InclusionExt where
  derive e := do
    unless e.isConstOf ``Complex.I do failure
    return ⟨mkConst ``Ball.I, mkConst ``I_mem⟩

@[inclusionExt complex.ball | Neg.neg _]
meta def evalNeg : InclusionExt where
  derive e := evalComplexUnary e ``Ball.neg ``neg_mem

@[inclusionExt complex.ball | (_ : ℂ) + (_ : ℂ)]
meta def evalAdd : InclusionExt where
  derive e := evalComplexBinary e ``Ball.add ``add_mem

@[inclusionExt complex.ball | (_ : ℂ) - (_ : ℂ)]
meta def evalSub : InclusionExt where
  derive e := evalComplexBinary e ``Ball.sub ``sub_mem

@[inclusionExt complex.ball | (_ : ℂ) * (_ : ℂ)]
meta def evalMul : InclusionExt where
  derive e := evalComplexBinary e ``Ball.mul ``mul_mem

@[inclusionExt complex.ball | (_ : ℂ) / (_ : ℂ)]
meta def evalDiv : InclusionExt where
  derive e := evalComplexBinary e ``Ball.div ``div_mem

@[inclusionExt complex.ball | ‖(_ : ℂ)‖]
meta def evalAbs : InclusionExt where
  derive e := do
    let .app _ z ← whnfR e | failure
    unless ← isDefEq (← inferType z) (mkConst ``Complex) do failure
    unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
    let body ← mkExprInclusionBody z
    return ⟨← mkAppM ``Ball.absBounds #[body.inclusionBody],
      ← mkAppM ``abs_mem #[body.proofBody]⟩

@[inclusionExt complex.ball | (_ : ℂ)]
meta def mkComplexIVar : InclusionExt :=
  mkNDIVarExt (mkConst ``Complex) (pure (mkConst ``Ball))

meta def closedBallArgs? (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let (``Membership.mem, #[_, _, _, set, z]) := (← whnfR type).getAppFnArgs | return none
  let (``Metric.closedBall, args) := set.getAppFnArgs | return none
  if args.size < 2 then return none
  return some (z, args[args.size - 2]!, args[args.size - 1]!)

meta def deriveClosedBallHyp (h type : Expr) : HypothesisM Unit := do
  let some (z, center, radius) ← closedBallArgs? type | failure
  let some iExpr ← requestedIVar? z | return
  let centerBody ← mkHypInclusionBody center iExpr.iType
  let radiusSetType ← mkAppM ``Interval #[mkConst ``Dyadic]
  let radiusToSet ← synthInstance
    (← mkAppM ``ToSet #[radiusSetType, mkConst ``Real])
  let radiusType : IType := ⟨mkConst ``Real, radiusSetType, radiusToSet⟩
  let radiusBody ← mkHypInclusionBody radius radiusType
  let set ← mkAppM ``closedBallHull #[centerBody.inclusionBody, radiusBody.inclusionBody]
  let proof ← mkAppM ``closedBallHull_mem #[centerBody.proofBody, radiusBody.proofBody, h]
  addInclusionHyp iExpr ⟨set, proof⟩

@[hypothesisExt complex.ball | (_ : ℂ) ∈ Metric.closedBall _ _]
meta def evalClosedBallHyp : HypothesisExt where
  derive := deriveClosedBallHyp

end Inclusion.ComplexBall
