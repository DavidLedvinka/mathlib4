module

public import Mathlib.Tactic.Inclusion.Experimental.DyadicRealOperations
public import Mathlib.Tactic.Inclusion.Experimental.Sum
public meta import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Extensions
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public meta import Mathlib.Tactic.FunProp

set_option linter.style.header false

@[expose] public section

open Lean Meta
open Set MeasureTheory

namespace Inclusion

def unitIntegralStep : Dyadic := Dyadic.ofIntWithPrec 1 2

def unitIntegralPoint (i : ℕ) : Dyadic := Dyadic.ofIntWithPrec i 2

def unitIntegralPiece (i : ℕ) : Interval Dyadic :=
  ⟨unitIntegralPoint i, unitIntegralPoint (i + 1)⟩

def unitIntegral (g : Interval Dyadic → Interval Dyadic) : Interval Dyadic :=
  sumRangeIntervals 4 fun i =>
    mul (Interval.singleton Dyadic unitIntegralStep) (g (unitIntegralPiece i))

@[simp]
theorem unitIntegralPoint_toReal (i : ℕ) :
    Dyadic.toReal (unitIntegralPoint i) = (i : ℝ) / 4 := by
  norm_num [unitIntegralPoint, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  ring

@[simp]
theorem unitIntegralStep_toReal : Dyadic.toReal unitIntegralStep = (1 : ℝ) / 4 := by
  norm_num [unitIntegralStep, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

theorem integralPiece_mem {a b : ℝ} {f : ℝ → ℝ} {w : Dyadic} {I : Interval Dyadic}
    (hab : a ≤ b) (hw : b - a = Dyadic.toReal w)
    (hf : IntervalIntegrable f volume a b) (h : ∀ x ∈ Icc a b, f x ∈ I) :
    (∫ x in a..b, f x) ∈ mul (Interval.singleton Dyadic w) I := by
  match I with
  | ⟨some l, some u⟩ =>
    have hl : ∫ _ in a..b, Dyadic.toReal l ≤ ∫ x in a..b, f x := by
      apply intervalIntegral.integral_mono_on hab
        (Continuous.intervalIntegrable continuous_const _ _) hf
      intro x hx
      exact WithBot.coe_le_coe.mp (h x hx).1
    have hu : ∫ x in a..b, f x ≤ ∫ _ in a..b, Dyadic.toReal u := by
      apply intervalIntegral.integral_mono_on hab hf
        (Continuous.intervalIntegrable continuous_const _ _)
      intro x hx
      exact WithTop.coe_le_coe.mp (h x hx).2
    rw [intervalIntegral.integral_const, hw] at hl hu
    constructor
    · apply WithBot.coe_le_coe.mpr
      simpa [mul, Interval.singleton, min4] using
        (min_le_left (Dyadic.toReal w * Dyadic.toReal l)
          (Dyadic.toReal w * Dyadic.toReal u)).trans hl
    · apply WithTop.coe_le_coe.mpr
      simpa [mul, Interval.singleton, max4] using
        hu.trans (le_max_right (Dyadic.toReal w * Dyadic.toReal l)
          (Dyadic.toReal w * Dyadic.toReal u))
  | ⟨⊥, _⟩ | ⟨some _, ⊤⟩ =>
    exact mem_univ _

theorem unitIntegral_mem {f : ℝ → ℝ}
    (g : Interval Dyadic → Interval Dyadic) (hf : Continuous f)
    (h : ∀ (x : ℝ) (I : Interval Dyadic), x ∈ I → f x ∈ g I) :
    (∫ x in (0 : ℝ)..1, f x) ∈ unitIntegral g := by
  have hpiece (i : ℕ) :
      (∫ x in Dyadic.toReal (unitIntegralPoint i)..
        Dyadic.toReal (unitIntegralPoint (i + 1)), f x) ∈
        mul (Interval.singleton Dyadic unitIntegralStep) (g (unitIntegralPiece i)) := by
    apply integralPiece_mem
    · simp only [unitIntegralPoint_toReal, Nat.cast_add, Nat.cast_one]
      linarith
    · simp [unitIntegralPoint_toReal, unitIntegralStep_toReal]
      ring
    · exact hf.intervalIntegrable _ _
    · intro x hx
      apply h x (unitIntegralPiece i)
      exact ⟨WithBot.coe_le_coe.mpr hx.1, WithTop.coe_le_coe.mpr hx.2⟩
  have hsum := sumRangeIntervals_mem 4 hpiece
  have hpartition :=
    intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun i => Dyadic.toReal (unitIntegralPoint i)) (μ := volume) (m := 0) (n := 4)
      (by omega) (fun _ _ => hf.intervalIntegrable _ _)
  have hpartition' :
      (∑ i ∈ Finset.range 4,
        ∫ x in Dyadic.toReal (unitIntegralPoint i)..
          Dyadic.toReal (unitIntegralPoint (i + 1)), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    simpa using hpartition
  rw [← hpartition']
  simpa [unitIntegral] using hsum

private meta def proveContinuous (x integrand : Expr) : MetaM Expr := do
  let integrandFn ← mkLambdaFVars #[x] integrand
  let continuousGoal ← mkAppM ``Continuous #[integrandFn]
  let some proof ←
    Mathlib.Meta.FunProp.tacticToDischarge (← `(tactic| fun_prop)) continuousGoal
    | throwError "fun_prop could not prove {continuousGoal}"
  return proof

@[inclusionExt real.dyadic | intervalIntegral (_ : ℝ → ℝ) _ _ volume]
meta def evalUnitIntegral : InclusionExt where
  derive e := do
    let (``intervalIntegral, #[E, _, _, f, a, b, _]) := e.getAppFnArgs | failure
    unless ← isDefEq E (mkConst ``Real) do failure
    let some (0, _) ← getOfNatValue? a ``Real | failure
    let some (1, _) ← getOfNatValue? b ``Real | failure
    lambdaTelescope f fun xs integrand => do
      let #[x] := xs | failure
      let continuousProof ← proveContinuous x integrand
      let xType ← inferType x
      let setType ← mkAppM ``Interval #[mkConst ``Dyadic]
      let toSetInst ← synthInstance (← mkAppM ``ToSet #[setType, xType])
      withLocalDeclD `integralInterval setType fun interval => do
        let iExpr : IExpr := ⟨⟨xType, setType, toSetInst⟩, x⟩
        let hypType ← iExpr.mkMem interval
        withLocalDeclD `integralHyp hypType fun hyp => do
          let iVar : IVar := { iExpr, setVar := interval, hypVar := hyp, cover := none }
          modify fun state => { state with iVars := state.iVars.insert iVar.expr iVar }
          let body ← try mkExprInclusionBody integrand finally
            modify fun state => { state with iVars := state.iVars.erase x }
          let intervalFn ← mkLambdaFVars #[interval] body.inclusionBody
          let proofFn ← mkLambdaFVars #[x, interval, hyp] body.proofBody
          return ⟨← mkAppM ``unitIntegral #[intervalFn],
            ← mkAppM ``unitIntegral_mem #[intervalFn, continuousProof, proofFn]⟩

end Inclusion
