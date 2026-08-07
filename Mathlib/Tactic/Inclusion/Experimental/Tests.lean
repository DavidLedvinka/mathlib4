module

public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace Inclusion.Tests

def unitInterval : Interval Dyadic := ⟨1, 2⟩

def positiveInterval : Interval Dyadic := ⟨3, 4⟩

def negativeInterval : Interval Dyadic := ⟨some (-4), some (-2)⟩

def zeroInterval : Interval Dyadic := ⟨some (-1), 1⟩

def metaValue : ℝ := 1

theorem metaValue_mem : metaValue ∈ Inclusion.ofNat 1 := by
  simpa [metaValue] using Inclusion.ofNat_mem 1

@[inclusionExt metaValue]
meta def evalMetaValue : InclusionExt where
  eval e := do
    unless e.isConstOf ``metaValue do failure
    return ⟨← mkAppM ``Inclusion.ofNat #[mkNatLit 1], mkConst ``metaValue_mem⟩

theorem natCast_mem (n : ℕ) : (n : ℝ) ∈ Inclusion.ofNat n := by
  constructor
  · exact WithBot.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast]
  · exact WithTop.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast]

def indexedValue (i : ℕ) : ℝ := i

theorem indexedValue_mem (i : ℕ) : indexedValue i ∈ Inclusion.ofNat i := by
  simpa [indexedValue] using natCast_mem i

def unregisteredIndexedValue (i : ℕ) : ℝ := i

@[inclusionExt indexedValue _]
meta def evalIndexedValue : InclusionExt where
  eval e := do
    let (``indexedValue, #[i]) := e.getAppFnArgs | failure
    return ⟨← mkAppM ``Inclusion.ofNat #[i], ← mkAppM ``indexedValue_mem #[i]⟩

def natPow (x : Interval Dyadic) : ℕ → Interval Dyadic
  | 0 => Inclusion.ofNat 1
  | n + 1 => Inclusion.mul (natPow x n) x

theorem natPow_mem {r : ℝ} {x : Interval Dyadic} (h : r ∈ x) (n : ℕ) :
    r ^ n ∈ natPow x n := by
  induction n with
  | zero => simpa [natPow] using Inclusion.ofNat_mem 1
  | succ n ih =>
    rw [pow_succ]
    exact Inclusion.mul_mem ih h

@[inclusionExt _ ^ _]
meta def evalNatPow : InclusionExt where
  eval e := do
    let (``HPow.hPow, #[α, β, γ, _, x, n]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Real) do failure
    unless ← isDefEq β (mkConst ``Nat) do failure
    unless ← isDefEq γ (mkConst ``Real) do failure
    let body ← mkExprInclusionBody x
    return ⟨← mkAppM ``natPow #[body.inclusionBody, n],
      ← mkAppM ``natPow_mem #[body.proofBody, n]⟩

@[inclusionExt Finset.sum (Finset.range _) _]
meta def evalRangeSum : InclusionExt where
  eval e := do
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

theorem true_mem : True ∈ IntervalBool.true := Inclusion.mem_intervalBool_true trivial

@[inclusionExt True]
meta def evalTrue : InclusionExt where
  eval e := do
    unless e.isConstOf ``True do failure
    return ⟨mkConst ``IntervalBool.true, mkConst ``true_mem⟩

@[inclusionParam]
meta def testParam : InclusionParamDecl where
  name := `testParam
  enabledByDefault := true
  defaultValue := 7

def parameterizedTrue : Prop := True

def parameterizedTrueCheck (n : Nat) : IntervalBool :=
  if n = 7 then .true else .undetermined

theorem parameterizedTrue_mem (n : Nat) : parameterizedTrue ∈ parameterizedTrueCheck n := by
  unfold parameterizedTrueCheck
  split
  · exact Inclusion.mem_intervalBool_true trivial
  · exact Inclusion.mem_intervalBool_undetermined _

@[inclusionExt parameterizedTrue]
meta def evalParameterizedTrue : InclusionExt where
  eval e := do
    unless e.isConstOf ``parameterizedTrue do failure
    let some n ← getParam? `testParam | failure
    return ⟨← mkAppM ``parameterizedTrueCheck #[n], ← mkAppM ``parameterizedTrue_mem #[n]⟩

def parameterizedBound : ℝ := 1

def parameterizedBoundInterval (n : Nat) : Interval Dyadic :=
  if n = 7 then Inclusion.ofNat 1 else Interval.univ Dyadic

theorem parameterizedBound_mem (n : Nat) : parameterizedBound ∈ parameterizedBoundInterval n := by
  simp only [parameterizedBoundInterval]
  split
  · simpa [parameterizedBound] using Inclusion.ofNat_mem 1
  · exact Inclusion.mem_univ _

@[inclusionExt parameterizedBound]
meta def evalParameterizedBound : InclusionExt where
  eval e := do
    unless e.isConstOf ``parameterizedBound do failure
    let some n ← getParam? `testParam | failure
    return ⟨← mkAppM ``parameterizedBoundInterval #[n],
      ← mkAppM ``parameterizedBound_mem #[n]⟩

example : True := by
  inclusion

example : parameterizedTrue := by
  inclusion

example : True := by
  fail_if_success
    have : parameterizedTrue := by
      inclusion [testParam := 6]
  trivial

run_meta
  let enabled := ({} : NameSet).insert `testParam
  let fn ← toCoveredExprInclusionFunction (mkConst ``parameterizedTrue) enabled
  let check ← compileInclusionCheck fn
  match check #[6], check #[7] with
  | .undetermined, .true => pure ()
  | _, _ => throwError "Compiled inclusion parameters cannot be varied without recompilation"

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let bound := mkConst ``parameterizedBound
    let hypType ← mkAppM ``LE.le #[x, bound]
    withLocalDeclD `hx hypType fun _hx => do
      let one ← mkNumeral (mkConst ``Real) 1
      let target ← mkAppM ``LE.le #[x, one]
      let enabled := ({} : NameSet).insert `testParam
      let raw ← toCoveredExprInclusionFunction target enabled
      let closed ← raw.closeWithBounds (← mkInclusionHypBounds raw enabled)
      let check ← compileInclusionCheck closed
      match check #[6], check #[7] with
      | .undetermined, .true => pure ()
      | _, _ => throwError "Hypothesis-bound parameters cannot be varied without recompilation"

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let one ← mkNumeral (mkConst ``Real) 1
    let target ← mkAppM ``LE.le #[x, one]
    let raw ← toCoveredExprInclusionFunction target
    let closed ← raw.closeWithBounds (← mkInclusionHypBounds raw {})
    unless closed.iexprs.isEmpty do
      throwError "Universal hypothesis preprocessing did not close all inclusion variables"
    let check ← compileInclusionCheck closed
    match check #[] with
    | .undetermined => pure ()
    | _ => throwError "An unbounded inclusion variable unexpectedly verified the test inequality"

example : metaValue ≤ 2 := by
  inclusion

example : ∑ i ∈ Finset.range 3, indexedValue i + 1 ≤ 6 := by
  inclusion

example {x : ℝ} (hx : x ∈ unitInterval) : x ^ 3 ≤ 8 := by
  inclusion

example {x : ℝ} (hx : x ∈ unitInterval) :
    (∑ i ∈ Finset.range 3, x ^ (i + 1)) ≤ 14 := by
  inclusion

example : (∫ x in (0 : ℝ)..1, x * x) ≤ 1 / 2 := by
  inclusion

example : 0 ≤ ∫ x in (0 : ℝ)..1, x * x := by
  inclusion

example {y : ℝ} (hy : y ∈ unitInterval) :
    (∫ x in (0 : ℝ)..1, x * y) ≤ 5 / 4 := by
  inclusion

example : (1 : ℝ) + 2 ≤ 4 := by
  inclusion

example : (1 : ℝ) / 3 ≤ 334 / 1000 := by
  inclusion

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) : x + y ≤ 6 := by
  inclusion

example {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x < 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx₁ : x ∈ unitInterval) (hx₂ : x ≤ 3) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x = 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : 2 = x) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Ici 1) : -x ≤ -1 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Ioi 1) : -x ≤ -1 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Iic 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Iio 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Ico 1 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Ioc 1 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x ∈ Set.Ioo 1 2) : x + x ≤ 4 := by
  inclusion

example {x : ℝ} (hx : x ≤ parameterizedBound) : x ≤ 1 := by
  inclusion

example {x : ℝ} (hx : x ∈ unitInterval) : x + x ≤ 4 := by
  inclusion

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) : x - y ≤ -1 := by
  inclusion

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) : x * y ≤ 8 := by
  inclusion

example {x y : ℝ} (hx : x ∈ negativeInterval) (hy : y ∈ unitInterval) : x * y ≤ -2 := by
  inclusion

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ unitInterval) : x / y ≤ 2 := by
  inclusion

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ negativeInterval) :
    x / y ≤ -(1 / 4) := by
  inclusion

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) :
    (x + 1) * (y - 2) / 2 ≤ 5 := by
  inclusion

example {x : ℝ} (hx : x ∈ unitInterval) : -x ≤ -1 := by
  inclusion

def unsupportedValue (x : ℝ) : ℝ := x

example {x : ℝ} (hx : unsupportedValue x ∈ unitInterval) : unsupportedValue x + 1 ≤ 3 := by
  inclusion

example {x : ℝ} (hx : unsupportedValue x ≤ 2) : unsupportedValue x + 1 ≤ 3 := by
  inclusion

example (_x : ℝ) : True := by
  fail_if_success
    have : _x ≤ 1 := by
      inclusion
  trivial

example {x y : ℝ} (_hx : x ∈ unitInterval) (_hy : y ∈ zeroInterval) : True := by
  fail_if_success
    have : x / y ≤ 10 := by
      inclusion
  trivial

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let e ← mkAppM ``HAdd.hAdd #[x, x]
    InclusionM.run do
      discard <| mkExprInclusionBody e
      unless (← get).ivars.size == 1 do
        throwError "Expected repeated expressions to share one inclusion variable"

run_meta
  let succeeded ← try
    discard <| InclusionM.run do
      withLocalDeclD `i (mkConst ``Nat) fun i => do
        let e ← mkAppM ``unregisteredIndexedValue #[i]
        mkExprInclusionBody e
    pure true
  catch _ =>
    pure false
  if succeeded then
    throwError "A binder-dependent expression must not be used as an inclusion variable"

end Inclusion.Tests
