module

public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions

set_option linter.style.header false

@[expose] public section

open Lean Meta
open IntervalArithmetic

namespace IntervalArithmetic.Inclusion.Tests

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

example : True := by
  inclusion

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
    let fn ← toExprInclusionFunction e
    unless fn.ivars.size == 1 do
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

end IntervalArithmetic.Inclusion.Tests
