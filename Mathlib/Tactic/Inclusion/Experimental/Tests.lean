module

public import Mathlib.Tactic.Inclusion.Experimental.DyadicRealOperations
public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Experimental.Integral
public meta import Mathlib.Tactic.Inclusion.Experimental.Families

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

@[inclusionExt real.dyadic | metaValue]
meta def evalMetaValue : InclusionExt where
  derive e := do
    unless e.isConstOf ``metaValue do failure
    return ⟨← mkAppM ``Inclusion.ofNat #[mkNatLit 1], mkConst ``metaValue_mem⟩

def familyValue : ℝ := 1

theorem familyValue_mem : familyValue ∈ Inclusion.ofNat 1 := by
  simpa [familyValue] using Inclusion.ofNat_mem 1

@[inclusionExt test.family | familyValue]
meta def evalFamilyValue : InclusionExt where
  userName := `familyValue
  derive e := do
    unless e.isConstOf ``familyValue do failure
    return ⟨← mkAppM ``Inclusion.ofNat #[mkNatLit 1], mkConst ``familyValue_mem⟩

@[inclusionExt test.other | familyValue]
meta def evalFamilyValueOther : InclusionExt where
  userName := `familyValue
  derive e := do
    unless e.isConstOf ``familyValue do failure
    return ⟨← mkAppM ``Inclusion.ofNat #[mkNatLit 1], mkConst ``familyValue_mem⟩

inductive FamilyUpperBound (x : ℝ) : Prop where
  | intro (h : x ≤ 1)

@[hypothesisOp test.hypothesis]
theorem FamilyUpperBound.mem {x : ℝ} (h : FamilyUpperBound x) :
    x ∈ (Inclusion.ofNat 1).downwardClosure := by
  rcases h with ⟨hx⟩
  exact downwardClosure_mem hx (Inclusion.ofNat_mem 1)

inductive IsSum (z x y : ℝ) : Prop where
  | intro (h : z = x + y)

@[hypothesisOp test.hypothesis]
theorem IsSum.mem {z x y : ℝ} {I J : Interval Dyadic}
    (h : IsSum z x y) (hx : x ∈ I) (hy : y ∈ J) : z ∈ Inclusion.add I J := by
  obtain ⟨rfl⟩ := h
  exact Inclusion.add_mem hx hy

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

@[inclusionExt real.dyadic | indexedValue _]
meta def evalIndexedValue : InclusionExt where
  derive e := do
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

@[inclusionExt real.dyadic | _ ^ _]
meta def evalNatPow : InclusionExt where
  derive e := do
    let (``HPow.hPow, #[α, β, γ, _, x, n]) := e.getAppFnArgs | failure
    unless ← isDefEq α (mkConst ``Real) do failure
    unless ← isDefEq β (mkConst ``Nat) do failure
    unless ← isDefEq γ (mkConst ``Real) do failure
    let body ← mkExprInclusionBody x
    return ⟨← mkAppM ``natPow #[body.inclusionBody, n],
      ← mkAppM ``natPow_mem #[body.proofBody, n]⟩

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

theorem true_mem : True ∈ IntervalBool.true := Inclusion.mem_intervalBool_true trivial

@[inclusionExt real.dyadic | True]
meta def evalTrue : InclusionExt where
  derive e := do
    unless e.isConstOf ``True do failure
    return ⟨mkConst ``IntervalBool.true, mkConst ``true_mem⟩

@[inclusionParam]
meta def testParam : InclusionParamDecl where
  name := `testParam
  defaultValue := some 7

inductive ParameterizedUpperBound (x : ℝ) : Prop where
  | intro (h : x ≤ 1)

def parameterizedUpperInterval (n : ℕ) : Interval Dyadic :=
  if n = 7 then (Inclusion.ofNat 1).downwardClosure else Interval.univ Dyadic

@[hypothesisOp test.hypothesis]
theorem ParameterizedUpperBound.mem (testParam : ℕ) {x : ℝ}
    (h : ParameterizedUpperBound x) : x ∈ parameterizedUpperInterval testParam := by
  rcases h with ⟨hx⟩
  by_cases hn : testParam = 7
  · simpa [parameterizedUpperInterval, hn] using
      downwardClosure_mem hx (Inclusion.ofNat_mem 1)
  · simpa [parameterizedUpperInterval, hn] using Inclusion.mem_univ x

def parameterizedTrue : Prop := True

def parameterizedTrueCheck (n : Nat) : IntervalBool :=
  if n = 7 then .true else .undetermined

@[inclusionOp real.dyadic 900]
theorem parameterizedTrue_mem (testParam : Nat) :
    parameterizedTrue ∈ parameterizedTrueCheck testParam := by
  unfold parameterizedTrueCheck
  split
  · exact Inclusion.mem_intervalBool_true trivial
  · exact Inclusion.mem_intervalBool_undetermined _

def parameterizedEndpoint : ℝ := 1

def parameterizedEndpointInterval (n : Nat) : Interval Dyadic :=
  if n = 7 then Inclusion.ofNat 1 else Interval.univ Dyadic

theorem parameterizedEndpoint_mem (n : Nat) :
    parameterizedEndpoint ∈ parameterizedEndpointInterval n := by
  simp only [parameterizedEndpointInterval]
  split
  · simpa [parameterizedEndpoint] using Inclusion.ofNat_mem 1
  · exact Inclusion.mem_univ _

@[inclusionExt real.dyadic | parameterizedEndpoint]
meta def evalParameterizedEndpoint : InclusionExt where
  derive e := do
    unless e.isConstOf ``parameterizedEndpoint do failure
    let n ← getParam `testParam
    return ⟨← mkAppM ``parameterizedEndpointInterval #[n],
      ← mkAppM ``parameterizedEndpoint_mem #[n]⟩

example : True := by
  inclusion [core, real.dyadic]

example : True := by
  fail_if_success
    have : True := by
      inclusion []
  trivial

example : True := by
  inclusion +kernel [core, real.dyadic]

example : True := by
  inclusion (kernel := true) [core, real.dyadic]

example : parameterizedTrue := by
  inclusion [core, real.dyadic]

example : parameterizedTrue := by
  inclusion +kernel [core, real.dyadic] (testParam := 7)

example : True := by
  fail_if_success
    have : parameterizedTrue := by
      inclusion [core, real.dyadic] (testParam := 6)
  trivial

example : True := by
  fail_if_success
    have : parameterizedTrue := by
      inclusion +kernel [core, real.dyadic] (testParam := 6)
  trivial

example : True := by
  fail_if_success
    have : parameterizedTrue := by
      inclusion +kernel +native [core, real.dyadic]
  trivial

run_meta
  let enabled := ({} : NameSet).insert `testParam
  let families := #[`core, `real.dyadic]
  let fn ← (toExprInclusion (mkConst ``parameterizedTrue)).run enabled families
  let check6 ← compileInclusionCheck (mkApp fn.inclusion (mkNatLit 6))
  let check7 ← compileInclusionCheck (mkApp fn.inclusion (mkNatLit 7))
  match check6, check7 with
  | .undetermined, .true => pure ()
  | _, _ => throwError "Exact compiled inclusion checks used unexpected parameter values"

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let endpoint := mkConst ``parameterizedEndpoint
    let hypType ← mkAppM ``LE.le #[x, endpoint]
    withLocalDeclD `hx hypType fun _hx => do
      let goal ← mkAppM ``LE.le #[x, endpoint]
      let enabled := ({} : NameSet).insert `testParam
      let families := #[`core, `real.dyadic]
      let inclusion ← (toExprInclusion goal).run enabled families
      unless inclusion.params == #[`testParam] do
        throwError "Goal and hypothesis computations did not share their inclusion parameter"
      let check6 ← compileInclusionCheck (mkApp inclusion.inclusion (mkNatLit 6))
      let check7 ← compileInclusionCheck (mkApp inclusion.inclusion (mkNatLit 7))
      match check6, check7 with
      | .undetermined, .true => pure ()
      | _, _ => throwError "Exact compiled hypothesis checks used unexpected parameter values"

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let one ← mkNumeral (mkConst ``Real) 1
    let goal ← mkAppM ``LE.le #[x, one]
    let families := #[`core, `real.dyadic]
    let inclusion ← (toExprInclusion goal).run (families := families)
    match ← compileInclusionCheck inclusion.inclusion with
    | .undetermined => pure ()
    | _ => throwError "An inclusion variable without a hypothesis unexpectedly verified the test \
      inequality"

example : metaValue ≤ 2 := by
  inclusion [core, real.dyadic]

example : familyValue + 1 ≤ 2 := by
  inclusion [core, real.dyadic, test.family]

example : familyValue ≤ 1 := by
  inclusion +kernel [core, real.dyadic, test.family]

example : familyValue ≤ 1 := by
  inclusion [core, real.dyadic, test.other]

example : True := by
  fail_if_success
    have : familyValue ≤ 1 := by
      inclusion [core, real.dyadic]
  trivial

example {x : ℝ} (hx : x ≤ familyValue) : x ≤ 1 := by
  inclusion [core, real.dyadic, test.family]

example {x : ℝ} (hx : FamilyUpperBound x) : x ≤ 1 := by
  inclusion [core, real.dyadic, test.hypothesis]

example {z : ℝ} (hz : IsSum z 1 2) : z ≤ 3 := by
  inclusion [core, real.dyadic, test.hypothesis]

example {x : ℝ} (hx : ParameterizedUpperBound x) : x ≤ 1 := by
  inclusion [core, real.dyadic, test.hypothesis]

example {x : ℝ} (_hx : ParameterizedUpperBound x) : True := by
  fail_if_success
    have : x ≤ 1 := by
      inclusion [core, real.dyadic, test.hypothesis] (testParam := 6)
  trivial

example {x : ℝ} (_hx : FamilyUpperBound x) : True := by
  fail_if_success
    have : x ≤ 1 := by
      inclusion [core, real.dyadic]
  trivial

example : True := by
  fail_if_success
    have : familyValue ≤ 1 := by
      inclusion [core, real.dyadic, test.unknown]
  trivial

example : ∑ i ∈ Finset.range 3, indexedValue i + 1 ≤ 6 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ unitInterval) : x ^ 3 ≤ 8 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ unitInterval) :
    (∑ i ∈ Finset.range 3, x ^ (i + 1)) ≤ 14 := by
  inclusion [core, real.dyadic]

example : (∫ x in (0 : ℝ)..1, x * x) ≤ 1 / 2 := by
  inclusion [core, real.dyadic]

example : 0 ≤ ∫ x in (0 : ℝ)..1, x * x := by
  inclusion [core, real.dyadic]

example {y : ℝ} (hy : y ∈ unitInterval) :
    (∫ x in (0 : ℝ)..1, x * y) ≤ 5 / 4 := by
  inclusion [core, real.dyadic]

example : (1 : ℝ) + 2 ≤ 4 := by
  inclusion [core, real.dyadic]

example : (1 : ℝ) / 3 ≤ 334 / 1000 := by
  inclusion [core, real.dyadic]

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) : x + y ≤ 6 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x < 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx₁ : x ∈ unitInterval) (hx₂ : x ≤ 3) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x = 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : 2 = x) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Ici 1) : -x ≤ -1 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Ioi 1) : -x ≤ -1 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Iic 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Iio 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Ico 1 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Ioc 1 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Icc (indexedValue 1) (indexedValue 2)) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Ioo 1 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ≤ parameterizedEndpoint) : x ≤ 1 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ unitInterval) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ unitInterval) : x + x ≤ 4 := by
  inclusion +kernel [core, real.dyadic]

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) : x - y ≤ -1 := by
  inclusion [core, real.dyadic]

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) : x * y ≤ 8 := by
  inclusion [core, real.dyadic]

example {x y : ℝ} (hx : x ∈ negativeInterval) (hy : y ∈ unitInterval) : x * y ≤ -2 := by
  inclusion [core, real.dyadic]

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ unitInterval) : x / y ≤ 2 := by
  inclusion [core, real.dyadic]

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ negativeInterval) :
    x / y ≤ -(1 / 4) := by
  inclusion [core, real.dyadic]

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ positiveInterval) :
    (x + 1) * (y - 2) / 2 ≤ 5 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ unitInterval) : -x ≤ -1 := by
  inclusion [core, real.dyadic]

def unsupportedValue (x : ℝ) : ℝ := x

example {x : ℝ} (hx : unsupportedValue x ∈ unitInterval) : unsupportedValue x + 1 ≤ 3 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : unsupportedValue x ≤ 2) : unsupportedValue x + 1 ≤ 3 := by
  inclusion [core, real.dyadic]

example (_x : ℝ) : True := by
  fail_if_success
    have : _x ≤ 1 := by
      inclusion [core, real.dyadic]
  trivial

example {x y : ℝ} (_hx : x ∈ unitInterval) (_hy : y ∈ zeroInterval) : True := by
  fail_if_success
    have : x / y ≤ 10 := by
      inclusion [core, real.dyadic]
  trivial

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let e ← mkAppM ``HAdd.hAdd #[x, x]
    InclusionM.run (families := #[`core, `real.dyadic]) do
      discard <| mkExprInclusionBody e
      unless (← get).iVars.size == 1 do
        throwError "Expected repeated expressions to share one inclusion variable"

run_meta
  let succeeded ← try
    discard <| InclusionM.run (families := #[`core, `real.dyadic]) do
      withLocalDeclD `i (mkConst ``Nat) fun i => do
        let e ← mkAppM ``unregisteredIndexedValue #[i]
        mkExprInclusionBody e
    pure true
  catch _ =>
    pure false
  if succeeded then
    throwError "A binder-dependent expression must not be used as an inclusion variable"

end Inclusion.Tests
