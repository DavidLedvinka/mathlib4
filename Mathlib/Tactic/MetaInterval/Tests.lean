module

public import Mathlib.Tactic.MetaInterval.Extensions
public meta import Mathlib.Tactic.MetaInterval.Extensions

set_option linter.style.header false

@[expose] public section

open IntervalArithmetic

namespace IntervalArithmetic.MetaInterval.Tests

def unitInterval : Interval Dyadic := ⟨1, 2⟩

def positiveInterval : Interval Dyadic := ⟨3, 4⟩

def negativeInterval : Interval Dyadic := ⟨some (-4), some (-2)⟩

def zeroInterval : Interval Dyadic := ⟨some (-1), 1⟩

example : (1 : ℝ) + 2 ≤ 4 := by
  meta_interval

example : (1 : ℝ) / 3 ≤ 334 / 1000 := by
  meta_interval

example {x y : ℝ} (hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (hy : y ∈ (positiveInterval.map Dyadic.toReal).toSet) : x + y ≤ 6 := by
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

example {x y : ℝ} (_hx : x ∈ (unitInterval.map Dyadic.toReal).toSet)
    (_hy : y ∈ (zeroInterval.map Dyadic.toReal).toSet) : True := by
  fail_if_success
    have : x / y ≤ 10 := by
      meta_interval
  trivial

end IntervalArithmetic.MetaInterval.Tests
