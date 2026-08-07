module

public meta import Mathlib.Tactic.Inclusion.Experimental.BenchmarkCommand
public meta import Mathlib.Tactic.Inclusion.Experimental.LargeExtensions
public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

namespace Inclusion.Experimental.ExpSplittingBenchmark

def expInputInterval : Interval Dyadic :=
  ⟨1, 1 + Dyadic.ofIntWithPrec 1 96⟩

def expSingleBoxInterval : Interval Dyadic :=
  ⟨1, 1 + Dyadic.ofIntWithPrec 1 102⟩

set_option inclusion.large.precision 120 in
#time_with_kernel theorem exp_dependency_30_digits_one_box {x : ℝ}
    (hx : x ∈ expSingleBoxInterval) :
    Real.exp x - Real.exp x ≤ 0.000000000000000000000000000001 := by
  inclusion [split := 0]

set_option inclusion.large.precision 120 in
example {x : ℝ} (_hx : x ∈ expInputInterval) : True := by
  fail_if_success
    have : Real.exp x - Real.exp x ≤ 0.000000000000000000000000000001 := by
      inclusion [split := 5]
  trivial

set_option inclusion.large.precision 120 in
#time_with_kernel theorem exp_dependency_30_digits {x : ℝ} (hx : x ∈ expInputInterval) :
    Real.exp x - Real.exp x ≤ 0.000000000000000000000000000001 := by
  inclusion [split := 6]

end Inclusion.Experimental.ExpSplittingBenchmark
