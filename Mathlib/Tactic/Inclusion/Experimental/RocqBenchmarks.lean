module

public meta import Mathlib.Tactic.Inclusion.Experimental.BenchmarkCommand
public meta import Mathlib.Tactic.Inclusion.Experimental.RocqBenchmarkExtensions
public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

open IntervalArithmetic

namespace IntervalArithmetic.Inclusion.Experimental.RocqBenchmark

def mt25Domain : Interval Dyadic := ⟨0, 2⟩

/- The paper's MT25 benchmark, whose Rocq script uses plain interval bisection. -/
set_option inclusion.large.precision 30 in
#time_with_kernel theorem mt25 {x : ℝ} (hx : x ∈ mt25Domain) :
    12 - 14.2 * Real.exp (-0.318 * x) +
      (3.25 * Real.cos (1.16 * x) - 0.155 * Real.sin (1.16 * x)) *
        Real.exp (-1.34 * x) > 0 := by
  inclusion [split := 4]

end IntervalArithmetic.Inclusion.Experimental.RocqBenchmark
