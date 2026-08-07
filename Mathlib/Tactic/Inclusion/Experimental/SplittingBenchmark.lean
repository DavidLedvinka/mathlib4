module

public meta import Mathlib.Tactic.Inclusion.Experimental.BenchmarkCommand
public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

namespace Inclusion.Experimental.SplittingBenchmark

def unitInterval : Interval Dyadic := ⟨1, 2⟩

#time_with_kernel theorem one_variable_64_pieces {x : ℝ} (hx : x ∈ unitInterval) :
    x - x ≤ 1 / 64 := by
  inclusion [split := 6]

#time_with_kernel theorem two_variables_4096_boxes {x y : ℝ}
    (hx : x ∈ unitInterval) (hy : y ∈ unitInterval) :
    (x - x) + (y - y) ≤ 1 / 32 := by
  inclusion [split := 6]

end Inclusion.Experimental.SplittingBenchmark
