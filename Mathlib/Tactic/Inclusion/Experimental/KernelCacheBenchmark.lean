module

public meta import Mathlib.Tactic.Inclusion.Experimental.BenchmarkCommand
public meta import Mathlib.Tactic.Inclusion.Experimental.LargeExtensions
public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

namespace Inclusion.Experimental.KernelCacheBenchmark

def domain : Interval Dyadic := ⟨1, 2⟩

set_option inclusion.large.precision 30 in
#time_with_kernel theorem expensive_x_16_pieces {x : ℝ} (hx : x ∈ domain) :
    Real.exp (x + x) - Real.exp (x + x) < 100 := by
  inclusion [split := 4]

#time_with_kernel theorem simple_256_boxes {x y : ℝ}
    (hx : x ∈ domain) (hy : y ∈ domain) :
    (x - x) + (y - y) < 100 := by
  inclusion [split := 4]

set_option inclusion.large.precision 30 in
#time_with_kernel theorem separable_exp_256_boxes {x y : ℝ}
    (hx : x ∈ domain) (hy : y ∈ domain) :
    (Real.exp (x + x) - Real.exp (x + x)) + (y - y) < 100 := by
  inclusion [split := 4]

set_option inclusion.large.precision 30 in
#time_with_kernel theorem coupled_exp_256_boxes {x y : ℝ}
    (hx : x ∈ domain) (hy : y ∈ domain) :
    (Real.exp (x + y) - Real.exp (x + y)) + (x - y) < 100 := by
  inclusion [split := 4]

end Inclusion.Experimental.KernelCacheBenchmark
