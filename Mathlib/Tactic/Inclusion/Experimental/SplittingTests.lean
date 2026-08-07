module

public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

namespace Inclusion.Experimental.Tests

def unitInterval : Interval Dyadic := ⟨1, 2⟩

example : (1 : ℝ) ≤ 2 := by
  inclusion [split := 4]

example {x : ℝ} (_hx : x ∈ unitInterval) : True := by
  fail_if_success
    have : x - x ≤ 1 / 2 := by
      inclusion
  trivial

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 2 := by
  inclusion [split := 1]

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ unitInterval) :
    (x - x) + (y - y) ≤ 1 := by
  inclusion [split := 1]

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 8 := by
  inclusion [split := 4]

end Inclusion.Experimental.Tests
