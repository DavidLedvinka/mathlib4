module

public import Mathlib.Tactic.Inclusion.Experimental.ComplexBallExtensions
public meta import Mathlib.Tactic.Inclusion.Experimental.ComplexBallExtensions

set_option linter.style.header false

@[expose] public section

namespace Inclusion.ComplexBall.Tests

def unitBall : Ball := ⟨GaussianDyadic.zero, 1⟩

def denominatorBall : Ball :=
  ⟨GaussianDyadic.ofNat 2, Dyadic.ofIntWithPrec 1 1⟩

example {z : ℂ} (hz : z ∈ unitBall) : ‖z + 1‖ ≤ 2 := by
  inclusion [core, real.dyadic, complex.ball]

example {z w : ℂ} (hz : z ∈ unitBall) (hw : w ∈ unitBall) :
    ‖z * w‖ ≤ 1 := by
  inclusion [core, real.dyadic, complex.ball]

example {z : ℂ} (hz : z ∈ unitBall) :
    ‖(z + 1) * (z - 1)‖ ≤ 4 := by
  inclusion [core, real.dyadic, complex.ball]

example {z w : ℂ} (hz : z ∈ unitBall) (hw : w ∈ denominatorBall) :
    ‖z / w‖ ≤ 1 := by
  inclusion [core, real.dyadic, complex.ball]

example {z : ℂ} (hz : z = 1 + Complex.I) : ‖z * z‖ ≤ 2 := by
  inclusion [core, real.dyadic, complex.ball]

example {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : ‖z‖ ≤ 1 := by
  inclusion [core, real.dyadic, complex.ball]

example {z : ℂ} (hz : z ∈ Metric.closedBall ((1 : ℂ) + Complex.I) 1) :
    ‖z - (1 + Complex.I)‖ ≤ 1 := by
  inclusion [core, real.dyadic, complex.ball]

example {z : ℂ} (hzLarge : z ∈ Metric.closedBall (0 : ℂ) 2)
    (hzSmall : z ∈ Metric.closedBall (0 : ℂ) 1) : ‖z‖ ≤ 1 := by
  inclusion [core, real.dyadic, complex.ball]

end Inclusion.ComplexBall.Tests
