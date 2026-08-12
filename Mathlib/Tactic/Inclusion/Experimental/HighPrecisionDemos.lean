module

public meta import Mathlib.Tactic.Inclusion.Experimental.HighPrecisionExtensions

set_option linter.style.header false

@[expose] public section

open Real
open scoped BigOperators Nat Real

namespace Inclusion.Experimental.HighPrecision.Demos

set_option inclusion.large.precision 112 in
theorem ramanujan_sato_30_digits :
    |(2 * √2 / 9801 *
      ∑ k ∈ Finset.range 4,
        ((((4 * k)! * (1103 + 26390 * k) : ℕ) : ℝ) /
          (((k)! ^ 4 * 396 ^ (4 * k) : ℕ) : ℝ))) - 1 / π| <
      (10 : ℝ) ^ (-30 : ℤ) := by
  inclusion [core, real.dyadic]

set_option inclusion.large.precision 112 in
theorem gaussian_integral_30_digits :
    |(∫ x in (0 : ℝ)..1, Real.exp (-(x ^ 2))) -
      0.746824132812427025399467436132| < (10 : ℝ) ^ (-30 : ℤ) := by
  inclusion [core, real.dyadic]

end Inclusion.Experimental.HighPrecision.Demos
