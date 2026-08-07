module

public meta import Mathlib.Tactic.Inclusion.Experimental.BenchmarkCommand
public meta import Mathlib.Tactic.Inclusion.Experimental.HighPrecisionExtensions

set_option linter.style.header false

@[expose] public section

open scoped BigOperators

namespace Inclusion.Experimental.HighPrecision.Tests

set_option inclusion.large.precision 112 in
#time_with_kernel theorem ramanujan_sato_30_digits :
    |(2 * Real.sqrt 2 / 9801 *
      ∑ k ∈ Finset.range 4, ramanujanSummand k) - 1 / Real.pi| <
        0.000000000000000000000000000001 := by
  inclusion

set_option inclusion.large.precision 112 in
#time_with_kernel theorem gaussian_integral_30_digits :
    |gaussianIntegral - 0.746824132812427025399467436132| <
      0.000000000000000000000000000001 := by
  inclusion

end Inclusion.Experimental.HighPrecision.Tests
