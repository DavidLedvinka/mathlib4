/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Extension.Core.Function
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic

/-!
# Pointwise dyadic interval bounds for real-valued functions

Explicit nondependent lambdas recurse through the usual arithmetic extensions. Other functions
are treated atomically and bounded using quantified or point-specific hypotheses. Index types
and indices occurring in the resulting computation must be closed and computational; for
example, natural numbers and `Fin n` for a fixed numeral `n` are supported.

This does not add sums or products, or the function-refinement cleanup optimization.
-/

public meta section

open Lean Qq

namespace Inclusion.IntervalDyadicReal

/-- Use pointwise dyadic intervals for nondependent real-valued functions. -/
@[inclusion_ext _]
def realFunction : InclusionExt :=
  mkFunctionExt `interval_dyadic_real
    ⟨q(ℝ), q(Interval Dyadic), q(instToSetIntervalDyadicReal)⟩

end Inclusion.IntervalDyadicReal
