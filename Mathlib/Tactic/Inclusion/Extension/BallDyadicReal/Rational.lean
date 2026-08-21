/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.BallDyadicReal.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Rational constants for ball_dyadic_real

This file defines dyadic-ball enclosures of rational casts and scientific literals for the
`ball_dyadic_real` inclusion family.
-/

@[expose] public section

namespace Inclusion

namespace BallDyadicReal

/-- Enclose a rational number in a dyadic ball with precision `prec`. -/
def ratBall (q : ℚ) (prec : ℕ) : Ball Dyadic Dyadic :=
  match IntervalDyadicReal.ratInterval q prec with
  | ⟨some a, some b⟩ => ofEndpoints a b
  | _ => Ball.singleton 0

/-- Enclose a scientific literal in a dyadic ball with precision `prec`. -/
def scientificBall (m : ℕ) (s : Bool) (e prec : ℕ) : Ball Dyadic Dyadic :=
  match IntervalDyadicReal.scientificInterval m s e prec with
  | ⟨some a, some b⟩ => ofEndpoints a b
  | _ => Ball.singleton 0

@[inclusionOp ball_dyadic_real]
theorem ratCast_mem (q : ℚ) (prec : ℕ) : (q : ℝ) ∈ ratBall q prec := by
  simpa [ratBall, IntervalDyadicReal.ratInterval, Interval.Icc] using
    mem_ofEndpoints (IntervalDyadicReal.ratCast_mem q prec)

@[inclusionOp ball_dyadic_real]
theorem scientific_mem (m : ℕ) (s : Bool) (e prec : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e) ∈ scientificBall m s e prec := by
  cases s with
  | false =>
    simpa [scientificBall, IntervalDyadicReal.scientificInterval,
      IntervalDyadicReal.divNatInterval, Interval.singleton, Interval.Icc] using
      mem_ofEndpoints (IntervalDyadicReal.scientific_mem m false e prec)
  | true =>
    simpa [scientificBall, IntervalDyadicReal.scientificInterval,
      IntervalDyadicReal.divNatInterval, Interval.singleton, Interval.Icc] using
      mem_ofEndpoints (IntervalDyadicReal.scientific_mem m true e prec)

end BallDyadicReal

end Inclusion
