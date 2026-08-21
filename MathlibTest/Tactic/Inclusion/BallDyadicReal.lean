/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Extension.BallDyadicReal.Extensions
import Mathlib.Tactic.Inclusion.Extension.Core.Core

open Inclusion

namespace Inclusion.Tests

def wideBall : Ball Dyadic Dyadic := ⟨2, 2⟩
def unitInterval : Interval Dyadic := ⟨0, 1⟩

macro:max "quad(" x:term ")" : term => `(($x + $x) + ($x + $x))

section Basic

example : (1 : ℝ) + 2 ≤ 3 := by
  inclusion [core, ball_dyadic_real]

example : -(2 : ℝ) ≤ -1 := by
  inclusion [core, ball_dyadic_real]

example : (3 : ℝ) - 1 = 2 := by
  inclusion [core, ball_dyadic_real]

example : (((1 : ℚ) / 3 : ℚ) : ℝ) < (((334 : ℚ) / 1000 : ℚ) : ℝ) := by
  inclusion [core, ball_dyadic_real, prec := 12]

example : (0.12345678901234567890123456789 : ℝ) < 0.1234567890123456789012345679 := by
  inclusion [core, ball_dyadic_real, prec := 100]

end Basic

section Hypotheses

example :
    (CenteredBounds.combine
      (CenteredBounds.lower (Ball.singleton (R := Dyadic) (1 : Dyadic)))
      (CenteredBounds.lower (Ball.singleton (R := Dyadic) (2 : Dyadic)))).lower?.map
        (fun B => B.center) = some 2 := by
  native_decide

example :
    (BallDyadicReal.centeredBoundsToBall? (some 1) (some 1)
      (CenteredBounds.between
        (Ball.singleton (R := Dyadic) (0 : Dyadic))
        (Ball.singleton (R := Dyadic) (Dyadic.ofIntWithPrec 3 2)))).map
      (fun B => (B.center, B.radius)) =
        some (Dyadic.ofIntWithPrec 1 1, Dyadic.ofIntWithPrec 1 1) := by
  native_decide

example {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ 4) : x + x ≤ 8 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Icc 0 4) : x - x ≤ 4 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hx : x ∈ wideBall) : x + 1 ≤ 5 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hx : x ∈ unitInterval) : x + x ≤ 2 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hl : x ∈ Interval.Ici (0 : WithBot Dyadic))
    (hu : x ∈ Interval.Iic (4 : WithTop Dyadic)) : x + x ≤ 8 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hx : x = 2) : x + x ≤ 4 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 4) : x + x ≤ 8 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hl : 0 < x) (hu : x < 4) : x ∈ Set.Icc 0 4 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (h₀ : 0 ≤ x) (h₁ : 1 ≤ x) (h₃ : x ≤ 3) (h₄ : x ≤ 4) :
    x ∈ Set.Icc 1 3 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (hl : (((1 : ℚ) / 3 : ℚ) : ℝ) ≤ x)
    (hu : x ≤ (((7 : ℚ) / 5 : ℚ) : ℝ)) :
    x + x ≤ 4 := by
  inclusion [core, ball_dyadic_real, prec := 40, centerPrec := 2, radiusPrec := 3]

example {x : ℝ} (_hu : x ≤ 4) : True := by
  fail_if_success
    have : x ≤ 4 := by
      inclusion [core, ball_dyadic_real]
  trivial

end Hypotheses

section Performance

example {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ 4) :
    quad(quad(quad(x))) ≤ 256 := by
  inclusion [core, ball_dyadic_real]

example {x : ℝ} (h₀ : 0 ≤ x) (hl : (((1 : ℚ) / 3 : ℚ) : ℝ) ≤ x)
    (hu : x ≤ (((7 : ℚ) / 5 : ℚ) : ℝ)) (h₂ : x ≤ 2) :
    quad(quad(quad(quad(x)))) ≤ 359 := by
  inclusion [core, ball_dyadic_real, prec := 64, centerPrec := 32, radiusPrec := 20]

example :
    quad(quad((0.12345678901234567890123456789 : ℝ))) < 2 := by
  inclusion [core, ball_dyadic_real, prec := 110]

example {a b c d e f g h : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1)
    (he : e ∈ Set.Icc 0 1) (hf : f ∈ Set.Icc 0 1)
    (hg : g ∈ Set.Icc 0 1) (hh : h ∈ Set.Icc 0 1) :
    ((a + b) + (c + d)) + ((e + f) + (g + h)) ≤ 8 := by
  inclusion [core, ball_dyadic_real]

end Performance

end Inclusion.Tests
