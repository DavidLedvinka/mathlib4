/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.Ball
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Init
import Mathlib.Tactic.Ring

/-!
# Initialization for the dyadic real ball extension family

This file initializes the `ball_dyadic_real` inclusion family and defines its inclusion and
hypothesis representations.
-/

@[expose] public section

namespace Inclusion

namespace BallDyadicReal

/-- Initialize the `ball_dyadic_real` inclusion family. -/
meta initialize ballDyadicRealFamily : InclusionFamily ←
  registerInclusionFamily `ball_dyadic_real

/-- Interpret a dyadic ball as the closed real interval determined by its center and radius. -/
def toSet (B : Ball Dyadic Dyadic) : Set ℝ :=
  {x | Dyadic.toReal B.lower ≤ x ∧ x ≤ Dyadic.toReal B.upper}

instance instToSetBallDyadicReal : ToSet (Ball Dyadic Dyadic) ℝ := ⟨toSet⟩

theorem mem_iff {x : ℝ} {B : Ball Dyadic Dyadic} :
    x ∈ B ↔ Dyadic.toReal B.lower ≤ x ∧ x ≤ Dyadic.toReal B.upper := Iff.rfl

/-- Interpret centered lower and upper bounds as a set of real numbers. -/
def centeredBoundsToSet (S : CenteredBounds Dyadic Dyadic) : Set ℝ :=
  {x | (match S.lower? with
      | none => True
      | some B => Dyadic.toReal B.lower ≤ x) ∧
    (match S.upper? with
      | none => True
      | some B => x ≤ Dyadic.toReal B.upper)}

instance instToSetCenteredBoundsDyadicReal : ToSet (CenteredBounds Dyadic Dyadic) ℝ :=
  ⟨centeredBoundsToSet⟩

theorem centeredBounds_mem_iff {x : ℝ} {S : CenteredBounds Dyadic Dyadic} :
    x ∈ S ↔ (match S.lower? with
      | none => True
      | some B => Dyadic.toReal B.lower ≤ x) ∧
    (match S.upper? with
      | none => True
      | some B => x ≤ Dyadic.toReal B.upper) := Iff.rfl

/-- The dyadic ball whose lower and upper endpoints are `a` and `b`. -/
def ofEndpoints (a b : Dyadic) : Ball Dyadic Dyadic :=
  let half := Dyadic.ofIntWithPrec 1 1
  ⟨(a + b) * half, (b - a) * half⟩

private theorem toReal_half : Dyadic.toReal (Dyadic.ofIntWithPrec 1 1) = (2 : ℝ)⁻¹ := by
  norm_num [Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

@[simp]
theorem lower_ofEndpoints (a b : Dyadic) :
    Dyadic.toReal (ofEndpoints a b).lower = Dyadic.toReal a := by
  simp [ofEndpoints, Ball.lower, toReal_half]
  ring

@[simp]
theorem upper_ofEndpoints (a b : Dyadic) :
    Dyadic.toReal (ofEndpoints a b).upper = Dyadic.toReal b := by
  simp [ofEndpoints, Ball.upper, toReal_half]
  ring

theorem mem_ofEndpoints {x : ℝ} {a b : Dyadic}
    (hx : x ∈ Interval.Icc (a : WithBot Dyadic) (b : WithTop Dyadic)) :
    x ∈ ofEndpoints a b := by
  change x ∈ (Interval.Icc (a : WithBot Dyadic) (b : WithTop Dyadic)).map Dyadic.toReal at hx
  rw [mem_iff, lower_ofEndpoints, upper_ofEndpoints]
  exact ⟨WithBot.coe_le_coe.mp hx.1, WithTop.coe_le_coe.mp hx.2⟩

/-- Round a dyadic number downward to `prec` binary fractional digits. -/
def roundDown (x : Dyadic) (prec : ℕ) : Dyadic := x.toRat.toDyadic prec

/-- Round a dyadic number upward to `prec` binary fractional digits. -/
def roundUp (x : Dyadic) (prec : ℕ) : Dyadic := -(-x).toRat.toDyadic prec

theorem roundDown_le (x : Dyadic) (prec : ℕ) : roundDown x prec ≤ x := by
  rw [← Dyadic.toReal_le_toReal, Dyadic.toReal, Dyadic.toReal, roundDown]
  exact Rat.cast_le.mpr Rat.toRat_toDyadic_le

theorem le_roundUp (x : Dyadic) (prec : ℕ) : x ≤ roundUp x prec := by
  rw [← Dyadic.toReal_le_toReal]
  change Dyadic.toReal x ≤ Dyadic.toReal (-roundDown (-x) prec)
  have h := Dyadic.toReal_le_toReal.mpr (roundDown_le (-x) prec)
  have h' : Dyadic.toReal (roundDown (-x) prec) ≤ -Dyadic.toReal x := by
    simpa only [Dyadic.toReal_neg] using h
  rw [Dyadic.toReal_neg]
  simpa using neg_le_neg h'

/-- Optionally round a ball center to the nearest value at the requested precision. -/
def roundCenter (x : Dyadic) : Option ℕ → Dyadic
  | none => x
  | some prec =>
    let lower := roundDown x prec
    let upper := lower + Dyadic.ofIntWithPrec 1 prec
    if x - lower ≤ upper - x then lower else upper

/-- Optionally round a ball radius upward to the requested precision. -/
def roundRadius (x : Dyadic) : Option ℕ → Dyadic
  | none => x
  | some prec => roundUp x prec

theorem le_roundRadius (x : Dyadic) (prec? : Option ℕ) : x ≤ roundRadius x prec? := by
  cases prec? <;> simp [roundRadius, le_roundUp]

/-- Construct a ball from a lower-bound ball and an upper-bound ball, optionally rounding its
center and radius independently. -/
def ofCenteredBounds (A B : Ball Dyadic Dyadic) (centerPrec? radiusPrec? : Option ℕ) :
    Ball Dyadic Dyadic :=
  let half := Dyadic.ofIntWithPrec 1 1
  let center := roundCenter ((A.lower + B.upper) * half) centerPrec?
  let radius := roundRadius (max (center - A.lower) (B.upper - center)) radiusPrec?
  ⟨center, radius⟩

/-- Convert centered lower and upper bounds to a ball when both bounds are present. -/
def centeredBoundsToBall? (centerPrec? radiusPrec? : Option ℕ) :
    CenteredBounds Dyadic Dyadic → Option (Ball Dyadic Dyadic)
  | ⟨some A, some B⟩ => some (ofCenteredBounds A B centerPrec? radiusPrec?)
  | _ => none

private theorem mem_ofCenteredBounds {x : ℝ} {A B : Ball Dyadic Dyadic}
    (centerPrec? radiusPrec? : Option ℕ) (hA : Dyadic.toReal A.lower ≤ x)
    (hB : x ≤ Dyadic.toReal B.upper) : x ∈ ofCenteredBounds A B centerPrec? radiusPrec? := by
  let center := roundCenter
    ((A.lower + B.upper) * Dyadic.ofIntWithPrec 1 1) centerPrec?
  let exactRadius := max (center - A.lower) (B.upper - center)
  let radius := roundRadius exactRadius radiusPrec?
  have hleft : center - A.lower ≤ radius :=
    (le_max_left _ _).trans (le_roundRadius exactRadius radiusPrec?)
  have hright : B.upper - center ≤ radius :=
    (le_max_right _ _).trans (le_roundRadius exactRadius radiusPrec?)
  rw [mem_iff]
  change Dyadic.toReal (center - radius) ≤ x ∧ x ≤ Dyadic.toReal (center + radius)
  rw [Dyadic.toReal_sub, Dyadic.toReal_add]
  rw [← Dyadic.toReal_le_toReal] at hleft hright
  simp only [Dyadic.toReal_sub] at hleft hright
  constructor
  · apply le_trans ?_ hA
    apply (sub_le_iff_le_add).2
    rw [add_comm]
    exact (sub_le_iff_le_add).1 hleft
  · apply hB.trans
    rw [add_comm]
    exact (sub_le_iff_le_add).1 hright

theorem centeredBounds_mem_combine {x : ℝ} {S T : CenteredBounds Dyadic Dyadic}
    (hS : x ∈ S) (hT : x ∈ T) : x ∈ S.combine T := by
  rcases S with ⟨lowerS, upperS⟩
  rcases T with ⟨lowerT, upperT⟩
  cases lowerS <;> cases upperS <;> cases lowerT <;> cases upperT <;>
    simp_all [ToSet.toSet, centeredBoundsToSet, CenteredBounds.combine]
  all_goals split_ifs <;> simp_all

/-- Accumulate the strongest centered lower and upper bounds and construct one final ball, with
independent optional precisions for its center and radius. -/
def hypothesisAccumulator (centerPrec? radiusPrec? : Option ℕ) :
    HypothesisAccumulator (CenteredBounds Dyadic Dyadic) (Ball Dyadic Dyadic) ℝ where
  empty := CenteredBounds.univ
  mem_empty := by simp [ToSet.toSet, centeredBoundsToSet, CenteredBounds.univ]
  combine := CenteredBounds.combine
  mem_combine := centeredBounds_mem_combine
  ofMain := CenteredBounds.ofBall
  mem_ofMain := by
    intro x B hx
    change Dyadic.toReal B.lower ≤ x ∧ x ≤ Dyadic.toReal B.upper
    exact mem_iff.mp hx
  toMain? := centeredBoundsToBall? centerPrec? radiusPrec?
  mem_toMain := by
    intro x S B hx h
    rcases S with ⟨lower?, upper?⟩
    cases lower? with
    | none => cases h
    | some A =>
      cases upper? with
      | none => cases h
      | some B' =>
        replace h := Option.some.inj h
        subst B
        rw [centeredBounds_mem_iff] at hx
        exact mem_ofCenteredBounds centerPrec? radiusPrec? hx.1 hx.2

end BallDyadicReal

end Inclusion
