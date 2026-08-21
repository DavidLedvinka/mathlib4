/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.BallDyadicReal.Basic

/-!
# Hypothesis operations for dyadic real balls

This file defines the hypothesis extensions for the `ball_dyadic_real` inclusion family.
-/

@[expose] public section

namespace Inclusion

namespace BallDyadicReal

/-- Convert the finite endpoints of a dyadic interval to centered bounds. -/
def centeredBoundsOfInterval (I : Interval Dyadic) : CenteredBounds Dyadic Dyadic where
  lower? := match I.lb with
    | none => none
    | some a => some (Ball.singleton a)
  upper? := match I.ub with
    | none => none
    | some b => some (Ball.singleton b)

theorem mem_centeredBoundsOfInterval {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) :
    x ∈ centeredBoundsOfInterval I := by
  rcases I with ⟨lb, ub⟩
  change x ∈ (Interval.mk lb ub).map Dyadic.toReal at hx
  rw [centeredBounds_mem_iff]
  constructor
  · cases lb with
    | bot => trivial
    | coe a =>
      simpa [centeredBoundsOfInterval, Ball.singleton, Ball.lower] using
        WithBot.coe_le_coe.mp hx.1
  · cases ub with
    | top => trivial
    | coe b =>
      simpa [centeredBoundsOfInterval, Ball.singleton, Ball.upper] using
        WithTop.coe_le_coe.mp hx.2

@[hypothesisOp ball_dyadic_real]
theorem upper_mem_of_le {x y : ℝ} {B : Ball Dyadic Dyadic} (hxy : x ≤ y) (hy : y ∈ B) :
    x ∈ CenteredBounds.upper B := by
  change True ∧ x ≤ Dyadic.toReal B.upper
  exact ⟨trivial, hxy.trans (mem_iff.mp hy).2⟩

@[hypothesisOp ball_dyadic_real]
theorem lower_mem_of_le {x y : ℝ} {B : Ball Dyadic Dyadic} (hxy : x ≤ y) (hx : x ∈ B) :
    y ∈ CenteredBounds.lower B := by
  change Dyadic.toReal B.lower ≤ y ∧ True
  exact ⟨(mem_iff.mp hx).1.trans hxy, trivial⟩

@[hypothesisOp ball_dyadic_real]
theorem upper_mem_of_lt {x y : ℝ} {B : Ball Dyadic Dyadic} (hxy : x < y) (hy : y ∈ B) :
    x ∈ CenteredBounds.upper B :=
  upper_mem_of_le hxy.le hy

@[hypothesisOp ball_dyadic_real]
theorem lower_mem_of_lt {x y : ℝ} {B : Ball Dyadic Dyadic} (hxy : x < y) (hx : x ∈ B) :
    y ∈ CenteredBounds.lower B :=
  lower_mem_of_le hxy.le hx

@[hypothesisOp ball_dyadic_real]
theorem lower_mem_of_mem_Ici {a x : ℝ} {B : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Ici a) (ha : a ∈ B) :
    x ∈ CenteredBounds.lower B :=
  lower_mem_of_le hx (x := a) ha

@[hypothesisOp ball_dyadic_real]
theorem lower_mem_of_mem_Ioi {a x : ℝ} {B : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Ioi a) (ha : a ∈ B) :
    x ∈ CenteredBounds.lower B :=
  lower_mem_of_lt hx (x := a) ha

@[hypothesisOp ball_dyadic_real]
theorem upper_mem_of_mem_Iic {b x : ℝ} {B : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Iic b) (hb : b ∈ B) :
    x ∈ CenteredBounds.upper B :=
  upper_mem_of_le hx hb

@[hypothesisOp ball_dyadic_real]
theorem upper_mem_of_mem_Iio {b x : ℝ} {B : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Iio b) (hb : b ∈ B) :
    x ∈ CenteredBounds.upper B :=
  upper_mem_of_lt hx hb

@[hypothesisOp ball_dyadic_real]
theorem between_mem_of_mem_Ico {a b x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Ico a b) (ha : a ∈ B₁) (hb : b ∈ B₂) :
    x ∈ CenteredBounds.between B₁ B₂ := by
  change Dyadic.toReal B₁.lower ≤ x ∧ x ≤ Dyadic.toReal B₂.upper
  exact ⟨(mem_iff.mp ha).1.trans hx.1, hx.2.le.trans (mem_iff.mp hb).2⟩

@[hypothesisOp ball_dyadic_real]
theorem between_mem_of_mem_Ioc {a b x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Ioc a b) (ha : a ∈ B₁) (hb : b ∈ B₂) :
    x ∈ CenteredBounds.between B₁ B₂ := by
  change Dyadic.toReal B₁.lower ≤ x ∧ x ≤ Dyadic.toReal B₂.upper
  exact ⟨(mem_iff.mp ha).1.trans hx.1.le, hx.2.trans (mem_iff.mp hb).2⟩

@[hypothesisOp ball_dyadic_real]
theorem between_mem_of_mem_Icc {a b x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Icc a b) (ha : a ∈ B₁) (hb : b ∈ B₂) :
    x ∈ CenteredBounds.between B₁ B₂ := by
  change Dyadic.toReal B₁.lower ≤ x ∧ x ≤ Dyadic.toReal B₂.upper
  exact ⟨(mem_iff.mp ha).1.trans hx.1, hx.2.trans (mem_iff.mp hb).2⟩

@[hypothesisOp ball_dyadic_real]
theorem between_mem_of_mem_Ioo {a b x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ Set.Ioo a b) (ha : a ∈ B₁) (hb : b ∈ B₂) :
    x ∈ CenteredBounds.between B₁ B₂ := by
  change Dyadic.toReal B₁.lower ≤ x ∧ x ≤ Dyadic.toReal B₂.upper
  exact ⟨(mem_iff.mp ha).1.trans hx.1.le, hx.2.le.trans (mem_iff.mp hb).2⟩

end BallDyadicReal

end Inclusion
