/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Core.ToSet

/-!
# Balls

This file defines a computational ball with potentially different types for its center and radius.
-/

@[expose] public section

namespace Inclusion

/-- A ball represented by a center of type `C` and a radius of type `R`. -/
structure Ball (C R : Type*) where
  /-- The center of the ball. -/
  center : C
  /-- The radius of the ball. -/
  radius : R
  deriving Inhabited

/-- A pair of optional bounds which retains the centered representation supplying each endpoint.
`lower? = some B` represents the lower bound `B.lower`, while `upper? = some B` represents the
upper bound `B.upper`. -/
structure CenteredBounds (C R : Type*) where
  /-- The centered interval supplying the lower bound, if one is known. -/
  lower? : Option (Ball C R)
  /-- The centered interval supplying the upper bound, if one is known. -/
  upper? : Option (Ball C R)
  deriving Inhabited

variable {C R : Type*}

/-- The ball of radius zero centered at `c`. -/
def Ball.singleton [Zero R] (c : C) : Ball C R := ⟨c, 0⟩

/-- The lower endpoint of a ball in an ordered one-dimensional space. -/
def Ball.lower [HSub C R C] (B : Ball C R) : C := B.center - B.radius

/-- The upper endpoint of a ball in an ordered one-dimensional space. -/
def Ball.upper [HAdd C R C] (B : Ball C R) : C := B.center + B.radius

/-- Centered bounds with neither a lower nor an upper bound. -/
def CenteredBounds.univ : CenteredBounds C R := ⟨none, none⟩

/-- The lower bound supplied by `B`. -/
def CenteredBounds.lower (B : Ball C R) : CenteredBounds C R := ⟨some B, none⟩

/-- The upper bound supplied by `B`. -/
def CenteredBounds.upper (B : Ball C R) : CenteredBounds C R := ⟨none, some B⟩

/-- The lower and upper bounds supplied by `B`. -/
def CenteredBounds.ofBall (B : Ball C R) : CenteredBounds C R := ⟨some B, some B⟩

/-- The lower bound supplied by `A` and the upper bound supplied by `B`. -/
def CenteredBounds.between (A B : Ball C R) : CenteredBounds C R := ⟨some A, some B⟩

/-- Combine centered bounds by retaining the ball with the largest lower endpoint and the ball
with the smallest upper endpoint. -/
def CenteredBounds.combine [HSub C R C] [HAdd C R C] [LE C] [DecidableLE C]
    (A B : CenteredBounds C R) : CenteredBounds C R where
  lower? := match A.lower?, B.lower? with
    | none, lower? | lower?, none => lower?
    | some A, some B => some <| if A.lower ≤ B.lower then B else A
  upper? := match A.upper?, B.upper? with
    | none, upper? | upper?, none => upper?
    | some A, some B => some <| if A.upper ≤ B.upper then A else B

/-- Add two balls by adding their centers and radii. -/
def Ball.add [Add C] [Add R] (B₁ B₂ : Ball C R) : Ball C R :=
  ⟨B₁.center + B₂.center, B₁.radius + B₂.radius⟩

/-- Negate a ball by negating its center. -/
def Ball.neg [Neg C] (B : Ball C R) : Ball C R := ⟨-B.center, B.radius⟩

/-- Subtract two balls by subtracting their centers and adding their radii. -/
def Ball.sub [Sub C] [Add R] (B₁ B₂ : Ball C R) : Ball C R :=
  ⟨B₁.center - B₂.center, B₁.radius + B₂.radius⟩

/-- Check `x ≤ y` for `x` and `y` in one-dimensional balls. -/
def Ball.le [HSub C R C] [HAdd C R C] [LE C] [DecidableLE C]
    (B₁ B₂ : Ball C R) : IntervalBool :=
  if B₁.upper ≤ B₂.lower then .true
  else if B₁.lower ≤ B₂.upper then .undetermined else .false

/-- Check `x < y` for `x` and `y` in one-dimensional balls. -/
def Ball.lt [HSub C R C] [HAdd C R C] [LT C] [DecidableLT C]
    (B₁ B₂ : Ball C R) : IntervalBool :=
  if B₁.upper < B₂.lower then .true
  else if B₁.lower < B₂.upper then .undetermined else .false

/-- Check equality by checking both inequalities between two balls. -/
def Ball.eq [HSub C R C] [HAdd C R C] [LE C] [DecidableLE C]
    (B₁ B₂ : Ball C R) : IntervalBool :=
  (B₁.le B₂).and (B₂.le B₁)

end Inclusion
