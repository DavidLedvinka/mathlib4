/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Integrals with a measure derived from probability mass functions.

This file connects `PMF` with `integral`. The main result is that the integral (i.e. the expected
value) with regard to a measure derived from a `PMF` is a sum weighted by the `PMF`.

It also provides the expected value for specific probability mass functions.
-/

public section

namespace PMF

open MeasureTheory NNReal ENNReal TopologicalSpace

section General

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_eq_tsum (p : PMF α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a := by
  rw [MeasureTheory.integral_eq_tsum hf]
  simp [measureReal_def, p.toMeasure_apply_singleton _ (measurableSet_singleton _)]

theorem integral_eq_sum [Fintype α] (p : PMF α) (f : α → E) :
    ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a := by
  simp [p.integral_eq_tsum f .of_finite]

end General

end PMF
