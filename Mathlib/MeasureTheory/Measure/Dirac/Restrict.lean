/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Restrictions to singletons and restrictions of Dirac measures

These results do not require measurable singletons or finiteness assumptions on measures.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {a : α} {s : Set α}

namespace Measure

@[simp]
theorem restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a := by
  ext1 s hs
  by_cases ha : a ∈ s
  · have : s ∩ {a} = {a} := by simpa
    simp [*]
  · have : s ∩ {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]

/-- Restricting a Dirac measure to a set containing its point leaves it unchanged. -/
theorem restrict_dirac_of_mem (ha : a ∈ s) : (dirac a).restrict s = dirac a := by
  ext t ht
  by_cases hat : a ∈ t
  · simp [restrict_apply ht, hat, ha]
  · rw [dirac_apply' _ ht, indicator_of_notMem hat, restrict_apply ht]
    exact measure_mono_null inter_subset_left (by simp [dirac_apply' _ ht, hat])

end Measure

open Measure

/-- A scaled Dirac measure is bounded by a measure exactly when its weight is bounded
by the mass of its singleton. -/
lemma smul_dirac_le_iff {c : ℝ≥0∞} {μ : Measure α} : c • dirac a ≤ μ ↔ c ≤ μ {a} := by
  refine ⟨fun h ↦ by simpa using h {a}, fun h ↦ ?_⟩
  grw [h, ← restrict_singleton]
  exact restrict_le_self

/-- Taking the infimum of measures takes the infimum of their singleton masses. -/
lemma Measure.inf_apply_singleton (μ ν : Measure α) (a : α) :
    (μ ⊓ ν) {a} = μ {a} ⊓ ν {a} := by
  apply le_antisymm (le_inf (measure_mono_left inf_le_left _) (measure_mono_left inf_le_right _))
  rw [← smul_dirac_le_iff, le_inf_iff]
  simp [smul_dirac_le_iff]

end MeasureTheory
