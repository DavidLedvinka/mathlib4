/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.Probability.Kernel.Irreducible

/-!
# Resolvent kernel

This file defines the resolvent kernel of a kernel and its basic API.

## Main definitions

* `ProbabilityTheory.Kernel.resolvent`: for a kernel `κ : Kernel E E` and `q : ℝ≥0∞`,
  the kernel `κ.resolvent q = ∑ n, qⁿ • κⁿ`.

## Main statements

* `ProbabilityTheory.Kernel.isIrreducible_iff_absolutelyContinuous_resolvent`: for `q ≠ 0`,
  `IsIrreducible φ κ` is equivalent to `∀ x, φ ≪ κ.resolvent q x`.

## References

* [Meyn, S.P. and Tweedie, R.L., *Markov Chains and Stochastic Stability*][meyntweedie1993]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {E : Type*} [MeasurableSpace E]

/-- `resolvent κ q` is the kernel defined by `∑ n, qⁿ • κⁿ`. -/
noncomputable def resolvent (κ : Kernel E E) (q : ℝ≥0∞) : Kernel E E :=
  Kernel.sum (fun n : ℕ ↦ q ^ n • κ ^ n)

variable (κ : Kernel E E) (q : ℝ≥0∞)

lemma resolvent_def :
    resolvent κ q = Kernel.sum (fun n : ℕ ↦ q ^ n • κ ^ n) := rfl

lemma resolvent_apply (x : E) :
    κ.resolvent q x = Measure.sum (fun n : ℕ ↦ q ^ n • (κ ^ n) x) := rfl

lemma resolvent_apply' (x : E) (s : Set E) :
    κ.resolvent q x s = ∑' n : ℕ, q ^ n * (κ ^ n) x s := by
  simp [resolvent_apply, Measure.sum_apply_of_countable]

@[simp]
lemma resolvent_apply_univ [IsMarkovKernel κ] (x : E) :
    κ.resolvent q x .univ = (1 - q)⁻¹ := by
  simp [resolvent_apply' _ _ _ .univ]

lemma lintegral_resolvent (x : E) (f : E → ℝ≥0∞) :
    ∫⁻ y, f y ∂κ.resolvent q x = ∑' n : ℕ, q ^ n * ∫⁻ y, f y ∂(κ ^ n) x := by
  simp [resolvent_apply]

@[simp]
lemma resolvent_zero : κ.resolvent 0 = Kernel.id := by
  ext x s hs
  simp [resolvent_apply' _ _ _ s, zero_pow_eq, one_eq_id]

@[simp]
lemma resolvent_id : (Kernel.id : Kernel E E).resolvent q = (1 - q)⁻¹ • Kernel.id := by
  simp [resolvent_def, ← one_eq_id, sum_smul, ENNReal.tsum_geometric]

lemma resolvent_mono {q r : ℝ≥0∞} (hqr : q ≤ r) : κ.resolvent q ≤ κ.resolvent r := by
  intro x
  refine Measure.le_iff'.mpr fun s ↦ ?_
  simp only [resolvent_apply' _ _ _ s]
  refine tsum_le_tsum fun n ↦ ?_
  gcongr

lemma resolvent_apply_eq_zero_iff {q : ℝ≥0∞} (hq : q ≠ 0) (x : E) (s : Set E) :
    κ.resolvent q x s = 0 ↔ ∀ n : ℕ, (κ ^ n) x s = 0 := by
  simp [resolvent_apply' _ _ _ s, tsum_eq_zero_iff, hq]

lemma resolvent_apply_pos_iff {q : ℝ≥0∞} (hq : q ≠ 0) (x : E) (s : Set E) :
    0 < κ.resolvent q x s ↔ ∃ n : ℕ, 0 < (κ ^ n) x s := by
  simp [pos_iff_ne_zero, resolvent_apply_eq_zero_iff κ hq x s]

theorem absolutelyContinuous_resolvent_of_isIrreducible (φ : Measure E) [IsIrreducible φ κ]
    {q : ℝ≥0∞} (hq : q ≠ 0) (x : E) : φ ≪ κ.resolvent q x := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h ↦ ?_
  rw [resolvent_apply_eq_zero_iff _ hq _ s] at h
  contrapose! h
  simp only [← pos_iff_ne_zero] at h ⊢
  exact IsIrreducible.irreducible hs h _

theorem isIrreducible_of_absolutelyContinuous_resolvent {κ : Kernel E E}
    (φ : Measure E) {q : ℝ≥0∞} (hq : q ≠ 0) (h : ∀ x, φ ≪ κ.resolvent q x) :
    IsIrreducible φ κ where
  irreducible s hs hφs x := by
    simp [← resolvent_apply_pos_iff κ hq x s, (h x).pos_mono hφs]

theorem isIrreducible_iff_absolutelyContinuous_resolvent (φ : Measure E)
    {q : ℝ≥0∞} (hq : q ≠ 0) :
    IsIrreducible φ κ ↔ ∀ x, φ ≪ κ.resolvent q x :=
  ⟨fun _ ↦ absolutelyContinuous_resolvent_of_isIrreducible κ φ hq,
    isIrreducible_of_absolutelyContinuous_resolvent φ hq⟩

end ProbabilityTheory.Kernel
