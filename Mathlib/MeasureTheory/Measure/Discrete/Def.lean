/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Sum

/-!
# Discrete measures: definitions and algebra

`discreteMeasure p x` is the sum of the weighted Dirac measures at `x i`.
`IsDiscreteMeasure μ` asserts that `μ` has such a representation.
The coefficients may be infinite.

This file contains the definitions, the algebra of indexed discrete measures, and the
instances obtained directly from these representations.
-/

@[expose] public section

open Function Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory

open Measure

section DiscreteMeasure

variable {α ι κ : Type*} [MeasurableSpace α]
  {p q : ι → ℝ≥0∞} {x : ι → α}

/-- The sum of the Dirac measures at `x i`, with weights `p i`. -/
def discreteMeasure (p : ι → ℝ≥0∞) (x : ι → α) : Measure α :=
  sum fun i ↦ p i • dirac (x i)

lemma discreteMeasure_def (p : ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure p x = sum fun i ↦ p i • dirac (x i) := rfl

@[simp]
lemma discreteMeasure_univ (p : ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure p x univ = ∑' i, p i := by
  simp [discreteMeasure_def]

@[simp]
lemma discreteMeasure_zero (x : ι → α) : discreteMeasure 0 x = 0 := by
  simp [discreteMeasure_def]

@[simp]
lemma discreteMeasure_eq_zero_iff (x : ι → α) : discreteMeasure p x = 0 ↔ p = 0 := by
  simp [← measure_univ_eq_zero, discreteMeasure_univ, funext_iff]

lemma discreteMeasure_congr {y : ι → α} (h : ∀ i, p i ≠ 0 → x i = y i) :
    discreteMeasure p x = discreteMeasure p y := by
  simp only [discreteMeasure_def]
  congr with i
  by_cases hi : p i = 0
  · simp [hi]
  · simp [h i hi]

@[simp]
lemma discreteMeasure_single [DecidableEq ι] (i : ι) (c : ℝ≥0∞) (x : ι → α) :
    discreteMeasure (Pi.single i c) x = c • dirac (x i) := by
  ext s hs
  simp [discreteMeasure_def, hs, Pi.single_apply, apply_ite, ite_apply]

lemma discreteMeasure_add (p q : ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure (p + q) x = discreteMeasure p x + discreteMeasure q x := by
  ext s hs
  simp [discreteMeasure_def, hs, add_mul, tsum_add]

lemma discreteMeasure_smul (c : ℝ≥0∞) (p : ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure (c • p) x = c • discreteMeasure p x := by
  ext s hs
  simp [discreteMeasure_def, hs, mul_assoc, ENNReal.tsum_mul_left]

lemma discreteMeasure_sum (s : Finset κ) (p : κ → ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure (fun i ↦ ∑ j ∈ s, p j i) x = ∑ j ∈ s, discreteMeasure (p j) x := by
  ext t ht
  simp [discreteMeasure_def, ht, Finset.sum_mul, Summable.tsum_finsetSum]

lemma discreteMeasure_tsum (p : κ → ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure (fun i ↦ ∑' j, p j i) x = sum (fun j ↦ discreteMeasure (p j) x) := by
  ext s hs
  simp [discreteMeasure_def, hs, ← ENNReal.tsum_mul_right, tsum_comm (ι := ι)]

lemma discreteMeasure_mono (x : ι → α) (h : p ≤ q) : discreteMeasure p x ≤ discreteMeasure q x := by
  refine Measure.le_iff.mpr fun s hs ↦ ?_
  simp only [discreteMeasure_def, Measure.sum_apply _ hs, smul_apply, smul_eq_mul]
  exact tsum_le_tsum fun i ↦ mul_le_mul_left (h i) _

lemma discreteMeasure_eq_discreteMeasure_id (p : ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure p x = discreteMeasure (fun a ↦ ∑' i : x ⁻¹' {a}, p i) id := by
  ext s hs
  simp only [discreteMeasure_def, Measure.sum_apply _ hs, smul_apply, smul_eq_mul,
    ← ENNReal.tsum_mul_right, id_eq]
  rw [← tsum_fiberwise (fun i ↦ p i * dirac (x i) s) x]
  exact tsum_congr fun a ↦ tsum_congr fun i ↦ by rw [i.property]

lemma discreteMeasure_eq_sum_support (p : ι → ℝ≥0∞) (x : ι → α) :
    discreteMeasure p x = sum (fun i : support p ↦ p i • dirac (x i)) := by
  ext s hs
  simp only [discreteMeasure_def, Measure.sum_apply _ hs, smul_apply, smul_eq_mul]
  exact (tsum_subtype_eq_of_support_subset
    (support_mul_subset_left p (fun i ↦ dirac (x i) s))).symm

end DiscreteMeasure

/-- A measure that can be written as a sum of scaled Dirac measures. -/
class IsDiscreteMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop where
  exists_eq_discreteMeasure : ∃ p : α → ℝ≥0∞, μ = discreteMeasure p id

namespace IsDiscreteMeasure

variable {α ι : Type*} [MeasurableSpace α] {μ ν : Measure α}

instance discreteMeasure (p : ι → ℝ≥0∞) (x : ι → α) :
    IsDiscreteMeasure (discreteMeasure p x) :=
  ⟨⟨_, discreteMeasure_eq_discreteMeasure_id p x⟩⟩

instance zero : IsDiscreteMeasure (0 : Measure α) :=
  ⟨⟨0, (discreteMeasure_zero id).symm⟩⟩

instance dirac (x : α) : IsDiscreteMeasure (Measure.dirac x) := by
  classical
  exact ⟨⟨Pi.single x 1, by simp⟩⟩

instance add [IsDiscreteMeasure μ] [IsDiscreteMeasure ν] : IsDiscreteMeasure (μ + ν) := by
  obtain ⟨p, rfl⟩ := exists_eq_discreteMeasure (μ := μ)
  obtain ⟨q, rfl⟩ := exists_eq_discreteMeasure (μ := ν)
  exact ⟨⟨p + q, (discreteMeasure_add p q id).symm⟩⟩

instance smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) [IsDiscreteMeasure μ] : IsDiscreteMeasure (c • μ) := by
  obtain ⟨p, rfl⟩ := exists_eq_discreteMeasure (μ := μ)
  refine ⟨⟨(c • (1 : ℝ≥0∞)) • p, ?_⟩⟩
  rw [discreteMeasure_smul, smul_one_smul]

instance sum (μ : ι → Measure α) [∀ i, IsDiscreteMeasure (μ i)] :
    IsDiscreteMeasure (Measure.sum μ) := by
  choose p hp using fun i ↦ exists_eq_discreteMeasure (μ := μ i)
  exact ⟨⟨_, (congrArg Measure.sum (funext hp)).trans (discreteMeasure_tsum p id).symm⟩⟩

instance finsetSum (s : Finset ι) (μ : ι → Measure α) [∀ i : s, IsDiscreteMeasure (μ i)] :
    IsDiscreteMeasure (∑ i ∈ s, μ i) := by
  rw [← Measure.sum_coe_finset]
  infer_instance

end IsDiscreteMeasure

end MeasureTheory
