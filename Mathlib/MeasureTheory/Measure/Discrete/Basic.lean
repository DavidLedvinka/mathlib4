/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Discrete.Def

/-!
# Basic properties of discrete measures

Every measure on a countable space is discrete, without any measurability assumption on
singletons. Discrete measures are determined by their values on singletons. If singletons
are null-measurable, those values give the coefficients in the Dirac representation.
-/

@[expose] public section

open Function Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory

open Measure

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ ν : Measure α} {p : ι → ℝ≥0∞} {x : ι → α} {s : Set α}

namespace Measure

/-- Every measure on a countable space has a discrete representation indexed by a subset,
with coefficients given by the measures of measurable atoms. With null-measurable singletons,
`IsDiscreteMeasure.eq_discreteMeasure` gives a simpler representation. -/
lemma exists_eq_discreteMeasure [Countable α] (μ : Measure α) :
    ∃ s : Set α, μ = discreteMeasure (fun x : s ↦ μ (measurableAtom x)) Subtype.val := by
  let measurableAtoms := measurableAtom '' (Set.univ : Set α)
  have h_nonempty (s : measurableAtoms) : Set.Nonempty s.val := by
    obtain ⟨y, _, hy⟩ := s.property
    rw [← hy]
    exact ⟨y, mem_measurableAtom_self y⟩
  let points : measurableAtoms → α := fun s ↦ (h_nonempty s).some
  have h_points_mem (s : measurableAtoms) : points s ∈ s.val := (h_nonempty s).some_mem
  refine ⟨Set.range points, ext_of_measurableAtoms fun x ↦ ?_⟩
  rw [discreteMeasure_def, Measure.sum_apply _ (MeasurableSet.measurableAtom_of_countable x)]
  simp only [smul_apply, smul_eq_mul]
  simp_rw [dirac_apply' _ (MeasurableSet.measurableAtom_of_countable x)]
  rw [tsum_eq_single ⟨points ⟨measurableAtom x, by simp [measurableAtoms]⟩, by simp⟩]
  · rw [indicator_of_mem]
    · simp only [Pi.one_apply, mul_one]
      congr 1
      refine (measurableAtom_eq_of_mem ?_).symm
      convert! h_points_mem _
      simp
    · convert! h_points_mem _
      simp
  · simp only [ne_eq, mul_eq_zero, indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false,
      Subtype.forall, Set.mem_range, Subtype.exists, Subtype.mk.injEq, forall_exists_index]
    refine fun y s hs hsy hyx ↦ .inr fun hyx' ↦ hyx ?_
    rw [← hsy]
    congr
    have h1 : measurableAtom y = measurableAtom x := measurableAtom_eq_of_mem hyx'
    have h2 : measurableAtom y = s := by
      specialize h_points_mem ⟨s, hs⟩
      obtain ⟨z, _, hz⟩ := hs
      simp only at h_points_mem
      rw [← hz, ← hsy]
      refine measurableAtom_eq_of_mem ?_
      convert! h_points_mem
    rw [← h2, h1]

end Measure

namespace IsDiscreteMeasure

/-- Every measure on a countable space is discrete, even without measurable singletons. -/
-- Use low priority to try structural instances before searching for `Countable α`.
instance (priority := 100) of_countable [Countable α] (μ : Measure α) : IsDiscreteMeasure μ := by
  obtain ⟨s, hs⟩ := μ.exists_eq_discreteMeasure
  exact ⟨⟨_, hs.trans (discreteMeasure_eq_discreteMeasure_id _ _)⟩⟩

/-- A discrete measure is bounded by any measure that dominates its singleton masses. -/
lemma le_of_singleton_le [IsDiscreteMeasure μ] (h : ∀ a, μ {a} ≤ ν {a}) : μ ≤ ν := by
  have hfin (F : Finset α) : μ.restrict (F : Set α) = (μ ⊓ ν).restrict (F : Set α) := by
    rw [← Set.biUnion_of_singleton (F : Set α), Measure.restrict_biUnion_congr F.countable_toSet]
    simp [Measure.inf_apply_singleton, inf_of_le_left, h]
  obtain ⟨p, rfl⟩ := exists_eq_discreteMeasure (μ := μ)
  refine Measure.le_iff.mpr fun s hs ↦ ?_
  rw [discreteMeasure_def, Measure.sum_apply _ hs]
  refine CompleteLattice.summable.tsum_le_of_sum_le fun F ↦ ?_
  have hle := (sum_le_tsum F).trans
    (le_sum_apply (fun i ↦ p i • Measure.dirac (id i)) (s ∩ (F : Set α)))
  rw [← discreteMeasure_def, ← Measure.restrict_apply hs, hfin] at hle
  simpa +contextual [← Measure.restrict_apply hs, restrict_dirac_of_mem] using
    hle.trans ((Measure.restrict_le_self.trans inf_le_right) s)

lemma le_iff [IsDiscreteMeasure μ] : μ ≤ ν ↔ ∀ a, μ {a} ≤ ν {a} :=
  ⟨fun h a ↦ h {a}, le_of_singleton_le⟩

end IsDiscreteMeasure

/-- Two discrete measures are equal if they agree on singletons. -/
theorem Measure.ext_of_singleton [IsDiscreteMeasure μ] [IsDiscreteMeasure ν]
    (h : ∀ a, μ {a} = ν {a}) : μ = ν :=
  le_antisymm (IsDiscreteMeasure.le_of_singleton_le fun a ↦ (h a).le)
    (IsDiscreteMeasure.le_of_singleton_le fun a ↦ (h a).ge)

/-- Two discrete measures are equal if and only if they agree on singletons. -/
theorem Measure.ext_iff_singleton [IsDiscreteMeasure μ] [IsDiscreteMeasure ν] :
    μ = ν ↔ ∀ a, μ {a} = ν {a} :=
  ⟨fun h _ ↦ h ▸ rfl, Measure.ext_of_singleton⟩

lemma NullMeasurableSet.dirac_of_discreteMeasure
    (hs : NullMeasurableSet s (discreteMeasure p x)) {i : ι} (hi : p i ≠ 0) :
    NullMeasurableSet s (dirac (x i)) := by
  rw [discreteMeasure_def] at hs
  exact (nullMeasurableSet_smul_measure_iff hi).mp
    (hs.mono (le_sum (fun j ↦ p j • dirac (x j)) i))

lemma discreteMeasure_apply₀ (hs : NullMeasurableSet s (discreteMeasure p x)) :
    discreteMeasure p x s = ∑' i : x ⁻¹' s, p i := by
  classical
  rw [discreteMeasure_def, Measure.sum_apply₀ _ hs, tsum_subtype]
  refine tsum_congr fun i ↦ ?_
  by_cases hi : p i = 0 <;> simp [hi, dirac_apply₀, hs.dirac_of_discreteMeasure, indicator]

lemma discreteMeasure_id_apply_singleton₀ {p : α → ℝ≥0∞} {a : α}
    (ha : NullMeasurableSet {a} (discreteMeasure p id)) : discreteMeasure p id {a} = p a := by
  classical
  simp [discreteMeasure_apply₀ ha]

@[simp]
lemma discreteMeasure_id_apply_singleton (p : α → ℝ≥0∞)
    [MeasurableSingletonClass (NullMeasurableSpace α (discreteMeasure p id))] (a : α) :
    discreteMeasure p id {a} = p a :=
  discreteMeasure_id_apply_singleton₀ (nullMeasurableSet_singleton a)

/-- With null-measurable singletons, a discrete measure is the sum of its singleton masses. -/
lemma IsDiscreteMeasure.eq_discreteMeasure (μ : Measure α) [IsDiscreteMeasure μ]
    [MeasurableSingletonClass (NullMeasurableSpace α μ)] :
    μ = MeasureTheory.discreteMeasure (fun a ↦ μ {a}) id := by
  obtain ⟨p, rfl⟩ := IsDiscreteMeasure.exists_eq_discreteMeasure (μ := μ)
  simp

/-- Reconstructing a discrete measure from its singleton masses gives the original measure. -/
@[simp]
lemma discreteMeasure_measure_singleton (μ : Measure α) [IsDiscreteMeasure μ]
    [MeasurableSingletonClass (NullMeasurableSpace α μ)] :
    discreteMeasure (fun a ↦ μ {a}) id = μ :=
  (IsDiscreteMeasure.eq_discreteMeasure μ).symm

lemma map_discreteMeasure₀ {f : α → β} (hf : AEMeasurable f (discreteMeasure p x)) :
    (discreteMeasure p x).map f = discreteMeasure p (f ∘ x) := by
  ext s hs
  simp [map_apply_of_aemeasurable hf hs, discreteMeasure_apply₀ (hf.nullMeasurable hs),
    discreteMeasure_apply₀ hs.nullMeasurableSet, preimage_comp]

instance IsDiscreteMeasure.map (μ : Measure α) [IsDiscreteMeasure μ] (f : α → β) :
    IsDiscreteMeasure (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · obtain ⟨p, rfl⟩ := IsDiscreteMeasure.exists_eq_discreteMeasure (μ := μ)
    rw [map_discreteMeasure₀ hf]
    infer_instance
  · rw [Measure.map_def, dite_eq_right hf]
    split_ifs <;> infer_instance

/-- A discrete pushforward with null-measurable singletons is determined by its fibers. -/
theorem Measure.map_eq_discreteMeasure₀ (μ : Measure α) (f : α → β) [IsDiscreteMeasure (μ.map f)]
    [MeasurableSingletonClass (NullMeasurableSpace β (μ.map f))] (hf : AEMeasurable f μ) :
    μ.map f = discreteMeasure (fun b ↦ μ (f ⁻¹' {b})) id := by
  rw [IsDiscreteMeasure.eq_discreteMeasure (μ.map f)]
  simp [map_apply₀ hf (nullMeasurableSet_singleton _)]

/-- A discrete pushforward with null-measurable singletons is determined by its fibers. -/
theorem Measure.map_eq_discreteMeasure (μ : Measure α) (f : α → β) [IsDiscreteMeasure (μ.map f)]
    [MeasurableSingletonClass (NullMeasurableSpace β (μ.map f))] (hf : Measurable f) :
    μ.map f = discreteMeasure (fun b ↦ μ (f ⁻¹' {b})) id :=
  μ.map_eq_discreteMeasure₀ f hf.aemeasurable

/-- A discrete measure with null-measurable singletons evaluates a null-measurable set by
summing its singleton masses. -/
theorem Measure.tsum_indicator_apply_singleton₀ (μ : Measure α) [IsDiscreteMeasure μ]
    [MeasurableSingletonClass (NullMeasurableSpace α μ)] (s : Set α)
    (hs : NullMeasurableSet s μ) : (∑' x, s.indicator (fun x ↦ μ {x}) x) = μ s := by
  obtain ⟨p, rfl⟩ := IsDiscreteMeasure.exists_eq_discreteMeasure (μ := μ)
  simp [discreteMeasure_apply₀ hs, tsum_subtype]

/-- A discrete measure with null-measurable singletons evaluates a measurable set by
summing its singleton masses. -/
theorem Measure.tsum_indicator_apply_singleton (μ : Measure α) [IsDiscreteMeasure μ]
    [MeasurableSingletonClass (NullMeasurableSpace α μ)] (s : Set α) (hs : MeasurableSet s) :
    (∑' x, s.indicator (fun x ↦ μ {x}) x) = μ s :=
  μ.tsum_indicator_apply_singleton₀ s hs.nullMeasurableSet

@[deprecated Measure.exists_eq_discreteMeasure +typeChanged (since := "2026-11-27")]
lemma Measure.exists_sum_smul_dirac [Countable α] (μ : Measure α) :
    ∃ s : Set α, μ = sum (fun x : s ↦ μ (measurableAtom x) • dirac (x : α)) :=
  μ.exists_eq_discreteMeasure

@[deprecated discreteMeasure_measure_singleton +typeChanged (since := "2026-11-27")]
theorem Measure.sum_smul_dirac (μ : Measure α) [IsDiscreteMeasure μ]
    [MeasurableSingletonClass (NullMeasurableSpace α μ)] :
    (sum fun a ↦ μ {a} • dirac a) = μ :=
  discreteMeasure_measure_singleton μ

@[deprecated discreteMeasure_id_apply_singleton +typeChanged (since := "2026-11-27")]
lemma Measure.sum_smul_dirac_singleton {f : α → ℝ≥0∞} {a : α}
    [MeasurableSingletonClass (NullMeasurableSpace α (sum fun b ↦ f b • dirac b))] :
    sum (fun b ↦ f b • dirac b) {a} = f a :=
  discreteMeasure_id_apply_singleton₀
    (nullMeasurableSet_singleton (μ := sum fun b ↦ f b • dirac b) a)

@[deprecated Measure.map_eq_discreteMeasure₀ +typeChanged (since := "2026-11-27")]
theorem Measure.map_eq_sum₀ (μ : Measure α) (f : α → β) [IsDiscreteMeasure (μ.map f)]
    [MeasurableSingletonClass (NullMeasurableSpace β (μ.map f))] (hf : AEMeasurable f μ) :
    μ.map f = sum fun b ↦ μ (f ⁻¹' {b}) • dirac b :=
  μ.map_eq_discreteMeasure₀ f hf

@[deprecated Measure.map_eq_discreteMeasure +typeChanged (since := "2026-11-27")]
theorem Measure.map_eq_sum (μ : Measure α) (f : α → β) [IsDiscreteMeasure (μ.map f)]
    [MeasurableSingletonClass (NullMeasurableSpace β (μ.map f))] (hf : Measurable f) :
    μ.map f = sum fun b ↦ μ (f ⁻¹' {b}) • dirac b :=
  μ.map_eq_discreteMeasure f hf

end MeasureTheory
