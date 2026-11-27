/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Discrete.Basic

import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Integral with respect to a sum of measures

In this file we prove that a function `f` is integrable with respect to a countable sum of measures
`Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the sequence
`fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable. We then show that under this integrability condition,
`∫ x, f x ∂Measure.sum μ = ∑' i, ∫ f x ∂μ i`.

We specialize these results to indexed discrete measures `discreteMeasure c x`.
The integral formulas sum over the original indices, including repeated atoms.

Finally we compute integrals with respect to discrete measures and over countable and finite sets.

## Main statements

* `integrable_sum_measure_iff`: A function `f` is integrable with respect to a countable sum
  of measures `Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the
  sequence `fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable.
* `integrable_discreteMeasure_iff`: For countably many finite weights, a function `f` is integrable
  with respect to `discreteMeasure c x` if and only if
  the family `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable.
* `hasSum_integral_measure`: If `f` is integrable with respect to `Measure.sum μ`,
  then the sequence `fun i ↦ ∫ x, f x ∂μ i` is summable and its sum is `∫ x, f x ∂Measure.sum μ`.
* `hasSum_integral_discreteMeasure`: If `f` is integrable with respect to `discreteMeasure c x`,
  then `fun i ↦ (c i).toReal • f (x i)` sums to its integral, with no countability assumption.
* `integral_discreteMeasure`: The corresponding formula for the integral as a `tsum`.

## Tags

sum of measures, integral, Dirac mass
-/

public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {ι X E : Type*} [Countable ι] {mX : MeasurableSpace X} [NormedAddCommGroup E]
  {μ : ι → Measure X} {f : X → E}

section Integrable

lemma integrable_sum_measure
    (hf : ∀ i, Integrable f (μ i)) (h : Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i)) :
    Integrable f (Measure.sum μ) := by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr fun i ↦ (hf i).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_sum_measure]
  convert! h.tsum_ofReal_lt_top with i
  rw [ofReal_integral_eq_lintegral_ofReal (hf i).norm]
  · simp_rw [ofReal_norm]
  · exact ae_of_all _ fun _ ↦ by positivity

omit [Countable ι] in
lemma Integrable.summable_integral (hf : Integrable f (Measure.sum μ)) :
    Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i) := by
  convert! ENNReal.summable_toReal (f := fun i ↦ ∫⁻ x, ‖f x‖ₑ ∂μ i) ?_ with i
  · rw [← integral_toReal ?_ (by simp)]
    · simp
    · exact (hf.aestronglyMeasurable.mono_measure (Measure.le_sum _ i)).eNorm
  rw [← lintegral_sum_measure]
  exact hf.2.ne

/-- A function `f` is integrable with respect to a countable sum of measures `Measure.sum μ`
if and only if `f` is integrable with respect to each `μ i` and
the sequence `fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable. -/
lemma integrable_sum_measure_iff :
    Integrable f (Measure.sum μ) ↔
      (∀ i, Integrable f (μ i)) ∧ Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i) where
  mp h := ⟨fun i ↦ h.mono_measure (Measure.le_sum _ i), h.summable_integral⟩
  mpr h := integrable_sum_measure h.1 h.2

section DiscreteMeasure

variable [MeasurableSingletonClass X] {x : ι → X} {c : ι → ℝ≥0∞}

lemma integrable_discreteMeasure (hc : ∀ i, c i ≠ ∞)
    (h : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    Integrable f (discreteMeasure c x) := by
  rw [discreteMeasure_def]
  exact integrable_sum_measure (fun i ↦ (integrable_dirac (by simp)).smul_measure (hc i))
    (by simpa using h)

omit [Countable ι] in
lemma Integrable.summable_discreteMeasure (hf : Integrable f (discreteMeasure c x)) :
    Summable (fun i ↦ (c i).toReal * ‖f (x i)‖) := by
  rw [discreteMeasure_def] at hf
  simpa using hf.summable_integral

/-- For countably many finite weights, integrability with respect to `discreteMeasure c x`
is equivalent to summability of the weighted norms. -/
lemma integrable_discreteMeasure_iff (hc : ∀ i, c i ≠ ∞) :
    Integrable f (discreteMeasure c x) ↔
      Summable (fun i ↦ (c i).toReal * ‖f (x i)‖) where
  mp h := h.summable_discreteMeasure
  mpr h := integrable_discreteMeasure hc h

@[deprecated integrable_discreteMeasure +typeChanged (since := "2026-11-27")]
lemma integrable_sum_dirac (hc : ∀ i, c i ≠ ∞) (h : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i))) :=
  integrable_discreteMeasure hc h

omit [Countable ι] in
@[deprecated Integrable.summable_discreteMeasure +typeChanged (since := "2026-11-27")]
lemma Integrable.summable_of_dirac
    (hf : Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i)))) :
    Summable (fun i ↦ (c i).toReal * ‖f (x i)‖) :=
  hf.summable_discreteMeasure

@[deprecated integrable_discreteMeasure_iff +typeChanged (since := "2026-11-27")]
lemma integrable_sum_dirac_iff (hc : ∀ i, c i ≠ ∞) :
    Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i))) ↔
      Summable (fun i ↦ (c i).toReal * ‖f (x i)‖) :=
  integrable_discreteMeasure_iff hc

end DiscreteMeasure

end Integrable

section Integral

variable [NormedSpace ℝ E]

omit [Countable ι] in
/-- If `f` is integrable with respect to `Measure.sum μ`, then the sequence
`fun i ↦ ∫ x, f x ∂μ i` is summable and its sum is `∫ x, f x ∂Measure.sum μ`. -/
theorem hasSum_integral_measure (hf : Integrable f (Measure.sum μ)) :
    HasSum (fun i ↦ ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.sum μ) := by
  have hfi : ∀ i, Integrable f (μ i) := fun i ↦ hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finsetSum_measure fun i _ ↦ hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 ↦ ?_
  lift ε to ℝ≥0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : ∀ᶠ y in 𝓝 (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ), (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := ℝ≥0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x ↦ ‖f x‖ₑ) μ).eventually hmem).mono fun s hs ↦ ?_
  obtain ⟨ν, hν⟩ : ∃ ν, (∑ i ∈ s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) ↦ μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using! Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball, ← coe_nnDist, NNReal.coe_lt_coe, ← ENNReal.coe_lt_coe, ← hν]
  rw [← hν, integrable_add_measure] at hf
  refine (nnDist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν, lintegral_add_measure, lintegral_finsetSum_measure] at hs
  exact lt_of_add_lt_add_left hs

omit [Countable ι] in
theorem integral_sum_measure (hf : Integrable f (Measure.sum μ)) :
    ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i :=
  (hasSum_integral_measure hf).tsum_eq.symm

section DiscreteMeasure

variable [MeasurableSingletonClass X] {x : ι → X} {c : ι → ℝ≥0∞}

omit [Countable ι] in
/-- The weighted values of an integrable function sum to its integral against a discrete measure.
The index type need not be countable, and coefficients may be infinite. -/
lemma hasSum_integral_discreteMeasure [CompleteSpace E]
    (hf : Integrable f (discreteMeasure c x)) :
    HasSum (fun i ↦ (c i).toReal • f (x i)) (∫ a, f a ∂discreteMeasure c x) := by
  rw [discreteMeasure_def] at hf ⊢
  simpa using hasSum_integral_measure hf

omit [Countable ι] in
/-- The integral against an indexed discrete measure is the sum of the weighted values. -/
lemma integral_discreteMeasure [CompleteSpace E] (hf : Integrable f (discreteMeasure c x)) :
    ∫ a, f a ∂discreteMeasure c x = ∑' i, (c i).toReal • f (x i) :=
  (hasSum_integral_discreteMeasure hf).tsum_eq.symm

/-- For countably many finite weights and a finite-dimensional codomain, the integral formula
also holds without an integrability hypothesis: both sides are zero when the sum diverges. -/
lemma integral_discreteMeasure_of_finiteDimensional [FiniteDimensional ℝ E] (hc : ∀ i, c i ≠ ∞) :
    ∫ a, f a ∂discreteMeasure c x = ∑' i, (c i).toReal • f (x i) := by
  by_cases hf : Integrable f (discreteMeasure c x)
  · exact integral_discreteMeasure hf
  · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
    apply mt Summable.norm
    convert! mt (integrable_discreteMeasure hc) hf
    simp [norm_smul]

@[deprecated integral_discreteMeasure_of_finiteDimensional +typeChanged (since := "2026-11-27")]
lemma integral_sum_dirac [FiniteDimensional ℝ E] (hc : ∀ i, c i ≠ ∞) :
    ∫ a, f a ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) :=
  integral_discreteMeasure_of_finiteDimensional hc

@[deprecated hasSum_integral_discreteMeasure +typeChanged (since := "2026-11-27")]
lemma hasSum_integral_sum_dirac [CompleteSpace E] (hc : ∀ i, c i ≠ ∞)
    (hf : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    HasSum (fun i ↦ (c i).toReal • f (x i))
      (∫ a, f a ∂Measure.sum (fun i ↦ (c i) • .dirac (x i))) :=
  hasSum_integral_discreteMeasure (integrable_discreteMeasure hc hf)

@[deprecated integral_discreteMeasure +typeChanged (since := "2026-11-27")]
lemma integral_sum_dirac_eq_tsum [CompleteSpace E] (hc : ∀ i, c i ≠ ∞)
    (hf : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    ∫ a, f a ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) :=
  integral_discreteMeasure (integrable_discreteMeasure hc hf)

variable [CompleteSpace E] {μ : Measure X}

/-- The integral of an integrable function with respect to a discrete measure is the sum weighted
by its singleton masses. -/
theorem integral_eq_tsum [IsDiscreteMeasure μ] (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x := by
  rw [IsDiscreteMeasure.eq_discreteMeasure μ] at hf
  conv_lhs =>
    rw [IsDiscreteMeasure.eq_discreteMeasure μ, integral_discreteMeasure hf]
  rfl

@[deprecated (since := "2026-11-27")] alias integral_countable := integral_eq_tsum

theorem setIntegral_countable (f : X → E) {s : Set X} (hs : s.Countable) (hf : IntegrableOn f s μ) :
    ∫ x in s, f x ∂μ = ∑' x : s, μ.real {(x : X)} • f x := by
  have hi : Countable { x // x ∈ s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) ↦ f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn, ← map_comap_subtypeVal, integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtypeVal
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet, integral_eq_tsum hf']
  congr 1 with a : 1
  rw [measureReal_def, Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' ↦ MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp [measureReal_def]

theorem setIntegral_finset (s : Finset X) (hf : IntegrableOn f s μ) :
    ∫ x in s, f x ∂μ = ∑ x ∈ s, μ.real {x} • f x := by
  rw [setIntegral_countable _ s.countable_toSet hf, ← Finset.tsum_subtype']

theorem integral_fintype [Fintype X] (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x := by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← setIntegral_finset .univ, Finset.coe_univ, Measure.restrict_univ]
  simp [Finset.coe_univ, hf]

@[simp] lemma integral_count [Fintype X] (f : X → E) :
    ∫ x, f x ∂.count = ∑ a, f a := by simp [integral_fintype]

end DiscreteMeasure

end Integral

end MeasureTheory
