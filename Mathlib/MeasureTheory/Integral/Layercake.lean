/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The layer cake formula / Cavalieri's principle / tail probability formula

The layer cake formula expresses the integral of a nonnegative function as an integral of
its tail measures: `∫⁻ x, f x ∂μ = ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x}`.
In probability theory, these tail measures are the tail probabilities of a random variable.

We first prove the more general identity
`∫⁻ x, ν (Iio (f x)) ∂μ = ∫⁻ t, μ {x | t < f x} ∂ν`
for an `ℝ≥0∞`-valued function `f` and arbitrary measures `μ` and `ν`. The proof uses induction
on measurable functions and monotone convergence, so neither measure needs to be s-finite.
When `ν` has no atoms at singletons, we also obtain the version with non-strict inequalities.

Taking `ν` to be the pushforward of a measure on the positive real line gives the usual
layer cake formula and its weighted versions. The function and the weight may take the value
`∞`; no integrability assumption is needed for these Lebesgue integral statements.
The real-valued formulas, including the versions using Bochner interval integrals, follow
by applying the `ℝ≥0∞`-valued formulas to `ENNReal.ofReal ∘ f`.

## Main results

* `MeasureTheory.lintegral_measure_Iio_eq_lintegral_meas_lt` and
  `MeasureTheory.lintegral_measure_Iic_eq_lintegral_meas_le`: the arbitrary-measure formulas.
* `MeasureTheory.lintegral_eq_lintegral_measure_ofReal_lt` and
  `MeasureTheory.lintegral_eq_lintegral_measure_ofReal_le`: the standard formulas for
  `ℝ≥0∞`-valued functions.
* `MeasureTheory.lintegral_comp_eq_lintegral_measure_ofReal_lt_mul` and
  `MeasureTheory.lintegral_comp_eq_lintegral_measure_ofReal_le_mul`: the weighted formulas
  for `ℝ≥0∞`-valued functions and weights on the positive real line.
* `MeasureTheory.lintegral_ofReal_eq_lintegral_meas_lt` and
  `MeasureTheory.lintegral_ofReal_eq_lintegral_meas_le`: the standard formulas for real-valued
  functions, without a nonnegativity assumption. Both sides ignore negative values of `f`.
* `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` and
  `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`: the weighted real-valued formulas,
  with the primitive of the weight expressed as a Bochner interval integral.
* `MeasureTheory.Integrable.integral_eq_integral_meas_lt` and
  `MeasureTheory.Integrable.integral_eq_integral_meas_le`: Bochner integral versions for
  integrable, almost everywhere nonnegative real-valued functions.

## See also

A representation of the integral of a real power of a nonnegative function is given in
`Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean`.

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/

public section

open scoped ENNReal MeasureTheory Topology

open Set MeasureTheory Filter Measure

namespace MeasureTheory

section

variable {α R : Type*} [MeasurableSpace α] (μ : Measure α) [LinearOrder R]

theorem countable_meas_le_ne_meas_lt (g : α → R) :
    {t : R | μ {a : α | t ≤ g a} ≠ μ {a : α | t < g a}}.Countable := by
  -- the target set is contained in the set of points where the function `t ↦ μ {a : α | t ≤ g a}`
  -- jumps down on the right of `t`. This jump set is countable for any function.
  let F : R → ℝ≥0∞ := fun t ↦ μ {a : α | t ≤ g a}
  apply (countable_image_gt_image_Ioi F).mono
  intro t ht
  have : μ {a | t < g a} < μ {a | t ≤ g a} :=
    lt_of_le_of_ne (measure_mono (fun a ha ↦ le_of_lt ha)) (Ne.symm ht)
  exact ⟨μ {a | t < g a}, this, fun s hs ↦ by grw [hs]⟩

theorem meas_le_ae_eq_meas_lt {R : Type*} [LinearOrder R] [MeasurableSpace R]
    (ν : Measure R) [NullSingletonClass ν] (g : α → R) :
    (fun t => μ {a : α | t ≤ g a}) =ᵐ[ν] fun t => μ {a : α | t < g a} :=
  Set.Countable.measure_zero (countable_meas_le_ne_meas_lt μ g) _

end

/-! ### Layer cake formulas for `ℝ≥0∞`-valued functions -/

section LayercakeENNReal

variable {α : Type*} [MeasurableSpace α]

private lemma lintegral_measure_Iio_eq_lintegral_meas_lt_of_measurable
    (μ : Measure α) (ν : Measure ℝ≥0∞)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, ν (Iio (f x)) ∂μ = ∫⁻ t, μ {x | t < f x} ∂ν := by
  have hm : Measurable (fun r : ℝ≥0∞ ↦ ν (Iio r)) :=
    (show Monotone (fun r : ℝ≥0∞ ↦ ν (Iio r)) from
      fun _ _ h ↦ measure_mono (Iio_subset_Iio h)).measurable
  have ht (f : α → ℝ≥0∞) : Antitone (fun t ↦ μ {x | t < f x}) :=
    fun _ _ h ↦ measure_mono (fun _ hx ↦ h.trans_lt hx)
  refine hf.ennreal_induction ?_ ?_ ?_
  · -- A constant on a measurable set gives the product of the two measures.
    intro c s hs
    have hleft : (fun x ↦ ν (Iio (s.indicator (fun _ ↦ c) x))) =
        s.indicator (fun _ ↦ ν (Iio c)) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    have hright : (fun t ↦ μ {x | t < s.indicator (fun _ ↦ c) x}) =
        (Iio c).indicator (fun _ ↦ μ s) := by
      funext t
      by_cases htc : t < c
      · have hset : {x | t < s.indicator (fun _ ↦ c) x} = s := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx, htc]
        simp [hset, htc]
      · have hset : {x | t < s.indicator (fun _ ↦ c) x} = ∅ := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx, htc]
        simp [hset, htc]
    rw [hleft, hright, lintegral_indicator_const hs,
      lintegral_indicator_const measurableSet_Iio, mul_comm]
  · -- With disjoint supports, each superlevel set is a disjoint union.
    intro f g hfg hf hg ihf ihg
    have hz (x) : f x = 0 ∨ g x = 0 := by
      by_cases hx : f x = 0
      · exact Or.inl hx
      · exact Or.inr (not_not.mp (fun hgx ↦ Set.disjoint_left.mp hfg hx hgx))
    have hleft (x) : ν (Iio ((f + g) x)) = ν (Iio (f x)) + ν (Iio (g x)) := by
      rcases hz x with h | h <;> simp [h]
    have hright (t) :
        μ {x | t < (f + g) x} = μ {x | t < f x} + μ {x | t < g x} := by
      have hset : {x | t < (f + g) x} = {x | t < f x} ∪ {x | t < g x} := by
        ext x
        rcases hz x with h | h <;> simp [h]
      rw [hset, measure_union]
      · exact hfg.mono
          (fun x hx ↦ ne_of_gt ((bot_le : (0 : ℝ≥0∞) ≤ t).trans_lt hx))
          (fun x hx ↦ ne_of_gt ((bot_le : (0 : ℝ≥0∞) ≤ t).trans_lt hx))
      · exact measurableSet_lt measurable_const hg
    simp_rw [hleft, hright]
    rw [lintegral_add_left (f := fun x ↦ ν (Iio (f x))) (hm.comp hf),
      lintegral_add_left (ht f).measurable, ihf, ihg]
  · -- Strict superlevel sets commute with increasing suprema.
    intro f hf hmono ih
    have hleft (x) : ν (Iio (⨆ n, f n x)) = ⨆ n, ν (Iio (f n x)) := by
      rw [← iUnion_Iio_eq_Iio_iSup]
      exact (show Monotone (fun n ↦ Iio (f n x)) from
        fun i j hij ↦ Iio_subset_Iio (hmono hij x)).measure_iUnion
    have hright (t) : μ {x | t < ⨆ n, f n x} = ⨆ n, μ {x | t < f n x} := by
      have hset : {x | t < ⨆ n, f n x} = ⋃ n, {x | t < f n x} := by
        ext x
        simp [lt_iSup_iff]
      rw [hset]
      exact (show Monotone (fun n ↦ {x | t < f n x}) from
        fun i j hij x hx ↦ hx.trans_le (hmono hij x)).measure_iUnion
    simp_rw [hleft, hright]
    rw [lintegral_iSup (f := fun n x ↦ ν (Iio (f n x))) (fun n ↦ hm.comp (hf n))
      (fun i j hij x ↦ measure_mono (Iio_subset_Iio (hmono hij x))),
      lintegral_iSup (fun n ↦ (ht (f n)).measurable)
        (fun i j hij t ↦ measure_mono (fun x hx ↦ hx.trans_le (hmono hij x)))]
    exact iSup_congr ih

/-- The layer cake formula for an `ℝ≥0∞`-valued function and arbitrary measures:
its integral against the cumulative function `r ↦ ν (Iio r)` is the integral of its strict
tail measures against `ν`. Neither measure needs to be s-finite. -/
lemma lintegral_measure_Iio_eq_lintegral_meas_lt (μ : Measure α) (ν : Measure ℝ≥0∞)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x, ν (Iio (f x)) ∂μ = ∫⁻ t, μ {x | t < f x} ∂ν := by
  calc
    _ = ∫⁻ x, ν (Iio (hf.mk f x)) ∂μ :=
      lintegral_congr_ae (hf.ae_eq_mk.fun_comp (fun r ↦ ν (Iio r)))
    _ = ∫⁻ t, μ {x | t < hf.mk f x} ∂ν :=
      lintegral_measure_Iio_eq_lintegral_meas_lt_of_measurable μ ν hf.measurable_mk
    _ = _ := by
      apply lintegral_congr
      intro t
      apply measure_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]

/-- The non-strict layer cake formula for an `ℝ≥0∞`-valued function and arbitrary measures.
Only the measure on the thresholds is required to vanish on singletons. -/
lemma lintegral_measure_Iic_eq_lintegral_meas_le (μ : Measure α) (ν : Measure ℝ≥0∞)
    [NullSingletonClass ν] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x, ν (Iic (f x)) ∂μ = ∫⁻ t, μ {x | t ≤ f x} ∂ν := by
  calc
    _ = ∫⁻ x, ν (Iio (f x)) ∂μ :=
      lintegral_congr (fun _ ↦ (measure_congr Iio_ae_eq_Iic).symm)
    _ = ∫⁻ t, μ {x | t < f x} ∂ν := lintegral_measure_Iio_eq_lintegral_meas_lt μ ν hf
    _ = _ := lintegral_congr_ae (meas_le_ae_eq_meas_lt μ ν f).symm

private lemma lintegral_measure_ofReal_lt (μ : Measure α) (ρ : Measure ℝ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x, ρ {t | ENNReal.ofReal t < f x} ∂μ =
      ∫⁻ t, μ {x | ENNReal.ofReal t < f x} ∂ρ := by
  have hm : Measurable (fun t : ℝ≥0∞ ↦ μ {x | t < f x}) :=
    (show Antitone (fun t : ℝ≥0∞ ↦ μ {x | t < f x}) from
      fun _ _ h ↦ measure_mono (fun _ hx ↦ h.trans_lt hx)).measurable
  have h := lintegral_measure_Iio_eq_lintegral_meas_lt μ (ρ.map ENNReal.ofReal) hf
  simp_rw [Measure.map_apply ENNReal.measurable_ofReal measurableSet_Iio] at h
  rw [lintegral_map hm ENNReal.measurable_ofReal] at h
  exact h

private lemma nullSingletonClass_map_ofReal (ρ : Measure ℝ) [NullSingletonClass ρ] :
    NullSingletonClass ((ρ.restrict (Ioi 0)).map ENNReal.ofReal) := by
  refine ⟨fun c ↦ ?_⟩
  rw [Measure.map_apply ENNReal.measurable_ofReal (measurableSet_singleton c),
    Measure.restrict_apply ((measurableSet_singleton c).preimage ENNReal.measurable_ofReal)]
  apply measure_mono_null (t := {c.toReal}) ?_ (measure_singleton _)
  intro t ht
  have h : ENNReal.ofReal t = c := ht.1
  simpa [ENNReal.toReal_ofReal (le_of_lt ht.2)] using congrArg ENNReal.toReal h

private lemma lintegral_measure_ofReal_le (μ : Measure α) (ρ : Measure ℝ) [NullSingletonClass ρ]
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x, (ρ.restrict (Ioi 0)) {t | ENNReal.ofReal t ≤ f x} ∂μ =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t ≤ f x} ∂ρ := by
  let := nullSingletonClass_map_ofReal ρ
  have hm : Measurable (fun t : ℝ≥0∞ ↦ μ {x | t ≤ f x}) :=
    (show Antitone (fun t : ℝ≥0∞ ↦ μ {x | t ≤ f x}) from
      fun _ _ h ↦ measure_mono (fun _ hx ↦ h.trans hx)).measurable
  have h := lintegral_measure_Iic_eq_lintegral_meas_le μ
    ((ρ.restrict (Ioi 0)).map ENNReal.ofReal) hf
  simp_rw [Measure.map_apply ENNReal.measurable_ofReal measurableSet_Iic] at h
  rw [lintegral_map hm ENNReal.measurable_ofReal] at h
  exact h

private lemma volume_ofReal_lt (c : ℝ≥0∞) :
    (volume.restrict (Ioi (0 : ℝ))) {t | ENNReal.ofReal t < c} = c := by
  by_cases hc : c = ∞
  · subst c
    simp
  rw [Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
  have hset : {t : ℝ | ENNReal.ofReal t < c} ∩ Ioi 0 = Ioo 0 c.toReal := by
    ext t
    by_cases ht : 0 < t
    · simp [ht, ENNReal.ofReal_lt_iff_lt_toReal ht.le hc]
    · simp [ht]
  rw [hset]
  simp [Real.volume_Ioo, ENNReal.ofReal_toReal hc]

private lemma volume_ofReal_le (c : ℝ≥0∞) :
    (volume.restrict (Ioi (0 : ℝ))) {t | ENNReal.ofReal t ≤ c} = c := by
  by_cases hc : c = ∞
  · subst c
    simp
  rw [Measure.restrict_apply (measurableSet_le ENNReal.measurable_ofReal measurable_const)]
  have hset : {t : ℝ | ENNReal.ofReal t ≤ c} ∩ Ioi 0 = Ioc 0 c.toReal := by
    ext t
    rw [← ENNReal.ofReal_toReal hc]
    simp [ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, and_comm]
  rw [hset]
  simp [Real.volume_Ioc, ENNReal.ofReal_toReal hc]

/-- The layer cake formula / Cavalieri's principle / tail probability formula for an
`ℝ≥0∞`-valued function, using strict superlevel sets. -/
lemma lintegral_eq_lintegral_measure_ofReal_lt (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} := by
  have h := lintegral_measure_ofReal_lt μ (volume.restrict (Ioi 0)) hf
  simp_rw [volume_ofReal_lt] at h
  exact h

/-- The layer cake formula / Cavalieri's principle / tail probability formula for an
`ℝ≥0∞`-valued function, using non-strict superlevel sets. -/
theorem lintegral_eq_lintegral_measure_ofReal_le (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t ≤ f x} := by
  have h := lintegral_measure_ofReal_le μ volume hf
  simp_rw [volume_ofReal_le] at h
  exact h

/-- The weighted layer cake formula for an `ℝ≥0∞`-valued function and an `ℝ≥0∞`-valued
weight on the positive real line, using strict superlevel sets. The inner integral runs over
the whole positive real line when `f x = ∞`. No integrability or s-finiteness is required. -/
lemma lintegral_comp_eq_lintegral_measure_ofReal_lt_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict (Ioi 0))) :
    ∫⁻ x, (∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x}, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} * g t := by
  have hm : Measurable (fun t : ℝ ↦ μ {x | ENNReal.ofReal t < f x}) :=
    (show Antitone (fun t : ℝ≥0∞ ↦ μ {x | t < f x}) from
      fun _ _ h ↦ measure_mono (fun _ hx ↦ h.trans_lt hx)).measurable.comp
        ENNReal.measurable_ofReal
  have h := lintegral_measure_ofReal_lt μ
    ((volume.restrict (Ioi 0)).withDensity g) hf
  simp_rw [withDensity_apply _ (measurableSet_lt ENNReal.measurable_ofReal measurable_const)] at h
  rw [lintegral_withDensity_eq_lintegral_mul₀ hg hm.aemeasurable] at h
  simpa [Measure.restrict_restrict, measurableSet_lt ENNReal.measurable_ofReal measurable_const,
    Set.inter_comm, Set.ofPred_and, Set.Ioi, mul_comm] using h

/-- The weighted layer cake formula for an `ℝ≥0∞`-valued function and an `ℝ≥0∞`-valued
weight on the positive real line, using non-strict superlevel sets. The inner integral runs over
the whole positive real line when `f x = ∞`. No integrability or s-finiteness is required. -/
lemma lintegral_comp_eq_lintegral_measure_ofReal_le_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict (Ioi 0))) :
    ∫⁻ x, (∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t ≤ f x}, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t ≤ f x} * g t := by
  have hm : Measurable (fun t : ℝ ↦ μ {x | ENNReal.ofReal t ≤ f x}) :=
    (show Antitone (fun t : ℝ≥0∞ ↦ μ {x | t ≤ f x}) from
      fun _ _ h ↦ measure_mono (fun _ hx ↦ h.trans hx)).measurable.comp
        ENNReal.measurable_ofReal
  have h := lintegral_measure_ofReal_le μ (volume.withDensity g) hf
  simp_rw [restrict_withDensity measurableSet_Ioi,
    withDensity_apply _ (measurableSet_le ENNReal.measurable_ofReal measurable_const)] at h
  rw [lintegral_withDensity_eq_lintegral_mul₀ hg hm.aemeasurable] at h
  simpa [Measure.restrict_restrict, measurableSet_le ENNReal.measurable_ofReal measurable_const,
    Set.inter_comm, Set.ofPred_and, Set.Ioi, mul_comm] using h

end LayercakeENNReal

/-! ### Layer cake formulas for real-valued functions -/

section Layercake

variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} {g : ℝ → ℝ}

/-- The layer cake formula for the positive part of a real-valued function, using non-strict
superlevel sets. No nonnegativity assumption on the function is needed. -/
lemma lintegral_ofReal_eq_lintegral_meas_le (μ : Measure α) {f : α → ℝ}
    (hf : AEMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ t in Ioi 0, μ {x | t ≤ f x} := by
  rw [lintegral_eq_lintegral_measure_ofReal_le μ hf.ennreal_ofReal]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 0 < t at ht
  have hset : {x | ENNReal.ofReal t ≤ ENNReal.ofReal (f x)} = {x | t ≤ f x} := by
    ext x
    simp [ENNReal.ofReal_le_ofReal_iff', not_le_of_gt ht]
  simp [hset]

/-- The layer cake formula for the positive part of a real-valued function, using strict
superlevel sets. No nonnegativity assumption on the function is needed. -/
theorem lintegral_ofReal_eq_lintegral_meas_lt (μ : Measure α) (hf : AEMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ t in Ioi 0, μ {x | t < f x} := by
  rw [lintegral_ofReal_eq_lintegral_meas_le μ hf]
  exact lintegral_congr_ae (meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f)

private lemma lintegral_comp_eq_lintegral_meas_le_mul_aux (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t)
    (g_mble : AEMeasurable g (volume.restrict (Ioi 0))) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  have hg : AEMeasurable (fun t ↦ ENNReal.ofReal (g t)) (volume.restrict (Ioi 0)) :=
    g_mble.ennreal_ofReal
  have heq : (fun x ↦ ENNReal.ofReal (∫ t in 0..f x, g t)) =ᵐ[μ]
      (fun x ↦ ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t ≤ ENNReal.ofReal (f x)},
        ENNReal.ofReal (g t)) := by
    filter_upwards [f_nn] with x hx
    change 0 ≤ f x at hx
    have hset : {t : ℝ | 0 < t ∧ ENNReal.ofReal t ≤ ENNReal.ofReal (f x)} = Ioc 0 (f x) := by
      ext t
      simp [ENNReal.ofReal_le_ofReal_iff hx]
    have hint : IntervalIntegrable g volume 0 (f x) := by
      rcases eq_or_lt_of_le hx with h | h
      · simp [← h]
      · exact g_intble _ h
    rw [hset, intervalIntegral.integral_of_le hx]
    exact ofReal_integral_eq_lintegral_ofReal hint.1
      (ae_mono (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) g_nn)
  rw [lintegral_congr_ae heq,
    lintegral_comp_eq_lintegral_measure_ofReal_le_mul μ f_mble.ennreal_ofReal hg]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 0 < t at ht
  have hset : {x | ENNReal.ofReal t ≤ ENNReal.ofReal (f x)} = {x | t ≤ f x} := by
    ext x
    simp [ENNReal.ofReal_le_ofReal_iff', not_le_of_gt ht]
  simp [hset]

/-- The layer cake formula / **Cavalieri's principle** / tail probability formula:

Let `f` be a non-negative measurable function on a measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) ≥ t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω | f(ω) ≥ t}`.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` for a version with sets of the form
`{ω | f(ω) > t}` instead. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  exact lintegral_comp_eq_lintegral_meas_le_mul_aux μ f_nn f_mble g_intble g_nn
    (aemeasurable_Ioi_of_forall_Ioc fun t ht ↦ (g_intble t ht).1.1.aemeasurable)

/-- A version of the real-valued weighted layer cake formula with pointwise measurability and
nonnegativity hypotheses. The measurability hypothesis on `g` follows from local integrability,
but is retained for compatibility.

See `lintegral_comp_eq_lintegral_meas_le_mul` for the almost everywhere formulation. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable (μ : Measure α)
    (f_nn : 0 ≤ f) (f_mble : Measurable f)
    (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t) (g_mble : Measurable g)
    (g_nn : ∀ t > 0, 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  refine lintegral_comp_eq_lintegral_meas_le_mul_aux μ (.of_forall f_nn) f_mble.aemeasurable
    g_intble ?_ g_mble.aemeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using g_nn t ht

/-- The former s-finite version of the real-valued weighted layer cake formula, retained for
compatibility. The s-finiteness assumption is unnecessary; see
`lintegral_comp_eq_lintegral_meas_le_mul_of_measurable` or
`lintegral_comp_eq_lintegral_meas_le_mul`. -/
@[deprecated lintegral_comp_eq_lintegral_meas_le_mul_of_measurable +typeChanged
  (since := "2026-11-05")]
theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinite
    (μ : Measure α) [SFinite μ]
    (f_nn : 0 ≤ f) (f_mble : Measurable f)
    (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t) (g_mble : Measurable g)
    (g_nn : ∀ t > 0, 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  exact lintegral_comp_eq_lintegral_meas_le_mul_of_measurable μ f_nn f_mble g_intble g_mble g_nn

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) ≥ t}`.

See `MeasureTheory.lintegral_eq_lintegral_meas_lt` for a version with strict superlevel sets,
and `lintegral_ofReal_eq_lintegral_meas_le` for a version without the nonnegativity assumption. -/
theorem lintegral_eq_lintegral_meas_le (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} := by
  rw [lintegral_eq_lintegral_measure_ofReal_le μ f_mble.ennreal_ofReal]
  congr with t
  apply measure_congr
  filter_upwards [f_nn] with x hx
  change 0 ≤ f x at hx
  simp [ENNReal.ofReal_le_ofReal_iff hx]

end Layercake

section LayercakeLT

variable {α : Type*} [MeasurableSpace α]
variable {f : α → ℝ} {g : ℝ → ℝ}

/-- The layer cake formula / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) > t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0..∞, g(t) * μ {ω | f(ω) > t}`.

See `lintegral_comp_eq_lintegral_meas_le_mul` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
theorem lintegral_comp_eq_lintegral_meas_lt_mul (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (g t) := by
  rw [lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn]
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f]
    with t ht
  rw [ht]

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0..∞, μ {ω | f(ω) > t}`.

See `lintegral_eq_lintegral_meas_le` for a version with non-strict superlevel sets,
and `lintegral_ofReal_eq_lintegral_meas_lt` for a version without the nonnegativity assumption. -/
theorem lintegral_eq_lintegral_meas_lt (μ : Measure α)
    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t < f a} := by
  rw [lintegral_eq_lintegral_meas_le μ f_nn f_mble]
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f]
    with t ht
  rw [ht]

end LayercakeLT

section LayercakeIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For an integrable a.e.-nonnegative real-valued function `f`, the Bochner integral of `f` can be
written (roughly speaking) as: `∫ f ∂μ = ∫ t in 0..∞, μ {ω | f(ω) > t}`.

See `MeasureTheory.lintegral_eq_lintegral_meas_lt` for a version with Lebesgue integral `∫⁻`
instead. -/
theorem Integrable.integral_eq_integral_meas_lt
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Set.Ioi 0, μ.real {a : α | t < f a} := by
  have key := lintegral_eq_lintegral_meas_lt μ f_nn f_intble.aemeasurable
  have lhs_finite : ∫⁻ (ω : α), ENNReal.ofReal (f ω) ∂μ < ∞ := Integrable.lintegral_lt_top f_intble
  have rhs_finite : ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a} < ∞ := by simp only [← key, lhs_finite]
  have rhs_integrand_finite : ∀ (t : ℝ), t > 0 → μ {a | t < f a} < ∞ :=
    fun t ht ↦ measure_gt_lt_top f_intble ht
  convert (ENNReal.toReal_eq_toReal_iff' lhs_finite.ne rhs_finite.ne).mpr key
  · exact integral_eq_lintegral_of_nonneg_ae f_nn f_intble.aestronglyMeasurable
  · have aux := @integral_eq_lintegral_of_nonneg_ae _ _ ((volume : Measure ℝ).restrict (Set.Ioi 0))
      (fun t ↦ μ.real {a : α | t < f a}) ?_ ?_
    · rw [aux]
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      exact fun t t_pos ↦ ENNReal.ofReal_toReal (rhs_integrand_finite t t_pos).ne
    · exact Eventually.of_forall (fun x ↦ by positivity)
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      exact Antitone.measurable (fun _ _ hst ↦ measure_mono (fun _ h ↦ lt_of_le_of_lt hst h))

theorem Integrable.integral_eq_integral_meas_le
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Set.Ioi 0, μ.real {a : α | t ≤ f a} := by
  rw [Integrable.integral_eq_integral_meas_lt f_intble f_nn]
  apply integral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f] with t ht
  exact congrArg ENNReal.toReal ht.symm

lemma Integrable.integral_eq_integral_Ioc_meas_le {f : α → ℝ} {M : ℝ}
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) (f_bdd : f ≤ᵐ[μ] (fun _ ↦ M)) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 M, μ.real {a : α | t ≤ f a} := by
  rw [f_intble.integral_eq_integral_meas_le f_nn]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self ?_]
  apply Eventually.of_forall (fun t ht ↦ ?_)
  have htM : M < t := by simp_all only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le]
  have obs : μ {a | M < f a} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [f_bdd] with a ha using not_lt.mpr ha
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  exact Or.inl <| measure_mono_null (fun a ha ↦ lt_of_lt_of_le htM ha) obs

end LayercakeIntegral

end MeasureTheory
