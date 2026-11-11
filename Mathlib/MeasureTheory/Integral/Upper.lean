/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

import all Mathlib.MeasureTheory.Integral.Lebesgue.Basic -- for proof translation

/-!
# Upper Lebesgue integral for `ℝ≥0∞`-valued functions

We define the upper Lebesgue integral of an `ℝ≥0∞`-valued function.

## Notation

We introduce the following notation for the upper Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁺ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁺ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁺ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁺ x, f x ∂(μ.restrict s)`;
* `∫⁺ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁺ x, f x ∂(volume.restrict s)`.

-/

@[expose] public section

open Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory

-- Keep the order on measures fixed only in this file. The attribute does not support `local` yet.
run_elab do
  Lean.modifyEnv fun env =>
    Mathlib.Tactic.ToDual.dontTranslateAttr.modifyState env
      (fun s ↦ s.map (fun m ↦ m.insert ``Measure ()))

variable {α β γ : Type*}

variable {m : MeasurableSpace α}

/-- The **upper Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
@[no_expose] noncomputable def uintegral (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ x, g x ∂μ

alias uintegral_def := uintegral.eq_def

attribute [to_dual existing uintegral] lintegral

@[inherit_doc MeasureTheory.uintegral]
notation3 "∫⁺ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => uintegral μ r

@[inherit_doc MeasureTheory.uintegral]
notation3 "∫⁺ "(...)", "r:60:(scoped f => uintegral volume f) => r

@[inherit_doc MeasureTheory.uintegral]
notation3 "∫⁺ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 =>
  uintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.uintegral]
notation3 "∫⁺ "(...)" in "s", "r:60:(scoped f => uintegral (Measure.restrict volume s) f) => r

section LIntegral

variable {μ : Measure α} {f g : α → ℝ≥0∞}

lemma lintegral_le_uintegral : ∫⁻ x, f x ∂μ ≤ ∫⁺ x, f x ∂μ := by
  rw [uintegral_def]
  exact le_iInf fun g ↦ le_iInf fun _ ↦ le_iInf fun hfg ↦ lintegral_mono hfg

lemma uintegral_le_lintegral (hg : Measurable g) (hfg : f ≤ g) :
    ∫⁺ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ := by
  rw [uintegral_def]
  exact iInf_le_of_le g <| iInf_le_of_le hg <| iInf_le _ hfg

lemma uintegral_lt_iff {r : ℝ≥0∞} :
    ∫⁺ x, f x ∂μ < r ↔
      ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁻ x, g x ∂μ < r := by
  simp only [uintegral_def, iInf_lt_iff, exists_prop]

lemma uintegral_le_lintegral_ae (hg : AEMeasurable g μ) (hfg : f ≤ᵐ[μ] g) :
    ∫⁺ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ := by
  obtain ⟨g', hg', hfg', hgg'⟩ := hg.exists_measurable_ge hfg
  exact (uintegral_le_lintegral hg' hfg').trans_eq (lintegral_congr_ae hgg'.symm)

lemma uintegral_eq_lintegral_ae (hf : AEMeasurable f μ) :
    ∫⁺ x, f x ∂μ = ∫⁻ x, f x ∂μ :=
  le_antisymm (uintegral_le_lintegral_ae hf Filter.EventuallyLE.rfl) lintegral_le_uintegral

lemma uintegral_eq_lintegral (hf : Measurable f) :
    ∫⁺ x, f x ∂μ = ∫⁻ x, f x ∂μ :=
  uintegral_eq_lintegral_ae hf.aemeasurable

theorem exists_measurable_ge_uintegral_eq_lintegral (μ : Measure α) (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁺ x, f x ∂μ = ∫⁻ x, g x ∂μ := by
  rcases eq_or_ne (∫⁺ x, f x ∂μ) ∞ with h_top | h_top
  · refine ⟨fun _ ↦ ∞, measurable_const, le_top, ?_⟩
    exact (uintegral_le_lintegral measurable_const le_top).antisymm (by simp [h_top])
  obtain ⟨c, _, hc, hc_tendsto⟩ := exists_seq_strictAnti_tendsto' h_top.lt_top
  choose g hg_meas hfg hg_lt using fun n ↦ uintegral_lt_iff.mp (hc n).1
  let g₀ : α → ℝ≥0∞ := fun x ↦ ⨅ n, g n x
  have hg₀ : Measurable g₀ := .iInf hg_meas
  have hfg₀ : f ≤ g₀ := fun x ↦ le_iInf (hfg · x)
  refine ⟨g₀, hg₀, hfg₀, (uintegral_le_lintegral hg₀ hfg₀).antisymm ?_⟩
  refine ge_of_tendsto' hc_tendsto fun n ↦ ?_
  grw [lintegral_mono fun x ↦ iInf_le _ n, (hg_lt n).le]

end LIntegral

section Basic

variable {m : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

theorem SimpleFunc.lintegral_eq_uintegral {m : MeasurableSpace α}
    (f : SimpleFunc α ℝ≥0∞) (μ : Measure α) :
    ∫⁺ x, f x ∂μ = f.lintegral μ := by
  rw [uintegral_eq_lintegral f.measurable, f.lintegral_eq_lintegral]

@[gcongr, mono, to_dual existing lintegral_mono']
theorem uintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ ≤ ν)
    ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : ∫⁺ x, f x ∂μ ≤ ∫⁺ x, g x ∂ν := by
  simp only [uintegral_def]
  refine iInf_mono fun h ↦ iInf_mono fun _ ↦ iInf_mono' fun hgh ↦ ?_
  exact ⟨hfg.trans hgh, lintegral_mono' hμν le_rfl⟩

-- version where `hfg` is an explicit forall, so that `@[gcongr]` can recognize it
@[gcongr, to_dual existing lintegral_mono_fn']
theorem uintegral_mono_fn' (h2 : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    ∫⁺ x, f x ∂μ ≤ ∫⁺ x, g x ∂ν :=
  uintegral_mono' h2 hfg

attribute [to_dual uintegral_mono] lintegral_mono

attribute [to_dual uintegral_mono_nnreal] lintegral_mono_nnreal

theorem iInf_uintegral_measurable_ge_eq_uintegral (f : α → ℝ≥0∞) :
    ⨅ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁺ a, g a ∂μ = ∫⁺ a, f a ∂μ := by
  grind [uintegral_def, uintegral_eq_lintegral]

attribute [to_dual uintegral_mono_set] lintegral_mono_set

attribute [to_dual uintegral_mono_set'] lintegral_mono_set'

attribute [to_dual monotone_uintegral] monotone_lintegral

@[simp, to_dual existing lintegral_const]
theorem uintegral_const (c : ℝ≥0∞) : ∫⁺ _, c ∂μ = c * μ Set.univ := by
  rw [uintegral_eq_lintegral measurable_const, lintegral_const]

attribute [to_dual uintegral_zero] lintegral_zero

attribute [to_dual uintegral_zero_fun] lintegral_zero_fun

attribute [to_dual uintegral_one] lintegral_one

attribute [to_dual setUIntegral_const] setLIntegral_const

attribute [to_dual setUIntegral_one] setLIntegral_one

attribute [to_dual iInf_mul_le_uintegral] iInf_mul_le_lintegral

attribute [to_dual uintegral_le_iSup_mul] lintegral_le_iSup_mul

theorem exists_measurable_ge_uintegral_eq (μ : Measure α) (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁺ a, f a ∂μ = ∫⁺ a, g a ∂μ := by
  obtain ⟨g, hg, hfg, heq⟩ := exists_measurable_ge_uintegral_eq_lintegral μ f
  exact ⟨g, hg, hfg, by rw [heq, uintegral_eq_lintegral hg]⟩

theorem exists_measurable_ge_forall_uintegral_eq {ι : Type*} [Countable ι]
    (μ : ι → Measure α) (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧
      ∀ i, ∫⁺ x, f x ∂μ i = ∫⁺ x, g x ∂μ i := by
  choose g hg hfg h using fun i ↦ exists_measurable_ge_uintegral_eq (μ i) f
  let g₀ : α → ℝ≥0∞ := fun x ↦ ⨅ i, g i x
  have hg₀ : Measurable g₀ := .iInf hg
  have hfg₀ : f ≤ g₀ := fun x ↦ le_iInf (hfg · x)
  refine ⟨g₀, hg₀, hfg₀, fun i ↦ ?_⟩
  refine le_antisymm (uintegral_mono hfg₀) ?_
  grw [h i, uintegral_mono fun _ ↦ iInf_le _ i]

attribute [to_dual iSup_uintegral_le] iSup_lintegral_le

attribute [to_dual iSup₂_uintegral_le] iSup₂_lintegral_le

attribute [to_dual le_iInf_uintegral] le_iInf_lintegral

attribute [to_dual le_iInf₂_uintegral] le_iInf₂_lintegral

theorem uintegral_mono_ae {f g : α → ℝ≥0∞} (h : f ≤ᵐ[μ] g) :
    ∫⁺ a, f a ∂μ ≤ ∫⁺ a, g a ∂μ := by
  obtain ⟨g', hg', hgg', hgeq⟩ := exists_measurable_ge_uintegral_eq_lintegral μ g
  grw [hgeq, uintegral_le_lintegral_ae hg'.aemeasurable (by grw [h, hgg'])]

to_dual_for lintegral_mono_ae := uintegral_mono_ae h

theorem setUIntegral_mono_ae {s : Set α} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.restrict s)) (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
    ∫⁺ x in s, f x ∂μ ≤ ∫⁺ x in s, g x ∂μ := by
  obtain ⟨g', hg'm, hle, hg'⟩ := exists_measurable_ge_uintegral_eq_lintegral (μ.restrict s) g
  grw [hle _] at hfg
  grw [uintegral_eq_lintegral_ae hf, hg', setLIntegral_mono_ae hg'm.aemeasurable hfg]

theorem setUIntegral_mono {s : Set α} {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hfg : ∀ x ∈ s, f x ≤ g x) :
    ∫⁺ x in s, f x ∂μ ≤ ∫⁺ x in s, g x ∂μ :=
  setUIntegral_mono_ae hf.aemeasurable (Filter.Eventually.of_forall hfg)

attribute [to_dual setUIntegral_mono_ae'] setLIntegral_mono_ae'

attribute [to_dual setUIntegral_mono'] setLIntegral_mono'

attribute [to_dual setUIntegral_le_uintegral] setLIntegral_le_lintegral

lemma iInf_mul_le_setUIntegral (f : α → ℝ≥0∞) {s : Set α} :
    (⨅ x ∈ s, f x) * μ s ≤ ∫⁺ x in s, f x ∂μ := by
  grw [← setUIntegral_const, setUIntegral_mono (g := f) measurable_const fun x hx ↦ iInf₂_le x hx]

lemma setUIntegral_le_iSup_mul (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁺ x in s, f x ∂μ ≤ (⨆ x ∈ s, f x) * μ s := by
  grw [← setUIntegral_const, setUIntegral_mono' hs fun x hx ↦ le_iSup₂ (f := fun x _ ↦ f x) x hx]

attribute [to_dual uintegral_congr_ae] lintegral_congr_ae

attribute [to_dual uintegral_congr] lintegral_congr

attribute [to_dual setUIntegral_congr] setLIntegral_congr

attribute [to_dual setUIntegral_congr_fun_ae₀] setLIntegral_congr_fun_ae₀

attribute [to_dual setUIntegral_congr_fun_ae] setLIntegral_congr_fun_ae

attribute [to_dual setUIntegral_congr_fun₀] setLIntegral_congr_fun₀

attribute [to_dual setUIntegral_congr_fun] setLIntegral_congr_fun

attribute [to_dual setUIntegral_eq_zero₀] setLIntegral_eq_zero₀

attribute [to_dual setUIntegral_eq_zero] setLIntegral_eq_zero

section

attribute [to_dual uintegral_eq_zero_of_ae_eq_zero] lintegral_eq_zero_of_ae_eq_zero

@[simp]
theorem uintegral_eq_zero_iff {f : α → ℝ≥0∞} : ∫⁺ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  refine ⟨fun hf ↦ ?_, uintegral_eq_zero_of_ae_eq_zero⟩
  obtain ⟨g, hg, hfg, h⟩ := exists_measurable_ge_uintegral_eq_lintegral μ f
  filter_upwards [(lintegral_eq_zero_iff hg).mp (h.symm.trans hf)] with x hx
  exact le_zero_iff.mp ((hfg x).trans_eq hx)

theorem setUIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α → ℝ≥0∞} :
    ∫⁺ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  uintegral_eq_zero_iff.trans (ae_restrict_iff' hs)

theorem uintegral_pos_iff_support {f : α → ℝ≥0∞} :
    (0 < ∫⁺ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by
  simp [pos_iff_ne_zero, Filter.EventuallyEq, ae_iff, Function.support]

to_dual_for lintegral_pos_iff_support := uintegral_pos_iff_support

attribute [to_dual setUIntegral_pos_iff] setLIntegral_pos_iff

theorem setUIntegral_pos_iff' {f : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) :
    0 < ∫⁺ a in s, f a ∂μ ↔ 0 < μ (Function.support f ∩ s) := by
  rw [uintegral_pos_iff_support, Measure.restrict_apply' hs]

end

/-- If `f` has finite upper integral, then `∫⁺ x in s, f x ∂μ` is absolutely continuous in `s`:
it tends to zero as `μ s` tends to zero. This lemma states this fact in terms of `ε` and `δ`. -/
@[to_dual existing exists_pos_setLIntegral_lt_of_measure_lt]
theorem exists_pos_setUIntegral_lt_of_measure_lt {f : α → ℝ≥0∞}
    (h : ∫⁺ x, f x ∂μ ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ > 0, ∀ s, μ s < δ → ∫⁺ x in s, f x ∂μ < ε := by
  obtain ⟨g, hg, hfg, hg_top⟩ := uintegral_lt_iff.mp h.lt_top
  obtain ⟨δ, hδ, hδs⟩ := exists_pos_setLIntegral_lt_of_measure_lt hg_top.ne hε
  exact ⟨δ, hδ, fun s hs ↦ (uintegral_le_lintegral hg hfg).trans_lt (hδs s hs)⟩

/-- If `f` has finite upper integral, then `∫⁺ x in s, f x ∂μ` is absolutely continuous in `s`:
it tends to zero as `μ s` tends to zero. -/
@[to_dual existing tendsto_setLIntegral_zero]
theorem tendsto_setUIntegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁺ x, f x ∂μ ≠ ∞)
    {l : Filter ι} {s : ι → Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁺ x in s i, f x ∂μ) l (𝓝 0) := by
  refine ENNReal.nhds_zero_basis.tendsto_right_iff.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδs⟩ := exists_pos_setUIntegral_lt_of_measure_lt h hε.ne'
  exact (hl.eventually (gt_mem_nhds hδ)).mono fun i hi ↦ hδs _ hi

@[simp, to_dual existing lintegral_smul_measure]
theorem uintegral_smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (f : α → ℝ≥0∞) : ∫⁺ a, f a ∂c • μ = c • ∫⁺ a, f a ∂μ := by
  rw [← smul_one_mul c (∫⁺ a, f a ∂μ)]
  apply le_antisymm
  · obtain ⟨g, hg, hfg, h⟩ := exists_measurable_ge_uintegral_eq_lintegral μ f
    grw [h, uintegral_le_lintegral hg hfg, lintegral_smul_measure, smul_one_mul]
  · obtain ⟨g, hg, hfg, h⟩ := exists_measurable_ge_uintegral_eq_lintegral (c • μ) f
    grw [h, uintegral_le_lintegral hg hfg, smul_one_mul, ← lintegral_smul_measure]

attribute [to_dual setUIntegral_smul_measure] setLIntegral_smul_measure

@[simp, to_dual existing lintegral_zero_measure]
theorem uintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) :
    ∫⁺ a, f a ∂(0 : Measure α) = 0 := by
  simp [uintegral_eq_lintegral_ae]

@[simp, to_dual existing lintegral_add_measure]
theorem uintegral_add_measure (f : α → ℝ≥0∞) (μ ν : Measure α) :
    ∫⁺ a, f a ∂(μ + ν) = ∫⁺ a, f a ∂μ + ∫⁺ a, f a ∂ν := by
  simp only [uintegral_def, lintegral_add_measure, iInf_and', iInf_subtype']
  refine (ENNReal.iInf_add_iInf ?_).symm
  rintro ⟨g, hg, hfg⟩ ⟨h, hh, hfh⟩
  refine ⟨⟨g ⊓ h, hg.inf hh, le_inf hfg hfh⟩, ?_⟩
  exact add_le_add (lintegral_mono inf_le_left) (lintegral_mono inf_le_right)

@[simp, to_dual existing lintegral_finsetSum_measure]
theorem uintegral_finsetSum_measure {ι} (s : Finset ι) (f : α → ℝ≥0∞)
    (μ : ι → Measure α) :
    ∫⁺ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫⁺ a, f a ∂μ i :=
  let F : Measure α →+ ℝ≥0∞ :=
    { toFun := (uintegral · f)
      map_zero' := uintegral_zero_measure f
      map_add' := uintegral_add_measure f }
  map_sum F μ s

theorem le_uintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞)
    (μ : ι → Measure α) :
    ∑' i, ∫⁺ a, f a ∂μ i ≤ ∫⁺ a, f a ∂Measure.sum μ := by
  rw [uintegral_def]
  refine le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ ?_
  grw [lintegral_sum_measure, tsum_le_tsum (fun i ↦ uintegral_le_lintegral hg hfg)]

@[simp]
theorem uintegral_sum_measure {m : MeasurableSpace α} {ι} [Countable ι]
    (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁺ a, f a ∂Measure.sum μ = ∑' i, ∫⁺ a, f a ∂μ i := by
  refine le_antisymm ?_ (le_uintegral_sum_measure f μ)
  obtain ⟨g, hg, hfg, h⟩ := exists_measurable_ge_forall_uintegral_eq μ f
  grw [uintegral_le_lintegral hg hfg, lintegral_sum_measure]
  simp [h, uintegral_eq_lintegral hg]

theorem uintegral_sum_measure_of_aemeasurable {m : MeasurableSpace α} {ι}
    (f : α → ℝ≥0∞) (μ : ι → Measure α) (hf : AEMeasurable f (Measure.sum μ)) :
    ∫⁺ a, f a ∂Measure.sum μ = ∑' i, ∫⁺ a, f a ∂μ i := by
  rw [uintegral_eq_lintegral_ae hf, lintegral_sum_measure]
  refine tsum_congr fun i ↦ ?_
  rw [uintegral_eq_lintegral_ae (hf.mono_measure (Measure.le_sum μ i))]

theorem uintegral_sum_measure_of_measurable {m : MeasurableSpace α} {ι}
    (f : α → ℝ≥0∞) (μ : ι → Measure α) (hf : Measurable f) :
    ∫⁺ a, f a ∂Measure.sum μ = ∑' i, ∫⁺ a, f a ∂μ i :=
  uintegral_sum_measure_of_aemeasurable f μ hf.aemeasurable

theorem hasSum_uintegral_measure {ι} {_ : MeasurableSpace α} [Countable ι]
    (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    HasSum (fun i ↦ ∫⁺ a, f a ∂μ i) (∫⁺ a, f a ∂Measure.sum μ) :=
  (uintegral_sum_measure f μ).symm ▸ CompleteLattice.summable.hasSum

theorem hasSum_uintegral_measure_of_aemeasurable {ι} {_ : MeasurableSpace α}
    (f : α → ℝ≥0∞) (μ : ι → Measure α) (hf : AEMeasurable f (Measure.sum μ)) :
    HasSum (fun i ↦ ∫⁺ a, f a ∂μ i) (∫⁺ a, f a ∂Measure.sum μ) :=
  (uintegral_sum_measure_of_aemeasurable f μ hf).symm ▸ CompleteLattice.summable.hasSum

theorem hasSum_uintegral_measure_of_measurable {ι} {_ : MeasurableSpace α}
    (f : α → ℝ≥0∞) (μ : ι → Measure α) (hf : Measurable f) :
    HasSum (fun i ↦ ∫⁺ a, f a ∂μ i) (∫⁺ a, f a ∂Measure.sum μ) :=
  hasSum_uintegral_measure_of_aemeasurable f μ hf.aemeasurable

@[simp, to_dual existing lintegral_of_isEmpty]
theorem uintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α]
    (μ : Measure α) (f : α → ℝ≥0∞) : ∫⁺ x, f x ∂μ = 0 := by
  rw [Subsingleton.elim μ 0, uintegral_zero_measure]

attribute [to_dual setUIntegral_empty] setLIntegral_empty

attribute [to_dual setUIntegral_univ] setLIntegral_univ

attribute [to_dual setUIntegral_measure_zero] setLIntegral_measure_zero

attribute [to_dual uintegral_rw₁] lintegral_rw₁

attribute [to_dual uintegral_rw₂] lintegral_rw₂

@[to_dual existing lintegral_indicator_le]
theorem uintegral_indicator_le (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁺ a, s.indicator f a ∂μ ≤ ∫⁺ a in s, f a ∂μ := by
  obtain ⟨g, hg, hfg, h⟩ := exists_measurable_ge_uintegral_eq_lintegral (μ.restrict s) f
  obtain ⟨t, hst, ht, hgt⟩ := exists_measurable_superset_setLIntegral_eq hg.aemeasurable s
  grw [h, ← hgt, ← lintegral_indicator ht, uintegral_le_lintegral (hg.indicator ht)]
  grw [hfg, hst]

@[simp, to_dual existing lintegral_indicator]
theorem uintegral_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁺ a, s.indicator f a ∂μ = ∫⁺ a in s, f a ∂μ := by
  refine le_antisymm (uintegral_indicator_le f s) ?_
  grw [← uintegral_congr_ae (indicator_ae_eq_restrict hs.nullMeasurableSet)]
  exact setUIntegral_le_uintegral s _

attribute [to_dual uintegral_indicator₀] lintegral_indicator₀

attribute [to_dual setUIntegral_indicator₀] setLIntegral_indicator₀

attribute [to_dual setUIntegral_indicator] setLIntegral_indicator

theorem uintegral_indicator_const (s : Set α) (c : ℝ≥0∞) :
    ∫⁺ a, s.indicator (fun _ ↦ c) a ∂μ = c * μ s := by
  refine le_antisymm ?_ ?_
  · grw [uintegral_indicator_le, setUIntegral_const]
  · grw [← setUIntegral_const, ← setUIntegral_le_uintegral s (s.indicator fun _ ↦ c)]
    exact setUIntegral_mono measurable_const fun x hx ↦ by simp [hx]

attribute [to_dual setUIntegral_eq_of_support_subset] setLIntegral_eq_of_support_subset

attribute [to_dual setUIntegral_eq_const] setLIntegral_eq_const

@[to_fun (attr := simp) uintegral_indicator_fun_one]
theorem uintegral_indicator_one (s : Set α) : ∫⁺ a, s.indicator 1 a ∂μ = μ s := by
  simp [Pi.one_def, uintegral_indicator_const]

to_dual_for lintegral_indicator_const_le := (uintegral_indicator_const s c).le

to_dual_for lintegral_indicator_const₀ := uintegral_indicator_const s c

to_dual_for lintegral_indicator_const := uintegral_indicator_const s c

to_dual_for lintegral_indicator_one_le := (uintegral_indicator_one s).le

to_dual_for lintegral_indicator_one₀ := uintegral_indicator_one s

to_dual_for lintegral_indicator_one := uintegral_indicator_one s

attribute [to_dual Measure.ext_iff_uintegral] Measure.ext_iff_lintegral

attribute [to_dual Measure.ext_of_uintegral] Measure.ext_of_lintegral

open Measure
open scoped Function

@[to_dual existing lintegral_iUnion₀]
theorem uintegral_iUnion₀ [Countable β] {s : β → Set α} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁺ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁺ a in s i, f a ∂μ := by
  rw [Measure.restrict_iUnion_ae hd hm, uintegral_sum_measure]

attribute [to_dual uintegral_iUnion] lintegral_iUnion

attribute [to_dual uintegral_biUnion₀] lintegral_biUnion₀

attribute [to_dual uintegral_biUnion] lintegral_biUnion

attribute [to_dual uintegral_biUnion_finset₀] lintegral_biUnion_finset₀

attribute [to_dual uintegral_biUnion_finset] lintegral_biUnion_finset

@[to_dual existing lintegral_iUnion_le]
theorem uintegral_iUnion_le [Countable β] (s : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁺ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁺ a in s i, f a ∂μ := by
  grw [← uintegral_sum_measure, uintegral_mono' restrict_iUnion_le le_rfl]

attribute [to_dual uintegral_union] lintegral_union

attribute [to_dual uintegral_union_le] lintegral_union_le

attribute [to_dual uintegral_inter_add_sdiff] lintegral_inter_add_sdiff

attribute [to_dual uintegral_add_compl₀] lintegral_add_compl₀

attribute [to_dual uintegral_add_compl] lintegral_add_compl

attribute [to_dual uintegral_piecewise] lintegral_piecewise

attribute [to_dual setUIntegral_compl₀] setLIntegral_compl₀

attribute [to_dual setUIntegral_compl] setLIntegral_compl

@[to_dual existing setLIntegral_iUnion_of_directed]
theorem setUIntegral_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α → ℝ≥0∞) {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    ∫⁺ x in ⋃ i, s i, f x ∂μ = ⨆ i, ∫⁺ x in s i, f x ∂μ := by
  refine le_antisymm ?_ (iSup_le fun i ↦ uintegral_mono_set (Set.subset_iUnion s i))
  obtain ⟨g, hg, hfg, h⟩ :=
    exists_measurable_ge_forall_uintegral_eq (fun i ↦ μ.restrict (s i)) f
  grw [uintegral_le_lintegral hg hfg, setLIntegral_iUnion_of_directed _ hd]
  simp [h, uintegral_eq_lintegral hg]

attribute [to_dual uintegral_max] lintegral_max

attribute [to_dual setUIntegral_max] setLIntegral_max

/-- The upper integral of an essentially bounded function over a set of finite measure is finite. -/
theorem setUIntegral_lt_top_of_ae_le_nnreal {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0∞}
    (hbdd : ∃ y : ℝ≥0, ∀ᵐ x ∂μ.restrict s, f x ≤ y) :
    ∫⁺ x in s, f x ∂μ < ∞ := by
  grw [uintegral_mono_ae hbdd.choose_spec]
  simp [ENNReal.mul_lt_top, hs.lt_top]

theorem setUIntegral_lt_top_of_le_nnreal₀ {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0∞}
    (hbdd : ∃ y : ℝ≥0, ∀ x ∈ s, f x ≤ y) (hsm : NullMeasurableSet s μ) :
    ∫⁺ x in s, f x ∂μ < ∞ := by
  obtain ⟨M, hM⟩ := hbdd
  exact setUIntegral_lt_top_of_ae_le_nnreal hs
    ⟨M, (ae_restrict_iff'₀ hsm).2 (Filter.Eventually.of_forall hM)⟩

theorem setUIntegral_lt_top_of_le_nnreal' {s : Set α} (hs : μ s ≠ ∞)
    {f : α → ℝ≥0∞} (hbdd : ∃ y : ℝ≥0, ∀ x ∈ s, f x ≤ y)
    (hf : AEMeasurable f (μ.restrict s)) : ∫⁺ x in s, f x ∂μ < ∞ := by
  rw [uintegral_eq_lintegral_ae hf]
  exact setLIntegral_lt_top_of_le_nnreal hs hbdd

theorem setUIntegral_lt_top_of_bddAbove₀ {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0}
    (hbdd : BddAbove (f '' s)) (hsm : NullMeasurableSet s μ) : ∫⁺ x in s, f x ∂μ < ∞ := by
  refine setUIntegral_lt_top_of_le_nnreal₀ hs ?_ hsm
  exact hbdd.imp fun _ hM x hx ↦ ENNReal.coe_le_coe.mpr (hM (Set.mem_image_of_mem f hx))

theorem setUIntegral_lt_top_of_bddAbove {s : Set α} (hs : μ s ≠ ∞)
    {f : α → ℝ≥0} (hbdd : BddAbove (f '' s)) (hf : AEMeasurable f (μ.restrict s)) :
    ∫⁺ x in s, f x ∂μ < ∞ := by
  refine setUIntegral_lt_top_of_le_nnreal' hs ?_ hf.coe_nnreal_ennreal
  exact hbdd.imp fun _ hM x hx ↦ ENNReal.coe_le_coe.mpr (hM (Set.mem_image_of_mem f hx))

theorem setUIntegral_lt_top_of_isCompact₀ [TopologicalSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : ContinuousOn f s)
    (hsm : NullMeasurableSet s μ) : ∫⁺ x in s, f x ∂μ < ∞ :=
  setUIntegral_lt_top_of_bddAbove₀ hs (hsc.image_of_continuousOn hf).bddAbove hsm

theorem setUIntegral_lt_top_of_isCompact [TopologicalSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : ContinuousOn f s)
    (hfm : AEMeasurable f (μ.restrict s)) : ∫⁺ x in s, f x ∂μ < ∞ :=
  setUIntegral_lt_top_of_bddAbove hs (hsc.image_of_continuousOn hf).bddAbove hfm

end Basic

end MeasureTheory
