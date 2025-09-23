import Mathlib

open MeasureTheory ProbabilityTheory Measure Function Complex

open scoped ENNReal

namespace ProbabilityTheory

section Fintype

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma moment_def (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) :
    moment X p μ = μ[X ^ p] := rfl

lemma moment_one (X : Ω → ℝ) (μ : Measure Ω) :
    moment X 1 μ = μ[X] := by simp [moment]

variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]

instance IsFiniteMeasure.count_withDensity {p : α → ℝ} :
    IsFiniteMeasure (count.withDensity (ENNReal.ofReal ∘ p)) := by
  apply isFiniteMeasure_withDensity
  simp [lintegral_fintype]

theorem HasLaw.lintegral_comp_fintype {X : Ω → α} {μ : Measure α}
    {f : α → ℝ≥0∞} (hX : HasLaw X μ P) :
    ∫⁻ ω, f (X ω) ∂P = ∑ a : α, f a * μ {a} := by
  rw [hX.lintegral_comp (by fun_prop (maxTransitionDepth := 2)), lintegral_fintype]


theorem HasLaw.lintegral_comp_fintype_count_withDensity {X : Ω → α} {p : α → ℝ≥0∞}
    {f : α → ℝ≥0∞} (hX : HasLaw X (count.withDensity p) P) :
    ∫⁻ ω, f (X ω) ∂P = ∑ a : α, f a * p a := by
  rw [hX.lintegral_comp_fintype]
  simp

theorem HasLaw.integral_comp_fintype {X : Ω → α} {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → E} (hX : HasLaw X μ P) :
    P[f ∘ X] = ∑ a : α, μ.real {a} • f a := by
  rw [hX.integral_comp (by fun_prop), integral_fintype _ .of_finite]

theorem HasLaw.integral_comp_fintype_count_withDensity {X : Ω → α} {p : α → ℝ}
    (ppos : 0 ≤ p) {f : α → E} (hX : HasLaw X (count.withDensity (ENNReal.ofReal ∘ p)) P) :
    P[f ∘ X] = ∑ a : α, p a • f a := by
  rw [hX.integral_comp_fintype]
  simp [Measure.real, fun x ↦ ENNReal.toReal_ofReal (ppos x)]

variable {β : Type*} {mβ : MeasurableSpace β}

-- Optimize measurability assumptions
theorem HasLaw.lintegral_comp_fintype_map {X : Ω → β} {μ : Measure α} {φ : α → β}
    {f : β → ℝ≥0∞} (hφ : Measurable φ) (hf : Measurable f) (hX : HasLaw X (μ.map φ) P) :
    ∫⁻ ω, f (X ω) ∂P = ∑ a : α, f (φ a) * μ {a} := by
  rw [hX.lintegral_comp hf.aemeasurable, lintegral_map hf hφ, lintegral_fintype]

-- Optimize measurability assumptions
theorem HasLaw.lintegral_comp_fintype_map_count_withDensity {X : Ω → β} {p : α → ℝ≥0∞}
    {φ : α → β} {f : β → ℝ≥0∞} (hf : Measurable f) (hφ : Measurable φ)
    (hX : HasLaw X ((count.withDensity p).map φ) P) :
    ∫⁻ ω, f (X ω) ∂P = ∑ a : α, f (φ a) * p a := by
  rw [hX.lintegral_comp_fintype_map hφ hf]
  simp

-- Optimize measurability assumptions
theorem HasLaw.integral_comp_fintype_map {X : Ω → β} {μ : Measure α} [IsFiniteMeasure μ]
    {φ : α → β} {f : β → E} (hφ : Measurable φ) (hf : AEStronglyMeasurable f (μ.map φ))
    (hX : HasLaw X (μ.map φ) P) :
    P[f ∘ X] =  ∑ a : α, μ.real {a} • f (φ a) := by
  rw [hX.integral_comp hf, integral_map hφ.aemeasurable hf, integral_fintype _ .of_finite]

-- Optimize measurability assumptions
theorem HasLaw.integral_comp_fintype_map_count_withDensity {X : Ω → β} {p : α → ℝ}
    (ppos : 0 ≤ p) {φ : α → β} {f : β → E} (hφ : Measurable φ)
    (hf : AEStronglyMeasurable f ((count.withDensity (ENNReal.ofReal ∘ p)).map φ))
    (hX : HasLaw X ((count.withDensity (ENNReal.ofReal ∘ p)).map φ) P) :
    P[f ∘ X] = ∑ a : α, p a • f (φ a) := by
  rw [hX.integral_comp_fintype_map hφ hf]
  simp [Measure.real, fun x ↦ ENNReal.toReal_ofReal (ppos x)]

end Fintype

section Bernoulli

/- # Bernoulli Distribution -/

/- Bernoulli Distribution on `Fin 2` -/

def fin_bernoulli_PMFReal (p : ℝ) (x : Fin 2) : ℝ := if x = 1 then p else 1 - p

def fin_bernoulli_PMF (p : ℝ) : Fin 2 → ℝ≥0∞ := ENNReal.ofReal ∘ (fin_bernoulli_PMFReal p)

lemma fin_bernoulli_PMF_eq (p : ℝ) (x : Fin 2) :
    fin_bernoulli_PMF p x = ENNReal.ofReal (if x = 1 then p else 1 - p) := rfl

noncomputable def fin_bernoulli (p : ℝ) : Measure (Fin 2) :=
  count.withDensity (fin_bernoulli_PMF p)

lemma fin_bernoulli_def (p : ℝ) : fin_bernoulli p = count.withDensity (fin_bernoulli_PMF p) := by
  rfl

lemma fin_bernoulli_PMFReal_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (x : Fin 2) :
    0 ≤ fin_bernoulli_PMFReal p x := by
  fin_cases x <;> (simp [fin_bernoulli_PMFReal]; bound)

lemma fin_bernoulli_PMFReal_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) (x : Fin 2) :
    0 < fin_bernoulli_PMFReal p x := by
  fin_cases x <;> (simp [fin_bernoulli_PMFReal]; bound)

theorem isProbabilityMeasure_fin_bernoulli {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (fin_bernoulli p) where
  measure_univ := by
    -- should be automatable (eventually ?)
    have : ENNReal.ofReal (1 - p) + ENNReal.ofReal p = 1 := by
      rw [← ENNReal.ofReal_add (by bound) (by bound), ← ENNReal.ofReal_one]
      simp
    simp [fin_bernoulli_def, lintegral_fintype, fin_bernoulli_PMF_eq, this]

/- Bernoulli Distribution on `ℝ` -/

noncomputable def real_bernoulli (p : ℝ) : Measure ℝ :=
  (fin_bernoulli p).map (↑)

lemma real_bernoulli_def (p : ℝ) :
  real_bernoulli p = (count.withDensity (fin_bernoulli_PMF p)).map (↑) := rfl

theorem isProbabilityMeasure_real_bernoulli {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (real_bernoulli p) :=
  have := isProbabilityMeasure_fin_bernoulli hp₀ hp₁
  isProbabilityMeasure_map AEMeasurable.of_discrete

/- **TODO** Possibly simplifiable by making lemmas-/
/- Characteristic Function of Bernoulli Measure -/
theorem real_bernoulli_charFun_eq (p t : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    charFun (real_bernoulli p) t = (1 - p) + p * exp (t * I) := by
  -- should be automatable (eventually ?)
  rw [charFun_apply, real_bernoulli_def, integral_map, integral_fintype]
  · simp [Measure.real, fin_bernoulli_PMF_eq, ENNReal.toReal_ofReal (r := p) (by bound),
    ENNReal.toReal_ofReal (r := 1 - p) (by bound)]
  · refine ⟨by fun_prop, ?_⟩
    simp [HasFiniteIntegral, lintegral_fintype, fin_bernoulli_PMF_eq]
    finiteness
  all_goals fun_prop (maxTransitionDepth := 2)

/- Bernoulli Random Variables -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {p : ℝ}

protected lemma HasLaw.real_bernoulli_def (hX : HasLaw X (real_bernoulli p) P) :
    HasLaw X ((count.withDensity (fin_bernoulli_PMF p)).map (↑)) P := hX

theorem HasLaw.real_bernoulli_moment_eq_p (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) {n : ℕ} (hn : 1 ≤ n) :
    moment X n P = p := by
  unfold moment
  conv in (X ^ n) => change (· ^ n) ∘ X
  rw [hX.real_bernoulli_def.integral_comp_fintype_map_count_withDensity
    (fin_bernoulli_PMFReal_nonneg hp₀ hp₁) (by fun_prop) (by fun_prop)]
  simp [fin_bernoulli_PMFReal]
  grind

theorem HasLaw.real_bernoulli_mean (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) :
    P[X] = p := by
  rw [← moment_one, hX.real_bernoulli_moment_eq_p hp₀ hp₁ (by rfl)]

#check isProbabilityMeasure_map
#check MeasureTheory.Measure.isFiniteMeasure_map

theorem HasLaw.real_bernoulli_variance (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hX : HasLaw X (real_bernoulli p) P) :
    Var[X; P] = p * (1 - p) := by
  -- need to prove lemmas for premap `isProbabilityMeasure` and `isFiniteMeasure`
  -- rw [variance_eq_sub]
  sorry

end Bernoulli

/- # Zero or One Distribution (for Yael) -/

section Yael

/- Zero or One Measures -/

def zero_or_one_PMF (a b : ℝ≥0∞) (x : Fin 2) : ℝ≥0∞ := if x = 1 then a else b

noncomputable def zero_or_one (a b : ℝ≥0∞) : Measure (Fin 2) :=
  count.withDensity (zero_or_one_PMF a b)

lemma zero_or_one_def (a b : ℝ≥0∞) :
    zero_or_one a b = count.withDensity (zero_or_one_PMF a b) := by
  rfl

noncomputable def real_zero_or_one (a b : ℝ≥0∞) : Measure ℝ :=
  (zero_or_one a b).map (↑)

lemma real_zero_or_one_def (a b : ℝ≥0∞) :
  real_zero_or_one a b = (count.withDensity (zero_or_one_PMF a b)).map (↑) := rfl

/- Zero or One Random Variables -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {p : ℝ}

lemma HasLaw.zero_or_one_ae_zero_or_one (a b : ℝ≥0∞) (hX : HasLaw X (real_zero_or_one a b) P) :
    ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1 := by
  change P (X ⁻¹' {0, 1}ᶜ) = 0
  rw [← Measure.map_apply₀ hX.aemeasurable (by simp), hX.map_eq]
  sorry

lemma HasLaw.zero_or_one_integral (a b : ℝ≥0∞) (hX : HasLaw X (real_zero_or_one a b) P) :
    P[X] = (P {ω | X ω = 1}).toReal := by sorry


lemma zero_or_one_ae_hasLaw_zero_or_one (hXmeas : AEMeasurable X P)
    (hX : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) :
    HasLaw X (real_zero_or_one (P {ω | X ω = 1}) (P {ω | X ω = 0})) P where
  map_eq := by
    apply ext_of_lintegral
    intro f hf
    rw [lintegral_map' hf.aemeasurable hXmeas, ← lintegral_add_compl (A := X ⁻¹' {0, 1})]
    have : ∫⁻ (ω : Ω) in {ω | X ω = 1}, f (X ω) ∂P = f 0 * (P {ω | X ω = 0}) := by
      sorry

theorem zero_or_one_ae_integral (hXmeas : AEMeasurable X P) (hX : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) :
    P[X] = (P {ω | X ω = 1}).toReal :=
  (zero_or_one_ae_hasLaw_zero_or_one hXmeas hX).zero_or_one_integral

end Yael

end ProbabilityTheory
