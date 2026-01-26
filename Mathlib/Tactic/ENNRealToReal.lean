import Mathlib

/- Generalization Ideas

Suppose we have a function `f : α → β`. We want to replace
`b : β` with `f a = b`.

We need to deal with the case that `¬ ∃ a, f a = b`.

We may want to record some properties of `a` given by the proof.
(This could go beyond whats needed, for example `0 < a` when only
`0 ≤ a` is originally needed)

-/

open ENNReal

@[simp]
lemma ENNReal.mul_top_of_pos (a : ℝ≥0∞) (h : 0 < a) : a * ∞ = ∞ := by
  simp [Ne.symm (ne_of_lt h)]

@[simp]
/- Rename this one to `top_div` and the current one to `top'` so it matches `mul_top` -/
lemma ENNReal.top_div' (a : ℝ≥0∞) (h : a ≠ ∞) : ∞ / a = ∞ := by
  simp [div_eq_mul_inv, h]

@[simp]
/- Rename this one to `top` and the other one to `top'` -/
lemma ENNReal.top_div_of_finite (a : ℝ≥0∞) (h : a < ∞) : ∞ / a = ∞ := by
  simp [LT.lt.ne_top h]

/-
High Level Idea
===============

Convert `a : ℝ≥0∞` to `ENNReal.ofReal a`.
-/

/- STEP 1: Try to prove `a ≠ ⊤` with `finiteness`.-/

/- STEP 2: Try to prove `a = ⊤` case is trivial by plugging it in and `simp`.
  But we also may need to split on the following cases. -/

/- CONVERSION STEP -/

/- Case split for `a : ℝ≥0∞` on `a ≠ 0` or `a = 0` -/
example (a : ℝ≥0∞) (h : a ≠ 0) : a * ∞ = ∞ := by simp [h]
example (a : ℝ≥0∞) (h : 0 < a) : a * ∞ = ∞ := by simp [h] -- this one doesn't work but should
example (a : ℝ≥0∞) (h : a = 0) : a * ∞ = 0 := by simp [h]

#check ENNReal.div_eq_zero_iff

/- Case split for `a : ℝ≥0∞` on `a ≠ ∞` or `a = ∞`. -/
example (a : ℝ≥0∞) (h : a ≠ ∞) : ∞ / a = ∞ := by simp [h]
example (a : ℝ≥0∞) (h : a < ∞) : ∞ / a = ∞ := by simp [h]
example (a : ℝ≥0∞) (h : a = ∞) : ∞ / a = 0 := by simp [h]

/- `a / ∞ = 0` always so no case splitting needed. -/

/- Case split for `p : ℝ` on `0 < p`, or `p = 0`, or `p < 0` -/
example (p : ℝ) (h : 0 < p) : ∞ ^ p = ∞ := by simp [h]
example (p : ℝ) (h : p = 0) : ∞ ^ p = 1 := by simp [h]
example (p : ℝ) (h : p < 0) : ∞ ^ p = 0 := by simp [h]



/- NORMALIZE STEP -/
