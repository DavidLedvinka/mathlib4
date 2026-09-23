/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Division for interval_dyadic_real

This file defines division of dyadic intervals, rounding each finite output endpoint once, using
the `prec` parameter. In particular, it does not first round a reciprocal and then multiply.
Division by zero follows the real-number convention `x / 0 = 0`.
-/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

attribute [local grind unfold] WithBot.some WithTop.some
attribute [local grind norm ←] WithBot.coe_zero WithTop.coe_zero
  WithBot.none_eq_bot WithTop.none_eq_top
attribute [local grind norm] WithBot.coe_le_coe WithTop.coe_le_coe
attribute [local grind =] WithBot.coe_le_iff WithTop.le_coe_iff
  WithBot.lt_iff_exists WithTop.lt_iff_exists
local grind_pattern Dyadic.toReal_le_toReal => a ≤ b
local grind_pattern Dyadic.toReal_lt_toReal => a < b
attribute [local grind norm] div_eq_mul_inv
attribute [local grind =] inv_nonneg inv_nonpos inv_le_inv₀ inv_le_inv_of_neg

/-- Divide dyadic interval bounds, rounding upward when `up` is true and downward otherwise.
A finite numerator divided by an infinite denominator gives the limiting bound zero; an infinite
numerator gives an infinite bound. The sign cases in `div` never divide two infinite bounds. -/
def divBound (up : Bool) (a b : Option Dyadic) (prec : ℕ) : Option Dyadic :=
  match a, b with
  | none, _ => none
  | some _, none => some 0
  | some a, some b => some (Dyadic.divRound up a b prec)

theorem map_divBound_le (a b : Option Dyadic) (prec : ℕ) {z : ℝ}
    (hdiv : ∀ x y, a = some x → b = some y → x.toReal / y.toReal ≤ z)
    (hzero : ∀ x, a = some x → b = none → 0 ≤ z) :
    WithBot.map Dyadic.toReal (divBound false a b prec) ≤ z := by
  rcases a with _ | a
  · exact bot_le
  rcases b with _ | b <;> apply WithBot.coe_le_coe.mpr
  · simpa using hzero a rfl rfl
  exact (Dyadic.toReal_divDown_le a b prec).trans (hdiv a b rfl rfl)

theorem le_map_divBound (a b : Option Dyadic) (prec : ℕ) {z : ℝ}
    (hdiv : ∀ x y, a = some x → b = some y → z ≤ x.toReal / y.toReal)
    (hzero : ∀ x, a = some x → b = none → z ≤ 0) :
    z ≤ WithTop.map Dyadic.toReal (divBound true a b prec) := by
  rcases a with _ | a
  · exact le_top
  rcases b with _ | b <;> apply WithTop.coe_le_coe.mpr
  · simpa using hzero a rfl rfl
  exact (hdiv a b rfl rfl).trans (Dyadic.le_toReal_divUp a b prec)

/-- Divide dyadic intervals, rounding finite quotient bounds outward to the `2⁻prec` grid.

When the denominator excludes zero, select the two extremal quotients directly. Infinite
denominator bounds contribute the limiting value zero. When the denominator contains zero,
include the value `x / 0 = 0` as well as the nonzero quotients. For nonempty inputs, the result is
the smallest closed interval on this grid containing all real quotients. -/
def div (I J : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  if 0 < J.lb then
    if 0 ≤ I.lb then
      ⟨divBound false I.lb J.ub prec, divBound true I.ub J.lb prec⟩
    else if I.ub ≤ 0 then
      ⟨divBound false I.lb J.lb prec, divBound true I.ub J.ub prec⟩
    else
      ⟨divBound false I.lb J.lb prec, divBound true I.ub J.lb prec⟩
  else if J.ub < 0 then
    if 0 ≤ I.lb then
      ⟨divBound false I.ub J.ub prec, divBound true I.lb J.lb prec⟩
    else if I.ub ≤ 0 then
      ⟨divBound false I.ub J.lb prec, divBound true I.lb J.ub prec⟩
    else
      ⟨divBound false I.ub J.ub prec, divBound true I.lb J.ub prec⟩
  else if I.lb = 0 ∧ I.ub = 0 ∨ J.lb = 0 ∧ J.ub = 0 then
    Interval.singleton 0
  else if 0 ≤ J.lb then
    if 0 ≤ I.lb then Interval.Ici 0
    else if I.ub ≤ 0 then Interval.Iic 0
    else Interval.univ Dyadic
  else if J.ub ≤ 0 then
    if 0 ≤ I.lb then Interval.Iic 0
    else if I.ub ≤ 0 then Interval.Ici 0
    else Interval.univ Dyadic
  else
    Interval.univ Dyadic

@[inclusion_op interval_dyadic_real]
theorem div_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x / y ∈ div I J prec := by
  have hzero := Dyadic.toReal_zero
  unfold div
  split_ifs
  -- A positive denominator reverses the order of its endpoints under reciprocation.
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul, mul_nonneg]
    · apply le_map_divBound <;> grind [mul_le_mul]
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonpos_of_nonneg]
    · apply le_map_divBound <;>
        grind [mul_le_mul_of_nonpos_of_nonneg, mul_nonpos_of_nonpos_of_nonneg]
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonpos_of_nonneg'']
    · apply le_map_divBound <;> grind [mul_le_mul]
  -- The same reversal holds for a negative denominator.
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonneg_of_nonpos]
    · apply le_map_divBound <;>
        grind [mul_le_mul_of_nonneg_of_nonpos, mul_nonpos_of_nonneg_of_nonpos]
  · constructor
    · apply map_divBound_le <;>
        grind [mul_le_mul_of_nonpos_of_nonpos', mul_nonneg_of_nonpos_of_nonpos]
    · apply le_map_divBound <;> grind [mul_le_mul_of_nonpos_of_nonpos]
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonneg_of_nonpos']
    · apply le_map_divBound <;> grind [mul_le_mul_of_nonpos_of_nonpos]
  -- Denominators containing zero give zero, a half-line, or the universal interval.
  all_goals
    grind [Interval.singleton, Interval.Ici, Interval.Iic, Interval.univ,
      mul_nonneg, mul_nonneg_of_nonpos_of_nonpos,
      mul_nonpos_of_nonneg_of_nonpos, mul_nonpos_of_nonpos_of_nonneg]

end Inclusion.IntervalDyadicReal
