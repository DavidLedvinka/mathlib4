/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Experimental dyadic interval operations for real expressions

This file retains preliminary multiplication and division operations used by the experimental
inclusion-tactic examples. They are kept outside the shipped `real.dyadic` extension family until
their computational implementations are improved.
-/

set_option linter.style.header false

@[expose] public section

namespace Inclusion

def min4 (a b c d : Dyadic) : Dyadic := min (min a b) (min c d)

def max4 (a b c d : Dyadic) : Dyadic := max (max a b) (max c d)

def mul (x y : Interval Dyadic) : Interval Dyadic :=
  match x, y with
  | ⟨some xl, some xu⟩, ⟨some yl, some yu⟩ =>
      ⟨some (min4 (xl * yl) (xl * yu) (xu * yl) (xu * yu)),
        some (max4 (xl * yl) (xl * yu) (xu * yl) (xu * yu))⟩
  | _, _ => Interval.univ Dyadic

def divisionPrecision : Int := 20

def lowerApprox (q : ℚ) : Dyadic := q.toDyadic divisionPrecision

def upperApprox (q : ℚ) : Dyadic :=
  let d := lowerApprox q
  if d.toRat = q then d else d + Dyadic.ofIntWithPrec 1 divisionPrecision

def inv (x : Interval Dyadic) : Interval Dyadic :=
  match x with
  | ⟨some xl, some xu⟩ =>
      if 0 < xl ∨ xu < 0 then
        ⟨some (lowerApprox (1 / xu.toRat)), some (upperApprox (1 / xl.toRat))⟩
      else
        Interval.univ Dyadic
  | _ => Interval.univ Dyadic

def div (x y : Interval Dyadic) : Interval Dyadic := mul x (inv y)

@[simp]
lemma toReal_mul (a b : Dyadic) :
    Dyadic.toReal (a * b) = Dyadic.toReal a * Dyadic.toReal b := by
  simp [Dyadic.toReal, Dyadic.toRat_mul]

@[simp]
lemma toReal_zero : Dyadic.toReal 0 = 0 := by
  simp [Dyadic.toReal]

lemma toReal_lt_toReal {a b : Dyadic} : Dyadic.toReal a < Dyadic.toReal b ↔ a < b := by
  simp [Dyadic.toReal]

lemma min4_mul_le {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have ha : min (a * c) (a * d) ≤ a * y := by
    rcases le_total 0 a with ha | ha
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 ha)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 ha)
  have hb : min (b * c) (b * d) ≤ b * y := by
    rcases le_total 0 b with hb | hb
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hb)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 hb)
  apply (min_le_min ha hb).trans
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy)

lemma mul_le_max4 {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have ha : a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with ha | ha
    · exact (mul_le_mul_of_nonneg_left hy.2 ha).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hy.1 ha).trans (le_max_left _ _)
  have hb : b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with hb | hb
    · exact (mul_le_mul_of_nonneg_left hy.2 hb).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hy.1 hb).trans (le_max_left _ _)
  apply (show x * y ≤ max (a * y) (b * y) by
    rcases le_total 0 y with hy | hy
    · exact (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)).trans
  exact max_le_max ha hb

@[inclusionOp real.dyadic]
theorem mul_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r * s ∈ mul x y := by
  match x, y with
  | ⟨some xl, some xu⟩, ⟨some yl, some yu⟩ =>
    have hx : Dyadic.toReal xl ≤ r ∧ r ≤ Dyadic.toReal xu :=
      ⟨WithBot.coe_le_coe.mp hrx.1, WithTop.coe_le_coe.mp hrx.2⟩
    have hy : Dyadic.toReal yl ≤ s ∧ s ≤ Dyadic.toReal yu :=
      ⟨WithBot.coe_le_coe.mp hsy.1, WithTop.coe_le_coe.mp hsy.2⟩
    constructor
    · exact WithBot.coe_le_coe.mpr <| by
        simpa [min4] using min4_mul_le hx hy
    · exact WithTop.coe_le_coe.mpr <| by
        simpa [max4] using mul_le_max4 hx hy
  | ⟨⊥, _⟩, _ | ⟨some _, ⊤⟩, _ | ⟨some _, some _⟩, ⟨⊥, _⟩
    | ⟨some _, some _⟩, ⟨some _, ⊤⟩ =>
    exact mem_univ _

lemma lowerApprox_le (q : ℚ) : Dyadic.toReal (lowerApprox q) ≤ (q : ℝ) := by
  exact Rat.cast_le.mpr Rat.toRat_toDyadic_le

lemma le_upperApprox (q : ℚ) : (q : ℝ) ≤ Dyadic.toReal (upperApprox q) := by
  simp only [upperApprox]
  split_ifs with h
  · rw [Dyadic.toReal]
    exact Rat.cast_le.mpr h.symm.le
  · rw [Dyadic.toReal, Dyadic.toRat_add]
    exact Rat.cast_le.mpr
      (by simpa [lowerApprox] using
        (Rat.lt_toRat_toDyadic_add (x := q) (prec := divisionPrecision)).le)

theorem inv_mem {r : ℝ} {x : Interval Dyadic} (hrx : r ∈ x) : 1 / r ∈ inv x := by
  match x with
  | ⟨some xl, some xu⟩ =>
    by_cases hsign : 0 < xl ∨ xu < 0
    · have hxlr : Dyadic.toReal xl ≤ r := WithBot.coe_le_coe.mp hrx.1
      have hrxu : r ≤ Dyadic.toReal xu := WithTop.coe_le_coe.mp hrx.2
      simp only [inv, hsign, if_pos]
      constructor
      · apply WithBot.coe_le_coe.mpr
        apply (lowerApprox_le (1 / xu.toRat)).trans
        rw [Rat.cast_div, Rat.cast_one]
        rcases hsign with hxl | hxu
        · have hxl' : 0 < Dyadic.toReal xl := by
            simpa using toReal_lt_toReal.mpr hxl
          exact one_div_le_one_div_of_le (hxl'.trans_le hxlr) hrxu
        · have hxu' : Dyadic.toReal xu < 0 := by
            simpa using toReal_lt_toReal.mpr hxu
          exact one_div_le_one_div_of_neg_of_le hxu' hrxu
      · apply WithTop.coe_le_coe.mpr
        apply (show 1 / r ≤ (1 / xl.toRat : ℚ) from ?_).trans (le_upperApprox _)
        rw [Rat.cast_div, Rat.cast_one]
        rcases hsign with hxl | hxu
        · have hxl' : 0 < Dyadic.toReal xl := by
            simpa using toReal_lt_toReal.mpr hxl
          exact one_div_le_one_div_of_le hxl' hxlr
        · have hxu' : Dyadic.toReal xu < 0 := by
            simpa using toReal_lt_toReal.mpr hxu
          exact one_div_le_one_div_of_neg_of_le (hrxu.trans_lt hxu') hxlr
    · simpa [inv, hsign] using mem_univ (1 / r)
  | ⟨⊥, _⟩ | ⟨some _, ⊤⟩ => simpa [inv] using mem_univ (1 / r)

@[inclusionOp real.dyadic]
theorem div_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r / s ∈ div x y := by
  rw [div_eq_mul_one_div]
  exact mul_mem hrx (inv_mem hsy)

end Inclusion
