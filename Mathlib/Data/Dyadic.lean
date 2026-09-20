/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

/-!
# Dyadic rationals

This file provides general API for Dyadic rationals that are used in Mathlib but not available in
core.
-/

@[expose] public section

instance : LinearOrder Dyadic where
  le_refl := Std.IsPreorder.le_refl
  le_trans := Std.IsPreorder.le_trans
  le_antisymm := Std.IsPartialOrder.le_antisymm
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  le_total := Std.IsLinearOrder.le_total
  toDecidableLE := Dyadic.instDecidableLE

instance : AddCommGroup Dyadic where
  nsmul := (· * ·)
  zsmul := (· * ·)
  add_zero := Dyadic.add_zero
  zero_add := Dyadic.zero_add
  add_assoc := Dyadic.add_assoc
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel := Dyadic.neg_add_cancel
  add_comm := Dyadic.add_comm
  nsmul_zero := by grind
  nsmul_succ := by grind
  zsmul_zero' := by grind
  zsmul_succ' := by grind
  zsmul_neg' := by grind

namespace Dyadic

/-- One unit on the dyadic grid with precision `prec`. -/
def step (prec : Int) : Dyadic := .ofOdd 1 prec (by decide)

theorem ofIntWithPrec_one (prec : Int) : ofIntWithPrec 1 prec = step prec := by
  simp [step, ofIntWithPrec, Int.trailingZeros_eq_zero_of_mod_eq (show 1 % 2 = 1 by decide)]

/-- Divide dyadics, rounding to the `2⁻prec` grid in the direction selected by `up`.
The odd mantissas let us detect exact quotients before shifting and avoid a remainder calculation
when the requested grid is coarser than the quotient's exponent. -/
def divRound (up : Bool) (a b : Dyadic) (prec : Int) : Dyadic :=
  match a, b with
  | .zero, _ | _, .zero => 0
  | .ofOdd an ak ha, .ofOdd bn bk hb =>
    let num := if bn < 0 then -an else an
    let den := bn.natAbs
    match prec + bk - ak with
    | .ofNat s =>
      let q := num / den
      if h : q * den = num then
        -- An exact quotient of odd mantissas is already normalized.
        .ofOdd q (ak - bk) (by
          have := congrArg (· % 2) h
          grind [Int.mul_emod, Int.natAbs_emod_two, Int.neg_emod_two])
      else
        -- Multiplying by a power of two cannot make an inexact quotient of odd mantissas exact.
        let q := if s = 0 then q else (num <<< s) / den
        .ofIntWithPrec (if up then q + 1 else q) prec
    | .negSucc s =>
      -- Shift the numerator right instead of constructing a large shifted denominator.
      -- The odd numerator makes this quotient inexact, including for negative numerators.
      let q := (num >>> (s + 1)) / den
      .ofIntWithPrec (if up then q + 1 else q) prec

private theorem toRat_ediv_bounds (n d prec : ℤ) (hd : 0 < d) :
    (ofIntWithPrec (n / d) prec).toRat ≤ (n : ℚ) / d * 2 ^ (-prec) ∧
      (n : ℚ) / d * 2 ^ (-prec) ≤ (ofIntWithPrec (n / d + 1) prec).toRat := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hlow : ((n / d : ℤ) : ℚ) ≤ (n : ℚ) / d := by
    rw [le_div_iff₀ hd']
    exact_mod_cast Int.ediv_mul_le n hd.ne'
  have hupp : (n : ℚ) / d ≤ ((n / d : ℤ) : ℚ) + 1 := by
    apply le_of_lt
    rw [div_lt_iff₀ hd']
    exact_mod_cast Int.lt_ediv_add_one_mul_self n hd
  constructor
  · simpa [toRat_ofIntWithPrec_eq_mul_two_pow] using
      mul_le_mul_of_nonneg_right hlow (le_of_lt (zpow_pos (by decide : (0 : ℚ) < 2) (-prec)))
  · simpa [toRat_ofIntWithPrec_eq_mul_two_pow] using
      mul_le_mul_of_nonneg_right hupp (le_of_lt (zpow_pos (by decide : (0 : ℚ) < 2) (-prec)))

private theorem toRat_div_ofOdd (an ak bn bk : ℤ) (ha : an % 2 = 1) (hb : bn % 2 = 1) :
    (ofOdd an ak ha).toRat / (ofOdd bn bk hb).toRat =
      ((if bn < 0 then -an else an : ℤ) : ℚ) / bn.natAbs * 2 ^ (bk - ak) := by
  have hsign : ((if bn < 0 then -an else an : ℤ) : ℚ) / bn.natAbs = (an : ℚ) / bn := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    by_cases h : bn < 0
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_nonneg (le_of_not_gt h)]
  rw [hsign, toRat_ofOdd_eq_mul_two_pow, toRat_ofOdd_eq_mul_two_pow,
    zpow_sub₀ (by decide : (2 : ℚ) ≠ 0)]
  simp [div_eq_mul_inv, _root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]

theorem toRat_divRound_bounds (a b : Dyadic) (prec : ℤ) :
    (divRound false a b prec).toRat ≤ a.toRat / b.toRat ∧
      a.toRat / b.toRat ≤ (divRound true a b prec).toRat := by
  cases a with
  | zero => simp [divRound]
  | ofOdd an ak ha =>
    cases b with
    | zero => simp [divRound]
    | ofOdd bn bk hb =>
      have hd : 0 < (bn.natAbs : ℤ) := by
        exact_mod_cast Int.natAbs_pos.mpr (show bn ≠ 0 by omega)
      rw [toRat_div_ofOdd]
      generalize hn : (if bn < 0 then -an else an) = n
      generalize hden : bn.natAbs = d at *
      generalize hs : prec + bk - ak = shift
      cases shift with
      | ofNat s =>
        simp only [divRound, hn, hden, hs]
        by_cases heq : n / (d : ℤ) * d = n
        · simp only [dite_eq_left heq, toRat_ofOdd_eq_mul_two_pow]
          have hq : ((n / d : ℤ) : ℚ) = (n : ℚ) / d := by
            apply (eq_div_iff (show (d : ℚ) ≠ 0 by exact_mod_cast hd.ne')).mpr
            exact_mod_cast heq
          simp [hq]
        · simp only [dite_eq_right heq, Bool.false_eq_true, ite_false, ite_true]
          have hpow : bk - ak = (s : ℤ) - prec := by
            simp only [Int.ofNat_eq_natCast] at hs
            omega
          have hscale : ((n <<< s : ℤ) : ℚ) / d * 2 ^ (-prec) =
              (n : ℚ) / d * 2 ^ (bk - ak) := by
            rw [hpow, Int.shiftLeft_eq, Int.cast_mul, Int.cast_pow,
              zpow_sub₀ (by decide : (2 : ℚ) ≠ 0)]
            simp [div_eq_mul_inv, _root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]
          have hbounds := toRat_ediv_bounds (n <<< s) d prec hd
          simp only [Int.cast_natCast] at hbounds
          rw [hscale] at hbounds
          simpa [show (if s = 0 then n / d else (n <<< s) / d) = (n <<< s) / d by
            split_ifs with h <;> simp_all] using hbounds
      | negSucc s =>
        simp only [divRound, hn, hden, hs, Bool.false_eq_true, ite_false, ite_true]
        rw [Int.shiftRight_eq_div_pow, Int.natCast_pow,
          Int.ediv_ediv_of_nonneg (le_of_lt (pow_pos (by decide) _))]
        have hpow : bk - ak = -((s + 1 : ℕ) : ℤ) - prec := by omega
        have hscale : (n : ℚ) / ((2 ^ (s + 1) * d : ℤ) : ℚ) * 2 ^ (-prec) =
            (n : ℚ) / d * 2 ^ (bk - ak) := by
          rw [hpow, zpow_sub₀ (by decide : (2 : ℚ) ≠ 0)]
          simp only [zpow_neg, zpow_natCast]
          simp [div_eq_mul_inv, _root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]
        have hbounds := toRat_ediv_bounds n (2 ^ (s + 1) * d) prec
          (mul_pos (pow_pos (by decide) _) hd)
        rwa [hscale] at hbounds

/-- Divide `a` by `b`, rounding downward to a multiple of `2⁻prec`. Returns zero when `b = 0`. -/
def divDown (a b : Dyadic) (prec : Int) : Dyadic := divRound false a b prec

theorem toRat_divDown_le (a b : Dyadic) (prec : Int) :
    (divDown a b prec).toRat ≤ a.toRat / b.toRat :=
  (toRat_divRound_bounds a b prec).1

/-- Divide `a` by `b`, rounding upward to a multiple of `2⁻prec`. Returns zero when `b = 0`. -/
def divUp (a b : Dyadic) (prec : Int) : Dyadic := divRound true a b prec

theorem le_toRat_divUp (a b : Dyadic) (prec : Int) :
    a.toRat / b.toRat ≤ (divUp a b prec).toRat :=
  (toRat_divRound_bounds a b prec).2

section Real

/-- Interpret a dyadic rational as a real number. -/
def toReal (d : Dyadic) : ℝ := d.toRat

@[simp]
lemma toReal_zero : toReal 0 = 0 := by simp [toReal]

@[simp]
lemma toReal_natCast (n : ℕ) : toReal (n : Dyadic) = (n : ℝ) := by simp [toReal]

@[simp]
lemma toReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    toReal (ofNat(n) : Dyadic) = (ofNat(n) : ℝ) := by
  rw [← Nat.cast_ofNat (R := Dyadic), ← Nat.cast_ofNat (R := ℝ)]
  exact toReal_natCast n

@[simp]
lemma toReal_intCast (z : ℤ) : toReal (z : Dyadic) = (z : ℝ) := by simp [toReal]

@[simp]
lemma toReal_add (a b : Dyadic) : toReal (a + b) = toReal a + toReal b := by simp [toReal]

@[simp]
lemma toReal_mul (a b : Dyadic) : toReal (a * b) = toReal a * toReal b := by simp [toReal]

@[simp]
lemma toReal_pow (a : Dyadic) (n : ℕ) : toReal (a ^ n) = toReal a ^ n := by
  simpa [toReal] using map_pow (Rat.castHom ℝ) a.toRat n

theorem toReal_divDown_le (a b : Dyadic) (prec : Int) :
    (divDown a b prec).toReal ≤ a.toReal / b.toReal := by
  simpa [toReal] using (Rat.cast_le (K := ℝ)).mpr (toRat_divDown_le a b prec)

theorem le_toReal_divUp (a b : Dyadic) (prec : Int) :
    a.toReal / b.toReal ≤ (divUp a b prec).toReal := by
  simpa [toReal] using (Rat.cast_le (K := ℝ)).mpr (le_toRat_divUp a b prec)

/-- `Dyadic.toReal` as an additive monoid homomorphism. -/
def toRealAddMonoidHom : Dyadic →+ ℝ where
  toFun := toReal
  map_zero' := by simp [toReal]
  map_add' := toReal_add

@[simp]
lemma toReal_le_toReal {a b : Dyadic} : toReal a ≤ toReal b ↔ a ≤ b := by simp [toReal]

@[simp]
lemma toReal_lt_toReal {a b : Dyadic} : toReal a < toReal b ↔ a < b := by simp [toReal]

/-- `Dyadic.toReal` as an order embedding. -/
def toRealOrderEmbedding : Dyadic ↪o ℝ :=
  OrderEmbedding.ofStrictMono toReal fun _ _ h ↦ toReal_lt_toReal.mpr h

end Real

end Dyadic
