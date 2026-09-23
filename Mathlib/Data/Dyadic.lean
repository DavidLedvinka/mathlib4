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

/-- Divide `a` by `b`, rounding upward when `up` is true and downward otherwise, to a multiple
of `2⁻prec`. Returns zero when `b = 0`.

This uses unsigned mantissa division, rounding the magnitude toward or away from zero before
restoring the sign. The quotient in grid units has magnitude
`(num : ℚ) / den * 2 ^ (prec + bk - ak)`. When the grid is fine enough, exact quotients are returned
before shifting, avoiding construction and normalization of a potentially large power of two. -/
def divRound (up : Bool) (a b : Dyadic) (prec : Int) : Dyadic :=
  match a, b with
  | .zero, _ | _, .zero => 0
  | .ofOdd an ak ha, .ofOdd bn bk hb =>
    -- `decNonneg` inspects the constructors without the arithmetic of integer order tests.
    let negative := an.decNonneg.decide != bn.decNonneg.decide
    let num := an.natAbs
    let den := bn.natAbs
    -- Negative quotients reverse the rounding direction for their magnitudes.
    let away := up != negative
    let magnitude :=
      match prec + bk - ak with
      | .ofNat s =>
        -- Reuse this quotient when no shift is needed.
        let q := num / den
        if h : q * den = num then
          -- An exact quotient of odd mantissas is already normalized.
          .ofOdd (q : Int) (ak - bk) (by
            have := congrArg (fun n : Nat => n % 2) h
            grind [Nat.mul_mod, Int.natAbs_emod_two])
        else
          -- An odd denominator cannot divide `num * 2^s` unless it already divides `num`.
          let q := if s = 0 then q else (num <<< s) / den
          .ofIntWithPrec (if away then q + 1 else q : Nat) prec
      | .negSucc s =>
        -- Divide after shifting right instead of constructing a large shifted denominator.
        -- Since `num` is odd, the division in grid units cannot be exact.
        let q := (num >>> (s + 1)) / den
        .ofIntWithPrec (if away then q + 1 else q : Nat) prec
    if negative then -magnitude else magnitude

private theorem toRat_natDiv_bounds (n d : ℕ) (prec : ℤ) (hd : 0 < d) :
    (ofIntWithPrec (n / d : ℕ) prec).toRat ≤ (n : ℚ) / d * 2 ^ (-prec) ∧
      (n : ℚ) / d * 2 ^ (-prec) ≤ (ofIntWithPrec (n / d + 1 : ℕ) prec).toRat := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  simp only [toRat_ofIntWithPrec_eq_mul_two_pow,
    mul_le_mul_iff_left₀ (zpow_pos (by decide : (0 : ℚ) < 2) _),
    le_div_iff₀ hd', div_le_iff₀ hd']
  constructor
  · exact_mod_cast Nat.div_mul_le_self n d
  · norm_cast
    simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm] using
      (Nat.lt_mul_div_self_add hd (x := n)).le

private theorem toRat_div_ofOdd (an ak bn bk : ℤ) (ha : an % 2 = 1) (hb : bn % 2 = 1) :
    (ofOdd an ak ha).toRat / (ofOdd bn bk hb).toRat =
      if an.decNonneg.decide != bn.decNonneg.decide then
        -((an.natAbs : ℚ) / bn.natAbs * 2 ^ (bk - ak))
      else (an.natAbs : ℚ) / bn.natAbs * 2 ^ (bk - ak) := by
  rw [toRat_ofOdd_eq_mul_two_pow, toRat_ofOdd_eq_mul_two_pow,
    zpow_sub₀ (by decide : (2 : ℚ) ≠ 0)]
  cases an <;> cases bn <;>
    simp only [Int.decNonneg, Decidable.decide, Int.natAbs] <;>
    simp [-neg_add_rev, Int.negSucc_eq, div_eq_mul_inv,
      _root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]

theorem toRat_divRound_bounds (a b : Dyadic) (prec : ℤ) :
    (divRound false a b prec).toRat ≤ a.toRat / b.toRat ∧
      a.toRat / b.toRat ≤ (divRound true a b prec).toRat := by
  unfold divRound
  rcases a with _ | ⟨an, ak, ha⟩
  · simp
  rcases b with _ | ⟨bn, bk, hb⟩
  · simp
  have hd : 0 < bn.natAbs := Int.natAbs_pos.mpr (by omega)
  rw [toRat_div_ofOdd]
  generalize hnegative : (an.decNonneg.decide != bn.decNonneg.decide) = negative
  set n := an.natAbs with ← hn
  set d := bn.natAbs with ← hden
  cases hs : prec + bk - ak with
  | ofNat s =>
    simp only [hnegative, hn, hden, hs]
    by_cases heq : n / d * d = n
    · simp only [dite_eq_left heq]
      have hq : ((n / d : ℕ) : ℚ) = (n : ℚ) / d := by
        apply (eq_div_iff (show (d : ℚ) ≠ 0 by exact_mod_cast hd.ne')).mpr
        exact_mod_cast heq
      cases negative <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, toRat_neg,
          toRat_ofOdd_eq_mul_two_pow, Int.cast_natCast, neg_sub, hq] <;> simp
    · simp only [dite_eq_right heq]
      have hpow : bk - ak = (s : ℤ) - prec := by
        simp only [Int.ofNat_eq_natCast] at hs
        omega
      have hq : (if s = 0 then n / d else (n <<< s) / d) = (n <<< s) / d := by
        split_ifs <;> simp_all
      rw [hq]
      have hbounds := toRat_natDiv_bounds (n <<< s) d prec hd
      have hscale : ((n <<< s : ℕ) : ℚ) / d * 2 ^ (-prec) =
          (n : ℚ) / d * 2 ^ (bk - ak) := by
        simp [hpow, Nat.shiftLeft_eq, zpow_sub₀, div_eq_mul_inv,
          _root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]
      rw [hscale] at hbounds
      cases negative <;> simpa [-neg_ofIntWithPrec, and_comm] using hbounds
  | negSucc s =>
    simp only [hnegative, hn, hden, hs]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
    have hpow : bk - ak = -((s + 1 : ℕ) : ℤ) - prec := by omega
    have hbounds := toRat_natDiv_bounds n (2 ^ (s + 1) * d) prec
      (Nat.mul_pos (Nat.two_pow_pos _) hd)
    have hscale : (n : ℚ) / (2 ^ (s + 1) * d) * 2 ^ (-prec) =
        (n : ℚ) / d * 2 ^ (bk - ak) := by
      rw [hpow, zpow_sub₀ (by decide : (2 : ℚ) ≠ 0)]
      simp only [zpow_neg, zpow_natCast]
      simp [div_eq_mul_inv,
        _root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hbounds
    rw [hscale] at hbounds
    cases negative <;> simpa [-neg_ofIntWithPrec, and_comm] using hbounds

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
