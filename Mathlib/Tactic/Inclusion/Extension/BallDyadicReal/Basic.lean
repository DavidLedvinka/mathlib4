/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.BallDyadicReal.Init
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr
import Mathlib.Tactic.Ring

/-!
# Basic inclusion extensions for ball_dyadic_real

This file defines basic operations for the `ball_dyadic_real` inclusion family.
-/

@[expose] public section

namespace Inclusion

namespace BallDyadicReal

section Constants

@[inclusionOp ball_dyadic_real]
theorem natCast_mem (n : ℕ) : (n : ℝ) ∈ Ball.singleton (R := Dyadic) (n : Dyadic) := by
  rw [mem_iff]
  simp [Ball.singleton, Ball.lower, Ball.upper]

@[inclusionOp ball_dyadic_real]
theorem ofNat_mem (n : ℕ) : (OfNat.ofNat n : ℝ) ∈ Ball.singleton (R := Dyadic) (n : Dyadic) := by
  rw [Semiring.toGrindSemiring_ofNat]
  exact natCast_mem n

@[inclusionOp ball_dyadic_real]
theorem intCast_mem (z : ℤ) : (z : ℝ) ∈ Ball.singleton (R := Dyadic) (z : Dyadic) := by
  rw [mem_iff]
  simp [Ball.singleton, Ball.lower, Ball.upper]

end Constants

section Arithmetic

@[simp]
theorem lower_add (B₁ B₂ : Ball Dyadic Dyadic) :
    Dyadic.toReal (B₁.add B₂).lower =
      Dyadic.toReal B₁.lower + Dyadic.toReal B₂.lower := by
  simp [Ball.add, Ball.lower]
  ring

@[simp]
theorem upper_add (B₁ B₂ : Ball Dyadic Dyadic) :
    Dyadic.toReal (B₁.add B₂).upper =
      Dyadic.toReal B₁.upper + Dyadic.toReal B₂.upper := by
  simp [Ball.add, Ball.upper]
  ring

@[simp]
theorem lower_neg (B : Ball Dyadic Dyadic) :
    Dyadic.toReal B.neg.lower = -Dyadic.toReal B.upper := by
  simp [Ball.neg, Ball.lower, Ball.upper]
  ring

@[simp]
theorem upper_neg (B : Ball Dyadic Dyadic) :
    Dyadic.toReal B.neg.upper = -Dyadic.toReal B.lower := by
  simp [Ball.neg, Ball.lower, Ball.upper]
  ring

@[simp]
theorem lower_sub (B₁ B₂ : Ball Dyadic Dyadic) :
    Dyadic.toReal (B₁.sub B₂).lower =
      Dyadic.toReal B₁.lower - Dyadic.toReal B₂.upper := by
  simp [Ball.sub, Ball.lower, Ball.upper]
  ring

@[simp]
theorem upper_sub (B₁ B₂ : Ball Dyadic Dyadic) :
    Dyadic.toReal (B₁.sub B₂).upper =
      Dyadic.toReal B₁.upper - Dyadic.toReal B₂.lower := by
  simp [Ball.sub, Ball.lower, Ball.upper]
  ring

@[inclusionOp ball_dyadic_real]
theorem add_mem {x y : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ B₁) (hy : y ∈ B₂) : x + y ∈ B₁.add B₂ := by
  rw [mem_iff] at hx hy ⊢
  simp only [lower_add, upper_add]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

@[inclusionOp ball_dyadic_real]
theorem neg_mem {x : ℝ} {B : Ball Dyadic Dyadic} (hx : x ∈ B) : -x ∈ B.neg := by
  rw [mem_iff] at hx ⊢
  simp only [lower_neg, upper_neg]
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

@[inclusionOp ball_dyadic_real]
theorem sub_mem {x y : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ B₁) (hy : y ∈ B₂) : x - y ∈ B₁.sub B₂ := by
  rw [mem_iff] at hx hy ⊢
  simp only [lower_sub, upper_sub]
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

end Arithmetic

section Props

@[inclusionOp ball_dyadic_real]
theorem le_mem {x y : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ B₁) (hy : y ∈ B₂) : (x ≤ y) ∈ B₁.le B₂ := by
  rw [mem_iff] at hx hy
  simp only [Ball.le]
  split_ifs with h₁ h₂
  · exact IntervalBool.mem_true <| hx.2.trans <|
      (Dyadic.toReal_le_toReal.mpr h₁).trans hy.1
  · exact IntervalBool.mem_undetermined _
  · apply IntervalBool.mem_false
    intro hxy
    exact h₂ <| Dyadic.toReal_le_toReal.mp <| hx.1.trans <| hxy.trans hy.2

@[inclusionOp ball_dyadic_real]
theorem lt_mem {x y : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ B₁) (hy : y ∈ B₂) : (x < y) ∈ B₁.lt B₂ := by
  rw [mem_iff] at hx hy
  simp only [Ball.lt]
  split_ifs with h₁ h₂
  · exact IntervalBool.mem_true <| hx.2.trans_lt <|
      (Dyadic.toReal_lt_toReal.mpr h₁).trans_le hy.1
  · exact IntervalBool.mem_undetermined _
  · apply IntervalBool.mem_false
    intro hxy
    exact h₂ <| Dyadic.toReal_lt_toReal.mp <| hx.1.trans_lt <| hxy.trans_le hy.2

@[inclusionOp ball_dyadic_real]
theorem eq_mem {x y : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ B₁) (hy : y ∈ B₂) : (x = y) ∈ B₁.eq B₂ := by
  apply ToSet.mem_of_eq_of_mem (propext le_antisymm_iff)
  exact IntervalBool.and_mem (le_mem hx hy) (le_mem hy hx)

@[inclusionOp ball_dyadic_real]
theorem mem_Ici {a x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (ha : a ∈ B₁) (hx : x ∈ B₂) : (x ∈ Set.Ici a) ∈ B₁.le B₂ := le_mem ha hx

@[inclusionOp ball_dyadic_real]
theorem mem_Ioi {a x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (ha : a ∈ B₁) (hx : x ∈ B₂) : (x ∈ Set.Ioi a) ∈ B₁.lt B₂ := lt_mem ha hx

@[inclusionOp ball_dyadic_real]
theorem mem_Iic {b x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ B₁) (hb : b ∈ B₂) : (x ∈ Set.Iic b) ∈ B₁.le B₂ := le_mem hx hb

@[inclusionOp ball_dyadic_real]
theorem mem_Iio {b x : ℝ} {B₁ B₂ : Ball Dyadic Dyadic}
    (hx : x ∈ B₁) (hb : b ∈ B₂) : (x ∈ Set.Iio b) ∈ B₁.lt B₂ := lt_mem hx hb

@[inclusionOp ball_dyadic_real]
theorem mem_Icc {a b x : ℝ} {B₁ B₂ B₃ : Ball Dyadic Dyadic}
    (ha : a ∈ B₁) (hx : x ∈ B₂) (hb : b ∈ B₃) :
    (x ∈ Set.Icc a b) ∈ (B₁.le B₂).and (B₂.le B₃) :=
  IntervalBool.and_mem (le_mem ha hx) (le_mem hx hb)

@[inclusionOp ball_dyadic_real]
theorem mem_Ico {a b x : ℝ} {B₁ B₂ B₃ : Ball Dyadic Dyadic}
    (ha : a ∈ B₁) (hx : x ∈ B₂) (hb : b ∈ B₃) :
    (x ∈ Set.Ico a b) ∈ (B₁.le B₂).and (B₂.lt B₃) :=
  IntervalBool.and_mem (le_mem ha hx) (lt_mem hx hb)

@[inclusionOp ball_dyadic_real]
theorem mem_Ioc {a b x : ℝ} {B₁ B₂ B₃ : Ball Dyadic Dyadic}
    (ha : a ∈ B₁) (hx : x ∈ B₂) (hb : b ∈ B₃) :
    (x ∈ Set.Ioc a b) ∈ (B₁.lt B₂).and (B₂.le B₃) :=
  IntervalBool.and_mem (lt_mem ha hx) (le_mem hx hb)

@[inclusionOp ball_dyadic_real]
theorem mem_Ioo {a b x : ℝ} {B₁ B₂ B₃ : Ball Dyadic Dyadic}
    (ha : a ∈ B₁) (hx : x ∈ B₂) (hb : b ∈ B₃) :
    (x ∈ Set.Ioo a b) ∈ (B₁.lt B₂).and (B₂.lt B₃) :=
  IntervalBool.and_mem (lt_mem ha hx) (lt_mem hx hb)

end Props

end BallDyadicReal

end Inclusion
