/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Dyadic
public import Mathlib.Data.Rat.Floor

/-!
# Floor and ceil of dyadic rationals

This file defines integer floor and ceil for dyadic rationals using bit shifts.
-/

@[expose] public section

namespace Dyadic

/-- Round a dyadic rational down to an integer. -/
def floor : Dyadic → ℤ
  | .zero => 0
  | .ofOdd n (.ofNat k) _ => n >>> k
  | .ofOdd n (.negSucc k) _ => n <<< (k + 1)

/-- Round a dyadic rational up to an integer. -/
def ceil : Dyadic → ℤ
  | .zero => 0
  | .ofOdd n (.ofNat 0) _ => n
  | .ofOdd n (.ofNat (k + 1)) _ => (n >>> (k + 1)) + 1
  | .ofOdd n (.negSucc k) _ => n <<< (k + 1)

@[simp]
theorem floor_toRat (x : Dyadic) : ⌊x.toRat⌋ = x.floor := by
  cases x with
  | zero => simp [floor]
  | ofOdd n k hn =>
    cases k with
    | ofNat k => simp [floor, toRat, Rat.floor_def', Int.shiftRight_eq_div_pow]
    | negSucc k =>
      simp only [floor, toRat, Int.floor_intCast, Int.shiftLeft_eq,
        Nat.cast_pow, Nat.cast_ofNat]

@[simp]
theorem ceil_toRat (x : Dyadic) : ⌈x.toRat⌉ = x.ceil := by
  cases x with
  | zero => simp [ceil]
  | ofOdd n k hn =>
    cases k with
    | ofNat k =>
      cases k with
      | zero => simp [ceil, toRat]
      | succ k =>
        have h : ¬ (2 : ℤ) ^ (k + 1) ∣ n := by
          intro h
          have : (2 : ℤ) ∣ n := (dvd_pow_self 2 (by simp)).trans h
          simp [Int.dvd_iff_emod_eq_zero, hn] at this
        simp [ceil, toRat, Rat.ceil_def', Int.shiftRight_eq_div_pow, Int.neg_ediv, h,
          Int.sign_eq_one_of_pos (show (0 : ℤ) < 2 ^ (k + 1) by positivity), Int.add_comm]
    | negSucc k =>
      simp only [ceil, toRat, Int.ceil_intCast, Int.shiftLeft_eq,
        Nat.cast_pow, Nat.cast_ofNat]

@[simp]
theorem floor_toReal (x : Dyadic) : ⌊x.toReal⌋ = x.floor := by
  simp [toReal]

@[simp]
theorem ceil_toReal (x : Dyadic) : ⌈x.toReal⌉ = x.ceil := by
  simp [toReal]

end Dyadic
