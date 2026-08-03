module

public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions
public import Mathlib.Tactic.Inclusion.Core.Splitting

set_option linter.style.header false

@[expose] public section

open Set

namespace IntervalArithmetic.Inclusion.Experimental

def half (x : Dyadic) : Dyadic :=
  match x with
  | .zero => 0
  | .ofOdd n k _ => Dyadic.ofIntWithPrec n (k + 1)

def midpoint (a b : Dyadic) : Dyadic := half (a + b)

def bisect (I : Interval Dyadic) : Array (Interval Dyadic) :=
  match I with
  | ⟨some l, some u⟩ =>
      let m := midpoint l u
      #[⟨l, m⟩, ⟨m, u⟩]
  | _ => #[I]

theorem exists_mem_bisect {r : ℝ} {I : Interval Dyadic} (hr : r ∈ I) :
    ∃ J ∈ bisect I, r ∈ J := by
  match I with
  | ⟨some l, some u⟩ =>
      by_cases h : r ≤ Dyadic.toReal (midpoint l u)
      · refine ⟨⟨l, midpoint l u⟩, ?_, ?_⟩
        · simp [bisect]
        · exact ⟨hr.1, WithTop.coe_le_coe.mpr h⟩
      · refine ⟨⟨midpoint l u, u⟩, ?_, ?_⟩
        · simp [bisect]
        · exact ⟨WithBot.coe_le_coe.mpr (le_of_not_ge h), hr.2⟩
  | ⟨⊥, u⟩ => exact ⟨⟨⊥, u⟩, by simp [bisect], hr⟩
  | ⟨some l, ⊤⟩ => exact ⟨⟨some l, ⊤⟩, by simp [bisect], hr⟩

def splitDyadic : ℕ → Interval Dyadic → Array (Interval Dyadic)
  | 0, I => #[I]
  | n + 1, I => (bisect I).flatMap (splitDyadic n)

def splitCheck : ℕ → Interval Dyadic → (Interval Dyadic → IntervalBool) → IntervalBool
  | 0, I, P => P I
  | n + 1, I, P =>
      match I with
      | ⟨some l, some u⟩ =>
          let m := midpoint l u
          match splitCheck n ⟨l, m⟩ P with
          | .true => splitCheck n ⟨m, u⟩ P
          | .false | .undetermined => .undetermined
      | _ => splitCheck n I P

@[simp]
theorem splitCheck_eq_true (n : ℕ) (I : Interval Dyadic)
    (P : Interval Dyadic → IntervalBool) :
    splitCheck n I P = IntervalBool.true ↔
      ∀ J, J ∈ splitDyadic n I → P J = IntervalBool.true := by
  induction n generalizing I with
  | zero => simp [splitCheck, splitDyadic]
  | succ n ih =>
      rcases I with ⟨lb, ub⟩
      cases lb with
      | bot =>
          cases ub with
          | top => simpa [splitCheck, splitDyadic, bisect] using ih (I := ⟨⊥, ⊤⟩)
          | coe u => simpa [splitCheck, splitDyadic, bisect] using ih (I := ⟨⊥, u⟩)
      | coe l =>
          cases ub with
          | top => simpa [splitCheck, splitDyadic, bisect] using ih (I := ⟨l, ⊤⟩)
          | coe u =>
              let m := midpoint l u
              let left : Interval Dyadic := ⟨l, m⟩
              let right : Interval Dyadic := ⟨m, u⟩
              have hLeaves :
                  (∀ J, J ∈ splitDyadic (n + 1) ⟨l, u⟩ → P J = IntervalBool.true) ↔
                    splitCheck n left P = IntervalBool.true ∧
                      splitCheck n right P = IntervalBool.true := by
                rw [ih left, ih right]
                have mem_iff (J : Interval Dyadic) :
                    J ∈ splitDyadic (n + 1) ⟨l, u⟩ ↔
                      J ∈ splitDyadic n left ∨ J ∈ splitDyadic n right := by
                  simp [splitDyadic, bisect, left, right, m]
                constructor
                · intro h
                  exact ⟨fun J hJ => h J (mem_iff J |>.mpr (Or.inl hJ)),
                    fun J hJ => h J (mem_iff J |>.mpr (Or.inr hJ))⟩
                · rintro ⟨hleft, hright⟩ J hJ
                  rcases (mem_iff J).mp hJ with hJ | hJ
                  · exact hleft J hJ
                  · exact hright J hJ
              rw [hLeaves]
              change (match splitCheck n left P with
                | .true => splitCheck n right P
                | .false | .undetermined => .undetermined) = .true ↔ _
              cases splitCheck n left P <;> simp

theorem exists_mem_split {r : ℝ} {I : Interval Dyadic} (n : ℕ) (hr : r ∈ I) :
    ∃ J ∈ splitDyadic n I, r ∈ J := by
  induction n generalizing I with
  | zero => exact ⟨I, by simp [splitDyadic], hr⟩
  | succ n ih =>
      obtain ⟨J, hJ, hrJ⟩ := exists_mem_bisect hr
      obtain ⟨K, hK, hrK⟩ := ih hrJ
      exact ⟨K, by simpa [splitDyadic, Array.mem_flatMap] using ⟨J, hJ, hK⟩, hrK⟩

instance : IntervalArithmetic.Splitter (Interval Dyadic) ℝ where
  «split» := splitDyadic
  cover := fun n _ _ hr => by
    simp only [Set.mem_iUnion]
    obtain ⟨J, hJ, hrJ⟩ := exists_mem_split n hr
    exact ⟨J, hJ, hrJ⟩
  check := splitCheck
  check_eq_true := splitCheck_eq_true

end IntervalArithmetic.Inclusion.Experimental
