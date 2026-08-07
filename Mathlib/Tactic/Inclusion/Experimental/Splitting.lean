module

public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions
public import Mathlib.Tactic.Inclusion.Extension.Splitter

set_option linter.style.header false

@[expose] public section

namespace Inclusion.Experimental

def half (x : Dyadic) : Dyadic :=
  match x with
  | .zero => 0
  | .ofOdd n k _ => Dyadic.ofIntWithPrec n (k + 1)

def midpoint (a b : Dyadic) : Dyadic := half (a + b)

def splitCheckAux : ℕ → Interval Dyadic → (Interval Dyadic → IntervalBool) → IntervalBool
  | 0, I, P => P I
  | n + 1, I, P =>
      match I with
      | ⟨some l, some u⟩ =>
          let m := midpoint l u
          match splitCheckAux n ⟨l, m⟩ P with
          | .true => splitCheckAux n ⟨m, u⟩ P
          | .false | .undetermined => .undetermined
      | _ => splitCheckAux n I P

def splitCheck (n : ℕ) (I : Interval Dyadic)
    (P : Interval Dyadic → IntervalBool) : IntervalBool :=
  match splitCheckAux n I P with
  | .true => .true
  | .false | .undetermined => .undetermined

theorem splitCheckAux_sound (n : ℕ) (I : Interval Dyadic)
    (P : Interval Dyadic → IntervalBool) (hcheck : splitCheckAux n I P = IntervalBool.true)
    (r : ℝ) (hr : r ∈ I) : ∃ J, r ∈ J ∧ P J = IntervalBool.true := by
  induction n generalizing I with
  | zero => exact ⟨I, hr, hcheck⟩
  | succ n ih =>
      rcases I with ⟨lb, ub⟩
      cases lb with
      | bot =>
          cases ub with
          | top => exact ih _ hcheck hr
          | coe u => exact ih _ hcheck hr
      | coe l =>
          cases ub with
          | top => exact ih _ hcheck hr
          | coe u =>
              let m := midpoint l u
              let left : Interval Dyadic := ⟨l, m⟩
              let right : Interval Dyadic := ⟨m, u⟩
              have hboth :
                  splitCheckAux n left P = IntervalBool.true ∧
                    splitCheckAux n right P = IntervalBool.true := by
                change (match splitCheckAux n left P with
                  | .true => splitCheckAux n right P
                  | .false | .undetermined => .undetermined) = .true at hcheck
                revert hcheck
                cases splitCheckAux n left P <;> simp
              by_cases h : r ≤ Dyadic.toReal m
              · exact ih left hboth.1 ⟨hr.1, WithTop.coe_le_coe.mpr h⟩
              · exact ih right hboth.2 ⟨WithBot.coe_le_coe.mpr (le_of_not_ge h), hr.2⟩

theorem splitCheck_mem (n : ℕ) (I : Interval Dyadic)
    (P : Interval Dyadic → IntervalBool) {p : Prop} {r : ℝ} (hr : r ∈ I)
    (hp : ∀ J, r ∈ J → p ∈ P J) : p ∈ splitCheck n I P := by
  cases hcheck : splitCheckAux n I P with
  | true =>
      obtain ⟨J, hrJ, hJ⟩ := splitCheckAux_sound n I P hcheck r hr
      simpa [splitCheck, hcheck, hJ] using hp J hrJ
  | false =>
      simpa [splitCheck, hcheck, ToSet.toSet, IntervalBool.toPropSet] using Classical.em p
  | undetermined =>
      simpa [splitCheck, hcheck, ToSet.toSet, IntervalBool.toPropSet] using Classical.em p

instance : Splitter (Interval Dyadic) ℝ where
  coverCheck n := {
    check := splitCheck n
    mem_check := splitCheck_mem n
  }

end Inclusion.Experimental
