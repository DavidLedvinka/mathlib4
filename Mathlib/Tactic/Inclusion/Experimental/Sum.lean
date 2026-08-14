module

public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false

@[expose] public section

namespace Inclusion

def sumRangeIntervals : ℕ → (ℕ → Interval Dyadic) → Interval Dyadic
  | 0, _ => ofNat 0
  | n + 1, f => add (sumRangeIntervals n f) (f n)

theorem sumRangeIntervals_mem (n : ℕ) {f : ℕ → ℝ} {I : ℕ → Interval Dyadic}
    (h : ∀ i, f i ∈ I i) : Finset.sum (Finset.range n) f ∈ sumRangeIntervals n I := by
  induction n with
  | zero => simpa [sumRangeIntervals] using ofNat_mem 0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact add_mem ih (h n)

end Inclusion
