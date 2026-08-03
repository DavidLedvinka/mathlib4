module

public import Mathlib.Tactic.Inclusion.Core.ToSet
public import Mathlib.Order.SetNotation

set_option linter.style.header false

@[expose] public section

namespace IntervalArithmetic

variable {Iα α : Type*}

class Splitter (Iα α : Type*) [ToSet Iα α] where
  split : ℕ → Iα → Array Iα
  cover : ∀ n s a, a ∈ s → a ∈ ⋃ t ∈ split n s, (t : Set α)
  check : ℕ → Iα → (Iα → IntervalBool) → IntervalBool
  check_eq_true : ∀ n s P, check n s P = IntervalBool.true ↔
    ∀ t, t ∈ split n s → P t = IntervalBool.true

/-- Eliminate a successful split check by selecting a split piece containing the given point. -/
theorem Splitter.splitElim [ToSet Iα α] (splitter : Splitter Iα α)
    (P : Iα → IntervalBool) (n : ℕ) (a : α) (s : Iα) (has : a ∈ s)
    {q : Prop} (hcheck : splitter.check n s P = IntervalBool.true)
    (next : ∀ t, a ∈ t → P t = IntervalBool.true → q) : q := by
  have ha := splitter.cover n s a has
  simp only [Set.mem_iUnion] at ha
  obtain ⟨t, ht, hat⟩ := ha
  exact next t hat (splitter.check_eq_true n s P |>.mp hcheck t ht)

end IntervalArithmetic
