module

public import Mathlib.Tactic.Inclusion.Experimental.ConcreteSplitting
public meta import Mathlib.Tactic.Inclusion.Experimental.ConcreteSplitting

set_option linter.style.header false

@[expose] public section

open Set

namespace Inclusion.Experimental.Tests

def concreteInterval : Interval Dyadic := ⟨1, 2⟩

def concreteMidpoint : Dyadic := midpoint 1 2

def concreteLeft : Interval Dyadic := ⟨1, concreteMidpoint⟩

def concreteRight : Interval Dyadic := ⟨concreteMidpoint, 2⟩

def concretePieces : Array (Interval Dyadic) := #[concreteLeft, concreteRight]

theorem concretePieces_cover :
    (concreteInterval : Set ℝ) ⊆ ⋃ t ∈ concretePieces, (t : Set ℝ) := by
  intro r hr
  simp only [Set.mem_iUnion]
  by_cases h : r ≤ Dyadic.toReal concreteMidpoint
  · exact ⟨concreteLeft, by simp [concretePieces], hr.1, WithTop.coe_le_coe.mpr h⟩
  · exact ⟨concreteRight, by simp [concretePieces],
      WithBot.coe_le_coe.mpr (le_of_not_ge h), hr.2⟩

example {x : ℝ} (_hx : x ∈ concreteInterval) : True := by
  fail_if_success
    have : x - x ≤ 1 / 2 := by
      inclusion [core, real.dyadic]
  trivial

example {x : ℝ} (hx : x ∈ concreteInterval) : x - x ≤ 1 / 2 := by
  inclusion_cover x in concreteInterval with concretePieces using concretePieces_cover

end Inclusion.Experimental.Tests
