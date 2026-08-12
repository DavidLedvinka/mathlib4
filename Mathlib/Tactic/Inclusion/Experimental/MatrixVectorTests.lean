module

public import Mathlib.Tactic.Inclusion.Experimental.MatrixVectorExtensions
public meta import Mathlib.Tactic.Inclusion.Experimental.MatrixVectorExtensions

set_option linter.style.header false

@[expose] public section

open scoped Matrix Matrix.Norms.Elementwise

namespace Inclusion.MatrixVector.Tests

abbrev Vec2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def range (lower upper : Dyadic) : Interval Dyadic := ⟨lower, upper⟩

def matrixBounds : MatrixBox 2 2 :=
  ⟨!![range 1 1, range 2 2; range (-1) (-1), range 3 3]⟩

def vectorBounds : VectorBox 2 :=
  ⟨![range 1 2, range (-1) 1]⟩

/-- Direct componentwise interval estimates for both the matrix and the vector. -/
example {A : Mat2} {x : Vec2} (hA : A ∈ matrixBounds) (hx : x ∈ vectorBounds) :
    ‖A *ᵥ x‖ ≤ 5 := by
  inclusion [core, real.dyadic, matrix.vector]

/-- Matrix and vector arithmetic remains compositional before matrix-vector multiplication. -/
example {A B : Mat2} {x : Vec2} (hA : A ∈ matrixBounds) (hB : B ∈ matrixBounds)
    (hx : x ∈ vectorBounds) : ‖(A - B) *ᵥ x‖ ≤ 10 := by
  inclusion [core, real.dyadic, matrix.vector]

/-- Matrix multiplication produces another componentwise matrix enclosure. -/
example {A B : Mat2} {x : Vec2} (hA : A ∈ matrixBounds) (hB : B ∈ matrixBounds)
    (hx : x ∈ vectorBounds) : ‖(A * B) *ᵥ x‖ ≤ 19 := by
  inclusion [core, real.dyadic, matrix.vector]

/-- Equality preprocessing can turn an exact vector value into a vector box. -/
example {A : Mat2} {x : Vec2} (hA : A ∈ matrixBounds) (hx : x = 0) :
    ‖A *ᵥ x‖ ≤ 0 := by
  inclusion [core, real.dyadic, matrix.vector]

/-- Ordinary metric-ball hypotheses are preprocessed into componentwise interval boxes. -/
example {A : Mat2} {x : Vec2} (hA : A ∈ Metric.closedBall 0 1)
    (hx : x ∈ Metric.closedBall 0 1) : ‖A *ᵥ x‖ ≤ 2 := by
  inclusion [core, real.dyadic, matrix.vector]

/-- The radius itself may be an expression handled by the scalar interval extensions. -/
example {A : Mat2} {x : Vec2} (hA : A ∈ Metric.closedBall 0 1)
    (hx : x ∈ Metric.closedBall 0 (1 / 2)) : ‖A *ᵥ x‖ ≤ 1 := by
  inclusion [core, real.dyadic, matrix.vector]

end Inclusion.MatrixVector.Tests
