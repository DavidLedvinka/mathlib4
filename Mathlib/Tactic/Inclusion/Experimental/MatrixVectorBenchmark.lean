module

public meta import Mathlib.Tactic.Inclusion.Experimental.BenchmarkCommand
public import Mathlib.Tactic.Inclusion.Experimental.MatrixVectorExtensions
public meta import Mathlib.Tactic.Inclusion.Experimental.MatrixVectorExtensions

set_option linter.style.header false
set_option linter.style.longLine false

@[expose] public section

open scoped Matrix Matrix.Norms.Elementwise

namespace Inclusion.MatrixVector.Benchmark

abbrev Vec10 := Fin 10 → ℝ
abbrev Mat10 := Matrix (Fin 10) (Fin 10) ℝ

def unitRange : Interval Dyadic := ⟨(-1 : Dyadic), (1 : Dyadic)⟩

/- A compact function-valued representation of the uniform entrywise box `[-1, 1]`. -/
#time def generatedMatrixBounds : MatrixBox 10 10 := ⟨fun _ _ => unitRange⟩

#time def generatedVectorBounds : VectorBox 10 := ⟨fun _ => unitRange⟩

/- The same box as `generatedMatrixBounds`, written using a 100-entry matrix literal. -/
#time def notationMatrixBounds : MatrixBox 10 10 :=
  ⟨!![
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange;
    unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange, unitRange
  ]⟩

#time def notationVectorBounds : VectorBox 10 :=
  ⟨![unitRange, unitRange, unitRange, unitRange, unitRange,
      unitRange, unitRange, unitRange, unitRange, unitRange]⟩

#time_with_kernel theorem generated_10x10_mulVec {A : Mat10} {x : Vec10}
    (hA : A ∈ generatedMatrixBounds) (hx : x ∈ generatedVectorBounds) :
    ‖A *ᵥ x‖ ≤ 10 := by
  inclusion

#time_with_kernel theorem notation_10x10_mulVec {A : Mat10} {x : Vec10}
    (hA : A ∈ notationMatrixBounds) (hx : x ∈ notationVectorBounds) :
    ‖A *ᵥ x‖ ≤ 10 := by
  inclusion

end Inclusion.MatrixVector.Benchmark
