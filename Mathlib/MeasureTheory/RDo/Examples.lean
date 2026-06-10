module

public import Mathlib.MeasureTheory.RDo.RDo
public import Mathlib.MeasureTheory.RDo.MeasurableSpaceInstances
public import Mathlib.Algebra.Ring.BooleanRing

set_option linter.style.header false

@[expose] public section

open MeasureTheory ProbabilityTheory Measure

/- # Nonpolymorphic examples -/

universe u v

noncomputable def measureSample : Measure Bool := rdo
  let x ← bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩
  let y ← bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩
  return x + y

def pseudoSample : PseudoRandom Bool := rdo
  let x ← Random.randBool
  let y ← Random.randBool
  return x + y

/- # Polymorphic examples -/

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]

class HasBit (m : (α : Type) → MeasurableSpace α → Type v) where
  bit : m Bool (by infer_instance)

noncomputable instance : HasBit Measure where
  bit := bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩

instance : HasBit PseudoRandom where
  bit := Random.randBool

def indepAnd [HasBit m] : m Bool := rdo
  let x ← HasBit.bit
  let y ← HasBit.bit
  return x && y

noncomputable def indepAndMeasure : Measure Bool := indepAnd (m := Measure)

def indepAndGen : PseudoRandom Bool := indepAnd (m := PseudoRandom)

variable {α : Type*} [MeasurableSpace α]

def sampleBitsArray [HasBit m] : m (Array Bool) := rdo
  let mut xs : Array Bool := #[]
  for _ in List.range 5 do
    let b ← HasBit.bit (m := m)
    xs := xs.push b
  return xs
