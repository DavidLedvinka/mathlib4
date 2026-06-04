module

public import Mathlib.Data.Vector.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option linter.style.header false

@[expose] public section

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

instance : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

instance : MeasurableSpace (Array α) :=
  MeasurableSpace.comap Array.toList inferInstance

instance : MeasurableSpace (List.Vector α n) :=
  MeasurableSpace.comap (Equiv.vectorEquivFin α n) inferInstance
