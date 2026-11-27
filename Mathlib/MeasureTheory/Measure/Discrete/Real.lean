/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Discrete.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Real-valued singleton masses of discrete measures

Sigma-finite discrete measures are determined by their real-valued singleton masses.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Two sigma-finite discrete measures are equal if and only if their real-valued singleton
masses agree. -/
theorem ext_iff_measureReal_singleton
    {μ1 μ2 : Measure α} [IsDiscreteMeasure μ1] [IsDiscreteMeasure μ2]
    [SigmaFinite μ1] [SigmaFinite μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton]
  congr! with x
  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  simp [measure_singleton_lt_top, ne_of_lt]

alias ⟨_, Measure.ext_of_measureReal_singleton⟩ := MeasureTheory.ext_iff_measureReal_singleton

end MeasureTheory
