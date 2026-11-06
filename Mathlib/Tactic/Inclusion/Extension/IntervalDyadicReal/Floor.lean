/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic

/-!
# Floor and ceiling for interval_dyadic_real

This file defines integer interval enclosures of the floor and ceiling of real expressions.
-/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

/-- Enclose the integer floor by taking the floor of each finite endpoint. -/
def floor (I : Interval Dyadic) : Interval ℤ := I.map Dyadic.floor

@[inclusion_op interval_dyadic_real]
theorem floor_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) : ⌊x⌋ ∈ floor I := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
  simp only [floor, Interval.mem_map_iff, ← Dyadic.floor_toRat,
    ← Rat.floor_cast (α := ℝ)]
  exact ⟨fun lb h ↦ Int.floor_mono (hx.1 lb h), fun ub h ↦ Int.floor_mono (hx.2 ub h)⟩

/-- Enclose the integer ceiling by taking the ceiling of each finite endpoint. -/
def ceil (I : Interval Dyadic) : Interval ℤ := I.map Dyadic.ceil

@[inclusion_op interval_dyadic_real]
theorem ceil_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) : ⌈x⌉ ∈ ceil I := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
  simp only [ceil, Interval.mem_map_iff, ← Dyadic.ceil_toRat,
    ← Rat.ceil_cast (α := ℝ)]
  exact ⟨fun lb h ↦ Int.ceil_mono (hx.1 lb h), fun ub h ↦ Int.ceil_mono (hx.2 ub h)⟩

end Inclusion.IntervalDyadicReal
