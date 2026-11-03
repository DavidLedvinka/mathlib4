/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Dyadic.Floor
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic

/-!
# Floor and ceil extensions for interval_dyadic_real

This file defines floor and ceil operations from dyadic real intervals to integer intervals.
-/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

@[inclusion_op interval_dyadic_real]
theorem floor_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) :
    ⌊x⌋ ∈ I.map Dyadic.floor := by
  simpa only [Interval.map_map, Function.comp_def, Dyadic.floor_toReal] using
    Interval.map_mem Int.floor_mono (mem_iff_mem_map.mp hx)

@[inclusion_op interval_dyadic_real]
theorem ceil_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) :
    ⌈x⌉ ∈ I.map Dyadic.ceil := by
  simpa only [Interval.map_map, Function.comp_def, Dyadic.ceil_toReal] using
    Interval.map_mem Int.ceil_mono (mem_iff_mem_map.mp hx)

end Inclusion.IntervalDyadicReal
