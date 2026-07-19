module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

set_option linter.style.header false

@[expose] public section

namespace IntervalArithmetic

instance : LinearOrder Dyadic where
  le_refl := Std.IsPreorder.le_refl
  le_trans := Std.IsPreorder.le_trans
  le_antisymm := Std.IsPartialOrder.le_antisymm
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  le_total := Std.IsLinearOrder.le_total
  toDecidableLE := Dyadic.instDecidableLE

def Dyadic.toReal (d : Dyadic) : ℝ := d.toRat

theorem Monotone.dyadicToReal : Monotone Dyadic.toReal := by
  intro _ _ h
  simp [Dyadic.toReal, h]

end IntervalArithmetic
