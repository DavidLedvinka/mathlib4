module

public import Mathlib.Tactic.MetaInterval.Interval

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace IntervalArithmetic

/-- If `e` is an `Expr` of the form `x ∈ s` return `some (x, s)`. -/
meta def memSet? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, s, x]) => some (x, s)
  | _ => none

/-- If `e` is an `Expr` of the form `Interval.toSet i` return `some i` -/
meta def intervaltoSet? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Interval.toSet, #[_, _, i]) => some i
  | _ => none

/-- If `e` is an `Expr` of the form `Interval.map i f` return `some (i, f)` -/
meta def intervalMap? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Interval.map, #[_, _, i, f]) => some (i, f)
  | _ => none

/-- If `e` is an `Expr` of the form `x ∈ (i.map f).toSet` return `some (x, i, f)` -/
meta def intervalHyp? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (r, s) ← memSet? e
  let i ← intervaltoSet? s
  let (i, f) ← intervalMap? i
  return (r, i, f)

/-- Create an expression of the form `x ∈ (i.map f).toSet`. -/
def mkIntervalMem (x i f : Expr) : MetaM Expr := do
  let intervalMap ← mkAppM ``Interval.map #[i, f]
  let intervalToSet ← mkAppM ``Interval.toSet #[intervalMap]
  mkAppM ``Membership.mem #[intervalToSet, x]

end IntervalArithmetic
