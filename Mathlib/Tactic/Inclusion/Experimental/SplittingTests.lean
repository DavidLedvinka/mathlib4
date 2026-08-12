module

public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace Inclusion.Experimental.Tests

def unitInterval : Interval Dyadic := ⟨1, 2⟩

example : (1 : ℝ) ≤ 2 := by
  inclusion [core, real.dyadic] (split := 4)

example {x : ℝ} (_hx : x ∈ unitInterval) : True := by
  fail_if_success
    have : x - x ≤ 1 / 2 := by
      inclusion [core, real.dyadic]
  trivial

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 2 := by
  inclusion [core, real.dyadic] (split := 1)

example {x y : ℝ} (hx : x ∈ unitInterval) (hy : y ∈ unitInterval) :
    (x - x) + (y - y) ≤ 1 := by
  inclusion [core, real.dyadic] (split := 1)

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 8 := by
  inclusion [core, real.dyadic] (split := 4)

run_meta
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let goal ← mkAppM ``HSub.hSub #[x, x]
    let intervalType ← mkAppM ``Interval #[mkConst ``Dyadic]
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[intervalType, mkConst ``Real])
    let hypType ← mkToSetMem (mkConst ``Real) intervalType x (mkConst ``unitInterval) toSetInst
    withLocalDeclD `hx hypType fun _hx => do
      let enabled := ({} : NameSet).insert `split
      let fn ← (toExprInclusion goal).run enabled #[`core, `real.dyadic]
      let compiledType ← mkArrow (mkConst ``Nat) intervalType
      let compiled ← unsafe evalExpr (ℕ → Interval Dyadic) compiledType fn.inclusion
      let half := Dyadic.ofIntWithPrec 1 1
      let result := compiled 1
      unless result.lb == some (-half) && result.ub == some half do
        throwError "A cover was not coarsened correctly for a non-proposition inclusion"

end Inclusion.Experimental.Tests
