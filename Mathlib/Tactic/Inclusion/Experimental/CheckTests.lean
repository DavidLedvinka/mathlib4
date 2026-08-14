module

public import Mathlib.Tactic.Inclusion.Experimental.CheckTestExtensions
public meta import Mathlib.Tactic.Inclusion.Experimental.CheckTestExtensions

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace Inclusion.Experimental.CheckTests

open CheckTestExtensions

def unitInterval : Interval Dyadic := ⟨1, 2⟩

private meta def withIntervalVariable {R : Type} (k : Expr → MetaM R) : MetaM R :=
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let intervalType ← mkAppM ``Interval #[mkConst ``Dyadic]
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[intervalType, mkConst ``Real])
    let hypType ← mkToSetMem (mkConst ``Real) intervalType x (mkConst ``unitInterval) toSetInst
    withLocalDeclD `hx hypType fun _ => k x

private meta def mkDifferenceGoal (x : Expr) (denominator : Nat)
    (extraTerm? : Option Expr := none) : MetaM Expr := do
  let difference ← mkAppM ``HSub.hSub #[x, x]
  let lhs ← match extraTerm? with
    | some extraTerm => mkAppM ``HAdd.hAdd #[extraTerm, difference]
    | none => pure difference
  let one ← mkNumeral (mkConst ``Real) 1
  let denominator ← mkNumeral (mkConst ``Real) denominator
  let rhs ← mkAppM ``HDiv.hDiv #[one, denominator]
  mkAppM ``LE.le #[lhs, rhs]

private meta def assertSplitSearch (denominator max expected : Nat) : MetaM Unit :=
  withIntervalVariable fun x => do
    let goal ← mkDifferenceGoal x denominator
    let config : InclusionConfig := { families := #[`core, `real.dyadic] }
    let result ← inclusionCheckCore goal config (some { name := `split, max })
    unless result == some (`split, expected) do
      throwError "Parameter search returned {result}, expected `split := {expected}`"

example : (1 : ℝ) ≤ 2 := by
  inclusion? [core, real.dyadic]
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 2 := by
  inclusion? [core, real.dyadic] (split := 1)
  inclusion [core, real.dyadic] (split := 1)

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 2 := by
  inclusion? [core, real.dyadic] (split := search[100])
  inclusion [core, real.dyadic] (split := 1)

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 2 := by
  fail_if_success inclusion? [core, real.dyadic] (split := search[0])
  inclusion [core, real.dyadic] (split := 1)

example {x : ℝ} (hx : x ∈ unitInterval) : x - x ≤ 1 / 64 := by
  inclusion? [core, real.dyadic] (split := search[6])
  inclusion [core, real.dyadic] (split := 6)

run_meta do
  assertSplitSearch 2 100 1
  assertSplitSearch 64 100 6
  assertSplitSearch 64 6 6

example {x : ℝ} (hx : x ∈ unitInterval) :
    parameterizedEndpoint + (x - x) ≤ 1 / 64 := by
  inclusion? [core, real.dyadic] (checkFixed := 7, checkFixed2 := 11, split := search[6])
  inclusion [core, real.dyadic] (checkFixed := 7, checkFixed2 := 11, split := 6)

example {x : ℝ} (hx : x ∈ unitInterval) :
    parameterizedEndpoint + (x - x) ≤ 1 / 64 := by
  fail_if_success
    inclusion? [core, real.dyadic] (checkFixed := 7, checkFixed2 := 10, split := search[6])
  inclusion [core, real.dyadic] (checkFixed := 7, checkFixed2 := 11, split := 6)

run_meta
  withIntervalVariable fun x => do
    let goal ← mkDifferenceGoal x 64 (some (mkConst ``parameterizedEndpoint))
    let config : InclusionConfig :=
      { paramValues := ({} : NameMap Nat).insert `checkFixed 7 |>.insert `checkFixed2 11
        families := #[`core, `real.dyadic] }
    let result ← inclusionCheckCore goal config (some { name := `split, max := 6 })
    unless result == some (`split, 6) do
      throwError "Multi-parameter search returned {result}, expected `split := 6`"

end Inclusion.Experimental.CheckTests
