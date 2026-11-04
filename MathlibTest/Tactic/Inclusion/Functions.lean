/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

open Lean Meta Qq Inclusion

namespace Inclusion.Tests.Functions

-- Test-only pointwise instances; no function or big-operator support is added to the library.
instance {ι α I : Type*} [ToSet I α] : ToSet (ι → I) (ι → α) where
  toSet F := {f | ∀ i, f i ∈ F i}

instance {ι α I : Type*} [ToSet I α] [Univ I α] : Univ (ι → I) (ι → α) where
  univ := fun _ => Univ.univ α
  mem_univ f i := Univ.mem_univ (f i)

instance {ι α I : Type*} [ToSet I α] [Refine I α] : Refine (ι → I) (ι → α) where
  refine F G := fun i => Refine.refine α (F i) (G i)
  mem_refine hf hg i := Refine.mem_refine (hf i) (hg i)

-- Check the expression's shape, not just its value, and have the kernel verify the transformation.
private meta def checkReduction (e expected : Expr) : MetaM Unit := do
  let actual ← reduceFunctionInclusions e
  unless actual == expected do
    throwError "Unexpected reduction:\n{actual}\nExpected:\n{expected}"
  discard <| withOptions (Elab.async.set · false) <|
    mkAuxLemma [] (← mkEq e actual) (← mkEqRefl e) (cache := false)

run_meta do
  let lower := q(Interval.Ici (0 : WithBot Dyadic))
  let upper := q(Interval.Iic (1 : WithTop Dyadic))
  let refined : Q(Interval Dyadic) := q(Refine.refine ℝ $lower $upper)
  let bounds : Q(ℕ → Interval Dyadic) :=
    q(Refine.refine (ℕ → ℝ) (fun _ : ℕ => $lower) (fun _ : ℕ => $upper))
  checkReduction bounds q(fun _ : ℕ => $refined)
  let applyBounds := q(fun F : ℕ → Interval Dyadic => (F 0).mul (F 1))
  checkReduction (mkApp applyBounds bounds) q(Interval.mul $refined $refined)
  checkReduction q(Univ.univ (ℕ → ℝ) : ℕ → Interval Dyadic)
    q(fun _ : ℕ => (Univ.univ ℝ : Interval Dyadic))
  -- Scalar refinement and multiplication remain unevaluated.
  checkReduction refined refined
  let scalar := mkApp q(fun I : Interval Dyadic => I.mul I) refined
  checkReduction scalar scalar
  -- A varying function bound stays shared through its enclosing application.
  let varying : Q(ℕ → Interval Dyadic) := q(fun i : ℕ => Interval.singleton (i : Dyadic))
  let varyingUse := mkApp applyBounds varying
  checkReduction varyingUse varyingUse
  let varyingBounds : Q(ℕ → Interval Dyadic) :=
    q(Refine.refine (ℕ → ℝ) $varying (fun _ : ℕ => $upper))
  let varyingRefined :=
    q(fun i : ℕ => Refine.refine ℝ (Interval.singleton (i : Dyadic)) $upper)
  checkReduction (mkApp applyBounds varyingBounds) (mkApp applyBounds varyingRefined)
  -- Partial applications are not mistaken for complete refinements.
  let partialRefine := q(Refine.refine (ℕ → ℝ) :
    (ℕ → Interval Dyadic) → (ℕ → Interval Dyadic) → ℕ → Interval Dyadic)
  checkReduction partialRefine partialRefine
  -- Constancy is relative to the function's own binder, not the surrounding context.
  checkReduction
    q(fun I : Interval Dyadic =>
      (fun F : ℕ → Interval Dyadic => (F 0).mul (F 1)) (fun _ => I))
    q(fun I : Interval Dyadic => I.mul I)

@[inclusion_ext (_ : ℕ → ℝ)]
meta def mkFunctionIVar : InclusionExt :=
  mkNDIVarExt `interval_dyadic_real
    ⟨q(ℕ → ℝ), q(ℕ → Interval Dyadic),
      q(inferInstance : ToSet (ℕ → Interval Dyadic) (ℕ → ℝ))⟩

@[inclusion_op interval_dyadic_real 200]
theorem apply_mem {f : ℕ → ℝ} {F : ℕ → Interval Dyadic} (hf : f ∈ F) (i : ℕ) :
    f i ∈ F i := hf i

-- Exercise the actual closing path, including both the inclusion and its soundness proof.
example (f : ℕ → ℝ)
    (hl : f ∈ fun _ : ℕ => Interval.Ici (0 : WithBot Dyadic))
    (hu : f ∈ fun _ : ℕ => Interval.Iic (1 : WithTop Dyadic)) : f 0 + f 1 ≤ 2 := by
  run_tac
    let inc ← (toExprInclusion (← Elab.Tactic.getMainTarget)).run
      (families := #[`core, `interval_dyadic_real])
    for e in #[inc.inclusion, inc.proof] do
      unless (← reduceFunctionInclusions e) == e do
        throwError "Function inclusions were not reduced when closing the inclusion"
    let proof ← mkInclusionTrueProof inc.inclusion
    (← Elab.Tactic.getMainGoal).assign <|
      inc.mkGoalProof (← Elab.Tactic.getMainTarget) proof

example (f : ℕ → ℝ)
    (hl : f ∈ fun _ : ℕ => Interval.Ici (0 : WithBot Dyadic))
    (hu : f ∈ fun _ : ℕ => Interval.Iic (1 : WithTop Dyadic)) : f 0 * f 1 ≤ 1 := by
  dyadic_interval +kernel

example (f : ℕ → ℝ) : 0 ≤ (f 0) ^ 2 := by dyadic_interval

end Inclusion.Tests.Functions
