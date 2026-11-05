/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Data.Finset.Range

open Inclusion

namespace Inclusion.Tests.Function

-- A small consumer of a function enclosure, without introducing sums or products.
def sample {ι : Type*} (f : ι → ℝ) (i : ι) : ℝ := f i

@[inclusion_op interval_dyadic_real]
theorem sample_mem {ι : Type*} {f : ι → ℝ} {I : ι → Interval Dyadic} (i : ι)
    (hf : f ∈ I) : sample f i ∈ I i := hf i

section Scalar

-- Function support must not steal scalar applications and lose their hypotheses.
example (f : ℕ → ℝ) (h : f 0 ≤ 1) : f 0 + 1 ≤ 2 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 10) (h₀ : f 0 ≤ 1) : f 0 + 1 ≤ 2 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 1) : f 0 + f 1 ≤ 2 := by dyadic_interval

example (f : ℕ → ℝ) (i : ℕ) (h : ∀ j, f j ≤ 1) : f i + 1 ≤ 2 := by dyadic_interval

-- One hypothesis can yield different specializations for the same application.
example (f : ℕ → ℕ → ℝ) (h : ∀ i, f i 1 ≤ 10 ∧ f 0 i ≤ 1) : f 0 1 + 1 ≤ 2 := by
  dyadic_interval

end Scalar

section Functions

example : sample (fun _ : ℕ => (2 : ℝ) + 3) 0 = 5 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 1) : sample f 4 + 1 ≤ 2 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ∈ Set.Icc (-1) 2) :
    sample (fun i => |f i| + (f i) ^ 2) 3 ≤ 6 := by dyadic_interval

example (f g : ℕ → ℝ) (hf : ∀ i, 1 ≤ f i) (hf' : ∀ i, f i ≤ 2)
    (hg : ∀ i, g i ∈ Set.Icc (-1) 1) :
    sample (fun i => f i * g (i + 1) - f i) 2 ∈ Set.Icc (-4) 1 := by dyadic_interval

-- Scalar and function representations of the same expression can coexist.
example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 10) (h₀ : f 0 ≤ 1) :
    sample f 0 + f 0 ≤ 2 := by dyadic_interval

-- Bounds can depend computationally on the index.
example (f : ℕ → ℝ) (h : ∀ i, f i ≤ (i : ℝ) + 1) : sample f 4 ≤ 5 := by
  dyadic_interval

example (f : Fin 3 → ℝ) (h : ∀ i, f i ∈ Set.Icc 0 2) :
    sample (fun i => f i * (f i + 1)) 1 ≤ 6 := by dyadic_interval

-- A captured scalar stays a single scalar inclusion variable outside the lambda.
example (x : ℝ) (hx : x ∈ Set.Icc 1 2) (f : ℕ → ℝ) (hf : ∀ i, f i ≤ 1) :
    sample (fun i => f i + x - x) 0 ≤ 2 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 1) :
    sample (fun i => sample (fun j => f (i + j) + 1) 2) 3 ≤ 2 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 1) : sample (fun i => f i) 0 ≤ 1 := by
  dyadic_interval +kernel

example (f : ℕ → ℝ) (h : ∀ i, f i ∈ Set.Icc (-0.25) 0.5) :
    sample (fun i => 1.5 * f i + 0.25) 3 ≤ 1 := by dyadic_interval [prec := 4]

-- Nested function variables, as well as partial applications fixed in the original context.
example (f : ℕ → ℕ → ℝ) (h : ∀ i j, f i j ≤ 1) :
    sample (fun i => sample (f i) 2) 3 ≤ 1 := by dyadic_interval

example (f : ℕ → Fin 3 → ℝ) (h : ∀ i j, f i j ≤ 1) : sample (f 0) 2 ≤ 1 := by
  dyadic_interval

example (f : ℕ → ℕ → ℝ) (a : ℕ) (h : ∀ i j, f i j ≤ 1) : sample (f a) 2 ≤ 1 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : f 0 ≤ 1) : sample (fun _ : ℕ => f 0 + 1) 3 ≤ 2 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 1) :
    sample (let g := fun i => f i + 1; (fun g : ℕ → ℝ => g) g) 0 ≤ 2 := by dyadic_interval

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : sample (fun _ : ℕ => x - x) 0 ≤ 0.5 := by
  dyadic_interval [binSplit := 1, prec := 1]

end Functions

section Hypotheses

example (f : ℕ → ℝ) (h : f 0 ≤ 1) : sample f 0 ≤ 1 := by dyadic_interval

example (f : ℕ → ℝ) (h₀ : 0 ≤ f 0) (h₁ : f 0 ≤ 1) : sample f 0 ∈ Set.Icc 0 1 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, 0 ≤ f i ∧ f i ≤ 2) : sample f 1 ∈ Set.Icc 0 2 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, i < 3 → f i ≤ 1) : sample f 2 ≤ 1 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ∈ (⟨0, 2⟩ : Interval Dyadic)) : sample f 0 ≤ 2 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i : ℕ, f i ∈ Interval.singleton (i : Dyadic)) : sample f 3 = 3 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : f ∈ fun _ => (⟨0, 1⟩ : Interval Dyadic)) : f 0 + f 1 ≤ 2 := by
  dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, i < 3 → f i ≤ 1) : f 2 + 1 ≤ 2 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, i ∈ Finset.range 3 → f i ∈ Set.Icc 0 2) :
    sample (fun i => f i ^ 2 + f i) 2 ≤ 6 := by dyadic_interval

-- A failed bound must not discard other usable bounds or leak its local variables.
example (f : ℕ → ℝ) (x : ℝ) (_hbad : ∀ i, f i ≤ x) (hgood : ∀ i, f i ≤ 1) :
    sample f 0 ≤ 1 := by dyadic_interval

example (f : ℕ → ℝ) (h : ∀ i, f i ≤ 10) (h₀ : f 0 ≤ 1) (h₁ : f 1 ≤ 2) :
    sample f 0 + sample f 1 ≤ 3 := by dyadic_interval +kernel

end Hypotheses

section Scope

-- A point bound cannot be used at a different point.
example (f : ℕ → ℝ) (_h : f 0 ≤ 1) : True := by
  fail_if_success have : sample f 1 ≤ 1 := by dyadic_interval
  trivial

-- Restricted bounds must not be applied outside their domain.
example (f : ℕ → ℝ) (_h : ∀ i, i < 3 → f i ≤ 1) : True := by
  fail_if_success have : sample f 3 ≤ 1 := by dyadic_interval
  fail_if_success have : f 3 ≤ 1 := by dyadic_interval
  trivial

-- Local values cannot be embedded in the closed computation, even under a lambda.
example (f : ℕ → ℝ) (_n : ℕ) (_h : ∀ i, f i ≤ 1) : True := by
  fail_if_success have : sample (fun i => f (_n + i)) 0 ≤ 1 := by dyadic_interval
  trivial

example (f : ℕ → ℝ) (x : ℝ) (_h : ∀ i, f i ≤ x) : True := by
  fail_if_success have : sample f 0 ≤ 1 := by dyadic_interval
  trivial

-- Dependent function representations are deliberately not part of this extension.
example (f : (n : ℕ) → Fin (n + 1) → ℝ) (_h : ∀ i j, f i j ≤ 1) : True := by
  fail_if_success have : sample (fun i => sample (f i) 0) 2 ≤ 1 := by dyadic_interval
  trivial

-- Unbounded functions use pointwise Univ, and must not recursively eta-expand forever.
example (f : ℕ → ℝ) : 0 ≤ sample (fun i => (f i) ^ 2) 0 := by dyadic_interval

end Scope

section Dispatch

-- Function-valued results also support covers of captured scalar variables.
open Lean Meta Qq in
run_meta do
  withLocalDeclD `x q(ℝ) fun x => do
    let x : Q(ℝ) := x
    withLocalDeclD `hx q($x ∈ Set.Icc 0 1) fun _ => do
      let e := q(fun _ : ℕ => $x - $x)
      let inc ← (toExprInclusion e).run
        (({} : NameMap Expr).insert `binSplit (mkNatLit 1)) #[`core, `interval_dyadic_real]
      let expected := q(fun _ : ℕ =>
        (⟨some (Dyadic.ofIntWithPrec (-1) 1), some (Dyadic.ofIntWithPrec 1 1)⟩ : Interval Dyadic))
      discard <| mkAuxLemma [] (← mkEq inc.inclusion expected) (← mkEqRefl inc.inclusion)

open Lean Meta Qq in
run_meta do
  withLocalDeclD `f q(ℕ → ℝ) fun f => do
    let e := mkApp f (mkNatLit 0)
    let ctx : InclusionM.Context := {
      localContext := ← getLCtx
      localInstances := ← getLocalInstances
      families := #[`core, `interval_dyadic_real]
      paramSettings := {} }
    let (_, state) ← (mkExprInclusionBody e).runWith ctx
    unless state.iVars.contains e && !state.iVars.contains f do
      throwError "A scalar application was promoted to a function inclusion variable"

open Lean Meta Qq in
run_meta do
  withLocalDeclD `f q(ℕ → ℝ) fun f => do
    withLocalDeclD `x q(ℝ) fun x => do
      let ctx : InclusionM.Context := {
        localContext := ← getLCtx
        localInstances := ← getLocalInstances
        families := #[`core, `interval_dyadic_real]
        paramSettings := {} }
      let f : Q(ℕ → ℝ) := f
      let x : Q(ℝ) := x
      let (_, state) ← (mkExprInclusionBody q(fun i => $f i + $x)).runWith ctx
      unless state.iVars.size == 2 && state.iVars.contains f && state.iVars.contains x do
        throwError "A lambda's bound index escaped, or its captured scalar was promoted"

-- A specialized enclosure of a function need not itself be a function.
structure UniformBound where
  interval : Interval Dyadic

instance uniformToSet : ToSet UniformBound (Fin 3 → ℝ) where
  toSet I := {f | ∀ i, f i ∈ I.interval}

def zeroVector : Fin 3 → ℝ := fun _ => 0

open Lean Qq in
@[inclusion_ext(_ : Fin 3 → ℝ)]
meta def uniformIVar : InclusionExt :=
  mkNDIVarExt `interval_dyadic_real ⟨q(Fin 3 → ℝ), q(UniformBound), q(uniformToSet)⟩
    (priority := eval_prio default)

open Lean Meta Qq in
run_meta do
  let body ← (mkExprInclusionBody q(zeroVector)).run (families := #[`interval_dyadic_real])
  unless ← isDefEq (← inferType body.inclusionBody) q(UniformBound) do
    throwError "The generic function extension overrode a specialized representation"

end Dispatch

end Inclusion.Tests.Function
