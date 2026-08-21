/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.BallDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.BallDyadicReal.Hypotheses
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Basic
public meta import Qq

/-!
# Inclusion extensions for dyadic real balls
-/

public meta section

open Lean Meta Qq

namespace Inclusion

namespace BallDyadicReal

/-- The binary precision used when constructing the center of a ball from hypotheses. -/
@[inclusionParam]
def centerPrecParam : InclusionParamDecl where
  name := `centerPrec
  type := q(ℕ)

/-- The binary precision used when constructing the radius of a ball from hypotheses. -/
@[inclusionParam]
def radiusPrecParam : InclusionParamDecl where
  name := `radiusPrec
  type := q(ℕ)

private def quoteNatOption : Option Expr → Q(Option ℕ)
  | none => q(none)
  | some value =>
    have value : Q(ℕ) := value
    q(some $value)

/-- Construct the parameterized hypothesis representation used by dyadic real balls. -/
def mkHypothesisType (_ : IExpr) : InclusionM HypothesisType := do
  let centerPrec? := quoteNatOption (← InclusionM.getParam? `centerPrec)
  let radiusPrec? := quoteNatOption (← InclusionM.getParam? `radiusPrec)
  let iType : IType :=
    ⟨q(ℝ), q(CenteredBounds Dyadic Dyadic), q(instToSetCenteredBoundsDyadicReal)⟩
  return ⟨iType, q(hypothesisAccumulator $centerPrec? $radiusPrec?)⟩

/-- Convert direct dyadic-interval hypotheses to the centered representation. -/
@[hypothesisExt ball_dyadic_real | _ ∈ (_ : Interval Dyadic)]
def intervalMembershipHyp : HypothesisExt where
  derive h := do
    let some (e, I, _) := toSetMem? (← instantiateMVars (← inferType h)) | failure
    unless ← isDefEq (← inferType I) q(Interval Dyadic) do failure
    let some iVar ← findIVar? e | failure
    let inclusionBody ← mkAppM ``centeredBoundsOfInterval #[I]
    let proofBody ← mkAppM ``mem_centeredBoundsOfInterval #[h]
    addInclusionHyp iVar { inclusionBody, proofBody }

/-- Construct an inclusion variable for a real expression using a dyadic ball. -/
@[inclusionExt ball_dyadic_real | (_ : ℝ)]
def mkRealIVar : InclusionExt :=
  let iType : IType := ⟨q(ℝ), q(Ball Dyadic Dyadic), q(instToSetBallDyadicReal)⟩
  mkNDIVarExt iType mkHypothesisType

end BallDyadicReal

end Inclusion
