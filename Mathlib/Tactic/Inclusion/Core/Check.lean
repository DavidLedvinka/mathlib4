/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core

/-!
# Compiled checks for the `inclusion` tactic

This file compiles parameterized inclusion functions for repeated evaluation and implements
parameter search. It does not construct a proof or assign the current goal.
-/

@[expose] public meta section

open Lean Meta

namespace Inclusion

/-- A request to search for the smallest successful value of an inclusion parameter, up to `max`.
The search assumes that success is monotone in the parameter. -/
structure InclusionParamSearch where
  name : Name
  max : Nat

/-- A compiled inclusion function of one searched natural-number parameter. -/
abbrev CompiledInclusionFunction := Nat → IntervalBool

/-- Compile an inclusion function after fixing every parameter except `paramIdx`. -/
def ExprInclusion.compile (exprInclusion : ExprInclusion) (paramValues : Array Nat)
    (paramIdx : Nat) : MetaM CompiledInclusionFunction := do
  withLocalDeclD `param (mkConst ``Nat) fun param => do
    let paramExprs := paramValues.mapIdx fun i value =>
      if i = paramIdx then param else mkNatLit value
    let inclusion ← mkLambdaFVars #[param] (mkAppN exprInclusion.inclusion paramExprs)
    let inclusionType ← mkArrow (mkConst ``Nat) (mkConst ``IntervalBool)
    unsafe evalExpr CompiledInclusionFunction inclusionType inclusion

/-- Find the smallest value of parameter `paramIdx`, up to `max`, for which `check` succeeds.

The search first finds a successful upper bound exponentially and then binary-searches the bracket.
This avoids evaluating an unnecessarily enormous value first when the cost of a parameter, such as
the depth of an interval split, grows rapidly. -/
def findMinimalInclusionParam? (check : CompiledInclusionFunction) (max : Nat) :
    MetaM (Option Nat) := do
  let succeeds (value : Nat) : MetaM Bool := do
    match check value with
    | .true => return true
    | .false => throwError "The proposition is provably false"
    | .undetermined => return false
  if ← succeeds 0 then
    return some 0
  if max = 0 then
    return none
  let mut lower := 0
  let mut upper := 1
  let mut successfulUpper? := none
  while successfulUpper?.isNone && lower < max do
    upper := min upper max
    if ← succeeds upper then
      successfulUpper? := some upper
    else
      lower := upper
      upper := upper * 2
  let some successfulUpper := successfulUpper? | return none
  let mut binaryLower := lower + 1
  let mut binaryUpper := successfulUpper
  while binaryLower < binaryUpper do
    let middle := binaryLower + (binaryUpper - binaryLower) / 2
    if ← succeeds middle then
      binaryUpper := middle
    else
      binaryLower := middle + 1
  return some binaryLower

/-- Check whether `inclusion` can prove `goal` using compiled computation, without constructing a
proof of the goal or assigning it to a metavariable. If `search?` is present, compile the inclusion
function once and return the smallest successful value of the searched parameter. -/
def inclusionCheckCore (goal : Expr) (config : InclusionConfig)
    (search? : Option InclusionParamSearch := none) : MetaM (Option (Name × Nat)) := do
  if config.kernel || config.native then
    throwError "`inclusion?` always uses compiled checking; +kernel and +native are not supported"
  let enabledParams := match search? with
    | some search => config.enabledParams.insert search.name
    | none => config.enabledParams
  let goal ← instantiateMVars goal
  unless ← isProp goal do
    throwError "The goal is not a proposition"
  let exprInclusion ← (toExprInclusion goal).run enabledParams config.families
  let paramValues ← exprInclusion.resolveParamValues <| match search? with
    | some search => config.paramValues.insert search.name 0
    | none => config.paramValues
  match search? with
  | none =>
    let inclusionExpr := mkAppN exprInclusion.inclusion (paramValues.map mkNatLit)
    match ← compileInclusionCheck inclusionExpr with
    | .true => return none
    | .false => throwError "The proposition is provably false"
    | .undetermined => throwError "The proposition was not proven true or false."
  | some search =>
    let some paramIdx := exprInclusion.params.findIdx? (· == search.name)
      | throwError "The inclusion parameter '{search.name}' is not used by this computation"
    let check ← exprInclusion.compile paramValues paramIdx
    let some value ← findMinimalInclusionParam? check search.max
      | throwError "No value of inclusion parameter '{search.name}' at most {search.max} verified \
          the proposition"
    return some (search.name, value)

end Inclusion
