/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Check
public meta import Mathlib.Tactic.Inclusion.Core.Elab

/-!
# Elaboration of the `inclusion?` tactic

This file defines the syntax and elaborator for compiled inclusion checks and parameter search.
-/

public meta section

open Lean Elab Tactic
open Lean.Parser.Tactic

namespace Inclusion

declare_syntax_cat inclusionCheckParam

syntax ident " := " num : inclusionCheckParam
syntax ident " := " "search" "[" num "]" : inclusionCheckParam

private def elabInclusionCheckParams (config : InclusionConfig) (paramStxs : Array Syntax) :
    TacticM (InclusionConfig × Option InclusionParamSearch) := do
  let registeredParams := inclusionParamExt.getState (← getEnv)
  let mut config := config
  let mut search? : Option InclusionParamSearch := none
  for paramStx in paramStxs do
    let (name, value?, max?) ← match paramStx with
      | `(inclusionCheckParam| $name:ident := $value:num) =>
        pure (name.getId, some value.getNat, none)
      | `(inclusionCheckParam| $name:ident := search[$max:num]) =>
        pure (name.getId, none, some max.getNat)
      | _ => throwUnsupportedSyntax
    unless (registeredParams.find? name).isSome do
      throwError "Unknown inclusion parameter '{name}'"
    if config.paramValues.contains name || search?.any (·.name == name) then
      throwError "Inclusion parameter '{name}' was specified more than once"
    match value?, max? with
    | some value, none =>
      config := { config with paramValues := config.paramValues.insert name value }
    | none, some max =>
      if let some existing := search? then
        throwError "Cannot search inclusion parameters '{existing.name}' and '{name}' \
          simultaneously"
      search? := some { name, max }
    | _, _ => unreachable!
  return (config, search?)

/-- Run a compiled inclusion check without assigning a proof to the goal. -/
def inclusionCheckTactic (config : InclusionConfig)
    (search? : Option InclusionParamSearch := none) : TacticM Unit := withMainContext do
  match ← inclusionCheckCore (← getMainTarget) config search? with
  | none => logInfo "The compiled inclusion check succeeded."
  | some (name, value) =>
    logInfo m!"The compiled inclusion check succeeded with '{name} := {value}'."

/-- `inclusion?` checks whether `inclusion` can prove the goal using compiled computation, but does
not construct or assign a proof. A parameter value `name := search[max]` searches for the smallest
successful value at most `max`, assuming success is monotone in that parameter. -/
syntax (name := inclusion?) "inclusion?" optConfig " [" ident,* "]"
  (" (" inclusionCheckParam,* ")")? : tactic

elab_rules : tactic
  | `(tactic| inclusion? $cfg:optConfig [$families,*] $[($params,*)]?) => do
      let config ← elabInclusionConfig cfg
      let config ← elabInclusionFamilies config families.getElems
      let params := params.map (·.getElems) |>.getD #[]
      let (config, search?) ← elabInclusionCheckParams config params
      inclusionCheckTactic config search?

end Inclusion
