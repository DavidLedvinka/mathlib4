/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core
meta import Lean.Elab.ConfigEval

/-!
# Elaboration of the `inclusion` tactic

This file defines the syntax and elaborator for the `inclusion` tactic.
-/

public meta section

open scoped Lean.Elab.ConfigEval

open Lean Elab Tactic
open Lean.Parser.Tactic

namespace Inclusion

declare_config_elab elabInclusionConfig InclusionConfig where
  omit paramValues, families

declare_syntax_cat inclusionParam

syntax ident " := " num : inclusionParam

def elabInclusionFamilies (config : InclusionConfig) (familyStxs : Array Syntax) :
    TacticM InclusionConfig := do
  if familyStxs.isEmpty then
    throwError "At least one inclusion family must be specified"
  let mut families := #[]
  for familyStx in familyStxs do
    let family := familyStx.getId
    unless (← getInclusionFamily? family).isSome do
      throwError "Unknown inclusion family '{family}'"
    if families.contains family then
      throwError "Inclusion family '{family}' was enabled more than once"
    families := families.push family
  return { config with families }

private def elabInclusionParams (config : InclusionConfig) (paramStxs : Array Syntax) :
    TacticM InclusionConfig := do
  let mut config := config
  -- Use the parameter registry to reject misspelled or unregistered parameter names.
  let params := inclusionParamExt.getState (← getEnv)
  for paramStx in paramStxs do
    let `(inclusionParam| $name:ident := $value:num) := paramStx
      | throwUnsupportedSyntax
    let name := name.getId
    unless (params.find? name).isSome do
      throwError "Unknown inclusion parameter '{name}'"
    if config.paramValues.contains name then
      throwError "Inclusion parameter '{name}' was specified more than once"
    config := { config with paramValues := config.paramValues.insert name value.getNat }
  return config

def inclusionTactic (config : InclusionConfig) : TacticM Unit :=
  closeMainGoalUsing `inclusion fun goal _ => inclusionCore goal config

-- The user supplies ordinary `optConfig`, a required family list, and an optional parameter list.
syntax (name := inclusion) "inclusion" optConfig " [" ident,* "]"
  (" (" inclusionParam,* ")")? : tactic

elab_rules : tactic
  | `(tactic| inclusion $cfg:optConfig [$families,*] $[($params,*)]?) => do
      let config ← elabInclusionConfig cfg
      -- Validate the custom family list and add it to the configuration.
      let config ← elabInclusionFamilies config families.getElems
      -- Normalize an absent optional parameter list to an empty array.
      let params := params.map (·.getElems) |>.getD #[]
      let config ← elabInclusionParams config params
      inclusionTactic config

end Inclusion
