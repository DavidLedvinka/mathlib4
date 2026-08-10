/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core
meta import Lean.Elab.ConfigEval
meta import Lean.Elab.Tactic.ElabTerm

/-!
# Elaboration of the `inclusion` tactic

This file defines the syntax and elaborator for the `inclusion` tactic.
-/

public meta section

open scoped Lean.Elab.ConfigEval

open Lean Elab Tactic
open Lean.Parser.Tactic

namespace Inclusion

declare_syntax_cat inclusionSetting
syntax ident " := " num : inclusionSetting
syntax "+" ident : inclusionSetting

/-- `inclusion` config elaborator. -/
declare_config_elab elabInclusionConfig InclusionConfig where
  omit paramValues, families

def elabInclusionSettings (config : InclusionConfig)
    (settings : Array Syntax) : TacticM InclusionConfig := do
  if settings.isEmpty then
    return config
  let mut config := config
  let env ← getEnv
  let params := inclusionParamExt.getState env
  let inclusionFamilies := (inclusionExt.getState env).tree
  let hypothesisFamilies := (hypothesisExt.getState env).tree
  for setting in settings do
    match setting with
    | `(inclusionSetting| $name:ident := $value:num) =>
      let name := name.getId
      unless (params.find? name).isSome do
        throwError "Unknown inclusion parameter '{name}'"
      if config.paramValues.contains name then
        throwError "Inclusion parameter '{name}' was specified more than once"
      config := { config with paramValues := config.paramValues.insert name value.getNat }
    | `(inclusionSetting| +$family:ident) =>
      let family := family.getId
      unless inclusionFamilies.contains family || hypothesisFamilies.contains family do
        throwError "Unknown inclusion family '{family}'"
      if config.families.contains family then
        throwError "Inclusion family '{family}' was enabled more than once"
      config := { config with families := config.families.push family }
    | _ => throwUnsupportedSyntax
  return config

def inclusionTactic (config : InclusionConfig) : TacticM Unit :=
  closeMainGoalUsing `inclusion fun goal _ => inclusionCore goal config

syntax (name := inclusion) "inclusion" optConfig (" [" inclusionSetting,* "]")? : tactic

elab_rules : tactic
  | `(tactic| inclusion $cfg:optConfig $[[$settings,*]]?) => do
      let config ← elabInclusionConfig cfg { families := #[`core, `real.dyadic] }
      let settings := settings.map (·.getElems) |>.getD #[]
      let config ← elabInclusionSettings config settings
      inclusionTactic config

end Inclusion
