/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Types
public meta import Mathlib.Tactic.Inclusion.Core.DiscrTreeExt

/-!
# Environment extensions for the `inclusion` tactic

This file defines the environment extensions used in the `inclusion` tactic.
-/

public meta section

open Lean Meta Elab Term DiscrTreeExt

namespace Inclusion

structure InclusionExt where
  declName : Name := by exact decl_name%
  userName : Name := by exact decl_name%
  family : Name
  derive (e : Expr) : InclusionM ExprInclusionBody
  priority : Nat := eval_prio default

initialize inclusionExt : EnvExt InclusionExt ← initializeEnvExt ``InclusionExt

structure HypothesisExt where
  declName : Name := by exact decl_name%
  userName : Name := by exact decl_name%
  family : Name
  derive (h type : Expr) : HypothesisM Unit
  priority : Nat := eval_prio default

initialize hypothesisExt : EnvExt HypothesisExt ← initializeEnvExt ``HypothesisExt

syntax (name := inclusionExtAttr) "inclusionExt" term,+ : attr

/-- The `inclusionExt` attribute registers an inclusion-function extension. -/
initialize registerBuiltinAttribute {
  name := `inclusionExtAttr
  descr := "adds an inclusion-function extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| inclusionExt $es,*) =>
      addDecl `inclusionExt inclusionExt ``InclusionExt declName
        (·.family) (es.getElems.map (·.raw)) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Inclusion extensions cannot be erased by declaration"
}

syntax (name := hypothesisExtAttr) "hypothesisExt" term,+ : attr

/-- The `hypothesisExt` attribute registers a hypothesis extension. -/
initialize registerBuiltinAttribute {
  name := `hypothesisExtAttr
  descr := "adds a hypothesis extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| hypothesisExt $es,*) =>
      addDecl `hypothesisExt hypothesisExt ``HypothesisExt declName
        (·.family) (es.getElems.map (·.raw)) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Hypothesis extensions cannot be erased by declaration"
}

section InclusionParam

structure InclusionParamDecl where
  name : Name
  defaultValue : Option Nat := none

structure InclusionParams where
  decls : NameMap InclusionParamDecl := {}
  deriving Inhabited

def InclusionParams.find? (params : InclusionParams) (name : Name) : Option InclusionParamDecl :=
  params.decls.find? name

def mkInclusionParamDecl (n : Name) : ImportM InclusionParamDecl := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck InclusionParamDecl opts ``InclusionParamDecl n

initialize inclusionParamExt :
    ScopedEnvExtension Name (Name × InclusionParamDecl) InclusionParams ←
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ n => return (n, ← mkInclusionParamDecl n)
    toOLeanEntry := (·.1)
    addEntry := fun state (_, decl) =>
      { state with decls := state.decls.insert decl.name decl }
  }

syntax (name := inclusionParamAttr) "inclusionParam" : attr

/-- The `inclusionParam` attribute registers a named natural-number inclusion parameter. -/
initialize registerBuiltinAttribute {
  name := `inclusionParamAttr
  descr := "registers an inclusion-tactic parameter"
  applicationTime := .afterCompilation
  add := fun declName _ kind => do
    let env ← getEnv
    ensureAttrDeclIsMeta `inclusionParam declName kind
    unless (env.getModuleIdxFor? declName).isNone do
      throwError "invalid attribute `inclusionParam`, declaration is in an imported module"
    if (IR.getSorryDep env declName).isSome then return
    let decl ← mkInclusionParamDecl declName
    let params := inclusionParamExt.getState env
    if params.decls.contains decl.name then
      throwError "Inclusion parameter '{decl.name}' is already registered"
    inclusionParamExt.add (declName, decl) kind
}

end InclusionParam

end Inclusion
