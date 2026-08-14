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

open Lean Meta DiscrTreeExt

namespace Inclusion

structure InclusionExt where
  declName : Name := by exact decl_name%
  userName : Name := by exact decl_name%
  derive (e : Expr) : InclusionM ExprInclusionBody
  priority : Nat := eval_prio default

structure HypothesisExt where
  declName : Name := by exact decl_name%
  userName : Name := by exact decl_name%
  derive (h type : Expr) : HypothesisM Unit
  priority : Nat := eval_prio default

/-- A named family of inclusion and hypothesis extensions. -/
structure InclusionFamily where
  ref : Name
  inclusionExt : EnvExt InclusionExt
  hypothesisExt : EnvExt HypothesisExt
  deriving Nonempty

abbrev InclusionFamilies := Std.HashMap Name InclusionFamily

initialize inclusionFamiliesRef : IO.Ref InclusionFamilies ← IO.mkRef {}

/-- Register an inclusion family containing a separate inclusion and hypothesis extension. -/
def registerInclusionFamily (name : Name) (ref : Name := by exact decl_name%) :
    IO InclusionFamily := do
  if (← inclusionFamiliesRef.get).contains name then
    throw <| IO.userError s!"Inclusion family '{name}' is already registered"
  let inclusionExt ← initializeEnvExt ``InclusionExt (ref.str "inclusionExt")
  let hypothesisExt ← initializeEnvExt ``HypothesisExt (ref.str "hypothesisExt")
  let family := { ref, inclusionExt, hypothesisExt }
  inclusionFamiliesRef.modify (·.insert name family)
  return family

/-- Return the registered inclusion family named `name`. -/
def getInclusionFamily? (name : Name) : CoreM (Option InclusionFamily) := do
  let family? := (← inclusionFamiliesRef.get)[name]?
  if let some family := family? then
    recordExtraModUseFromDecl (isMeta := true) family.ref
  return family?

/-- Return the registered inclusion family named `name`, or fail if it is not registered. -/
def getInclusionFamily (name : Name) : CoreM InclusionFamily := do
  let some family ← getInclusionFamily? name
    | throwError "Unknown inclusion family '{name}'"
  return family

private def getExtMatches {α β γ : Type}
    (extType : InclusionFamily → ScopedEnvExtension β γ (DiscrTreeExt.State α))
    (priority : α → Nat)
    (families : Array Name) (e : Expr) :
    MetaM (Array (Name × α)) := do
  let env ← getEnv
  let mut matched := #[]
  for familyName in families do
    let family ← getInclusionFamily familyName
    let extState := (extType family).getState env
    for ext in ← extState.getMatch e do
      matched := matched.push (familyName, ext)
  return matched.qsort fun (_, a) (_, b) => priority a > priority b

/-- Return the matching inclusion extensions in the enabled families, highest priority first. -/
def getInclusionExtMatches (families : Array Name) (e : Expr) :
    MetaM (Array (Name × InclusionExt)) :=
  getExtMatches InclusionFamily.inclusionExt InclusionExt.priority families e

/-- Return the matching hypothesis extensions in the enabled families, highest priority first. -/
def getHypothesisExtMatches (families : Array Name) (e : Expr) :
    MetaM (Array (Name × HypothesisExt)) :=
  getExtMatches InclusionFamily.hypothesisExt HypothesisExt.priority families e

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

end InclusionParam

end Inclusion
