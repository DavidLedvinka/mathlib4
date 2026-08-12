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
  derive (e : Expr) : InclusionM ExprInclusionBody
  priority : Nat := eval_prio default

structure HypothesisExt where
  declName : Name := by exact decl_name%
  userName : Name := by exact decl_name%
  derive (h type : Expr) : HypothesisM Unit
  priority : Nat := eval_prio default

/-- A named family of inclusion and hypothesis extensions. -/
structure InclusionFamily where
  inclusionExt : EnvExt InclusionExt
  hypothesisExt : EnvExt HypothesisExt
  deriving Nonempty

abbrev InclusionFamilyMap := Std.HashMap Name InclusionFamily

initialize inclusionFamilyMapRef : IO.Ref InclusionFamilyMap ← IO.mkRef {}

/-- Register an inclusion family containing a separate inclusion and hypothesis extension. -/
def registerInclusionFamily (name : Name) (ref : Name := by exact decl_name%) :
    IO InclusionFamily := do
  if (← inclusionFamilyMapRef.get).contains name then
    throw <| IO.userError s!"Inclusion family '{name}' is already registered"
  let inclusionExt ←
    (initializeEnvExt ``InclusionExt (Name.str ref "inclusionExt") : IO (EnvExt InclusionExt))
  let hypothesisExt ←
    (initializeEnvExt ``HypothesisExt (Name.str ref "hypothesisExt") :
      IO (EnvExt HypothesisExt))
  let family := { inclusionExt, hypothesisExt }
  inclusionFamilyMapRef.modify (·.insert name family)
  return family

/-- Return the registered inclusion family named `name`. -/
def getInclusionFamily? (name : Name) : CoreM (Option InclusionFamily) := do
  let family? := (← inclusionFamilyMapRef.get)[name]?
  if let some family := family? then
    recordExtraModUseFromDecl (isMeta := true) family.inclusionExt.ext.name
    recordExtraModUseFromDecl (isMeta := true) family.hypothesisExt.ext.name
  return family?

private def getInclusionFamily (name : Name) : CoreM InclusionFamily := do
  let some family ← getInclusionFamily? name
    | throwError "Unknown inclusion family '{name}'"
  return family

initialize
  discard <| registerInclusionFamily `core

syntax (name := inclusionExtAttr) "inclusionExt " ident " | " term,+ : attr

/-- The `inclusionExt` attribute registers an inclusion-function extension. -/
initialize registerBuiltinAttribute {
  name := `inclusionExtAttr
  descr := "adds an inclusion-function extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| inclusionExt $familyName:ident | $es,*) => do
      let family ← getInclusionFamily familyName.getId
      addDecl `inclusionExt family.inclusionExt ``InclusionExt declName
        (es.getElems.map (·.raw)) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Inclusion extensions cannot be erased by declaration"
}

syntax (name := hypothesisExtAttr) "hypothesisExt " ident " | " term,+ : attr

/-- The `hypothesisExt` attribute registers a hypothesis extension. -/
initialize registerBuiltinAttribute {
  name := `hypothesisExtAttr
  descr := "adds a hypothesis extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| hypothesisExt $familyName:ident | $es,*) => do
      let family ← getInclusionFamily familyName.getId
      addDecl `hypothesisExt family.hypothesisExt ``HypothesisExt declName
        (es.getElems.map (·.raw)) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Hypothesis extensions cannot be erased by declaration"
}

private def getFamilyMatches {α : Type} (familyNames : Array Name) (e : Expr)
    (getExt : InclusionFamily → EnvExt α) : MetaM (Array (Name × α)) := do
  let env ← getEnv
  let mut matched := #[]
  for familyName in familyNames do
    let family ← getInclusionFamily familyName
    for ext in ← (getExt family).getState env |>.getMatch e do
      matched := matched.push (familyName, ext)
  return matched

private def getSortedFamilyMatches {α : Type} (familyNames : Array Name) (e : Expr)
    (getExt : InclusionFamily → EnvExt α) (priority : α → Nat) :
    MetaM (Array (Name × α)) := do
  return (← getFamilyMatches familyNames e getExt).qsort fun a b =>
    priority a.2 < priority b.2

/-- Return the matching inclusion extensions in the enabled families, ordered by priority. -/
def getInclusionExtMatches (families : Array Name) (e : Expr) :
    MetaM (Array (Name × InclusionExt)) :=
  getSortedFamilyMatches families e (·.inclusionExt) (·.priority)

/-- Return the matching hypothesis extensions in the enabled families, ordered by priority. -/
def getHypothesisExtMatches (families : Array Name) (e : Expr) :
    MetaM (Array (Name × HypothesisExt)) :=
  getSortedFamilyMatches families e (·.hypothesisExt) (·.priority)

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
