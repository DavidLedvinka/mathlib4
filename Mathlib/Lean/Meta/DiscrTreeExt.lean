/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Init
public meta import Lean.Compiler.IR.CompilerM
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.DiscrTree

/-!
# Discrimination-tree-indexed environment extensions

This file provides an API for scoped environment extensions whose declarations are indexed by
elaborated expression patterns in a `DiscrTree`.
-/

public meta section

open Lean Elab Term Lean.Meta

namespace DiscrTreeExt

/-- Evaluate `declName` as a value of type `α`, checking that its Lean type is `typeName`. -/
def evalDecl (α : Type) (typeName declName : Name) : ImportM α := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck α opts typeName declName

/-- The discrimination-tree paths and declaration name stored in an `.olean` entry. -/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/-- The state of a discrimination-tree environment extension. -/
structure State (α : Type) where
  /-- The evaluated declaration values indexed by their expression patterns. -/
  tree : DiscrTree α := {}
  /-- The names of declarations erased in the current scope. -/
  erased : PHashSet Name := {}
  deriving Inhabited

/-- A scoped environment extension containing declaration values indexed by expression patterns. -/
abbrev EnvExt (α : Type) := ScopedEnvExtension Entry (Entry × α) (State α)

variable {α : Type}

/-- Return the declaration values whose patterns match `e`, without filtering erased
declarations. -/
@[inline]
def State.getMatch (state : State α) (e : Expr) : MetaM (Array α) := state.tree.getMatch e

/-- Mark `declName` as erased without checking that it is registered. -/
def State.eraseCore (state : State α) (declName : Name) : State α :=
  { state with erased := state.erased.insert declName }

/-- Verify that `declName` is registered and mark it as erased in the current scope. -/
def State.eraseDecl {m : Type → Type} [Monad m] [MonadError m]
    (state : State α) (nameOf : α → Name) (attrName declName : Name) : m (State α) := do
  unless state.tree.containsValueP (nameOf · == declName) && !state.erased.contains declName do
    throwError "'{declName}' does not have [{attrName}] attribute"
  return state.eraseCore declName

/-- Create a scoped environment extension whose declarations have type `typeName`. By default, the
environment extension is named after the declaration in which this function is called. -/
def initializeEnvExt (typeName : Name)
    (envExtName : Name := by exact decl_name%) : IO (EnvExt α) := do
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq α := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks v) dt
  registerScopedEnvExtension {
    name := envExtName
    mkInitial := pure {}
    ofOLeanEntry := fun _ entry@(_, declName) ↦
      return (entry, ← evalDecl α typeName declName)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((paths, declName), decl) ↦
      { tree := insert paths decl tree, erased := erased.erase declName }
  }

/-- Elaborate expression patterns into `DiscrTree` paths. -/
def elabExtKeys (patterns : Array Syntax) : CoreM (Array (Array DiscrTree.Key)) :=
  MetaM.run' <| patterns.mapM fun stx => do
    let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
      withReader ({ · with ignoreTCFailures := true }) do
        let e ← elabTerm stx none
        let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
        return e
    DiscrTree.mkPath e

/-- Evaluate `declName` and add it to `envExt` under the given expression patterns. Return whether
the declaration was added. -/
def addDecl (attrName : Name) (envExt : EnvExt α) (typeName declName : Name)
    (patterns : Array Syntax) (kind : AttributeKind) : AttrM Bool := do
  let env ← getEnv
  ensureAttrDeclIsMeta attrName declName kind
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid attribute `{attrName}`, declaration is in an imported module"
  if (IR.getSorryDep env declName).isSome then return false
  let decl ← evalDecl α typeName declName
  envExt.add ((← elabExtKeys patterns, declName), decl) kind
  return true

/-- Mark `declName` as erased from `envExt` in the current scope. -/
def eraseDecl (envExt : EnvExt α) (nameOf : α → Name)
    (attrName declName : Name) : AttrM Unit := do
  let state ← (envExt.getState (← getEnv)).eraseDecl nameOf attrName declName
  modifyEnv fun env => envExt.modifyState env fun _ => state

end DiscrTreeExt
