/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Lean.Compiler.IR.CompilerM
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.DiscrTree

/-!
# Discrimination-tree-indexed environment extensions

This file provides an API for scoped environment extensions whose declarations are indexed by
elaborated expression patterns in named `DiscrTree`s.
-/

public meta section

open Lean Elab Term Lean.Meta

namespace DiscrTreeExt

/-- Evaluate `declName` as a value of type `α`, checking that its Lean type is `typeName`. -/
def evalDecl (α : Type) (typeName declName : Name) : ImportM α := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck α opts typeName declName

/-- The tree name, discrimination-tree paths, and declaration name stored in an `.olean` entry. -/
abbrev Entry := Name × Array (Array DiscrTree.Key) × Name

/-- The state of a named-discrimination-tree environment extension. -/
structure State (α : Type) where
  /-- The evaluated declaration values indexed first by tree name and then by expression pattern. -/
  tree : NameMap (DiscrTree α) := {}
  /-- The names of declarations erased in the current scope. -/
  erased : PHashSet Name := {}
  deriving Inhabited

/-- A scoped environment extension containing declaration values indexed by a tree name and
expression patterns. -/
abbrev EnvExt (α : Type) := ScopedEnvExtension Entry (Entry × α) (State α)

variable {α : Type}

/-- Verify that `declName` is registered and mark it as erased in the current scope. -/
def State.eraseDecl {m : Type → Type} [Monad m] [MonadError m]
    (state : State α) (nameOf : α → Name) (attrName declName : Name) : m (State α) := do
  let registered := state.tree.toArray.any fun (_, tree) =>
    tree.values.any (nameOf · == declName)
  unless registered && !state.erased.contains declName do
    throwError "'{declName}' does not have [{attrName}] attribute"
  return { state with erased := state.erased.insert declName }

/-- Return the declaration values in `treeNames` whose patterns match `e`, without filtering erased
declarations. -/
def State.getMatch (state : State α) (treeNames : NameSet) (e : Expr) : MetaM (Array α) := do
  let mut results? : Option (Array α) := none
  for treeName in treeNames do
    if let some tree := state.tree.find? treeName then
      let matched ← tree.getMatch e
      unless matched.isEmpty do
        results? := some <| match results? with
          | some results => results ++ matched
          | none => matched
  return results?.getD #[]

/-- Return the declaration values whose patterns match `e`, ordered by increasing priority.
Erased declarations are not filtered. -/
def State.getSortedMatch (state : State α) (treeNames : NameSet) (e : Expr)
    (priority : α → Nat) : MetaM (Array α) := do
  return (← state.getMatch treeNames e).qsort fun a b => priority a < priority b

/-- Create a scoped environment extension whose declarations have type `typeName`. By default, the
extension is named after the declaration in which this function is called. -/
def initializeEnvExt (typeName : Name)
    (envExtName : Name := by exact decl_name%) : IO (EnvExt α) := do
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq α := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks v) dt
  registerScopedEnvExtension {
    name := envExtName
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, _, n) ↦ return (e, ← evalDecl α typeName n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((treeName, kss, n), ext) ↦
      let discrTree := tree.find? treeName |>.getD {}
      { tree := tree.insert treeName (insert kss ext discrTree), erased := erased.erase n }
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

/-- Evaluate `declName` and add it to the tree selected by `treeOf` under the given expression
patterns. -/
def addDecl (attrName : Name) (envExt : EnvExt α) (typeName declName : Name)
    (treeOf : α → Name) (patterns : Array Syntax) (kind : AttributeKind) : AttrM Unit := do
  let env ← getEnv
  ensureAttrDeclIsMeta attrName declName kind
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid attribute `{attrName}`, declaration is in an imported module"
  if (IR.getSorryDep env declName).isSome then return
  let ext ← evalDecl α typeName declName
  envExt.add ((treeOf ext, ← elabExtKeys patterns, declName), ext) kind

/-- Mark `declName` as erased from `envExt` in the current scope. -/
def eraseDecl (envExt : EnvExt α) (nameOf : α → Name)
    (attrName declName : Name) : AttrM Unit := do
  let state ← (envExt.getState (← getEnv)).eraseDecl nameOf attrName declName
  modifyEnv fun env => envExt.modifyState env fun _ => state

end DiscrTreeExt
