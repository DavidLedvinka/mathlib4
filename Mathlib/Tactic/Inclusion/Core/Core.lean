/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Inclusion
public meta import Lean.Meta.Native

/-!
# Core implementation of the `inclusion` tactic

**TODO (NOT FOR CODEX)**
-/

@[expose] public meta section

open Lean Meta

namespace Inclusion

structure InclusionConfig where
  kernel : Bool := false
  native : Bool := false
  paramValues : NameMap Nat := {}
  families : Array Name := #[]

def InclusionConfig.enabledParams (config : InclusionConfig) : NameSet :=
  ⟨Std.TreeMap.map (fun _ _ ↦ ()) config.paramValues⟩

def compileInclusionCheck (inclusionExpr : Expr) : MetaM IntervalBool :=
  unsafe evalExpr IntervalBool (mkConst ``IntervalBool) inclusionExpr

def mkInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  match ← compileInclusionCheck inclusionExpr with
  | .true => return mkIntervalBoolRefl inclusionExpr
  | .false => throwError "The proposition is provably false"
  | .undetermined => throwError "The proposition was not proven true or false."

def mkKernelInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  let expectedType ← mkEq inclusionExpr (mkConst ``IntervalBool.true)
  let lemmaLevels := (collectLevelParams {} expectedType).params.toList
  try
    let lemmaName ← withOptions (Elab.async.set · false) do
      mkAuxLemma lemmaLevels expectedType (mkIntervalBoolRefl inclusionExpr)
    return mkConst lemmaName (lemmaLevels.map .param)
  catch _ =>
    throwError "The kernel failed to verify the proposition."

def mkNativeInclusionTrueProof (inclusionExpr : Expr) : MetaM Expr := do
  let result := mkApp (mkConst ``IntervalBool.isTrue) inclusionExpr
  match ← nativeEqTrue `inclusion result (axiomDeclRange? := (← getRef)) with
  | .success proof => mkAppM ``IntervalBool.eq_true_of_isTrue_eq_true #[proof]
  | .notTrue => throwError "Native computation could not verify the proposition."

def inclusionCore (goal : Expr) (config : InclusionConfig) : MetaM Expr := do
  if config.kernel && config.native then
    throwError "Cannot simultaneously enable +kernel and +native"
  let goal ← instantiateMVars goal
  unless ← isProp goal do
    throwError "The goal is not a proposition"
  let exprInclusion ← (toExprInclusion goal).run config.enabledParams config.families
  let paramExts := inclusionParamExt.getState (← getEnv)
  let paramValues ← exprInclusion.params.mapM fun name => do
    if let some value := config.paramValues.find? name then
      return value
    let some paramExt := paramExts.find? name
      | throwError "Unknown inclusion parameter '{name}'"
    let some value := paramExt.defaultValue
      | throwError "No value was supplied for inclusion parameter '{name}'"
    return value
  let paramExprs := paramValues.map mkNatLit
  let inclusionExpr := mkAppN exprInclusion.inclusion paramExprs
  let inclusionProof ←
    if config.native then
      mkNativeInclusionTrueProof inclusionExpr
    else if config.kernel then
      mkKernelInclusionTrueProof inclusionExpr
    else
      mkInclusionTrueProof inclusionExpr
  return exprInclusion.mkGoalProof goal paramExprs inclusionExpr inclusionProof

end Inclusion
