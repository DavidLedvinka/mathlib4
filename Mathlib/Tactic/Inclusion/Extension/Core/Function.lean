/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Extension.Core.Init
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Function

/-!
# Function applications and quantified hypotheses

These extensions operate on pointwise function representations supplied by other inclusion
families. They do not choose an inclusion representation for a function's range.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- Apply a pointwise inclusion under a binder, after trying operation-specific extensions. -/
@[inclusion_ext(_ : _ → _) _]
def functionApplication : InclusionExt where
  family := `core
  priority := eval_prio low + 1
  derive := deriveFunctionApplication

/-- Collect quantified and pointwise bounds using the existing hypothesis extensions. -/
@[hypothesis_ext _]
def functionHyp : HypothesisExt where
  family := `core
  derive h := do
    let requests := (← read).iExprs.valuesArray.filter fun e =>
      e.expr.isApp || e.iType.function?.isSome
    if requests.isEmpty then return
    let type ← whnf (← inferType h)
    unless ← isProp type do return
    for iExpr in requests do
      let saved ← saveState
      try
        if let .forallE _ domain _ _ := type then
          if ← isProp domain then
            deriveConditionalHyp iExpr h
          else
            if iExpr.iType.function?.isSome then
              deriveForallFunctionHyp iExpr h
            deriveSpecializedHyp iExpr h
        else if iExpr.iType.function?.isSome then
          deriveFunctionPointHyp iExpr h
      catch err =>
        trace[Tactic.inclusion] "Could not use {type} for {iExpr.expr}: {err.toMessageData}"
        restoreState saved

end Inclusion
