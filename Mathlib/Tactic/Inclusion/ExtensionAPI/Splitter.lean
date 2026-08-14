/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.Splitter
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Basic

/-!
# API for split inclusion variables

This file defines helpers for attaching covers produced by `Splitter` instances to inclusion
variables.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- Construct the cover of `iType` at `depth` using its registered `Splitter` instance. -/
def IType.mkSplitterCover (iType : IType) (depth : Expr) : MetaM Expr := do
  let splitterType ←
    mkAppOptM ``Splitter #[iType.setType, iType.elemType, iType.toSetInst]
  let splitter ← try synthInstance splitterType catch _ =>
    throwError "No `Splitter` instance is registered for {iType.setType}"
  mkAppOptM ``Splitter.cover
    #[iType.setType, iType.elemType, iType.toSetInst, splitter, depth]

/-- Construct a splitter cover controlled by the explicitly enabled inclusion parameter
`paramName`, or return no cover when the parameter is not enabled. -/
def mkParametricSplitterCover (paramName : Name) (iExpr : IExpr) :
    InclusionM (Option Expr) := do
  let context ← read
  unless context.enabledParams.contains paramName do return none
  return some (← iExpr.iType.mkSplitterCover (← getParam paramName))

end Inclusion
