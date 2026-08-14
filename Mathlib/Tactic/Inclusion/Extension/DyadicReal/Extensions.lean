/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic
public meta import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic
public meta import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Hypotheses
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Splitter

/-!
# Inclusion extensions for dyadic real intervals
-/

public meta section

open Lean Meta

namespace Inclusion

@[inclusionParam]
meta def splitParam : InclusionParamDecl where
  name := `split

private def mkRealCover (iExpr : IExpr) : InclusionM (Option Expr) :=
  mkParametricSplitterCover `split iExpr

@[inclusionExt real.dyadic | (_ : ℝ)]
meta def mkRealIVar : InclusionExt :=
  mkNDIVarExt (mkConst ``Real) (mkAppM ``Interval #[mkConst ``Dyadic]) mkRealCover

end Inclusion
