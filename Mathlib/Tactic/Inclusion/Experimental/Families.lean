/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Extensions

/-!
# Experimental families for the `inclusion` tactic

This file registers the extension families used by the experimental implementations and tests.
-/

public meta section

namespace Inclusion.Experimental

initialize complexBallFamily : InclusionFamily ← registerInclusionFamily `complex.ball

initialize matrixVectorFamily : InclusionFamily ← registerInclusionFamily `matrix.vector

initialize realConcreteFamily : InclusionFamily ← registerInclusionFamily `real.concrete

initialize testFamily : InclusionFamily ← registerInclusionFamily `test.family

initialize testOtherFamily : InclusionFamily ← registerInclusionFamily `test.other

initialize testHypothesisFamily : InclusionFamily ← registerInclusionFamily `test.hypothesis

end Inclusion.Experimental
