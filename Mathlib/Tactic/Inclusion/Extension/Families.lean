/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Extensions

/-!
# Standard families for the `inclusion` tactic

This file registers the standard extension families used by the `inclusion` tactic.
-/

public meta section

namespace Inclusion

initialize realDyadicFamily : InclusionFamily ← registerInclusionFamily `real.dyadic

end Inclusion
