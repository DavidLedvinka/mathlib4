module

public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting

set_option linter.style.header false

@[expose] public section

namespace Inclusion.Experimental.CheckTestExtensions

@[inclusionParam]
meta def fixedParam : InclusionParamDecl where
  name := `checkFixed

@[inclusionParam]
meta def fixedParam2 : InclusionParamDecl where
  name := `checkFixed2

def parameterizedEndpoint : ℝ := 0

def parameterizedEndpointInterval (n m : ℕ) : Interval Dyadic :=
  if n = 7 ∧ m = 11 then Inclusion.ofNat 0 else Interval.univ Dyadic

@[inclusionOp real.dyadic]
theorem parameterizedEndpoint_mem (checkFixed checkFixed2 : ℕ) :
    parameterizedEndpoint ∈ parameterizedEndpointInterval checkFixed checkFixed2 := by
  simp only [parameterizedEndpointInterval]
  split
  · simpa [parameterizedEndpoint] using Inclusion.ofNat_mem 0
  · exact Inclusion.mem_univ _

end Inclusion.Experimental.CheckTestExtensions
