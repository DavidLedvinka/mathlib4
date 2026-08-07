module

public import Mathlib.Tactic.Inclusion.Core.ToSet

set_option linter.style.header false

@[expose] public section

namespace Inclusion

variable {Iα α : Type*}

/-- A procedure for checking a predicate on sufficiently many refinements of a represented set. -/
class Splitter (Iα α : Type*) [ToSet Iα α] where
  /-- The cover check obtained by refining a represented set to depth `n`. -/
  coverCheck (n : ℕ) : CoverCheck Iα α

end Inclusion
