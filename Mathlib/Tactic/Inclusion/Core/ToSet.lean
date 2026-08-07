/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Set.Insert

/-!
# Definition of `ToSet` and basic API

This file defines the `ToSet` class and it's API needed for the `inclusion` tactic.

-/

@[expose] public section

namespace Inclusion

/-- A `ToSet Iα α` instance provides a way of interpreting elements of `Iα` as sets of `α`,
through a function `toSet : Iα → Set α`. In its use in the `inclusion` tactic, `Iα` will be
a type with good computational properties (such as `Interval Dyadic`) and `α` will be some
type that appears in the user's expression, such as `ℝ`. -/
class ToSet (Iα : Type*) (α : outParam Type*) where
  /-- The mapping of elements of `Iα` to sets in `α`. -/
  toSet : Iα → Set α

instance {Iα α : Type*} [ToSet Iα α] : CoeTC Iα (Set α) where
  coe := ToSet.toSet

instance {Iα α : Type*} [ToSet Iα α] : Membership α Iα where
  mem s a := a ∈ (s : Set α)

@[simp]
lemma mem_set_iff_mem_toSet {Iα α : Type*} [ToSet Iα α] (a : α) (s : Iα) :
  a ∈ s ↔ a ∈ (s : Set α) := Iff.rfl

lemma ToSet.mem_of_eq_of_mem {Iα α : Type*} [ToSet Iα α] {x y : α} {s : Iα}
    (hxy : x = y) (hy : y ∈ s) : x ∈ s := hxy ▸ hy

lemma ToSet.mem_of_mem_of_eq {Iα α : Type*} [ToSet Iα α] {x y : α} {s : Iα}
    (hxy : x = y) (hx : x ∈ s) : y ∈ s := hxy ▸ hx

/-- A `Univ Iα α` instance is a specification of an element `univ : Iα` such that
every element of `α` belongs to `univ`. This is useful for assigning a container to inclusion
variables that have no inclusion hypotheses. -/
class Univ (Iα α : Type*) [ToSet Iα α] where
  /-- A (computational) representative of the universal set. -/
  univ : Iα
  /-- Every element of `α` belongs to `univ`. -/
  mem_univ (x : α) : x ∈ univ

/-- A `Refine Iα α` instance is a specification of a function `refine : Iα → Iα → Iα` such that
for any `s t : Iα`, `s ∩ t ⊆ refine s t` as sets of `α`. This is useful for merging multiple
inclusion hypotheses of a single inclusion variable. -/
class Refine (Iα α : Type*) [ToSet Iα α] where
  /-- A (computable) function to refine two inclusion hypotheses. -/
  refine : Iα → Iα → Iα
  /-- If `x ∈ s` and `x ∈ t` then `x ∈ refine s t`. -/
  mem_refine {x : α} {s t : Iα} (hs : x ∈ s) (ht : x ∈ t) : x ∈ refine s t

open ToSet

section IntervalBool

/-- An `IntervalBool` represents the result of a `Prop` inclusion and is either
`true` (if the proposition is computed true), `false` (if the proposition is computed false), or
`undetermined` (if the computation is indeterminate). -/
inductive IntervalBool
  | true
  | false
  | undetermined

/-- The mapping from `IntervalBool` to `Set Prop` which identifies each option
(`true`, `false`, `undetermined`) with its set of possible outcomes
(`{True}`, `{False}`, `{True, False}` respectively). -/
def IntervalBool.toPropSet : IntervalBool → Set Prop
  | true => {True}
  | false => {False}
  | undetermined => {True, False}

instance : ToSet IntervalBool Prop := ⟨IntervalBool.toPropSet⟩

theorem true_of_mem_intervalBool_true {p : Prop} (hp : p ∈ IntervalBool.true) : p := by
  simpa [mem_set_iff_mem_toSet, toSet, IntervalBool.toPropSet] using hp

theorem true_of_mem_intervalBool_eq_true {p : Prop} {b : IntervalBool} (hp : p ∈ b)
    (hb : b = IntervalBool.true) : p :=
  true_of_mem_intervalBool_true (hb ▸ hp)

section CoverCheck

/-- A `CoverCheck Iα α` specifies a way to check whether an inclusion predicate
`P : Iα → IntervalBool` is true on a family of represented sets covering a given `s : Iα`.
This is used to split the inclusion set of an inclusion variable, allowing the predicate to be
checked separately on smaller sets to reduce the dependency effect. -/
structure CoverCheck (Iα α : Type*) [ToSet Iα α] where
  /-- Check whether `P` succeeds on a family of represented sets covering `s`. -/
  check (s : Iα) (P : Iα → IntervalBool) : IntervalBool
  /-- If `P` contains `p` on every represented set containing `x`, then `check s P` contains `p`
  whenever `x ∈ s`. -/
  mem_check (s : Iα) (P : Iα → IntervalBool) {p : Prop} {x : α}
    (hx : x ∈ s) (hp : ∀ t, x ∈ t → p ∈ P t) : p ∈ check s P

/-- The cover check that checks an inclusion predicate directly on the supplied set. -/
def CoverCheck.self {Iα α : Type*} [ToSet Iα α] : CoverCheck Iα α where
  check s P := P s
  mem_check := fun s _ _ _ hx hp ↦ hp s hx

end CoverCheck

end IntervalBool

end Inclusion
