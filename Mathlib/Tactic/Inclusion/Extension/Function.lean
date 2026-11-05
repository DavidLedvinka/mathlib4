/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Inclusion.Core.ToSet

/-!
# Pointwise inclusions of functions

An inclusion function bounds each value of a function separately. Refinement is pointwise;
a bound at a single index gives a universal inclusion at all other indices.
-/

@[expose] public section

namespace Inclusion

variable {ι α Iα : Type*} [ToSet Iα α]

instance instToSetFun : ToSet (ι → Iα) (ι → α) where
  toSet I := {f | ∀ i, f i ∈ I i}

theorem fun_mem {f : ι → α} {I : ι → Iα} (h : ∀ i, f i ∈ I i) : f ∈ I := h

theorem apply_mem {f : ι → α} {I : ι → Iα} (h : f ∈ I) (i : ι) : f i ∈ I i := h i

instance [Univ Iα α] : Univ (ι → Iα) (ι → α) where
  univ := fun _ => Univ.univ α
  mem_univ _ _ := Univ.mem_univ _

instance [Refine Iα α] : Refine (ι → Iα) (ι → α) where
  refine I J := fun i => Refine.refine α (I i) (J i)
  mem_refine hI hJ i := Refine.mem_refine (hI i) (hJ i)

instance [Coarsen Iα α] : Coarsen (ι → Iα) (ι → α) where
  coarsen I J := fun i => Coarsen.coarsen α (I i) (J i)
  mem_coarsen_left h i := Coarsen.mem_coarsen_left (h i)
  mem_coarsen_right h i := Coarsen.mem_coarsen_right (h i)

theorem mem_update_univ [DecidableEq ι] [Univ Iα α] {f : ι → α} {i : ι} {I : Iα}
    (h : f i ∈ I) : f ∈ Function.update (fun _ => (Univ.univ α : Iα)) i I := by
  intro j
  by_cases hij : j = i
  · simpa [hij] using h
  · simpa [Function.update_of_ne hij] using Univ.mem_univ (f j)

theorem mem_dite_univ [Univ Iα α] {p : Prop} [Decidable p] {x : α} {I : p → Iα}
    (h : ∀ hp, x ∈ I hp) : x ∈ dite p I (fun _ => Univ.univ α) := by
  split_ifs with hp
  · exact h hp
  · exact Univ.mem_univ x

end Inclusion
