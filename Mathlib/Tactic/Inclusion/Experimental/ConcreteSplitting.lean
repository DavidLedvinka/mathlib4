module

public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Families
public import Init.Data.Array.Lemmas

set_option linter.style.header false

@[expose] public section

open Lean Meta Elab Tactic
open Set

namespace Inclusion.Experimental

deriving instance DecidableEq for Interval

def coverMapListAux {Iα Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (head : Iα) : List Iα → (Iα → Iβ) → Iβ
  | [], F => F head
  | next :: rest, F =>
      Coarsen.coarsen (Iα := Iβ) (α := β) (F head) (coverMapListAux next rest F)

def coverMapList {Iα Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (source : Iα) : List Iα → (Iα → Iβ) → Iβ
  | [], F => F source
  | head :: rest, F => coverMapListAux head rest F

theorem mem_coverMapListAux {Iα Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (head : Iα) (rest : List Iα) (F : Iα → Iβ) {t : Iα} {y : β}
    (ht : t ∈ head :: rest) (hy : y ∈ F t) : y ∈ coverMapListAux head rest F := by
  induction rest generalizing head with
  | nil =>
      simp only [List.mem_singleton] at ht
      subst t
      exact hy
  | cons next rest ih =>
      change y ∈ Coarsen.coarsen (Iα := Iβ) (α := β)
        (F head) (coverMapListAux next rest F)
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Coarsen.mem_coarsen_left hy
      · exact Coarsen.mem_coarsen_right (ih next (by simpa only [List.mem_cons] using ht))

theorem mem_coverMapList {Iα α Iβ β : Type*} [ToSet Iα α] [ToSet Iβ β] [Coarsen Iβ β]
    (source : Iα) (pieces : List Iα) (F : Iα → Iβ) {x : α} {y : β}
    (hx : x ∈ source) (hcover : ∃ t ∈ pieces, x ∈ t)
    (hy : ∀ t, x ∈ t → y ∈ F t) : y ∈ coverMapList source pieces F := by
  rcases pieces with _ | ⟨head, rest⟩
  · exact hy source hx
  · obtain ⟨t, ht, hxt⟩ := hcover
    exact mem_coverMapListAux head rest F ht (hy t hxt)

def Cover.ofArray {Iα α : Type*} [ToSet Iα α] [DecidableEq Iα]
    (source : Iα) (pieces : Array Iα)
    (hcover : (source : Set α) ⊆ ⋃ t ∈ pieces, (t : Set α)) : Cover Iα α where
  coverMap := fun s F ↦ if s = source then coverMapList source pieces.toList F else F s
  mem_coverMap := by
    intro Iβ β _ _ s F x y hx hy
    split <;> rename_i h
    · apply mem_coverMapList source pieces.toList F (h ▸ hx) _ hy
      have hx' := hcover (h ▸ hx)
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨t, ht, hxt⟩ := hx'
      exact ⟨t, Array.mem_toList_iff.mpr ht, hxt⟩
    · exact hy s hx

class ConcreteIntervalCover (x : ℝ) where
  source : Interval Dyadic
  pieces : Array (Interval Dyadic)
  cover : (source : Set ℝ) ⊆ ⋃ t ∈ pieces, (t : Set ℝ)

@[inclusionExt real.concrete | (_ : ℝ)]
meta def evalConcreteIntervalIVar : InclusionExt where
  priority := 0
  derive e := do
    unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
    let configType ← mkAppM ``ConcreteIntervalCover #[e]
    let config ← instantiateMVars (← whnf (← synthInstance configType))
    let (``ConcreteIntervalCover.mk, #[_, source, pieces, hcover]) := config.getAppFnArgs
      | failure
    let setType ← mkAppM ``Interval #[mkConst ``Dyadic]
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[setType, mkConst ``Real])
    let cover ← mkAppM' (mkConst ``Cover.ofArray [.zero, .zero, .zero])
      #[source, pieces, hcover]
    let iVar ← mkIVar e setType toSetInst (some cover)
    return iVar.toExprInclusionBody

syntax (name := inclusionCover) "inclusion_cover " term " in " term " with " term
  " using " term : tactic

elab "inclusion_cover_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goal ← goal.change (← goal.getType).consumeMData (checkDefEq := false)
  replaceMainGoal [goal]
  inclusionTactic { families := #[`core, `real.dyadic, `real.concrete] }

macro_rules
  | `(tactic| inclusion_cover $x in $source with $pieces using $cover) =>
      `(tactic|
        letI : ConcreteIntervalCover $x :=
          (ConcreteIntervalCover.mk $source $pieces $cover); inclusion_cover_core)

end Inclusion.Experimental
