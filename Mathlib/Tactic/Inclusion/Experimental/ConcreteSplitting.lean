module

public import Mathlib.Tactic.Inclusion.Experimental.Splitting
public meta import Mathlib.Tactic.Inclusion.Experimental.Splitting
public import Init.Data.Array.Lemmas

set_option linter.style.header false

@[expose] public section

open Lean Meta Elab Tactic
open Set

namespace Inclusion.Experimental

deriving instance DecidableEq for Interval

def allPiecesTrue {Iα : Type*} (pieces : Array Iα) (P : Iα → IntervalBool) : Bool :=
  pieces.toList.all fun t => P t matches .true

def checkPieces {Iα : Type*} (pieces : Array Iα) (P : Iα → IntervalBool) : IntervalBool :=
  if allPiecesTrue pieces P
  then .true
  else .undetermined

theorem allPiecesTrue_eq_true {Iα : Type*} (pieces : Array Iα) (P : Iα → IntervalBool) :
    allPiecesTrue pieces P = true ↔ ∀ t, t ∈ pieces → P t = IntervalBool.true := by
  rw [allPiecesTrue, List.all_eq_true]
  constructor
  · intro h t ht
    have ht' := h t (Array.mem_toList_iff.mpr ht)
    cases hP : P t <;> simp_all
  · intro h t ht
    have hPt := h t (Array.mem_toList_iff.mp ht)
    simp [hPt]

theorem checkPieces_mem {Iα α : Type*} [ToSet Iα α] (pieces : Array Iα)
    (P : Iα → IntervalBool) {p : Prop} {x : α}
    (hcover : ∃ t, t ∈ pieces ∧ x ∈ t) (hp : ∀ t, x ∈ t → p ∈ P t) :
    p ∈ checkPieces pieces P := by
  obtain ⟨t, ht, hxt⟩ := hcover
  unfold checkPieces
  split <;> rename_i h
  · have hPt := allPiecesTrue_eq_true pieces P |>.mp h t ht
    simpa [hPt] using hp t hxt
  · simpa [ToSet.toSet, IntervalBool.toPropSet] using Classical.em p

def CoverCheck.ofArray {Iα α : Type*} [ToSet Iα α] [DecidableEq Iα]
    (source : Iα) (pieces : Array Iα)
    (hcover : (source : Set α) ⊆ ⋃ t ∈ pieces, (t : Set α)) : CoverCheck Iα α where
  check s P := if s = source then checkPieces pieces P else P s
  mem_check := by
    intro s P p x hx hp
    split <;> rename_i h
    · apply checkPieces_mem pieces P _ hp
      have hx' := hcover (h ▸ hx)
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨t, ht, hxt⟩ := hx'
      exact ⟨t, ht, hxt⟩
    · exact hp s hx

class ConcreteIntervalCover (x : ℝ) where
  source : Interval Dyadic
  pieces : Array (Interval Dyadic)
  cover : (source : Set ℝ) ⊆ ⋃ t ∈ pieces, (t : Set ℝ)

@[inclusionExt(_ : ℝ)]
meta def evalConcreteIntervalIVar : InclusionExt where
  priority := 0
  eval e := do
    unless ← isDefEq (← inferType e) (mkConst ``Real) do failure
    let configType ← mkAppM ``ConcreteIntervalCover #[e]
    let config ← instantiateMVars (← whnf (← synthInstance configType))
    let (``ConcreteIntervalCover.mk, #[_, source, pieces, hcover]) := config.getAppFnArgs
      | failure
    let setType ← mkAppM ``Interval #[mkConst ``Dyadic]
    let toSetInst ← synthInstance (← mkAppM ``ToSet #[setType, mkConst ``Real])
    let coverCheck ← mkAppM ``CoverCheck.ofArray #[source, pieces, hcover]
    let iVar ← mkIVar e setType toSetInst coverCheck
    return iVar.toExprInclusionBody

syntax (name := inclusionCover) "inclusion_cover " term " in " term " with " term
  " using " term : tactic

elab "inclusion_cover_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goal ← goal.change (← goal.getType).consumeMData (checkDefEq := false)
  replaceMainGoal [goal]
  inclusionTactic (← defaultInclusionConfig)

macro_rules
  | `(tactic| inclusion_cover $x in $source with $pieces using $cover) =>
      `(tactic|
        letI : ConcreteIntervalCover $x :=
          (ConcreteIntervalCover.mk $source $pieces $cover); inclusion_cover_core)

end Inclusion.Experimental
