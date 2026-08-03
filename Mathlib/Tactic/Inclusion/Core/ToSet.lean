module

public import Mathlib.Data.Set.Insert

set_option linter.style.header false

@[expose] public section

class ToSet (Iα : Type*) (α : outParam Type*) where
  toSet : Iα → Set α

instance {Iα α : Type*} [ToSet Iα α] : CoeTC Iα (Set α) where
  coe := ToSet.toSet

instance {Iα α : Type*} [ToSet Iα α] : Membership α Iα where
  mem s a := a ∈ (s : Set α)

@[simp]
lemma mem_set_iff_mem_toSet {Iα α : Type*} [ToSet Iα α] (a : α) (s : Iα) :
  a ∈ s ↔ a ∈ (s : Set α) := Iff.rfl

open ToSet

variable {Iα α Iβ β : Type*}

def IsInclusionFunction [ToSet Iα α] [ToSet Iβ β] (F : Iα → Iβ) (f : α → β) : Prop :=
  ∀ a s, a ∈ s → f a ∈ F s

instance : ToSet PUnit PUnit where
  toSet _ := Set.univ

instance [ToSet Iα α] [ToSet Iβ β] : ToSet (Iα × Iβ) (α × β) where
  toSet s := {a | a.1 ∈ s.1 ∧ a.2 ∈ s.2}

section IntervalBool

inductive IntervalBool
  | true
  | false
  | undetermined

def IntervalBool.toPropSet : IntervalBool → Set Prop
  | true => {True}
  | false => {False}
  | undetermined => {True, False}

instance : ToSet IntervalBool Prop := ⟨IntervalBool.toPropSet⟩

theorem true_of_mem_intervalBool_true {p : Prop} (hp : p ∈ IntervalBool.true) : p := by
  simpa [mem_set_iff_mem_toSet, toSet, IntervalBool.toPropSet] using hp

theorem true_of_isInclusionFunction [ToSet Iα α] {p : α → Prop} {P : Iα → IntervalBool}
    (hFf : IsInclusionFunction P p) (a : α) (s : Iα) (has : a ∈ s)
    (h : P s = IntervalBool.true) : p a :=
  true_of_mem_intervalBool_true (h ▸ hFf a s has)

end IntervalBool
