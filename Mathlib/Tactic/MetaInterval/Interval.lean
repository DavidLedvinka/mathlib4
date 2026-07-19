module

public import Mathlib.Order.WithBot
public import Mathlib.Order.Interval.Set.Defs

set_option linter.style.header false

@[expose] public section

open Set

namespace IntervalArithmetic

variable {α β : Type*}

structure Interval (α : Type*) where
  lb : WithBot α
  ub : WithTop α
  deriving Inhabited

def Interval.map (i : Interval α) (f : α → β) : Interval β :=
  let lb := match i.lb with
    | some a => some (f a)
    | ⊥ => ⊥
  let ub := match i.ub with
    | some a => some (f a)
    | ⊤ => ⊤
  ⟨lb, ub⟩

def Interval.univ (α : Type*) : Interval α := ⟨⊥, ⊤⟩

def Interval.singleton (α : Type*) (a : α) : Interval α := ⟨a, a⟩

def Interval.toSet [Preorder α] (i : Interval α) : Set α := {a | i.lb ≤ a ∧ a ≤ i.ub}

def Interval.le [Preorder α] (i j : Interval α) : Prop :=
  match i.ub, j.lb with
  | some ub, some lb => ub ≤ lb
  | _, _ => False

instance [Preorder α] [DecidableLE α] (i j : Interval α) : Decidable (i.le j) :=
  match i, j with
  | ⟨_, ⊤⟩, _ => isFalse id
  | ⟨_, some _⟩, ⟨⊥, _⟩ => isFalse id
  | ⟨_, some ub⟩, ⟨some lb, _⟩ => inferInstanceAs (Decidable (ub ≤ lb))

/-- **Proof By Codex** -/
lemma Interval.le_of_le [Preorder α] [Preorder β] {f : α → β} (hf : Monotone f) {x y : β}
    {i j : Interval α} (hxi : x ∈ (i.map f).toSet) (hyj : y ∈ (j.map f).toSet) (hij : i.le j) :
    x ≤ y := by
  match i, j with
  | ⟨_, ⊤⟩, _ | _, ⟨⊥, _⟩ => simp [Interval.le] at hij
  | ⟨_, some ub⟩, ⟨some lb, _⟩ =>
    have hx : x ≤ f ub := WithTop.coe_le_coe.mp hxi.2
    have hy : f lb ≤ y := WithBot.coe_le_coe.mp hyj.1
    exact hx.trans ((hf hij).trans hy)

end IntervalArithmetic
