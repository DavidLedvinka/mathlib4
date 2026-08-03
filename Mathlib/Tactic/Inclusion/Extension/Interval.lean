module

public import Mathlib.Tactic.Inclusion.Core.ToSet
public import Mathlib.Order.WithBot

set_option linter.style.header false

@[expose] public section

open Set

namespace IntervalArithmetic

variable {α β : Type*}

structure Interval (α : Type*) where
  lb : WithBot α
  ub : WithTop α
  deriving Inhabited

def Interval.map (I : Interval α) (f : α → β) : Interval β :=
  let lb := match I.lb with
    | some a => some (f a)
    | ⊥ => ⊥
  let ub := match I.ub with
    | some a => some (f a)
    | ⊤ => ⊤
  ⟨lb, ub⟩

def Interval.univ (α : Type*) : Interval α := ⟨⊥, ⊤⟩

def Interval.singleton (α : Type*) (a : α) : Interval α := ⟨a, a⟩

def Interval.toSet [Preorder α] (I : Interval α) : Set α := {a | I.lb ≤ a ∧ a ≤ I.ub}

instance [Preorder α] : ToSet (Interval α) α := ⟨Interval.toSet⟩

end IntervalArithmetic
