module

public import Mathlib.Tactic.Inclusion.Core.ToSet
public import Mathlib.Order.WithBot

set_option linter.style.header false

@[expose] public section

open Set

namespace Inclusion

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

/-- The exact intersection of two intervals. -/
def Interval.inter [LinearOrder α] (I J : Interval α) : Interval α :=
  let lb := match I.lb, J.lb with
    | ⊥, lb | lb, ⊥ => lb
    | some a, some b => some (max a b)
  let ub := match I.ub, J.ub with
    | ⊤, ub | ub, ⊤ => ub
    | some a, some b => some (min a b)
  ⟨lb, ub⟩

/-- Forget the lower endpoint of an interval. -/
def Interval.downwardClosure (I : Interval α) : Interval α := ⟨⊥, I.ub⟩

/-- Forget the upper endpoint of an interval. -/
def Interval.upwardClosure (I : Interval α) : Interval α := ⟨I.lb, ⊤⟩

def Interval.toSet [Preorder α] (I : Interval α) : Set α := {a | I.lb ≤ a ∧ a ≤ I.ub}

instance [Preorder α] : ToSet (Interval α) α := ⟨Interval.toSet⟩

instance [Preorder α] : Univ (Interval α) α where
  univ := Interval.univ α
  mem_univ x :=
    ⟨show (⊥ : WithBot α) ≤ x from bot_le, show (x : WithTop α) ≤ ⊤ from le_top⟩

instance [LinearOrder α] : Refine (Interval α) α where
  refine := Interval.inter
  mem_refine := by
    intro x s t hs ht
    constructor
    · rcases hI : s.lb with _ | sl
      · simpa [Interval.inter, hI] using ht.1
      rcases hJ : t.lb with _ | tl
      · simpa [Interval.inter, hI, hJ] using hs.1
      have hs' := hs.1
      have ht' := ht.1
      rw [hI] at hs'
      rw [hJ] at ht'
      simp only [Interval.inter, hI, hJ]
      exact WithBot.coe_le_coe.mpr (max_le
        (WithBot.coe_le_coe.mp hs') (WithBot.coe_le_coe.mp ht'))
    · rcases hI : s.ub with _ | su
      · simpa [Interval.inter, hI] using ht.2
      rcases hJ : t.ub with _ | tu
      · simpa [Interval.inter, hI, hJ] using hs.2
      have hs' := hs.2
      have ht' := ht.2
      rw [hI] at hs'
      rw [hJ] at ht'
      simp only [Interval.inter, hI, hJ]
      exact WithTop.coe_le_coe.mpr (le_min
        (WithTop.coe_le_coe.mp hs') (WithTop.coe_le_coe.mp ht'))

theorem Interval.mem_downwardClosure_of_le [Preorder α] {x y : α} {I : Interval α}
    (hxy : x ≤ y) (hy : y ∈ I) : x ∈ I.downwardClosure :=
  ⟨by simp [Interval.downwardClosure], (WithTop.coe_le_coe.mpr hxy).trans hy.2⟩

theorem Interval.mem_upwardClosure_of_le [Preorder α] {x y : α} {I : Interval α}
    (hxy : x ≤ y) (hx : x ∈ I) : y ∈ I.upwardClosure :=
  ⟨hx.1.trans (WithBot.coe_le_coe.mpr hxy), by simp [Interval.upwardClosure]⟩

end Inclusion
