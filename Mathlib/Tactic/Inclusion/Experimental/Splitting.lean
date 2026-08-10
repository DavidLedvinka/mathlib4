module

public import Mathlib.Tactic.Inclusion.Extension.Extensions
public meta import Mathlib.Tactic.Inclusion.Extension.Extensions
public import Mathlib.Tactic.Inclusion.Extension.Splitter

set_option linter.style.header false

@[expose] public section

namespace Inclusion.Experimental

def half (x : Dyadic) : Dyadic :=
  match x with
  | .zero => 0
  | .ofOdd n k _ => Dyadic.ofIntWithPrec n (k + 1)

def midpoint (a b : Dyadic) : Dyadic := half (a + b)

@[specialize]
def bisectCoverMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β] :
    ℕ → Interval Dyadic → (Interval Dyadic → Iβ) → Iβ
  | 0, I, F => F I
  | n + 1, I, F =>
      match I with
      | ⟨some l, some u⟩ =>
          let m := midpoint l u
          Coarsen.coarsen (Iα := Iβ) (α := β) (bisectCoverMap n ⟨l, m⟩ F)
            (bisectCoverMap n ⟨m, u⟩ F)
      | _ => bisectCoverMap n I F

theorem mem_bisectCoverMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) (I : Interval Dyadic) (F : Interval Dyadic → Iβ) {y : β} {r : ℝ}
    (hr : r ∈ I) (hy : ∀ J, r ∈ J → y ∈ F J) : y ∈ bisectCoverMap n I F := by
  induction n generalizing I with
  | zero => exact hy I hr
  | succ n ih =>
      rcases I with ⟨lb, ub⟩
      cases lb with
      | bot => exact ih ⟨⊥, ub⟩ hr
      | coe l =>
        cases ub with
        | top => exact ih ⟨l, ⊤⟩ hr
        | coe u =>
          let m := midpoint l u
          let left : Interval Dyadic := ⟨l, m⟩
          let right : Interval Dyadic := ⟨m, u⟩
          change y ∈ Coarsen.coarsen (Iα := Iβ) (α := β)
            (bisectCoverMap n left F) (bisectCoverMap n right F)
          by_cases hl : r ≤ Dyadic.toReal m
          · apply Coarsen.mem_coarsen_left (Iα := Iβ) (α := β)
            exact ih left ⟨hr.1, WithTop.coe_le_coe.mpr hl⟩
          · apply Coarsen.mem_coarsen_right (Iα := Iβ) (α := β)
            exact ih right ⟨WithBot.coe_le_coe.mpr (le_of_not_ge hl), hr.2⟩

def bisectCover (n : ℕ) : Cover (Interval Dyadic) ℝ where
  coverMap := fun I F ↦ bisectCoverMap n I F
  mem_coverMap := by
    intro Iβ β _ _ I F x y hx hy
    exact mem_bisectCoverMap n I F hx hy

instance : Splitter (Interval Dyadic) ℝ where
  cover := bisectCover

end Inclusion.Experimental
