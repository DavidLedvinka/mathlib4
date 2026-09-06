/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Order.Hom.Order

/-!
# Lower and upper extensions of order homomorphisms

For `e : α →o β` and a complete lattice `γ`, `OrderHom.lowerExtension e` and
`OrderHom.upperExtension e` are the left and right adjoints of precomposition with `e`.
Their values at `b` are respectively the supremum of `f a` over `e a ≤ b` and the
infimum of `f a` over `b ≤ e a`. Empty sets of approximants give `⊥` and `⊤`.

The constructions and adjunctions only require `e` to be monotone. For order embeddings,
both constructions agree with the original map on the image and give the least and greatest
monotone extensions. In general, a monotone map that identifies distinct points need not admit
an extension agreeing with the original map.
-/

@[expose] public section

namespace OrderHom

variable {α β γ δ : Type*} [Preorder α] [Preorder β]

section Preorder

variable [Preorder γ] (e : α →o β) (f : α →o γ) {g k : β →o γ}

/-- Specified least upper bounds characterize the comparison with any monotone map,
without requiring the target to be complete. -/
@[to_dual le_iff_comp_le_of_isGLB
/-- Specified greatest lower bounds characterize the comparison with any monotone map,
without requiring the target to be complete. -/]
theorem le_iff_le_comp_of_isLUB
    (hg : ∀ b, IsLUB (f '' {a | e a ≤ b}) (g b)) : g ≤ k ↔ f ≤ k.comp e := by
  constructor
  · intro h a
    exact ((hg (e a)).1 ⟨a, le_rfl, rfl⟩).trans (h (e a))
  · intro h b
    refine (hg b).2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (h a).trans (k.monotone ha)

end Preorder

section CompleteLattice

variable [CompleteLattice γ]

/-- The lower extension along a monotone map, as a monotone operator on order homomorphisms. -/
def lowerExtension (e : α →o β) : (α →o γ) →o (β →o γ) where
  toFun f :=
    { toFun b := ⨆ (a : α) (_ : e a ≤ b), f a
      monotone' := fun _ _ h => iSup₂_le fun a ha => le_iSup₂_of_le a (ha.trans h) le_rfl }
  monotone' := fun _ _ h _ => iSup₂_mono fun a _ => h a

/-- The upper extension along a monotone map, obtained from lower extension by duality. -/
def upperExtension (e : α →o β) : (α →o γ) →o (β →o γ) where
  toFun f := (lowerExtension e.dual f.dual).dual
  monotone' := fun f g h b =>
    (lowerExtension e.dual).monotone (show g.dual ≤ f.dual from h) b

attribute [to_dual existing] lowerExtension

variable (e : α →o β) (f : α →o γ)

@[to_dual]
theorem lowerExtension_apply (b : β) :
    lowerExtension e f b = ⨆ (a : α) (_ : e a ≤ b), f a := rfl

@[to_dual]
theorem isLUB_lowerExtension (b : β) :
    IsLUB (f '' {a | e a ≤ b}) (lowerExtension e f b) := isLUB_biSup

/-- Lower extension is left adjoint to precomposition. -/
@[to_dual gc_comp_upperExtension
/-- Upper extension is right adjoint to precomposition. -/]
theorem gc_lowerExtension_comp :
    GaloisConnection (lowerExtension e : (α →o γ) → β →o γ) (fun g => g.comp e) :=
  fun f _ => le_iff_le_comp_of_isLUB e f (isLUB_lowerExtension e f)

@[to_dual (attr := simp) le_upperExtension_iff]
theorem lowerExtension_le_iff {g : β →o γ} :
    lowerExtension e f ≤ g ↔ f ≤ g.comp e := gc_lowerExtension_comp e f g

@[to_dual le_upperExtension_apply_iff]
theorem lowerExtension_apply_le_iff {b : β} {c : γ} :
    lowerExtension e f b ≤ c ↔ ∀ a, e a ≤ b → f a ≤ c := iSup₂_le_iff

@[to_dual le_upperExtension_apply]
theorem lowerExtension_apply_le {b : β} {c : γ} (h : ∀ a, e a ≤ b → f a ≤ c) :
    lowerExtension e f b ≤ c := (lowerExtension_apply_le_iff e f).2 h

@[to_dual upperExtension_apply_le]
theorem le_lowerExtension_apply {a : α} {b : β} (h : e a ≤ b) :
    f a ≤ lowerExtension e f b := (isLUB_lowerExtension e f b).1 ⟨a, h, rfl⟩

@[to_dual]
theorem lowerExtension_eq_of_isLUB {b : β} {c : γ}
    (h : IsLUB (f '' {a | e a ≤ b}) c) : lowerExtension e f b = c :=
  (isLUB_lowerExtension e f b).unique h

@[to_dual]
theorem lowerExtension_eq_bot {b : β} (h : ∀ a, ¬ e a ≤ b) :
    lowerExtension e f b = ⊥ := by
  simp [lowerExtension_apply, h]

@[to_dual (attr := simp)]
theorem lowerExtension_of_isEmpty [IsEmpty α] : lowerExtension e f = ⊥ := by
  ext b
  simp [lowerExtension_apply]

@[to_dual (attr := mono)]
theorem lowerExtension_mono {f g : α →o γ} (h : f ≤ g) :
    lowerExtension e f ≤ lowerExtension e g := (lowerExtension e).monotone h

@[to_dual comp_upperExtension_le]
theorem le_comp_lowerExtension : f ≤ (lowerExtension e f).comp e :=
  (gc_lowerExtension_comp e).le_u_l f

@[to_dual le_upperExtension_comp]
theorem lowerExtension_comp_le (g : β →o γ) : lowerExtension e (g.comp e) ≤ g :=
  (gc_lowerExtension_comp e).l_u_le g

@[to_dual le_upperExtension_of_comp_eq]
theorem lowerExtension_le_of_comp_eq {g : β →o γ} (h : g.comp e = f) :
    lowerExtension e f ≤ g := (lowerExtension_le_iff e f).2 h.ge

/-- The lower extension is the least monotone map whose restriction dominates the given map. -/
@[to_dual
/-- The upper extension is the greatest monotone map whose restriction is dominated by the
given map. -/]
theorem isLeast_lowerExtension :
    IsLeast {g : β →o γ | f ≤ g.comp e} (lowerExtension e f) :=
  (gc_lowerExtension_comp e).isLeast_l

@[to_dual (attr := simp)]
theorem lowerExtension_id : lowerExtension (OrderHom.id : α →o α) f = f :=
  (gc_lowerExtension_comp OrderHom.id).l_unique GaloisConnection.id (fun _ => comp_id _)

/-- Extending in two stages equals extending along the composite. -/
theorem lowerExtension_comp [Preorder δ] (k : β →o δ) :
    lowerExtension (k.comp e) f = lowerExtension k (lowerExtension e f) :=
  (gc_lowerExtension_comp (k.comp e)).l_unique
    ((gc_lowerExtension_comp e).compose (gc_lowerExtension_comp k)) (fun _ => rfl)

/-- Extending in two stages equals extending along the composite. -/
theorem upperExtension_comp [Preorder δ] (k : β →o δ) :
    upperExtension (k.comp e) f = upperExtension k (upperExtension e f) :=
  (gc_comp_upperExtension (k.comp e)).u_unique
    ((gc_comp_upperExtension k).compose (gc_comp_upperExtension e)) (fun _ => rfl)

@[simp]
theorem dual_lowerExtension : (lowerExtension e f).dual = upperExtension e.dual f.dual := rfl

@[simp]
theorem dual_upperExtension : (upperExtension e f).dual = lowerExtension e.dual f.dual := rfl

@[to_dual (attr := simp)]
theorem lowerExtension_iSup {ι : Sort*} (f : ι → α →o γ) :
    lowerExtension e (⨆ i, f i) = ⨆ i, lowerExtension e (f i) :=
  (gc_lowerExtension_comp e).l_iSup

@[to_dual (attr := simp)]
theorem lowerExtension_sSup (s : Set (α →o γ)) :
    lowerExtension e (sSup s) = sSup (lowerExtension e '' s) :=
  (gc_lowerExtension_comp e).l_sSup_eq_sSup_image

/-- Lower extension preserves arbitrary suprema of order homomorphisms. -/
@[to_dual
/-- Upper extension preserves arbitrary infima of order homomorphisms. -/]
def lowerExtensionSupHom : sSupHom (α →o γ) (β →o γ) where
  toFun := lowerExtension e
  map_sSup' := lowerExtension_sSup e

@[to_dual (attr := simp)]
theorem lowerExtensionSupHom_apply (f : α →o γ) :
    lowerExtensionSupHom e f = lowerExtension e f := rfl

/-- Precomposition as a complete lattice homomorphism. Its two adjoints are
`lowerExtension` and `upperExtension`. -/
def precompCompleteLatticeHom : CompleteLatticeHom (β →o γ) (α →o γ) where
  toFun g := g.comp e
  map_sSup' _ := (gc_comp_upperExtension e).l_sSup_eq_sSup_image
  map_sInf' _ := (gc_lowerExtension_comp e).u_sInf_eq_sInf_image

@[simp]
theorem precompCompleteLatticeHom_apply (g : β →o γ) :
    precompCompleteLatticeHom e g = g.comp e := rfl

section Target

variable [CompleteLattice δ]

/-- A monotone target map gives a one-sided comparison with lower extension. -/
@[to_dual comp_upperExtension_le_upperExtension_comp
/-- A monotone target map gives a one-sided comparison with upper extension. -/]
theorem lowerExtension_comp_le_comp_lowerExtension (g : γ →o δ) :
    lowerExtension e (g.comp f) ≤ g.comp (lowerExtension e f) :=
  (lowerExtension_le_iff e (g.comp f)).2 fun a =>
    g.monotone (le_comp_lowerExtension e f a)

/-- Postcomposition by a supremum-preserving map commutes with lower extension. -/
@[to_dual
/-- Postcomposition by an infimum-preserving map commutes with upper extension. -/]
theorem lowerExtension_comp_sSupHom (g : sSupHom γ δ) :
    lowerExtension e ((g : γ →o δ).comp f) =
      (g : γ →o δ).comp (lowerExtension e f) := by
  ext b
  exact (map_iSup₂ g _).symm

@[to_dual (attr := simp)]
theorem lowerExtension_prod (g : α →o δ) :
    lowerExtension e (f.prod g) = (lowerExtension e f).prod (lowerExtension e g) := by
  ext b <;> simp [lowerExtension_apply, Prod.fst_iSup, Prod.snd_iSup]

end Target

end CompleteLattice

end OrderHom

namespace OrderEmbedding

open OrderHom

variable {α β γ : Type*} [Preorder α] [Preorder β] [CompleteLattice γ]
  (e : α ↪o β) (f : α →o γ)

@[to_dual (attr := simp)]
theorem lowerExtension_apply (a : α) : lowerExtension e.toOrderHom f (e a) = f a := by
  apply le_antisymm
  · exact lowerExtension_apply_le _ _ fun x hx => f.monotone (e.le_iff_le.mp hx)
  · exact le_lowerExtension_apply _ _ le_rfl

@[to_dual (attr := simp)]
theorem lowerExtension_comp : (lowerExtension e.toOrderHom f).comp e.toOrderHom = f :=
  DFunLike.ext _ _ fun a => e.lowerExtension_apply f a

/-- Lower extension along an order embedding is the least monotone extension. -/
@[to_dual
/-- Upper extension along an order embedding is the greatest monotone extension. -/]
theorem isLeast_lowerExtension :
    IsLeast {g : β →o γ | g.comp e.toOrderHom = f} (lowerExtension e.toOrderHom f) :=
  ⟨e.lowerExtension_comp f, fun _ h => lowerExtension_le_of_comp_eq _ _ h⟩

theorem lowerExtension_le_upperExtension :
    lowerExtension e.toOrderHom f ≤ upperExtension e.toOrderHom f :=
  lowerExtension_le_of_comp_eq _ _ (e.upperExtension_comp f)

/-- Lower extension and restriction along an order embedding form a Galois coinsertion. -/
@[to_dual
/-- Restriction and upper extension along an order embedding form a Galois insertion. -/]
def lowerExtensionGaloisCoinsertion :
    GaloisCoinsertion (lowerExtension e.toOrderHom : (α →o γ) → β →o γ)
      (fun g => g.comp e.toOrderHom) :=
  (gc_lowerExtension_comp e.toOrderHom).toGaloisCoinsertion
    fun f => (e.lowerExtension_comp f).le

end OrderEmbedding

namespace OrderHom

variable {α γ : Type*} [Preorder α] [CompleteLattice γ] (s : Set α) (f : s →o γ)

@[to_dual]
theorem lowerExtension_subtype_apply (a : α) :
    lowerExtension (OrderEmbedding.subtype (· ∈ s)).toOrderHom f a =
      ⨆ (x : α) (hx : x ∈ s) (_ : x ≤ a), f ⟨x, hx⟩ := by
  simp [lowerExtension_apply, iSup_subtype]

@[to_dual (attr := simp)]
theorem lowerExtension_subtype_apply_coe (a : s) :
    lowerExtension (OrderEmbedding.subtype (· ∈ s)).toOrderHom f a = f a :=
  (OrderEmbedding.subtype (· ∈ s)).lowerExtension_apply f a

theorem lowerExtension_subtype_le_iff {g : α →o γ} :
    lowerExtension (OrderEmbedding.subtype (· ∈ s)).toOrderHom f ≤ g ↔
      ∀ (a : α) (ha : a ∈ s), f ⟨a, ha⟩ ≤ g a :=
  (lowerExtension_le_iff _ _).trans Subtype.forall

theorem le_upperExtension_subtype_iff {g : α →o γ} :
    g ≤ upperExtension (OrderEmbedding.subtype (· ∈ s)).toOrderHom f ↔
      ∀ (a : α) (ha : a ∈ s), g a ≤ f ⟨a, ha⟩ :=
  (le_upperExtension_iff _ _).trans Subtype.forall

end OrderHom
