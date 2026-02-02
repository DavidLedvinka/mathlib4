/-
Copyright (c) 2026  David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvnka`
-/
module

public import Mathlib
/-!
# TODO

-/

public section

open Function Module Submodule Finset RCLike

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem poincare {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (V : Submodule 𝕜 E) (i : Fin n)
    (hV : Module.finrank 𝕜 V = i + 1) : ∃ x ∈ V, x ≠ 0
      ∧ RCLike.re ⟪x, T x⟫ / ‖x‖ ^ 2 ≤ hT.eigenvalues hn i := by
    let N : Submodule 𝕜 E :=
      span 𝕜 (Set.range <| hT.eigenvectorBasis hn ∘ (fun k : Set.Ici i ↦ k))
    have hN : Module.finrank 𝕜 N = n - i := by
      unfold N
      rw [finrank_span_eq_card, Fintype.card_Ici, Fin.card_Ici]
      apply LinearIndependent.comp (hT.eigenvectorBasis hn |>.toBasis.linearIndependent)
      exact Subtype.val_injective
    obtain ⟨x, ⟨hxV, hxN⟩, hx₀⟩ : ∃ x ∈ V ⊓ N, x ≠ 0 := by
      apply exists_mem_ne_zero_of_ne_bot
      apply (not_congr disjoint_iff).mp
      grind [finrank_add_finrank_le_of_disjoint]
    obtain ⟨c, hcx⟩ := (mem_span_range_iff_exists_fun 𝕜).mp hxN
    use x, hxV, hx₀
    rw [div_le_iff₀ (c := ‖x‖ ^ 2) (by positivity), ← hcx]
    simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
      comp_apply, mul_sum, smul_comm (c _), ← inner_self_eq_norm_sq (𝕜 := 𝕜), re_ofReal_mul,
      hT.apply_eigenvectorBasis, orthonormal_iff_ite.mp (hT.eigenvectorBasis hn).orthonormal]
    gcongr
    · split_ifs with h
      · simp [mul_one, Subtype.coe_injective h, mul_conj]
      · simp
    · apply hT.eigenvalues_antitone hn (by grind)

#check ciInf_le

theorem minimax {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (i : Fin n) :
    hT.eigenvalues hn i =
      ⨆ V : {V : Submodule 𝕜 E // Module.finrank 𝕜 V = i + 1},
        ⨅ x : {x : ↑V // x ≠ 0}, RCLike.re ⟪(x : E), T x⟫ / ‖(x : E)‖ ^ 2 := by
    let N : Submodule 𝕜 E :=
      span 𝕜 (Set.range <| hT.eigenvectorBasis hn ∘ (fun k : Set.Iic i ↦ k))
    have hN : Module.finrank 𝕜 N = i + 1 := by
      unfold N
      rw [finrank_span_eq_card, Fintype.card_Iic, Fin.card_Iic]
      apply LinearIndependent.comp (hT.eigenvectorBasis hn |>.toBasis.linearIndependent)
      exact Subtype.val_injective
    apply le_antisymm
    · let N' : {V : Submodule 𝕜 E // Module.finrank 𝕜 V = i + 1} := ⟨N, hN⟩
      grw [← le_ciSup _ N']
      have : Nonempty { x : N // x ≠ 0} := by sorry
      apply le_ciInf (fun x ↦ ?_)
      -- have a lemma that decomposes the Rayleigh Quotient on a Basis
      sorry
    · have : Nonempty {V : Submodule 𝕜 E // Module.finrank 𝕜 V = i + 1} := by
        sorry
      apply ciSup_le (fun V ↦ ?_)
      obtain ⟨x, hxV, hx, h⟩ := poincare hn hT V.1 i V.2
      grw [ciInf_le _ ⟨⟨x, hxV⟩, by simp [hx]⟩]
      · simp [h]
      -- easier to prove on the sphere!
      sorry
