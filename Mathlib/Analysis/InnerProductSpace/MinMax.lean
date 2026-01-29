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

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem poincare {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (V : Submodule 𝕜 E) (i : Fin n)
    (hV : Module.finrank 𝕜 V = i) : ∃ x ∈ V, x ≠ 0
      ∧ RCLike.re ⟪x, T x⟫ / ‖x‖ ^ 2 ≤ hT.eigenvalues hn i := by
    let N : Submodule 𝕜 E :=
      span 𝕜 (Set.range <| hT.eigenvectorBasis hn ∘ (fun k : {k : Fin n | i ≤ k} ↦ k))
    obtain ⟨x, ⟨hxV, hxN⟩, hx₀⟩ : ∃ x ∈ V ⊓ N, x ≠ 0 := by sorry
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

theorem minimax {T : E →L[𝕜] E} (hT : T.IsSymmetric) (i : Fin n) :
    hT.eigenvalues hn i =
      ⨆ (V : Submodule 𝕜 E) (hV : Module.finrank 𝕜 V = i),
        ⨅ (x ∈ V) (_ : x ≠ 0), RCLike.re ⟪T x, x⟫ / ‖x‖ ^ 2 := by
    sorry
