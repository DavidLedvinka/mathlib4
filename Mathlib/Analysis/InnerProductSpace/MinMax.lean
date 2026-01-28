/-
Copyright (c) 2026  David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvnka`
-/
module

public import Mathlib
/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

The main results of this file are `IsSelfAdjoint.hasEigenvector_of_isMaxOn` and
`IsSelfAdjoint.hasEigenvector_of_isMinOn`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2` is the corresponding
eigenvalue.

The corollaries `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` state that if `E` is
finite-dimensional and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the
`iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ‖x‖ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ‖x‖ ^ 2` (not necessarily both).

-/

public section

open Module Submodule

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

#check OrthonormalBasis.span_apply
#check div_le_div_of_nonneg_right
#check Basis.span

-- Maybe try a calc proof that is more explicit?
theorem poincare {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (V : Submodule 𝕜 E) (i : Fin n)
    (hV : Module.finrank 𝕜 V = i) : ∃ x ∈ V, x ≠ 0
      ∧ RCLike.re ⟪x, T x⟫ / ‖x‖ ^ 2 ≤ hT.eigenvalues hn i := by
    classical
    let B := (hT.eigenvectorBasis hn).toBasis
    let B_ge_i := Basis.span B.linearIndependent
      -- (Basis.span (hT.eigenvectorBasis hn) {k : Fin n | i ≤ k}).toBasis
    -- have h := finrank_eq_card_basis bin.toBasis
    obtain ⟨x, hxin, hx⟩ : ∃ x ∈ V
        ⊓ (span 𝕜 (Finset.image (hT.eigenvectorBasis hn) {k | i ≤ k} : Set E)), x ≠ 0 := by
      sorry
    use x, hxin.1, hx
    rw [div_le_iff₀ (by positivity)]
    have hV := bin.sum_repr ⟨x , hxin.2⟩
    apply congrArg (fun (v : (span 𝕜 (Finset.image ⇑(hT.eigenvectorBasis hn) {k | i ≤ k} : Set E)))
      ↦ (v : E)) at hV
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at hV
    calc
      RCLike.re ⟪x, T x⟫ = ⟪x , ∑ i in {k | i ≤ k},   := by sorry
    -- nth_rw 2 [← hV]
    -- simp only [map_sum, map_smul, inner_sum]
    -- conv =>
    --   enter [1, 2, x]
    --   rw [OrthonormalBasis.span_apply, hT.apply_eigenvectorBasis, smul_comm, inner_smul_right]
    -- simp only [RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero]
    -- apply le_trans
    -- · apply Finset.sum_le_sum
    --   rintro ⟨i, hik⟩ _



    -- simp


    sorry





    -- rw [← (hT.eigenvectorBasis hn).sum_repr (T x)]
    -- simp only [hT.eigenvectorBasis_apply_self_apply hn x]
    -- rw [inner_sum]





    -- have h₂ := bin.sum_repr ⟨x, hxV.2⟩
    -- refine ⟨⟨x, hxV.1⟩, by simp [hx], ?_⟩
    -- simp only [ContinuousLinearMap.rayleighQuotient , ContinuousLinearMap.reApplyInnerSelf]

theorem minimax {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (i : Fin n) :
    hT.isSymmetric.eigenvalues hn i =
      ⨆ (V : Submodule 𝕜 E) (hV : Module.finrank 𝕜 E = i),
        ⨅ x : {x : V // ‖x‖ = 1}, RCLike.re ⟪T x, x⟫ := by
    sorry
