import Mathlib

open Module Submodule

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem poincare {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (V : Submodule 𝕜 E) (i : Fin n)
    (hV : Module.finrank 𝕜 V = i) : ∃ x ∈ V, x ≠ 0
      ∧ RCLike.re ⟪x, T x⟫ / ‖x‖ ^ 2 ≤ hT.eigenvalues hn i :=
    sorry


theorem minimax {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (i : Fin n) :
    hT.isSymmetric.eigenvalues hn i =
      ⨆ (V : Submodule 𝕜 E) (hV : Module.finrank 𝕜 E = i),
        ⨅ x : {x : V // ‖x‖ = 1}, RCLike.re ⟪T x, x⟫ :=
    sorry
