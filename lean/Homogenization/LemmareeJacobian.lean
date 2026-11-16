import Homogenization.ZaffFinite
import Homogenization.Examples.ProperDomainData

/-!
# `v(ζ) ≠ 0 ⟺ ker ζ = 0`, and Lemma `lemmaree` with the Jacobian hypothesis

`properDomainJacobian_ne_zero_iff`: the `N`-dimensional Jacobian `v(ζ)` (product of the singular
values, `ProperDomainData.lean`) is nonzero exactly when `ζ` has trivial kernel.
`lemmaree_of_jacobian` is Lemma `lemmaree` with the hypothesis of the paper,
`v(ζ) ≠ 0 ⟹ L(ζ) < ∞`, i.e. `L` finite on `Σ = properDomainSigma`.

Not done here: the application `dom (𝒵_aff W⁺) = 𝕄` to the integrand `W⁺` of
`prop:separating`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- The Jacobian `v(ζ)` (product of the singular values) vanishes exactly when `ζ` has a
nontrivial kernel. -/
theorem properDomainJacobian_ne_zero_iff (A : Mat m N) :
    properDomainJacobian A ≠ 0 ↔ LinearMap.ker (A : Sp N →ₗ[ℝ] Tgt m) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  have hiff := LinearMap.injective_iff_forall_lt_finrank_singularValues_pos
    (matrixEuclideanLinearMap A)
  have hcomp : Function.Injective (matrixEuclideanLinearMap A) ↔
      Function.Injective (A : Sp N →ₗ[ℝ] Tgt m) := by
    unfold matrixEuclideanLinearMap
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
    rw [EquivLike.comp_injective, EquivLike.injective_comp]
  rw [← hcomp, hiff]
  have hval : ((properDomainJacobian A : ℝ≥0) : ℝ) =
      ∏ i : Fin N, (matrixEuclideanLinearMap A).singularValues i := rfl
  rw [finrank_euclideanSpace, Fintype.card_fin]
  have hne : properDomainJacobian A ≠ 0 ↔
      ∏ i : Fin N, (matrixEuclideanLinearMap A).singularValues i ≠ 0 := by
    rw [← hval, ne_eq, ne_eq, NNReal.coe_eq_zero]
  rw [hne, Finset.prod_ne_zero_iff]
  constructor
  · intro h i hi
    exact lt_of_le_of_ne (LinearMap.singularValues_nonneg _ i)
      (h ⟨i, hi⟩ (Finset.mem_univ _)).symm
  · intro h i _
    exact (h i i.isLt).ne'

/-- **Lemma `lemmaree`**, with the hypothesis of the paper: if `N ≤ m` and `L(ζ) < ∞` whenever
`v(ζ) ≠ 0` (i.e. on `Σ = properDomainSigma`), then `𝒵_aff L` is finite everywhere. The Borel
measurability of `L` is not needed. -/
theorem lemmaree_of_jacobian (hNm : N ≤ m) (L : Mat m N → ℝ≥0∞)
    (hL : ∀ ζ ∈ properDomainSigma (m := m) (N := N), L ζ ≠ ⊤) (ξ : Mat m N) :
    Zaff L ξ ≠ ⊤ :=
  lemmaree hNm L (fun ζ hζ => hL ζ ((properDomainJacobian_ne_zero_iff ζ).2 hζ)) ξ

theorem dom_Zaff_eq_univ_of_jacobian (hNm : N ≤ m) (L : Mat m N → ℝ≥0∞)
    (hL : ∀ ζ ∈ properDomainSigma (m := m) (N := N), L ζ ≠ ⊤) : dom (Zaff L) = univ :=
  eq_univ_of_forall fun ξ => lt_top_iff_ne_top.2 (lemmaree_of_jacobian hNm L hL ξ)

end Homogenization
