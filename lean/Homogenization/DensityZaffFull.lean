import Homogenization.DensityZaff

/-!
# Proposition `prop:densityZaff` (full convergence)

For `L : 𝕄 → [0,∞]`, `A` bounded open nonempty with `|∂A| = 0` and `ξ ∈ 𝕄`, there are
`φ_k ∈ Aff₀(A)`, `φ_k → 0` uniformly, with `∫_A L(ξ + ∇φ_k) → |A| 𝒵_aff L(ξ)` (`densityZaff`).

The upper bound `limsup ≤ |A| 𝒵_aff L(ξ)` is `densityZaffUpper` and holds for every bounded open
`A`. The lower bound `|A| 𝒵_aff L(ξ) ≤ ∫_A L(ξ + ∇φ)` for every `φ ∈ Aff₀(A)` is the domain
independence `Zaff_le_normalized_Yt`, which needs `|∂A| = 0` (as in Proposition
`Zenvelopefacts-cite` (ii) of the paper). The statement of `prop:densityZaff` for an arbitrary
bounded open `A` (without `|∂A| = 0`) is not proved. No measurability of `L` is needed.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- The lower bound: `|A| 𝒵_aff L(ξ) ≤ ∫_A L(ξ + ∇φ)` for `φ ∈ Aff₀(A)`, `|∂A| = 0`. -/
theorem volume_mul_Zaff_le_lintegral (L : Mat m N → ℝ≥0∞) {A : Set (Sp N)} (hA : IsOpen A)
    (hAb : Bornology.IsBounded A) (hAne : A.Nonempty) (hAf : volume (frontier A) = 0)
    {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 A) (ξ : Mat m N) :
    volume A * Zaff L ξ ≤ ∫⁻ y in A, L (ξ + fderiv ℝ φ y) := by
  have hA0 : volume A ≠ 0 := (volume_pos_of_isOpen_nonempty hA hAne).ne'
  have hAt : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  calc volume A * Zaff L ξ ≤ volume A * ((volume A)⁻¹ * Yt (fun _ => L) A ξ) := by
        gcongr
        exact Zaff_le_normalized_Yt L hA hAb hAne hAf ξ
    _ = Yt (fun _ => L) A ξ := ENNReal.mul_inv_cancel_left hA0 hAt
    _ ≤ ∫⁻ y in A, L (ξ + fderiv ℝ φ y) := iInf₂_le φ hφ

/-- **Proposition `prop:densityZaff`** for `A` with `|∂A| = 0`: there are `φ_k ∈ Aff₀(A)`,
`φ_k → 0` uniformly, with `∫_A L(ξ + ∇φ_k) → |A| 𝒵_aff L(ξ)`.

Not proved: the case `|∂A| > 0` of the paper's statement (only the upper bound
`densityZaffUpper` is available there). -/
theorem densityZaff (L : Mat m N → ℝ≥0∞) {A : Set (Sp N)} (hA : IsOpen A)
    (hAb : Bornology.IsBounded A) (hAne : A.Nonempty) (hAf : volume (frontier A) = 0)
    (ξ : Mat m N) :
    ∃ φ : ℕ → Sp N → Tgt m, (∀ k, φ k ∈ Aff0 A) ∧ UnifSmall atTop φ ∧
      Tendsto (fun k => ∫⁻ y in A, L (ξ + fderiv ℝ (φ k) y)) atTop
        (𝓝 (volume A * Zaff L ξ)) := by
  obtain ⟨φ, hφ, hsmall, hlim⟩ := densityZaffUpper L A hA hAb ξ
  refine ⟨φ, hφ, hsmall, tendsto_of_le_liminf_of_limsup_le ?_ hlim⟩
  exact le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun k =>
    volume_mul_Zaff_le_lintegral L hA hAb hAne hAf (hφ k) ξ)

end Homogenization
