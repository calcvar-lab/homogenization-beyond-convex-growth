import Homogenization.Examples.ProperDomainBB

/-!
# Lemma `lem:BB` with a positive constant

`lem_BB` gives `R₁ F ≤ β(1 + G)` with `β ≥ 0`; the article states `β > 0`. `lem_BB_paper` gives
`β > 0` (replace `β` by `max β 1`). As in the article since 2026-10-15, no convexity of `g̃`, no
measurability of `F` and only `p ≥ 0` are assumed.
-/

open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- **Lemma `lem:BB`**, with the conclusion of the article: under the hypotheses of `lem_BB`, there
is `β > 0` with `R₁ F ≤ β(1 + G)` on `𝕄`. As in the paper, `γ` and `δ` are arbitrary reals. -/
theorem lem_BB_paper [NeZero N] (hNm : N ≤ m) {p : ℝ} (hp : 0 ≤ p) {gt : ℝ≥0 → ℝ≥0}
    (hgt_mono : Monotone gt) (hgt_shift : ∀ c : ℝ≥0, ∃ A B : ℝ≥0, ∀ s : ℝ≥0,
      gt (c + s) ≤ A + B * gt s)
    {F : Mat m N → ℝ≥0∞} {γ δ : ℝ}
    (hBB : ∀ ζ : Mat m N, γ ≤ (properDomainJacobian ζ : ℝ) →
      F ζ ≤ ENNReal.ofReal δ * (1 + bbG p gt ζ)) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ ξ, Rone F ξ ≤ β * (1 + bbG p gt ξ) := by
  obtain ⟨β, hβ⟩ := lem_BB hNm hp hgt_mono hgt_shift hBB
  refine ⟨max β 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun ξ => (hβ ξ).trans ?_⟩
  gcongr
  exact_mod_cast le_max_left β 1

end Homogenization
