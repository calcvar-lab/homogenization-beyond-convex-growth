import Homogenization.MeasurableYtloc

/-! # Theorem `th:product` (ii) in the form of the paper

`th_product_ii_paper` assembles `th_product_ii`, `prodW_setGrowth`, `prodW_measurable_Ytloc` and
`th_product_H8`: `G` and the integrand `W(x,ξ) = a(x) H(ξ)` are Borel measurable and satisfy
(H1)–(H3) and (H5)–(H8), with
`α = 1` and `β = Aγ` in (H3), (H6) in its exact form (joint Borel measurability of `𝒴_loc W`,
without modification on a null set) and (H8) without measurability assumption.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- **Theorem `th:product` (ii)**: for `G`, `H`, `a` as in the paper, `W = a H` satisfies
(H1)–(H3) and (H5)–(H8), with `α = 1` and `β = Aγ`. -/
theorem th_product_ii_paper [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} {a : Sp N → ℝ} {A : ℝ}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) (hG0 : (0 : Mat m N) ∈ dom G)
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hγ : 0 < γ) (hHusc : UpperSemicontinuous H) (hGH : ∀ ξ, G ξ ≤ H ξ)
    (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (hHrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ)
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (halsc : LowerSemicontinuous a)
    (haper : ∀ (z : Fin N → ℤ) x, a (x + fun i => (z i : ℝ)) = a x) :
    -- Borel measurability of `G` and `W`, and (H1)
    (Measurable G ∧ Measurable (uncurry (prodW a H)) ∧
      ConvexENN G ∧ LowerSemicontinuous G ∧ (0 : Mat m N) ∈ interior (dom G)) ∧
    -- (H2)
    IsPeriodic (prodW a H) ∧
    -- (H3) with `α = 1`, `β = Aγ`
    (∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      ((1 : ℝ≥0) : ℝ≥0∞) * volume U * G ξ ≤ Yt (prodW a H) U ξ ∧
        Yt (prodW a H) U ξ ≤ ((A.toNNReal * γ : ℝ≥0) : ℝ≥0∞) * volume U * (1 + G ξ)) ∧
    -- (H5)
    RUUSC (Ytloc (prodW a H)) ∧
    -- (H6)
    Measurable (uncurry (Ytloc (prodW a H))) ∧
    -- (H7)
    (∀ᵐ x, ∀ ξ, Ytloc (prodW a H) x ξ ≤ prodW a H x ξ) ∧
    -- (H8)
    (∀ ξ, Zaff (Haff (Ytloc (prodW a H))) ξ ≤
      radial (Hp (ENNReal.ofReal p) (Ytloc (prodW a H))) ξ) := by
  obtain ⟨⟨hGlsc, hG0i, hGm, hWm⟩, hper, -, hru, -, hH7, -⟩ :=
    th_product_ii (p := p) hG hGo hG0 hGsing hγ hHusc hGH hHG hHrad ha halsc haper
  exact ⟨⟨hGm, hWm, hG, hGlsc, hG0i⟩, hper,
    fun ξ U hUo hUb => prodW_setGrowth hG hGH hHG ha ξ U hUo hUb,
    hru, prodW_measurable_Ytloc hG hGH hHG ha halsc.measurable hHusc, hH7,
    th_product_H8 (p := p) hG hGo hG0 hGsing hγ hHusc hGH hHG hHrad ha halsc haper⟩

end Homogenization
