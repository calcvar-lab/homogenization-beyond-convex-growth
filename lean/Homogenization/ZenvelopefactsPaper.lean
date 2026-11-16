import Homogenization.RankOne
import Homogenization.CascGeneral

/-!
# Appendix A: `Zenvelopefacts-cite` (i) in the form of the article

* `meanZaff`: the inequality (eq:meanZaff) of Step 2 of Appendix A,
  `𝒵_aff L(ξ) ≤ ⨍_U 𝒵_aff L(ξ + ∇ψ)` for every bounded open nonempty `U` with `|∂U| = 0` and every
  `ψ ∈ Aff₀(U)`; no measurability of `L` is assumed.
* `Zenvelopefacts_i_paper`: Proposition `Zenvelopefacts-cite` (i) as stated in the article: for
  every `ξ ∈ int(dom 𝒵_aff L)`, every `t ∈ ]0,1[`, every `d ∈ ℝᵐ` (including `d = 0`) and every
  `ν ∈ ℝᴺ` with Euclidean norm `|ν| = 1`, the rank-one inequality (eq:rk1) holds, and `𝒵_aff L` is
  locally Lipschitz on `int(dom 𝒵_aff L)`. (`RankOneConvexOn` normalizes `ν` in the sup norm of
  `Sp N`; `Zaff.rankOneInequality` holds for every `ν ≠ 0`, which covers both conventions.)
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- **(eq:meanZaff).** For every bounded open nonempty `U` with `|∂U| = 0`, every `ψ ∈ Aff₀(U)` and
every `ξ`, `𝒵_aff L(ξ) ≤ |U|⁻¹ ∫_U 𝒵_aff L(ξ + ∇ψ)`. No measurability of `L` is assumed. -/
theorem meanZaff (L : Mat m N → ℝ≥0∞) {U : Set (Sp N)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) (hUf : volume (frontier U) = 0)
    {ψ : Sp N → Tgt m} (hψ : ψ ∈ Aff0 U) (ξ : Mat m N) :
    Zaff L ξ ≤ (volume U)⁻¹ * ∫⁻ y in U, Zaff L (ξ + fderiv ℝ ψ y) := by
  calc Zaff L ξ = Zaff (Zaff L) ξ := (Zaff_Zaff L ξ).symm
    _ ≤ (volume U)⁻¹ * Yt (fun _ => Zaff L) U ξ :=
        Zaff_le_normalized_Yt (Zaff L) hU hUb hUne hUf ξ
    _ ≤ _ := by
        gcongr
        exact iInf₂_le ψ hψ

/-- **Proposition `Zenvelopefacts-cite` (i)**, as stated in the article: the rank-one inequality
(eq:rk1) at every point of `int(dom 𝒵_aff L)`, for every `t ∈ ]0,1[`, every `d ∈ ℝᵐ` and every
`ν ∈ ℝᴺ` with `|ν| = 1` (Euclidean norm), and the local Lipschitz continuity of `𝒵_aff L` on
`int(dom 𝒵_aff L)`. No measurability of `L` is assumed. -/
theorem Zenvelopefacts_i_paper (L : Mat m N → ℝ≥0∞) :
    (∀ ξ ∈ interior (dom (Zaff L)), ∀ t ∈ Ioo (0 : ℝ) 1, ∀ (d : Tgt m) (ν : Sp N),
      euclNorm ν = 1 →
        Zaff L ξ ≤ ENNReal.ofReal t * Zaff L (ξ + (1 - t) • rankOne d ν) +
          ENNReal.ofReal (1 - t) * Zaff L (ξ - t • rankOne d ν)) ∧
      ∀ ξ ∈ interior (dom (Zaff L)),
        ∃ K : ℝ≥0, ∃ s ∈ 𝓝 ξ, LipschitzOnWith K (fun ζ => (Zaff L ζ).toReal) s := by
  refine ⟨fun ξ hξ t ht d ν hν => ?_, fun ξ hξ => citedZaffLocLip L ξ hξ⟩
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp [euclNorm] at hν
  have hfin : ∀ Z ∈ interior (dom (Zaff L)), Zaff L Z ≠ ⊤ := fun Z hZ =>
    lt_top_iff_ne_top.mp (by simpa [dom] using interior_subset hZ)
  have h := Zaff.rankOneInequality (Zaff L) isOpen_interior hfin hξ d hν0 1 ht
  simpa only [Zaff_Zaff, mul_one] using h

end Homogenization
