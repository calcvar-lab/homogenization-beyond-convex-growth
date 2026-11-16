import Homogenization.Recovery
import Homogenization.LowerBound
import Homogenization.Vitali
import Homogenization.MeasureLimit
import Homogenization.SobolevCompactUniform
import Homogenization.AffineApprox

/-!
# Assembly of Theorem 1.1 of AHM14 and of the main theorem

The results cited in the paper and used here are proved in Lean: (a) `citedSobolevCompact_holds`
(`SobolevCompact.lean`, `SobolevCompactUniform.lean`), (b) `citedSobolevDiff_holds`
(`Morrey.lean`), (c) `citedMeasureLimit_holds` (`MeasureLimit.lean`) and `CitedAffineApprox`
(`citedAffineApprox_holds`, `AffineApprox.lean`). This file assembles, without cited hypothesis:
* `localLowerBound`: the local lower bound, Proposition 2.1(i) of [oah-jpm-zorgati14];
* `citedAHM14_holds`: Theorem `th:AHM11` ([oah-jpm-zorgati14, Theorem 1.1]);
* `main_Ggrowth_final_unconditional`: Theorem `main-Ggrowth`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

/-- **Proposition 2.1(i)** of [oah-jpm-zorgati14], local form, without cited hypothesis:
`localLowerBound_of_cited` with (a), (b), (c) supplied by `citedSobolevCompact_holds`,
`citedSobolevDiff_holds` and `citedMeasureLimit_holds`. -/
theorem localLowerBound {N m : ℕ} [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] :
    LocalLowerBoundStatement N m p :=
  localLowerBound_of_cited N m (citedSobolevCompact_holds p) (citedSobolevDiff_holds p)
    citedMeasureLimit_holds

/-- **Theorem `th:AHM11`** ([oah-jpm-zorgati14, Theorem 1.1]) without cited hypothesis: the
Γ-liminf half is `localLowerBound` (with `O = Ω`), the Γ-limsup half is
`GammaLimsup_le_intHom_radialHp`. -/
theorem citedAHM14_holds {N m : ℕ} [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    CitedAHM14 N m p := by
  intro hp Ω hΩo hΩb hΩne hΩL G α β c₀ L hG h0 hα hc₀ hLm hLp hLc hLg hLr u
  exact ⟨(localLowerBound (N := N) (m := m) (p := p)).lowerBound
      hp Ω hΩo hΩb hΩne hΩL G α β c₀ L hG h0 hα hc₀ hLm hLp hLc hLg hLr u,
    GammaLimsup_le_intHom_radialHp hG hLg hα hLp hLr hΩo hΩb u hp h0 hLc hc₀⟩

variable {N : ℕ}

/-- **Theorem `main-Ggrowth`** without cited hypothesis: `main_Ggrowth_final_two` with
`CitedAHM14` supplied by `citedAHM14_holds` and `CitedAffineApprox` by
`citedAffineApprox_holds`. -/
theorem main_Ggrowth_final_unconditional {m : ℕ} [NeZero N] (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : (N : ℝ) < p) {Ω : Set (Sp N)}
    (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    (hW : Hypotheses p G W) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W)
      (intHom (Whom p W)) :=
  main_Ggrowth_final_two p hp hΩ hW (citedAHM14_holds p) (citedAffineApprox_holds p)

end Homogenization
