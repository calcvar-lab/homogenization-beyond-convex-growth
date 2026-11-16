import Homogenization.Examples.ProperDomainBB

/-!
# Upper bound of clause (iii) of `prop:properdomain` for `W♯`

`properDomainWSharpExample_Zaff_upper`: there is `β♯` such that, for every `x` and every matrix
`A`, `𝒵_aff W♯(x,·)(A) ≤ β♯ (1 + G♯(A))`. This combines the global bound of `sep:iii`
(`properDomainWv_Zaff_le_growth`, proved without cited hypothesis) with the conditional estimate
`properDomainWSharpExample_Zaff_upper_of_Wv_bound`, with `β♯ = max(β,1)`. The identity
`𝒴_loc W♯ = 𝒵_aff W♯` a.e. is not proved here.
-/

open scoped ENNReal NNReal

namespace Homogenization

variable {N m₁ m₂ : ℕ} [NeZero N] [NeZero m₂]

/-- **Clause (iii) of `prop:properdomain`, upper bound**: `𝒵_aff W♯(x,·) ≤ β♯ (1 + G♯)`,
uniformly in `x`, with no cited hypothesis. -/
theorem properDomainWSharpExample_Zaff_upper
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∃ β : ℝ≥0, ∀ x (A : Mat (m₁ + m₂) N),
      Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) A ≤
        (β : ℝ≥0∞) * (1 + properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D A) := by
  obtain ⟨β, hβ⟩ := properDomainWv_Zaff_le_growth D KD HD CD
  refine ⟨max β 1, fun x A => ?_⟩
  have h := properDomainWSharpExample_Zaff_upper_of_Wv_bound (m₂ := m₂) D KD HD CD x β (hβ x) A
  exact_mod_cast h

end Homogenization
