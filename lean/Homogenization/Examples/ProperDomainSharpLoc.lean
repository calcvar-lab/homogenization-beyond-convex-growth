import Homogenization.Examples.ProperDomainSepII
import Homogenization.Examples.ProperDomainEnvelopes

/-!
# Clause (iii) of `prop:properdomain`: `𝒴_loc W♯ = 𝒵_aff W♯` a.e.

`properDomainWSharpExample_Ytloc_eq`: there is a single null set of `x` outside which
`𝒴_loc W♯(x,·) = 𝒵_aff W♯(x,·) = 𝒵_aff W_v(x,ξ¹) + G₂(ξ²) ≤ W♯(x,·)`, and this function is upper
semicontinuous. As in the paper, `lem_sumosc` is applied with four terms, coefficients
`(1, b, a, 1)` and integrands `G(ξ¹)`, `K(ξ¹)`, `H(v(ξ¹))`, `G₂(ξ²)`. The upper semicontinuity of
`G₂` comes from `ConvexENN.upperSemicontinuous_of_isOpen_dom`: a convex function with open
effective domain is continuous on it and equals `∞` outside. Clause (iv) of `prop:properdomain`
is not proved here.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m₁ m₂ : ℕ}

/-- A convex `[0,∞]`-valued function with open effective domain is upper semicontinuous. -/
theorem ConvexENN.upperSemicontinuous_of_isOpen_dom {m : ℕ} {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) : UpperSemicontinuous G := by
  intro ξ y hy
  have hξ : ξ ∈ dom G := lt_of_lt_of_le hy le_top
  have hc : ContinuousAt G ξ := hG.continuousOn_interior_dom.continuousAt
    (isOpen_interior.mem_nhds (by rwa [hGo.interior_eq]))
  exact hc.eventually (gt_mem_nhds hy)

/-- **`prop:properdomain` (iii), local envelope.** For a.e. `x`,
`𝒴_loc W♯(x,·) = 𝒵_aff W♯(x,·) ≤ W♯(x,·)`, `𝒴_loc W♯(x,·)` is upper semicontinuous, and
`𝒴_loc W♯(x,ξ) = 𝒵_aff W_v(x,ξ¹) + G₂(ξ²)`. No cited hypothesis is used. -/
theorem properDomainWSharpExample_Ytloc_eq [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∀ᵐ x, Ytloc (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) x =
        Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) ∧
      Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) ≤
        properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x ∧
      UpperSemicontinuous (Ytloc (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) x) ∧
      ∀ A : Mat (m₁ + m₂) N,
        Ytloc (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) x A =
          Zaff (properDomainWv D KD HD CD x) (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
            properDomainG2 (m := m₂) D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2 := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  set a : Fin 4 → Sp N → ℝ := ![fun _ => 1, CD.coeffB, CD.coeffA, fun _ => 1]
  set H : Fin 4 → Mat (m₁ + m₂) N → ℝ≥0∞ :=
    ![fun A => properDomainG D (e A).1, fun A => (KD.K (e A).1 : ℝ≥0∞),
      fun A => HD.H (properDomainJacobian (e A).1), fun A => properDomainG2 D.p (e A).2]
  have hsum : (fun x ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) =
      properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD := by
    funext x ξ
    simp [a, H, e, Fin.sum_univ_four, properDomainWSharpExample, properDomainWSharp,
      separatedSum, properDomainWv, add_assoc]
  have hη : 0 < min 1 CD.eta := lt_min one_pos CD.eta_pos
  have ha : ∀ i x, min 1 CD.eta ≤ a i x ∧ a i x ≤ max 1 CD.Lambda := by
    intro i x
    fin_cases i
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨(min_le_right _ _).trans (CD.b_range x).1, (CD.b_range x).2.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (CD.a_range x).1, (CD.a_range x).2.trans (le_max_right _ _)⟩
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
  have halsc : ∀ i, LowerSemicontinuous (a i) := by
    intro i
    fin_cases i
    · exact lowerSemicontinuous_const
    · exact CD.b_lowerSemicontinuous
    · exact CD.a_lowerSemicontinuous
    · exact lowerSemicontinuous_const
  have h1 : Continuous fun A : Mat (m₁ + m₂) N => (e A).1 := continuous_fst.comp e.continuous
  have h2 : Continuous fun A : Mat (m₁ + m₂) N => (e A).2 := continuous_snd.comp e.continuous
  have hG2 : UpperSemicontinuous (properDomainG2 (m := m₂) (N := N) D.p) := by
    refine (properDomainG2_convexENN D.p D.dim_lt_p).upperSemicontinuous_of_isOpen_dom ?_
    have hdom : dom (properDomainG2 (m := m₂) (N := N) D.p) = properDomainHalfSpace := by
      ext χ
      exact mem_dom_properDomainG2_iff D.p χ
    rw [hdom]
    exact properDomainHalfSpace_isOpen
  have hH : ∀ i, UpperSemicontinuous (H i) := by
    intro i
    fin_cases i
    · exact (upperSemicontinuous_properDomainG D).comp h1
    · exact (ENNReal.continuous_coe.comp_upperSemicontinuous KD.upperSemicontinuous
        ENNReal.coe_mono).comp h1
    · exact (HD.upperSemicontinuous.comp continuous_properDomainJacobian).comp h1
    · exact hG2.comp h2
  have h := lem_sumosc hη ha halsc hH
  rw [hsum] at h
  filter_upwards [h] with x hx
  have e' : (fun ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) =
      properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x := congrFun hsum x
  rw [e'] at hx
  refine ⟨hx.1, hx.2.1, hx.2.2, fun A => ?_⟩
  rw [hx.1]
  exact properDomainWSharpExample_Zaff_eq D KD HD CD x A

end Homogenization
