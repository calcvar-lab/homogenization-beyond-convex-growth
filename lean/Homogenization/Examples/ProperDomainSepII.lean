import Homogenization.SumOsc
import Homogenization.Examples.ProperDomainData

/-!
# Proposition `prop:separating` (ii)

`properDomainWv_sep_ii`: for a.e. `x`, `𝒴_loc W_v(x,·) = 𝒵_aff W_v(x,·) ≤ W_v(x,·)`, and this
function is upper semicontinuous on `𝕄` (hence (H7)). As in the paper, `W_v` is written as
`∑_{i=1}^3 a_i(x) H_i(ξ)` with `a = (1, b, a)` and `H = (G, K, H∘v)`, and `lem_sumosc` is
applied with `η' = min 1 η`, `Λ' = max 1 Λ`.

The paper deduces the upper semicontinuity of `G` from its convexity and finiteness. Here it is
proved directly: `g̃` is monotone and convex on `[0,∞)`, hence upper semicontinuous
(`ProperDomainGData.upperSemicontinuous_gTilde`), and `|ξ|^p` is continuous
(`upperSemicontinuous_properDomainG`). Only clause (ii) is proved here; clause (iv) (H1–H8 and the
main theorem) is not.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Homogenization

variable {m N : ℕ}

/-- `g̃` is upper semicontinuous on `[0,∞)`: on the left by monotonicity, and on the right by
convexity, `g̃(s+λ) ≤ (1-λ) g̃(s) + λ g̃(s+1)` for `λ ∈ [0,1]`. -/
theorem ProperDomainGData.upperSemicontinuous_gTilde (D : ProperDomainGData N) :
    UpperSemicontinuous D.gTilde := by
  intro s c hc
  set M : ℝ := (D.gTilde (s + 1) : ℝ)
  have hcR : (D.gTilde s : ℝ) < c := by exact_mod_cast hc
  set δ : ℝ := min 1 ((c - D.gTilde s) / (M + 1))
  have hM : 0 ≤ M := (D.gTilde (s + 1)).2
  have hδ : 0 < δ := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hlt : s < s + δ.toNNReal := by
    simpa using Real.toNNReal_pos.2 hδ
  filter_upwards [eventually_lt_nhds hlt] with t ht
  rcases le_or_gt t s with hts | hst
  · exact lt_of_le_of_lt (D.gTilde_monotone hts) hc
  · have hts : (t : ℝ) - s < δ := by
      have : (t : ℝ) < s + δ := by
        have := (NNReal.coe_lt_coe.2 ht)
        simpa [Real.coe_toNNReal _ hδ.le] using this
      linarith
    set l : ℝ≥0 := t - s
    have hl : (l : ℝ) = t - s := NNReal.coe_sub hst.le
    have hl1 : l ≤ 1 := by
      rw [← NNReal.coe_le_coe, hl, NNReal.coe_one]
      linarith [min_le_left 1 ((c - D.gTilde s) / (M + 1))]
    have harg : l * (s + 1) + (1 - l) * s = t := by
      apply NNReal.eq
      push_cast [NNReal.coe_sub hl1, hl]
      ring
    have hconv := D.gTilde_convex (s + 1) s l hl1
    rw [harg] at hconv
    have hmono : (D.gTilde s : ℝ) ≤ M := by
      exact_mod_cast D.gTilde_monotone (le_self_add : s ≤ s + 1)
    have hlδ : (l : ℝ) * (M + 1) < c - D.gTilde s := by
      have h2 : (l : ℝ) < (c - D.gTilde s) / (M + 1) :=
        lt_of_lt_of_le (hl ▸ hts) (min_le_right _ _)
      rwa [lt_div_iff₀ (by linarith)] at h2
    have : (D.gTilde t : ℝ) < c := by
      have hl0 : (0 : ℝ) ≤ l := l.2
      nlinarith
    exact_mod_cast this

/-- `G(ξ) = |ξ|^p + g̃(|ξ|²)` is upper semicontinuous on `𝕄`. -/
theorem upperSemicontinuous_properDomainG (D : ProperDomainGData N) :
    UpperSemicontinuous (properDomainG D : Mat m N → ℝ≥0∞) := by
  have hnorm : Continuous (matrixFrobeniusNorm (m := m) (N := N)) := by
    unfold matrixFrobeniusNorm
    fun_prop
  have hp : 0 ≤ D.p := le_trans (Nat.cast_nonneg N) D.dim_lt_p.le
  have hpow : Continuous (fun A : Mat m N => (matrixFrobeniusNorm A ^ D.p).toNNReal) :=
    continuous_real_toNNReal.comp (hnorm.rpow_const (fun _ => Or.inr hp))
  have harg : Continuous (fun A : Mat m N =>
      (⟨matrixFrobeniusNorm A ^ 2, sq_nonneg _⟩ : ℝ≥0)) :=
    (hnorm.pow 2).subtype_mk (fun _ => sq_nonneg _)
  have hsum : UpperSemicontinuous (fun A : Mat m N =>
      (matrixFrobeniusNorm A ^ D.p).toNNReal +
        D.gTilde ⟨matrixFrobeniusNorm A ^ 2, sq_nonneg _⟩) :=
    hpow.upperSemicontinuous.add (D.upperSemicontinuous_gTilde.comp harg)
  have h := ENNReal.continuous_coe.comp_upperSemicontinuous hsum ENNReal.coe_mono
  convert h using 1
  funext A
  simp [properDomainG, ENNReal.ofReal]

/-- **Proposition `prop:separating` (ii).** There is a single null set of `x` outside which
`𝒴_loc W_v(x,·) = 𝒵_aff W_v(x,·) ≤ W_v(x,·)` and `𝒴_loc W_v(x,·)` is upper semicontinuous.
This is `lem_sumosc` with three terms; no cited hypothesis is used. Clause (iv) is not proved
here. -/
theorem properDomainWv_sep_ii [NeZero N] (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∀ᵐ x, Ytloc (properDomainWv D KD HD CD) x = Zaff (properDomainWv D KD HD CD x) ∧
      Zaff (properDomainWv D KD HD CD x) ≤ properDomainWv D KD HD CD x ∧
      UpperSemicontinuous (Ytloc (properDomainWv D KD HD CD) x) := by
  set a : Fin 3 → Sp N → ℝ := ![fun _ => 1, CD.coeffB, CD.coeffA] with ha_def
  set H : Fin 3 → Mat m N → ℝ≥0∞ :=
    ![properDomainG D, fun A => (KD.K A : ℝ≥0∞), fun A => HD.H (properDomainJacobian A)]
    with hH_def
  have hsum : (fun x ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) = properDomainWv D KD HD CD := by
    funext x ξ
    simp [a, H, Fin.sum_univ_three, properDomainWv, add_assoc]
  have hη : 0 < min 1 CD.eta := lt_min one_pos CD.eta_pos
  have ha : ∀ i x, min 1 CD.eta ≤ a i x ∧ a i x ≤ max 1 CD.Lambda := by
    intro i x
    fin_cases i
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨(min_le_right _ _).trans (CD.b_range x).1, (CD.b_range x).2.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (CD.a_range x).1, (CD.a_range x).2.trans (le_max_right _ _)⟩
  have halsc : ∀ i, LowerSemicontinuous (a i) := by
    intro i
    fin_cases i
    · exact lowerSemicontinuous_const
    · exact CD.b_lowerSemicontinuous
    · exact CD.a_lowerSemicontinuous
  have hH : ∀ i, UpperSemicontinuous (H i) := by
    intro i
    fin_cases i
    · exact upperSemicontinuous_properDomainG D
    · exact ENNReal.continuous_coe.comp_upperSemicontinuous KD.upperSemicontinuous
        ENNReal.coe_mono
    · exact HD.upperSemicontinuous.comp continuous_properDomainJacobian
  have h := lem_sumosc hη ha halsc hH
  rw [hsum] at h
  filter_upwards [h] with x hx
  have e : (fun ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) = properDomainWv D KD HD CD x :=
    congrFun hsum x
  rw [e] at hx
  exact hx

end Homogenization
