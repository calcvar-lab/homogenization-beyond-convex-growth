import Homogenization.Examples.ProperDomainSepIV
import Homogenization.Examples.ProperDomainSharpLoc

/-!
# Proposition `prop:properdomain` (iv)

`properDomainWSharpExample_hypotheses`: `W♯(x,ξ) = W_v(x,ξ¹) + G₂(ξ²)` satisfies the standing
hypotheses (H1)–(H8) of the main theorem with `G♯(ξ) = G(ξ¹) + G₂(ξ²)` and `α = 1`:
* (H1) convexity and lower semicontinuity of `G♯`, `0 ∈ dom G♯` open (`ProperDomainGeometry`);
* (H3) `properDomainWSharpExample_setGrowth`: Jensen for the lower bound; for the upper bound
  `W♯ ≤ W♯⁺ = W⁺(ξ¹) + G₂(ξ²)`, `𝒴 W♯⁺(U,·) ≤ |U| 𝒵_aff W♯⁺`, the decoupling
  `𝒵_aff W♯⁺ = 𝒵_aff W⁺(ξ¹) + G₂(ξ²)` and `sep:iii` (`properDomainWSharpPlus_Zaff_le`);
* (H4) `exists_coercive_properDomainGSharpExample`;
* (H5) `properDomainWSharpExample_ruuscWith`: `properDomainWv_ruuscWith` and convexity of `G₂`;
* (H6) `properDomainWSharpExample_measurable_Ytloc`, exact (`measurable_Ytloc_sumW`, four terms);
* (H7) `properDomainWSharpExample_Ytloc_eq`;
* (H8) `prop_Z3suff`; its radial condition on `G♯` is effective here and is
  `properDomainGSharpExample_tendsto_top`.

`properDomainWSharpExample_pd_iv`: the Γ-convergence of `∫_Ω W♯(x/ε, ∇u)`, without cited
hypothesis (the cited results of the main theorem are proved: `citedAffineApprox_holds`,
`citedSobolevCompact_holds`, `citedSobolevDiff_holds`, `citedMeasureLimit_holds`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m₁ m₂ : ℕ}

/-- `W♯` as a four-term sum `1·G(ξ¹) + b·K(ξ¹) + a·H(v(ξ¹)) + 1·G₂(ξ²)`. -/
theorem properDomainWSharpExample_eq_sumW [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD =
      sumW ![fun _ => 1, CD.coeffB, CD.coeffA, fun _ => 1]
        ![fun A => properDomainG D (matBlockSplitLinearEquiv m₁ m₂ N A).1,
          fun A => (KD.K (matBlockSplitLinearEquiv m₁ m₂ N A).1 : ℝ≥0∞),
          fun A => HD.H (properDomainJacobian (matBlockSplitLinearEquiv m₁ m₂ N A).1),
          fun A => properDomainG2 D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2] := by
  funext x ξ
  simp [sumW, Fin.sum_univ_four, properDomainWSharpExample, properDomainWSharp,
    separatedSum, properDomainWv, add_assoc]

/-- (H6) for `W♯`: `(x,ξ) ↦ 𝒴_loc W♯(x,ξ)` is jointly Borel measurable, without modification. -/
theorem properDomainWSharpExample_measurable_Ytloc [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    Measurable (uncurry (Ytloc (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD))) := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  have h1 : Continuous fun A : Mat (m₁ + m₂) N => (e A).1 := continuous_fst.comp e.continuous
  have h2 : Continuous fun A : Mat (m₁ + m₂) N => (e A).2 := continuous_snd.comp e.continuous
  have hG2 : UpperSemicontinuous (properDomainG2 (m := m₂) (N := N) D.p) := by
    refine (properDomainG2_convexENN D.p D.dim_lt_p).upperSemicontinuous_of_isOpen_dom ?_
    have hdom : dom (properDomainG2 (m := m₂) (N := N) D.p) = properDomainHalfSpace := by
      ext χ
      exact mem_dom_properDomainG2_iff D.p χ
    rw [hdom]
    exact properDomainHalfSpace_isOpen
  rw [properDomainWSharpExample_eq_sumW]
  refine measurable_Ytloc_sumW (lt_min one_pos CD.eta_pos) (Λ := max 1 CD.Lambda)
    (fun k x => ?_) (fun k => ?_) (fun k => ?_)
  · fin_cases k
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨(min_le_right _ _).trans (CD.b_range x).1, (CD.b_range x).2.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (CD.a_range x).1, (CD.a_range x).2.trans (le_max_right _ _)⟩
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · fin_cases k
    · exact measurable_const
    · exact CD.b_measurable
    · exact CD.a_measurable
    · exact measurable_const
  · fin_cases k
    · exact (upperSemicontinuous_properDomainG D).comp h1
    · exact (ENNReal.continuous_coe.comp_upperSemicontinuous KD.upperSemicontinuous
        ENNReal.coe_mono).comp h1
    · exact (HD.upperSemicontinuous.comp continuous_properDomainJacobian).comp h1
    · exact hG2.comp h2

/-- `𝒵_aff` of the spatially uniform majorant `W♯⁺(ξ) = W⁺(ξ¹) + G₂(ξ²)` is bounded by
`(β + 1)(1 + G♯)`, with `β` from `sep:iii`. -/
theorem properDomainWSharpPlus_Zaff_le [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∃ β : ℝ≥0, ∀ A : Mat (m₁ + m₂) N,
      Zaff (fun B : Mat (m₁ + m₂) N => separatedSum (properDomainWPlus D KD HD CD)
        (properDomainG2 D.p) (matBlockSplitLinearEquiv m₁ m₂ N B)) A ≤
        (β : ℝ≥0∞) * (1 + properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D A) := by
  obtain ⟨β, hβ⟩ := properDomainWPlus_Zaff_le_growth D KD HD CD
  refine ⟨β + 1, fun A => ?_⟩
  rw [congrFun (Zaff_separatedSum_matBlockSplit _ (properDomainG2 (m := m₂) D.p)) A,
    properDomainG2_Zaff_eq (m₂ := m₂) D]
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  change _ ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) *
    (1 + (properDomainG D (e A).1 + properDomainG2 D.p (e A).2))
  have hb : (β : ℝ≥0∞) ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_self_add
  have h1 : (1 : ℝ≥0∞) ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_add_self
  calc Zaff (properDomainWPlus D KD HD CD) (e A).1 + properDomainG2 D.p (e A).2
      ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) * (1 + properDomainG D (e A).1) +
          ((β + 1 : ℝ≥0) : ℝ≥0∞) * properDomainG2 D.p (e A).2 := by
        gcongr
        · exact (hβ _).trans (by gcongr)
        · calc properDomainG2 D.p (e A).2 = 1 * properDomainG2 D.p (e A).2 := (one_mul _).symm
            _ ≤ _ := by gcongr
    _ = _ := by ring

/-- (H3) for `W♯`, with `α = 1`. -/
theorem properDomainWSharpExample_setGrowth [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      ((1 : ℝ≥0) : ℝ≥0∞) * volume U * properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D ξ ≤
          Yt (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) U ξ ∧
        Yt (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) U ξ ≤
          (β : ℝ≥0∞) * volume U * (1 + properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D ξ) := by
  obtain ⟨β, hβ⟩ := properDomainWSharpPlus_Zaff_le (m₁ := m₁) (m₂ := m₂) D KD HD CD
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  refine ⟨β + 1, by positivity, fun ξ U hUo hUb => ⟨?_, ?_⟩⟩
  · rw [ENNReal.coe_one, one_mul]
    refine ((properDomainGSharpExample_convexENN (m₁ := m₁) (m₂ := m₂) D).volume_mul_le_Yt_of_isOpen
      hUo hUb ξ).trans (Yt_mono (fun y ζ => ?_) U ξ)
    change properDomainG D (e ζ).1 + properDomainG2 D.p (e ζ).2 ≤
      properDomainWv D KD HD CD y (e ζ).1 + properDomainG2 D.p (e ζ).2
    gcongr
    change properDomainG D (e ζ).1 ≤ properDomainG D (e ζ).1 + _ + _
    rw [add_assoc]
    exact le_self_add
  · by_cases hU0 : volume U = 0
    · refine (iInf₂_le (0 : Sp N → Tgt (m₁ + m₂)) (zero_mem_Aff0 hUo)).trans ?_
      rw [Measure.restrict_eq_zero.2 hU0, lintegral_zero_measure]
      exact zero_le
    calc Yt (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) U ξ
        ≤ Yt (fun _ (B : Mat (m₁ + m₂) N) => separatedSum (properDomainWPlus D KD HD CD)
            (properDomainG2 D.p) (e B)) U ξ :=
          Yt_mono (fun y B => add_le_add (properDomainWv_le_WPlus D KD HD CD y _) le_rfl) U ξ
      _ ≤ volume U * Zaff (fun B : Mat (m₁ + m₂) N => separatedSum
            (properDomainWPlus D KD HD CD) (properDomainG2 D.p) (e B)) ξ :=
          Yt_le_volume_mul_Zaff _ hUo hUb hU0 ξ
      _ ≤ volume U * ((β : ℝ≥0∞) * (1 + properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D ξ)) := by
          gcongr; exact hβ ξ
      _ ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) * volume U *
            (1 + properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D ξ) := by
          rw [← mul_assoc, mul_comm (volume U)]
          gcongr
          exact_mod_cast le_self_add

/-- `G₂(tχ) ≤ G₂(χ) + (1 - t) G₂(0)` for `t ∈ ]0,1[`, by convexity. -/
theorem properDomainG2_smul_le [NeZero N] [NeZero m₂] (p : ℝ) (hp : (N : ℝ) < p) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (χ : Mat m₂ N) :
    properDomainG2 p (t • χ) ≤
      properDomainG2 p χ + ENNReal.ofReal (1 - t) * properDomainG2 p (0 : Mat m₂ N) := by
  have hconv := properDomainG2_convexENN (m := m₂) (N := N) p hp χ 0 t.toNNReal
    (by rw [Real.toNNReal_le_one]; exact ht1.le)
  have e1 : ((t.toNNReal : ℝ) • χ + ((1 - t.toNNReal : ℝ≥0) : ℝ) • (0 : Mat m₂ N)) = t • χ := by
    rw [smul_zero, add_zero, Real.coe_toNNReal _ ht0.le]
  rw [e1] at hconv
  refine hconv.trans (add_le_add ?_ (le_of_eq ?_))
  · calc ((t.toNNReal : ℝ≥0) : ℝ≥0∞) * properDomainG2 p χ ≤ 1 * properDomainG2 p χ := by
          gcongr; exact_mod_cast Real.toNNReal_le_one.2 ht1.le
      _ = properDomainG2 p χ := one_mul _
  · rw [ENNReal.ofReal_sub _ ht0.le, ENNReal.ofReal_one, ENNReal.coe_sub, ENNReal.coe_one]
    rfl

/-- (H5) for `W♯` itself: uniform ru-usc relative to `0`. -/
theorem properDomainWSharpExample_ruuscWith [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    RUUSCWith (((properDomainG D (0 : Mat m₁ N)).toNNReal + 1) +
        ((properDomainG2 (m := m₂) (N := N) D.p 0).toNNReal + 1))
      (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) := by
  intro η hη
  have hη' : (0 : ℝ) < η := hη
  have h2 : ∀ᶠ t in 𝓝 (1 : ℝ), 1 - (η : ℝ) < t ∧ 0 < t :=
    (lt_mem_nhds (by linarith)).and (lt_mem_nhds one_pos)
  filter_upwards [properDomainWv_ruuscWith D KD HD CD η hη, nhdsWithin_le_nhds h2,
    self_mem_nhdsWithin] with t hWv ⟨ht1, ht0⟩ (htlt : t < 1) x A hfin
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  set c₁ : ℝ≥0 := (properDomainG D (0 : Mat m₁ N)).toNNReal + 1
  set c₂ : ℝ≥0 := (properDomainG2 (m := m₂) (N := N) D.p 0).toNNReal + 1
  set W1 := properDomainWv D KD HD CD x (e A).1
  set W2 := properDomainG2 D.p (e A).2
  have hfin' : W1 + W2 < ⊤ := hfin
  have hW1 : W1 < ⊤ := (ENNReal.add_lt_top.1 hfin').1
  have hG2 : properDomainG2 D.p (t • (e A).2) ≤ W2 + η * c₂ := by
    refine (properDomainG2_smul_le D.p D.dim_lt_p ht0 htlt _).trans (add_le_add le_rfl ?_)
    have h1t : ENNReal.ofReal (1 - t) ≤ η := by
      calc ENNReal.ofReal (1 - t) ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)
        _ = η := ENNReal.ofReal_coe_nnreal
    have hG0 : properDomainG2 (m := m₂) (N := N) D.p 0 ≤ c₂ := by
      have h : ((properDomainG2 (m := m₂) (N := N) D.p 0).toNNReal : ℝ≥0∞) =
          properDomainG2 D.p 0 := ENNReal.coe_toNNReal (by
            have : (0 : Mat m₂ N) ∈ dom (properDomainG2 (m := m₂) (N := N) D.p) := by
              rw [show dom (properDomainG2 (m := m₂) (N := N) D.p) = properDomainHalfSpace from
                Set.ext fun χ => mem_dom_properDomainG2_iff D.p χ]
              exact zero_mem_properDomainHalfSpace
            exact this.ne)
      calc properDomainG2 (m := m₂) (N := N) D.p 0 = _ := h.symm
        _ ≤ c₂ := by exact_mod_cast le_self_add
    exact mul_le_mul' h1t hG0
  have hsplit : properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x (t • A) =
      properDomainWv D KD HD CD x (t • (e A).1) + properDomainG2 D.p (t • (e A).2) := by
    change properDomainWv D KD HD CD x (e (t • A)).1 + properDomainG2 D.p (e (t • A)).2 = _
    rw [map_smul]
    rfl
  rw [hsplit]
  change _ ≤ (W1 + W2) + (η : ℝ≥0∞) * (((c₁ + c₂ : ℝ≥0) : ℝ≥0∞) + (W1 + W2))
  calc properDomainWv D KD HD CD x (t • (e A).1) + properDomainG2 D.p (t • (e A).2)
      ≤ (W1 + η * (c₁ + W1)) + (W2 + η * c₂) := add_le_add (hWv x _ hW1) hG2
    _ ≤ (W1 + W2) + (η : ℝ≥0∞) * (((c₁ + c₂ : ℝ≥0) : ℝ≥0∞) + (W1 + W2)) := by
        push_cast
        calc (W1 + η * (c₁ + W1)) + (W2 + η * c₂)
            = (W1 + W2) + (η : ℝ≥0∞) * ((c₁ + c₂) + W1) := by ring
          _ ≤ _ := by gcongr; exact le_self_add


/-- (H4) for `G♯`: `c₀ ‖A‖^p ≤ G♯(A)`, from `G ≥ |ξ¹|_F^p` and `G₂ ≥ |ξ²|_F^p`. -/
theorem exists_coercive_properDomainGSharpExample [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) :
    ∃ c₀ : ℝ≥0, 0 < c₀ ∧ ∀ A : Mat (m₁ + m₂) N,
      ENNReal.ofReal (c₀ * ‖A‖ ^ D.p) ≤ properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D A := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_frobenius (m := m₁) (N := N)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_le_frobenius (m := m₂) (N := N)
  set E : ℝ := ‖(e.symm : (Mat m₁ N × Mat m₂ N) →L[ℝ] Mat (m₁ + m₂) N)‖
  set K : ℝ := E * max C₁ C₂ + 1
  have hE : 0 ≤ E := by positivity
  have hK : 0 < K := by positivity
  have hp : 0 ≤ D.p := le_trans (Nat.cast_nonneg N) D.dim_lt_p.le
  have hKp : 0 < K ^ D.p := Real.rpow_pos_of_pos hK _
  refine ⟨((K ^ D.p)⁻¹).toNNReal, Real.toNNReal_pos.2 (inv_pos.2 hKp), fun A => ?_⟩
  set f₁ := matrixFrobeniusNorm (e A).1
  set f₂ := matrixFrobeniusNorm (e A).2
  have hf₁ : 0 ≤ f₁ := by unfold f₁ matrixFrobeniusNorm; positivity
  have hf₂ : 0 ≤ f₂ := by unfold f₂ matrixFrobeniusNorm; positivity
  set M := max f₁ f₂
  have hM : 0 ≤ M := le_max_of_le_left hf₁
  have hnorm : ‖A‖ ≤ K * M := by
    have h1 : ‖e A‖ ≤ max C₁ C₂ * M := by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · calc ‖(e A).1‖ ≤ C₁ * f₁ := h₁ _
          _ ≤ max C₁ C₂ * M := mul_le_mul (le_max_left _ _) (le_max_left _ _) hf₁
              (hC₁.le.trans (le_max_left _ _))
      · calc ‖(e A).2‖ ≤ C₂ * f₂ := h₂ _
          _ ≤ max C₁ C₂ * M := mul_le_mul (le_max_right _ _) (le_max_right _ _) hf₂
              (hC₁.le.trans (le_max_left _ _))
    calc ‖A‖ = ‖(e.symm : (Mat m₁ N × Mat m₂ N) →L[ℝ] Mat (m₁ + m₂) N) (e A)‖ := by simp
      _ ≤ E * ‖e A‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ E * (max C₁ C₂ * M) := by gcongr
      _ ≤ K * M := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) hM
  have hMp : M ^ D.p ≤ f₁ ^ D.p + f₂ ^ D.p := by
    rcases max_cases f₁ f₂ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [show M = f₁ from h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hf₂ _)
    · rw [show M = f₂ from h]; exact le_add_of_nonneg_left (Real.rpow_nonneg hf₁ _)
  have hreal : ((K ^ D.p)⁻¹).toNNReal * ‖A‖ ^ D.p ≤ f₁ ^ D.p + f₂ ^ D.p := by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hKp.le)]
    calc (K ^ D.p)⁻¹ * ‖A‖ ^ D.p ≤ (K ^ D.p)⁻¹ * (K * M) ^ D.p := by
          gcongr
      _ = M ^ D.p := by
          rw [Real.mul_rpow hK.le hM, ← mul_assoc, inv_mul_cancel₀ hKp.ne', one_mul]
      _ ≤ _ := hMp
  calc ENNReal.ofReal (((K ^ D.p)⁻¹).toNNReal * ‖A‖ ^ D.p)
      ≤ ENNReal.ofReal (f₁ ^ D.p + f₂ ^ D.p) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (f₁ ^ D.p) + ENNReal.ofReal (f₂ ^ D.p) :=
        ENNReal.ofReal_add (Real.rpow_nonneg hf₁ _) (Real.rpow_nonneg hf₂ _)
    _ ≤ properDomainG D (e A).1 + properDomainG2 D.p (e A).2 :=
        add_le_add le_self_add (properDomainG2_ge_frobenius_rpow D.p _)

/-- Radial blow-up of `G♯` outside its domain: `G♯(tξ) → ∞` as `t → 1⁻` for `ξ ∉ dom G♯`. -/
theorem properDomainGSharpExample_tendsto_top [NeZero N] [NeZero m₂]
    (D : ProperDomainGData N) {ξ : Mat (m₁ + m₂) N}
    (hξ : ξ ∉ dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)) :
    Tendsto (fun t : ℝ => properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D (t • ξ))
      (𝓝[<] 1) (𝓝 ⊤) := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  set χ := (e ξ).2
  have hχ : 1 ≤ χ (Pi.single 0 1) 0 := by
    rw [dom_properDomainGSharpExample] at hξ
    simp only [mem_preimage, mem_prod, mem_univ, true_and] at hξ
    exact le_of_not_gt hξ
  refine tendsto_nhds_top_mono boundarySingularity_tendsto_top ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with t
    (ht1 : t < 1) (ht0 : 0 < t)
  have hmono : boundarySingularity t ≤ boundarySingularity (t * χ (Pi.single 0 1) 0) := by
    unfold boundarySingularity
    refine ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  refine hmono.trans ?_
  change _ ≤ properDomainG D (e (t • ξ)).1 + properDomainG2 D.p (e (t • ξ)).2
  rw [map_smul]
  refine le_trans ?_ le_add_self
  change _ ≤ properDomainG2 D.p (t • χ)
  simp only [properDomainG2, smul_apply, Pi.smul_apply, smul_eq_mul]
  exact le_add_self

/-- **Proposition `prop:properdomain` (iv), hypotheses (H1)–(H8).** `W♯` satisfies the standing
hypotheses of the main theorem with `G♯`, `α = 1`, with no cited hypothesis ((H8) through
`prop_Z3suff`, whose radial condition on `G♯` is now effective,
`properDomainGSharpExample_tendsto_top`). -/
theorem properDomainWSharpExample_hypotheses [NeZero N] [NeZero m₂] (D : ProperDomainGData N)
    [Fact (1 ≤ ENNReal.ofReal D.p)] (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) :
    Hypotheses D.p (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)
      (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) := by
  have hG := properDomainGSharpExample_convexENN (m₁ := m₁) (m₂ := m₂) D
  have hGlsc := properDomainGSharpExample_lowerSemicontinuous (m₁ := m₁) (m₂ := m₂) D
  have hGo := dom_properDomainGSharpExample_isOpen (m₁ := m₁) (m₂ := m₂) D
  have hper : IsPeriodic (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) :=
    fun z x ξ => by
      simp only [properDomainWSharpExample, properDomainWSharp, separatedSum, properDomainWv,
        CD.a_periodic, CD.b_periodic]
  obtain ⟨β, hβ, hset⟩ := properDomainWSharpExample_setGrowth (m₁ := m₁) (m₂ := m₂) D KD HD CD
  have hgr := HasGGrowth.Ytloc hset
  have hYm := properDomainWSharpExample_measurable_Ytloc (m₁ := m₁) (m₂ := m₂) D KD HD CD
  have hloc := properDomainWSharpExample_Ytloc_eq (m₁ := m₁) (m₂ := m₂) D KD HD CD
  obtain ⟨c₀, hc₀, hcoerG⟩ := exists_coercive_properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D
  refine
    { measurable_G := hGlsc.measurable
      measurable_W := ?_
      convex := hG
      lsc := hGlsc
      zero_mem_interior := by
        rw [hGo.interior_eq]; exact zero_mem_dom_properDomainGSharpExample D
      periodic := hper
      setGrowth := ⟨1, β, one_pos, hβ, hset⟩
      coercive := ⟨c₀, hc₀, fun x ξ => (hcoerG ξ).trans (by simpa using (hgr x ξ).1)⟩
      ruusc := ⟨_, by positivity,
        (properDomainWSharpExample_ruuscWith (m₁ := m₁) (m₂ := m₂) D KD HD CD).Ytloc⟩
      measurable_Ytloc := hYm
      Ytloc_le := ?_
      Zaff_Haff_le := fun ξ => prop_Z3suff (p := D.p) hG hGlsc hGo
        (fun ξ hξ => properDomainGSharpExample_tendsto_top D hξ) one_pos hper hset hYm
        (hloc.mono fun x hx => hx.2.2.1) ξ }
  · set e := matBlockSplitLinearEquiv m₁ m₂ N
    have hK : Measurable fun A : Mat m₁ N => (KD.K A : ℝ≥0∞) :=
      KD.upperSemicontinuous.measurable.coe_nnreal_ennreal
    have hH : Measurable fun A : Mat m₁ N => HD.H (properDomainJacobian A) :=
      HD.upperSemicontinuous.measurable.comp continuous_properDomainJacobian.measurable
    have hG2 : Measurable (properDomainG2 (m := m₂) (N := N) D.p) :=
      (properDomainG2_lowerSemicontinuous D.p
        (le_trans (Nat.cast_nonneg N) D.dim_lt_p.le)).measurable
    have h1 : Measurable fun p : Sp N × Mat (m₁ + m₂) N => (e p.2).1 :=
      measurable_fst.comp (e.continuous.measurable.comp measurable_snd)
    have h2 : Measurable fun p : Sp N × Mat (m₁ + m₂) N => (e p.2).2 :=
      measurable_snd.comp (e.continuous.measurable.comp measurable_snd)
    change Measurable fun p : Sp N × Mat (m₁ + m₂) N => (properDomainG D (e p.2).1 +
      ENNReal.ofReal (CD.coeffB p.1) * (KD.K (e p.2).1 : ℝ≥0∞) +
        ENNReal.ofReal (CD.coeffA p.1) * HD.H (properDomainJacobian (e p.2).1)) +
      properDomainG2 D.p (e p.2).2
    exact ((((measurable_properDomainG D).comp h1).add
      ((CD.b_measurable.comp measurable_fst).ennreal_ofReal.mul (hK.comp h1))).add
      ((CD.a_measurable.comp measurable_fst).ennreal_ofReal.mul (hH.comp h1))).add (hG2.comp h2)
  · filter_upwards [hloc] with x hx ξ
    rw [hx.1]
    exact hx.2.1 ξ

/-- **Proposition `prop:properdomain` (iv).** `W♯` satisfies (H1)–(H8), and, without cited
hypothesis (`main_Ggrowth_final_unconditional`),
`∫_Ω W♯(x/ε, ∇u)` Γ(Lᵖ)-converges to
`∫_Ω \widehat{ℋ(𝒵_aff W♯)}(∇u)`. -/
theorem properDomainWSharpExample_pd_iv [NeZero N] [NeZero m₂] (D : ProperDomainGData N)
    [Fact (1 ≤ ENNReal.ofReal D.p)] (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) :
    Hypotheses D.p (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)
        (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) ∧
      Whom D.p (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD) =
        radial (Hp (ENNReal.ofReal D.p)
          (fun x ξ => Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) ξ)) ∧
      GammaConverges (X := W1p N (m₁ + m₂) (ENNReal.ofReal D.p) Ω)
        (intFun (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD))
        (intHom (Whom D.p (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD))) := by
  have hW := properDomainWSharpExample_hypotheses (m₁ := m₁) (m₂ := m₂) D KD HD CD
  refine ⟨hW, ?_, main_Ggrowth_final_unconditional D.p D.dim_lt_p hΩ hW⟩
  simp only [Whom]
  rw [Hp_congr_ae ((properDomainWSharpExample_Ytloc_eq (m₁ := m₁) (m₂ := m₂) D KD HD CD).mono
    fun x hx ξ => by rw [hx.1])]

end Homogenization
