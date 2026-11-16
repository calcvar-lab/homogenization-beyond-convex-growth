import Homogenization.MeasurableYtlocSum
import Homogenization.Examples.ProperDomainSepII
import Homogenization.Examples.ProperDomainBB
import Homogenization.Examples.ProperDomainGeometry

/-!
# Proposition `prop:separating` (iv)

`properDomainWv_hypotheses`: `W_v` satisfies the standing hypotheses (H1)–(H8) of the main
theorem, with `G` as in (Dg) and `α = 1`:
* (H1) `properDomainG_convexENN`, `dom G = 𝕄`; (H2) periodicity of `a`, `b`;
* (H3) `properDomainWv_setGrowth`: Jensen for the lower bound; `W_v ≤ W⁺`,
  `𝒴 W⁺(U,·) ≤ |U| 𝒵_aff W⁺` (`Yt_le_volume_mul_Zaff`) and `sep:iii` for the upper bound;
* (H4) `G ≥ |ξ|_F^p ≥ c₀ ‖ξ‖^p` (`exists_norm_le_frobenius`);
* (H5) `properDomainWv_ruuscWith`, from the convexity of `G`, the monotonicity of `K` along rays
  and `v(tξ) = t^N v(ξ)` (`properDomainJacobian_smul`) with the scaling condition of (DH);
* (H6) `properDomainWv_measurable_Ytloc`, exact joint measurability (`measurable_Ytloc_sumW`);
* (H7) `sep:ii`; (H8) `prop_Z3suff`.

`properDomainWv_sep_iv`: the Γ-convergence of `∫_Ω W_v(x/ε, ∇u)`, without cited
hypothesis. The paper proves (H6) through a Carathéodory function and a modification on a null
set; Lean proves the exact measurability of `𝒴_loc W_v` without modification. The cited results of
the main theorem are proved (`citedAffineApprox_holds`, `citedSobolevCompact_holds`,
`citedSobolevDiff_holds`, `citedMeasureLimit_holds`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {m N : ℕ}

/-- `v(tA) = |t|^N v(A)`. -/
theorem properDomainJacobian_smul (t : ℝ) (A : Mat m N) :
    (properDomainJacobian (t • A) : ℝ) = |t| ^ N * properDomainJacobian A := by
  have e : matrixEuclideanLinearMap (t • A) = t • matrixEuclideanLinearMap A := by
    ext x i
    simp [matrixEuclideanLinearMap_apply]
  rw [properDomainJacobian_coe_eq_normDet, properDomainJacobian_coe_eq_normDet, e,
    LinearMap.normDet_smul, finrank_euclideanSpace, Fintype.card_fin, Real.norm_eq_abs]

/-- The operator norm is dominated by the Frobenius norm. -/
theorem exists_norm_le_frobenius :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Mat m N, ‖ξ‖ ≤ C * matrixFrobeniusNorm ξ := by
  set e := matCoordEquiv m N
  refine ⟨‖(e.symm : (Fin m × Fin N → ℝ) →L[ℝ] Mat m N)‖ + 1, by positivity, fun ξ => ?_⟩
  have h1 : ‖e ξ‖ ≤ matrixFrobeniusNorm ξ := by
    refine (pi_norm_le_iff_of_nonneg (by unfold matrixFrobeniusNorm; positivity)).2 fun ij => ?_
    exact PiLp.norm_apply_le (WithLp.toLp 2 (e ξ)) ij
  have hF : 0 ≤ matrixFrobeniusNorm ξ := by unfold matrixFrobeniusNorm; positivity
  calc ‖ξ‖ = ‖(e.symm : (Fin m × Fin N → ℝ) →L[ℝ] Mat m N) (e ξ)‖ := by simp
    _ ≤ ‖(e.symm : (Fin m × Fin N → ℝ) →L[ℝ] Mat m N)‖ * ‖e ξ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(e.symm : (Fin m × Fin N → ℝ) →L[ℝ] Mat m N)‖ * matrixFrobeniusNorm ξ := by gcongr
    _ ≤ _ := by nlinarith


/-- (H5) for `W_v` itself: uniform ru-usc relative to `0`, with `c = G(0) + 1`. -/
theorem properDomainWv_ruuscWith [NeZero N] (D : ProperDomainGData N) (KD : ProperDomainKData N m D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    RUUSCWith ((properDomainG D (0 : Mat m N)).toNNReal + 1) (properDomainWv D KD HD CD) := by
  intro η hη
  have hη' : (0 : ℝ) < η := hη
  have hcont : ContinuousAt (fun t : ℝ => t ^ (-HD.kappa)) 1 :=
    Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
  have h1 : ∀ᶠ t in 𝓝 (1 : ℝ), t ^ (-HD.kappa) < 1 + (η : ℝ) := by
    refine hcont.eventually (gt_mem_nhds ?_)
    simp only [Real.one_rpow]; linarith
  have h2 : ∀ᶠ t in 𝓝 (1 : ℝ), 1 - (η : ℝ) < t ∧ 0 < t :=
    (lt_mem_nhds (by linarith)).and (lt_mem_nhds one_pos)
  filter_upwards [nhdsWithin_le_nhds (h1.and h2), self_mem_nhdsWithin] with t ⟨ht1, ht2, ht0⟩
    (htlt : t < 1) x ξ hfin
  set G := properDomainG (m := m) D
  set c : ℝ≥0 := (G 0).toNNReal + 1
  set B := ENNReal.ofReal (CD.coeffB x)
  set A := ENNReal.ofReal (CD.coeffA x)
  have hvξ : properDomainJacobian ξ ≠ 0 := by
    have := dom_properDomainWv D KD HD CD x
    have hmem : ξ ∈ dom (properDomainWv D KD HD CD x) := hfin
    rw [this] at hmem
    exact hmem
  -- `G`
  have hG : G (t • ξ) ≤ G ξ + ENNReal.ofReal (1 - t) * G 0 := by
    have hconv := properDomainG_convexENN (m₁ := m) D ξ 0 t.toNNReal
      (by rw [Real.toNNReal_le_one]; exact htlt.le)
    have e1 : ((t.toNNReal : ℝ) • ξ + ((1 - t.toNNReal : ℝ≥0) : ℝ) • (0 : Mat m N)) = t • ξ := by
      rw [smul_zero, add_zero, Real.coe_toNNReal _ ht0.le]
    rw [e1] at hconv
    refine hconv.trans (add_le_add ?_ (le_of_eq ?_))
    · calc ((t.toNNReal : ℝ≥0) : ℝ≥0∞) * G ξ ≤ 1 * G ξ := by
            gcongr; exact_mod_cast Real.toNNReal_le_one.2 htlt.le
        _ = G ξ := one_mul _
    · rw [ENNReal.ofReal_sub _ ht0.le, ENNReal.ofReal_one, ENNReal.coe_sub, ENNReal.coe_one]
      rfl
  -- `K` and `H ∘ v`
  have hK : (KD.K (t • ξ) : ℝ≥0∞) ≤ KD.K ξ := by
    exact_mod_cast KD.ray_mono t ξ ht0.le htlt.le
  have hH : HD.H (properDomainJacobian (t • ξ)) ≤
      ENNReal.ofReal (t ^ (-HD.kappa)) * HD.H (properDomainJacobian ξ) := by
    have e : properDomainJacobian (t • ξ) =
        ⟨t ^ N * (properDomainJacobian ξ : ℝ),
          mul_nonneg (pow_nonneg ht0.le _) (properDomainJacobian ξ).2⟩ :=
      NNReal.eq (by rw [properDomainJacobian_smul, abs_of_pos ht0]; rfl)
    rw [e]
    exact HD.scaling t _ ht0 htlt.le hvξ
  have hpow : ENNReal.ofReal (t ^ (-HD.kappa)) ≤ (1 : ℝ≥0∞) + (η : ℝ≥0∞) := by
    calc ENNReal.ofReal (t ^ (-HD.kappa)) ≤ ENNReal.ofReal (1 + (η : ℝ)) :=
          ENNReal.ofReal_le_ofReal ht1.le
      _ = (1 : ℝ≥0∞) + (η : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add zero_le_one (NNReal.coe_nonneg η),
            ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
  have h1t : ENNReal.ofReal (1 - t) ≤ η := by
    calc ENNReal.ofReal (1 - t) ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)
      _ = η := ENNReal.ofReal_coe_nnreal
  have hG0 : G 0 ≤ c := by
    have h : ((G 0).toNNReal : ℝ≥0∞) = G 0 :=
      ENNReal.coe_toNNReal (properDomainG_lt_top (m := m) D 0).ne
    calc G 0 = ((G 0).toNNReal : ℝ≥0∞) := h.symm
      _ ≤ c := by exact_mod_cast le_self_add
  set Hv := HD.H (properDomainJacobian ξ)
  change G (t • ξ) + B * (KD.K (t • ξ) : ℝ≥0∞) + A * HD.H (properDomainJacobian (t • ξ)) ≤
    (G ξ + B * KD.K ξ + A * Hv) + η * (c + (G ξ + B * KD.K ξ + A * Hv))
  calc G (t • ξ) + B * (KD.K (t • ξ) : ℝ≥0∞) + A * HD.H (properDomainJacobian (t • ξ))
      ≤ (G ξ + η * c) + B * KD.K ξ + A * (((1 : ℝ≥0∞) + (η : ℝ≥0∞)) * Hv) := by
        gcongr
        · exact hG.trans (add_le_add le_rfl (mul_le_mul' h1t hG0))
        · exact hH.trans (mul_le_mul_left hpow _)
    _ = (G ξ + B * KD.K ξ + A * Hv) + η * (c + A * Hv) := by ring
    _ ≤ (G ξ + B * KD.K ξ + A * Hv) + η * (c + (G ξ + B * KD.K ξ + A * Hv)) := by
        gcongr
        exact le_add_self


/-- `W_v` as a three-term sum `1·G + b·K + a·(H∘v)`. -/
theorem properDomainWv_eq_sumW (D : ProperDomainGData N) (KD : ProperDomainKData N m D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    properDomainWv D KD HD CD = sumW ![fun _ => 1, CD.coeffB, CD.coeffA]
      ![properDomainG D, fun A => (KD.K A : ℝ≥0∞), fun A => HD.H (properDomainJacobian A)] := by
  funext x ξ
  simp [sumW, Fin.sum_univ_three, properDomainWv, add_assoc]

/-- (H6) for `W_v`: `(x,ξ) ↦ 𝒴_loc W_v(x,ξ)` is jointly Borel measurable, without modification. -/
theorem properDomainWv_measurable_Ytloc (D : ProperDomainGData N) (KD : ProperDomainKData N m D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    Measurable (uncurry (Ytloc (properDomainWv D KD HD CD))) := by
  rw [properDomainWv_eq_sumW]
  refine measurable_Ytloc_sumW (lt_min one_pos CD.eta_pos) (Λ := max 1 CD.Lambda)
    (fun k x => ?_) (fun k => ?_) (fun k => ?_)
  · fin_cases k
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨(min_le_right _ _).trans (CD.b_range x).1, (CD.b_range x).2.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (CD.a_range x).1, (CD.a_range x).2.trans (le_max_right _ _)⟩
  · fin_cases k
    · exact measurable_const
    · exact CD.b_measurable
    · exact CD.a_measurable
  · fin_cases k
    · exact upperSemicontinuous_properDomainG D
    · exact ENNReal.continuous_coe.comp_upperSemicontinuous KD.upperSemicontinuous
        ENNReal.coe_mono
    · exact HD.upperSemicontinuous.comp continuous_properDomainJacobian

/-- (H3) for `W_v`, with `α = 1`: `|U| G(ξ) ≤ 𝒴 W_v(U,ξ) ≤ β |U| (1 + G(ξ))` for every bounded
open `U`. The upper bound uses `W_v ≤ W⁺`, `𝒴 W⁺(U,·) ≤ |U| 𝒵_aff W⁺` and `sep:iii`. -/
theorem properDomainWv_setGrowth [NeZero N] (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      ((1 : ℝ≥0) : ℝ≥0∞) * volume U * properDomainG D ξ ≤ Yt (properDomainWv D KD HD CD) U ξ ∧
        Yt (properDomainWv D KD HD CD) U ξ ≤ (β : ℝ≥0∞) * volume U * (1 + properDomainG D ξ) := by
  obtain ⟨β, hβ⟩ := properDomainWPlus_Zaff_le_growth D KD HD CD
  refine ⟨β + 1, by positivity, fun ξ U hUo hUb => ⟨?_, ?_⟩⟩
  · rw [ENNReal.coe_one, one_mul]
    refine ((properDomainG_convexENN (m₁ := m) D).volume_mul_le_Yt_of_isOpen hUo hUb ξ).trans
      (Yt_mono (fun y ζ => ?_) U ξ)
    change properDomainG D ζ ≤ properDomainG D ζ + _ + _
    rw [add_assoc]
    exact le_self_add
  · by_cases hU0 : volume U = 0
    · refine (iInf₂_le (0 : Sp N → Tgt m) (zero_mem_Aff0 hUo)).trans ?_
      rw [Measure.restrict_eq_zero.2 hU0, lintegral_zero_measure]
      exact zero_le
    calc Yt (properDomainWv D KD HD CD) U ξ
        ≤ Yt (fun _ => properDomainWPlus D KD HD CD) U ξ :=
          Yt_mono (fun y => properDomainWv_le_WPlus D KD HD CD y) U ξ
      _ ≤ volume U * Zaff (properDomainWPlus D KD HD CD) ξ :=
          Yt_le_volume_mul_Zaff _ hUo hUb hU0 ξ
      _ ≤ volume U * ((β : ℝ≥0∞) * (1 + properDomainG D ξ)) := by gcongr; exact hβ ξ
      _ ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) * volume U * (1 + properDomainG D ξ) := by
          rw [← mul_assoc, mul_comm (volume U)]
          gcongr
          exact_mod_cast le_self_add

/-- **Proposition `prop:separating` (iv), hypotheses (H1)–(H8).** `W_v` satisfies the standing
hypotheses of the main theorem with `G` as in (Dg), `α = 1`, with no cited hypothesis ((H8)
through `prop_Z3suff`). -/
theorem properDomainWv_hypotheses [NeZero N] (D : ProperDomainGData N)
    [Fact (1 ≤ ENNReal.ofReal D.p)] (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) :
    Hypotheses D.p (properDomainG D) (properDomainWv D KD HD CD) := by
  set G := properDomainG (m := m) D
  set W := properDomainWv D KD HD CD
  have hG : ConvexENN G := properDomainG_convexENN (m₁ := m) D
  have hdom : dom G = univ := eq_univ_of_forall fun ξ => properDomainG_lt_top D ξ
  have hGo : IsOpen (dom G) := by rw [hdom]; exact isOpen_univ
  have hGlsc : LowerSemicontinuous G :=
    hG.lowerSemicontinuous_of_isOpen_dom hGo (by rw [hdom]; trivial)
      (fun ξ hξ => by rw [hdom, frontier_univ] at hξ; exact absurd hξ (notMem_empty ξ))
  have hper : IsPeriodic W := fun z x ξ => by
    simp only [W, properDomainWv, CD.a_periodic, CD.b_periodic]
  obtain ⟨β, hβ, hset⟩ := properDomainWv_setGrowth D KD HD CD
  have hgr := HasGGrowth.Ytloc hset
  have hYm := properDomainWv_measurable_Ytloc D KD HD CD
  have hii := properDomainWv_sep_ii D KD HD CD
  obtain ⟨C, hC, hCF⟩ := exists_norm_le_frobenius (m := m) (N := N)
  have hp : 0 ≤ D.p := le_trans (Nat.cast_nonneg N) D.dim_lt_p.le
  set c₀ : ℝ≥0 := ((C ^ D.p)⁻¹).toNNReal
  have hCp : 0 < C ^ D.p := Real.rpow_pos_of_pos hC _
  have hcoer : IsCoercive D.p c₀ (Ytloc W) := fun x ξ => by
    refine le_trans ?_ (le_trans (by rw [ENNReal.coe_one, one_mul]) (hgr x ξ).1)
    have hF : 0 ≤ matrixFrobeniusNorm ξ := by unfold matrixFrobeniusNorm; positivity
    calc ENNReal.ofReal (c₀ * ‖ξ‖ ^ D.p)
        ≤ ENNReal.ofReal (matrixFrobeniusNorm ξ ^ D.p) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.coe_toNNReal _ (inv_nonneg.2 hCp.le)]
          calc (C ^ D.p)⁻¹ * ‖ξ‖ ^ D.p ≤ (C ^ D.p)⁻¹ * (C * matrixFrobeniusNorm ξ) ^ D.p := by
                gcongr; exact hCF ξ
            _ = matrixFrobeniusNorm ξ ^ D.p := by
                rw [Real.mul_rpow hC.le hF, ← mul_assoc, inv_mul_cancel₀ hCp.ne', one_mul]
      _ ≤ G ξ := le_self_add
  refine
    { measurable_G := measurable_properDomainG D
      measurable_W := ?_
      convex := hG
      lsc := hGlsc
      zero_mem_interior := by rw [hGo.interior_eq, hdom]; trivial
      periodic := hper
      setGrowth := ⟨1, β, one_pos, hβ, hset⟩
      coercive := ⟨c₀, ?_, hcoer⟩
      ruusc := ⟨_, by positivity, (properDomainWv_ruuscWith D KD HD CD).Ytloc⟩
      measurable_Ytloc := hYm
      Ytloc_le := ?_
      Zaff_Haff_le := fun ξ => prop_Z3suff (p := D.p) hG hGlsc hGo
        (fun ξ hξ => absurd (by rw [hdom]; trivial) hξ) one_pos hper hset hYm
        (hii.mono fun x hx => hx.2.2) ξ }
  · have hK : Measurable fun A : Mat m N => (KD.K A : ℝ≥0∞) :=
      KD.upperSemicontinuous.measurable.coe_nnreal_ennreal
    have hH : Measurable fun A : Mat m N => HD.H (properDomainJacobian A) :=
      HD.upperSemicontinuous.measurable.comp continuous_properDomainJacobian.measurable
    change Measurable fun p : Sp N × Mat m N => properDomainG D p.2 +
      ENNReal.ofReal (CD.coeffB p.1) * (KD.K p.2 : ℝ≥0∞) +
        ENNReal.ofReal (CD.coeffA p.1) * HD.H (properDomainJacobian p.2)
    exact (((measurable_properDomainG D).comp measurable_snd).add
      ((CD.b_measurable.comp measurable_fst).ennreal_ofReal.mul (hK.comp measurable_snd))).add
      ((CD.a_measurable.comp measurable_fst).ennreal_ofReal.mul (hH.comp measurable_snd))
  · exact Real.toNNReal_pos.2 (inv_pos.2 hCp)
  · filter_upwards [hii] with x hx ξ
    rw [hx.1]
    exact hx.2.1 ξ


/-- **Proposition `prop:separating` (iv).** `W_v` satisfies (H1)–(H8), and, without cited
hypothesis (`main_Ggrowth_final_unconditional`),
`∫_Ω W_v(x/ε, ∇u)` Γ(Lᵖ)-converges to `∫_Ω \widehat{ℋ(𝒵_aff W_v)}(∇u)`; the homogenized density
is computed with `𝒵_aff W_v(x,·)` in place of `𝒴_loc W_v(x,·)` (`sep:ii`). -/
theorem properDomainWv_sep_iv [NeZero N] (D : ProperDomainGData N)
    [Fact (1 ≤ ENNReal.ofReal D.p)] (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) :
    Hypotheses D.p (properDomainG D) (properDomainWv D KD HD CD) ∧
      Whom D.p (properDomainWv D KD HD CD) =
        radial (Hp (ENNReal.ofReal D.p) (fun x ξ => Zaff (properDomainWv D KD HD CD x) ξ)) ∧
      GammaConverges (X := W1p N m (ENNReal.ofReal D.p) Ω) (intFun (properDomainWv D KD HD CD))
        (intHom (Whom D.p (properDomainWv D KD HD CD))) := by
  have hW := properDomainWv_hypotheses D KD HD CD
  refine ⟨hW, ?_, main_Ggrowth_final_unconditional D.p D.dim_lt_p hΩ hW⟩
  simp only [Whom]
  rw [Hp_congr_ae ((properDomainWv_sep_ii D KD HD CD).mono fun x hx ξ => by rw [hx.1])]

end Homogenization
