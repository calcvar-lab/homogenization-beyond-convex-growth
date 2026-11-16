import Homogenization.OscGeneral
import Homogenization.Jensen
import Homogenization.RankOne
import Homogenization.SumOsc
import Homogenization.USCIneq
import Homogenization.AHM14
import Homogenization.RadialRep

/-!
# Integrands of the form `a(x) H(ξ)`

Formalization of Lemma `lem:product` and Theorem `th:product` of
`Homogenization_beyond_convex_growthV1.tex`.

* `lem_product`: for `G` convex with `dom G` open and `H` upper semicontinuous with
  `G ≤ H ≤ γ(1 + G)` and `H(tξ) ≤ H(ξ)` for `t ∈ [0,1]`, the envelope `𝒵_aff H` satisfies
  `G ≤ 𝒵_aff H ≤ H`, `dom 𝒵_aff H = dom G`, `𝒵_aff H(tξ) ≤ 𝒵_aff H(ξ)` for `t ∈ [0,1]`, and is
  locally Lipschitz on `dom G`, upper semicontinuous and Borel measurable on `𝕄`.
* `ConvexENN.volume_mul_le_Yt_of_isOpen`: Jensen's inequality `|U| G(ξ) ≤ 𝒴 G(U,ξ)` on every
  bounded open `U`, without `|∂U| = 0`. It rests on `ae_fderiv_eq_zero_of_eq_zero_on`: a
  Lipschitz function vanishing on `F` has zero derivative at a.e. point of `F` (Lebesgue density
  points and Rademacher's theorem).
* `th_product_i`, `th_product_ii`, `th_product_iii`: Theorem `th:product` (i), (ii), (iii) for
  `W = prodW a H`. The literal measurability (H6) of `𝒴_loc W` is not proved (only up to
  modification on a null set of `x`); it is an explicit hypothesis of (iii) and of (H8).
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Pointwise

namespace Homogenization

variable {N m : ℕ}

/-- Radial monotonicity passes to `𝒵_aff`: if `H(tξ) ≤ H(ξ)` for all `t ∈ [0,1]` and all `ξ`,
then `𝒵_aff H(tξ) ≤ 𝒵_aff H(ξ)` (test with `tφ ∈ Aff₀(Y)`). -/
theorem Zaff_smul_le {H : Mat m N → ℝ≥0∞}
    (hH : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ξ : Mat m N) : Zaff H (t • ξ) ≤ Zaff H ξ := by
  unfold Zaff Yt
  refine le_iInf₂ fun φ hφ => (iInf₂_le (t • φ) (smul_mem_Aff0 hφ t)).trans ?_
  refine lintegral_mono fun y => ?_
  have hd : fderiv ℝ (t • φ) y = t • fderiv ℝ φ y := by
    simpa using congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := φ) t) y
  rw [hd, ← smul_add]
  exact hH t ht0 ht1 _

/-- **Lemma `lem:product`.** Let `G` be convex with `dom G` open, and let `H` be upper
semicontinuous with `G ≤ H ≤ γ(1 + G)` and `H(tξ) ≤ H(ξ)` for `t ∈ [0,1]`. Then
`G ≤ 𝒵_aff H ≤ H`, `dom 𝒵_aff H = dom G`, `𝒵_aff H(tξ) ≤ 𝒵_aff H(ξ)` for `t ∈ [0,1]`,
`𝒵_aff H` is locally Lipschitz on `dom G` (on the real-valued function `ζ ↦ (𝒵_aff H ζ).toReal`),
upper semicontinuous and Borel measurable.

The hypotheses `0 ∈ dom G`, the singularity `G(tξ) → ∞` on `∂(dom G)`, the measurability of `H`
and the coefficient `a` of the paper are not used by these conclusions (they serve in
`th_product_ii`). -/
theorem lem_product {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} (hG : ConvexENN G) (hGo : IsOpen (dom G))
    (hHusc : UpperSemicontinuous H) (hGH : ∀ ξ, G ξ ≤ H ξ) (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (hHrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ) :
    (∀ ξ, G ξ ≤ Zaff H ξ ∧ Zaff H ξ ≤ H ξ) ∧ dom (Zaff H) = dom G ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, Zaff H (t • ξ) ≤ Zaff H ξ) ∧
      (∀ ξ ∈ dom G, ∃ K : ℝ≥0, ∃ s ∈ 𝓝 ξ,
        LipschitzOnWith K (fun ζ => (Zaff H ζ).toReal) s) ∧
      UpperSemicontinuous (Zaff H) ∧ Measurable (Zaff H) := by
  have hbounds : ∀ ξ, G ξ ≤ Zaff H ξ ∧ Zaff H ξ ≤ H ξ := fun ξ =>
    ⟨(congrFun hG.Zaff_eq ξ).symm.le.trans (Zaff_mono hGH ξ), Zaff_le H ξ⟩
  have hdom : dom (Zaff H) = dom G := by
    ext ξ
    refine ⟨fun h => (hbounds ξ).1.trans_lt h, fun h => ?_⟩
    have hfin : (γ : ℝ≥0∞) * (1 + G ξ) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, h⟩)
    exact ((hbounds ξ).2.trans (hHG ξ)).trans_lt hfin
  have husc : UpperSemicontinuous (Zaff H) := Zaff_upperSemicontinuous hHusc
  refine ⟨hbounds, hdom, fun t ht0 ht1 ξ => Zaff_smul_le hHrad ht0 ht1 ξ, fun ξ hξ => ?_, husc,
    husc.measurable⟩
  have hξ' : ξ ∈ interior (dom (Zaff H)) := by rwa [hdom, hGo.interior_eq]
  exact citedZaffLocLip H ξ hξ'

/-! ### Jensen's inequality on arbitrary bounded open sets -/

/-- A function vanishing on `F` has zero derivative at every density point of `F` where it is
differentiable. -/
theorem fderiv_eq_zero_of_density_one {f : Sp N → ℝ} {F : Set (Sp N)} {y : Sp N}
    (hf0 : ∀ z ∈ F, f z = 0) (hy : y ∈ F) (hd : DifferentiableAt ℝ f y)
    (hdens : Tendsto (fun r => volume (F ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1)) :
    fderiv ℝ f y = 0 := by
  by_contra hD
  set D := fderiv ℝ f y
  obtain ⟨w, hw⟩ : ∃ w, D w ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousLinearMap.ext h)
  set c := |D w|
  have hc : 0 < c := abs_pos.2 hw
  set δ := c / (2 * (‖D‖ + 1))
  have hδ : 0 < δ := by positivity
  have hlow : ∀ w' ∈ ball w δ, c / 2 ≤ |D w'| := by
    intro w' hw'
    have h1 : |D w' - D w| ≤ ‖D‖ * ‖w' - w‖ := by
      rw [← map_sub, ← Real.norm_eq_abs]
      exact D.le_opNorm _
    have h2 : ‖w' - w‖ < δ := by rwa [← dist_eq_norm, ← mem_ball]
    have h3 : ‖D‖ * δ ≤ c / 2 := by
      have : ‖D‖ * δ = c / 2 * (‖D‖ / (‖D‖ + 1)) := by
        simp only [δ]
        field_simp
      rw [this]
      exact mul_le_of_le_one_right (by positivity)
        ((div_le_one (by positivity)).2 (by linarith))
    have h4 : ‖D‖ * ‖w' - w‖ ≤ ‖D‖ * δ := mul_le_mul_of_nonneg_left h2.le (norm_nonneg _)
    have h5 := abs_sub_abs_le_abs_sub (D w) (D w')
    rw [abs_sub_comm] at h5
    linarith
  set ε := c / (4 * (‖w‖ + δ))
  have hε : 0 < ε := by positivity
  have ho := hd.hasFDerivAt.isLittleO.def hε
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.1 ho
  have hne := Measure.eventually_nonempty_inter_smul_of_density_one volume F y hdens (ball w δ)
    measurableSet_ball (measure_ball_pos volume w hδ).ne'
  obtain ⟨r, ⟨z, hzF, hz⟩, hr⟩ := (hne.and (Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / (‖w‖ + δ) by
    positivity))).exists
  rw [singleton_add] at hz
  obtain ⟨_, ⟨w', hw', rfl⟩, rfl⟩ := hz
  have hw'n : ‖w'‖ ≤ ‖w‖ + δ := by
    have := norm_le_norm_add_norm_sub' w' w
    rw [mem_ball, dist_eq_norm] at hw'
    linarith
  have hdist : dist (y + r • w') y < ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
    calc r * ‖w'‖ ≤ r * (‖w‖ + δ) := mul_le_mul_of_nonneg_left hw'n hr.1.le
      _ < ρ / (‖w‖ + δ) * (‖w‖ + δ) := by gcongr; exact hr.2
      _ = ρ := div_mul_cancel₀ _ (by positivity)
  have key := hρball hdist
  simp only at hzF
  rw [hf0 _ hzF, hf0 _ hy, sub_self, zero_sub, norm_neg, add_sub_cancel_left, map_smul,
    norm_smul, norm_smul, Real.norm_of_nonneg hr.1.le, Real.norm_eq_abs] at key
  have hk := hlow w' hw'
  have : r * (c / 2) ≤ r * (ε * (‖w‖ + δ)) := by
    calc r * (c / 2) ≤ r * |D w'| := mul_le_mul_of_nonneg_left hk hr.1.le
      _ ≤ ε * (r * ‖w'‖) := key
      _ ≤ ε * (r * (‖w‖ + δ)) := by have := hr.1.le; gcongr
      _ = r * (ε * (‖w‖ + δ)) := by ring
  have hε' : ε * (‖w‖ + δ) = c / 4 := by
    simp only [ε]
    field_simp
  rw [hε'] at this
  nlinarith [hr.1]

/-- A Lipschitz function vanishing on a measurable set `F` is differentiable with zero
derivative at almost every point of `F`. -/
theorem ae_fderiv_eq_zero_of_eq_zero_on {f : Sp N → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {F : Set (Sp N)} (hF : MeasurableSet F)
    (hf0 : ∀ z ∈ F, f z = 0) :
    ∀ᵐ y ∂(volume.restrict F), DifferentiableAt ℝ f y ∧ fderiv ℝ f y = 0 := by
  filter_upwards [ae_restrict_mem hF, Besicovitch.ae_tendsto_measure_inter_div volume F,
    ae_restrict_of_ae hf.ae_differentiableAt] with y hyF hdens hdiff
  exact ⟨hdiff, fderiv_eq_zero_of_density_one hf0 hyF hdiff hdens⟩

/-- **`∫_U ∇φ = 0`** for `φ ∈ Aff₀(U)` and `U` open and bounded, without assuming
`|∂U| = 0` (compare `sum_volume_smul_eq_zero`): on `∂U`, where `φ = 0`, the derivative of
`φ` vanishes a.e. (`ae_fderiv_eq_zero_of_eq_zero_on`). -/
theorem sum_volume_smul_eq_zero_of_isOpen {U : Set (Sp N)} (hUb : Bornology.IsBounded U)
    (hUo : IsOpen U) {φ : Sp N → Tgt m} {K : ℝ≥0} (hK : LipschitzWith K φ)
    (hφ0 : ∀ y ∉ U, φ y = 0) {n : ℕ} {V : Fin n → Set (Sp N)} {ζ : Fin n → Mat m N}
    (hVo : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVc : volume (U \ ⋃ i, V i) = 0) (hφV : ∀ i, ∀ y ∈ V i, HasFDerivAt φ (ζ i) y) :
    ∑ i, (volume (V i)).toReal • ζ i = 0 := by
  classical
  obtain ⟨R, hR⟩ := hUb.closure.exists_norm_le
  refine ContinuousLinearMap.ext fun v => funext fun k => ?_
  simp only [_root_.sum_apply, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, _root_.zero_apply, Pi.zero_apply]
  set f : Sp N → ℝ := fun y => φ y k
  have hf : LipschitzWith K f :=
    LipschitzWith.of_dist_le_mul fun x y => (dist_le_pi_dist (φ x) (φ y) k).trans
      (hK.dist_le_mul x y)
  -- `f` vanishes near every point off `closure U`
  have F0 : ∀ y, y ∉ closure U → f =ᶠ[𝓝 y] fun _ => 0 := by
    intro y hy
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
    exact congrFun (hφ0 z fun h => hz (subset_closure h)) k
  -- integration by parts against the plateau function
  have hIBP := hf.integral_lineDeriv_mul_eq (μ := volume) (lipschitzWith_plateau R)
    (hasCompactSupport_plateau R) v
  have hR' : (fun y => lineDeriv ℝ (plateau R) y (-v) * f y) = fun _ => 0 := by
    funext y
    by_cases hy : y ∈ closure U
    · rw [lineDeriv_eq_zero_of_eventuallyEq_const (plateau_eventuallyEq_one (hR y hy)), zero_mul]
    · rw [(F0 y hy).eq_of_nhds, mul_zero]
  have hL' : (fun y => lineDeriv ℝ f y v * plateau R y) = fun y => lineDeriv ℝ f y v := by
    funext y
    by_cases hy : y ∈ closure U
    · rw [(plateau_eventuallyEq_one (hR y hy)).eq_of_nhds, mul_one]
    · rw [lineDeriv_eq_zero_of_eventuallyEq_const (F0 y hy), zero_mul]
  rw [hR', hL', integral_zero] at hIBP
  -- the line derivative is a.e. the simple function `∑ᵢ 1_{Vᵢ} ζᵢ(v)ₖ`
  set s : Sp N → ℝ := fun y => ∑ i, (V i).indicator (fun _ => ζ i v k) y
  have hs_on : ∀ i, ∀ y ∈ V i, s y = ζ i v k := by
    intro i y hy
    simp only [s]
    rw [Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem
      (fun hj => (hVd hji).le_bot ⟨hj, hy⟩) _) (by simp), indicator_of_mem hy]
  have hfr0 : ∀ z ∈ frontier U, f z = 0 := fun z hz => congrFun (hφ0 z fun hzU =>
    (hUo.inter_frontier_eq.subset ⟨hzU, hz⟩ : z ∈ (∅ : Set (Sp N)))) k
  have hfr := (ae_restrict_iff' isClosed_frontier.measurableSet).1
    (ae_fderiv_eq_zero_of_eq_zero_on hf isClosed_frontier.measurableSet hfr0)
  have hae : (fun y => lineDeriv ℝ f y v) =ᵐ[volume] s := by
    refine measure_mono_null (t := (U \ ⋃ i, V i) ∪ {y | ¬(y ∈ frontier U →
      DifferentiableAt ℝ f y ∧ fderiv ℝ f y = 0)}) ?_ (measure_union_null hVc (ae_iff.1 hfr))
    intro y hy
    change ¬ (lineDeriv ℝ f y v = s y) at hy
    by_cases hyV : ∃ i, y ∈ V i
    · obtain ⟨i, hi⟩ := hyV
      exfalso; apply hy
      have hd : HasFDerivAt f ((ContinuousLinearMap.proj k).comp (ζ i)) y :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).hasFDerivAt.comp y
          (hφV i y hi)
      rw [(hd.hasLineDerivAt v).lineDeriv, hs_on i y hi]
      rfl
    · push Not at hyV
      have hs0 : s y = 0 := Finset.sum_eq_zero fun i _ => indicator_of_notMem (hyV i) _
      by_cases hyU : y ∈ U
      · exact Or.inl ⟨hyU, by simpa using hyV⟩
      · by_cases hyc : y ∈ closure U
        · refine Or.inr fun hP => hy ?_
          have hyf : y ∈ frontier U := ⟨hyc, by rwa [hUo.interior_eq]⟩
          obtain ⟨hd, h0⟩ := hP hyf
          rw [hd.hasFDerivAt.hasLineDerivAt v |>.lineDeriv, h0, hs0]
          rfl
        · exfalso; apply hy
          rw [lineDeriv_eq_zero_of_eventuallyEq_const (F0 y hyc), hs0]
  have hint : ∫ y, s y = ∑ i, (volume (V i)).toReal * ζ i v k := by
    simp only [s]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator_const _ (hVo i).measurableSet, measureReal_def, smul_eq_mul]
    · intro i _
      refine (integrable_indicator_iff (hVo i).measurableSet).2 ?_
      exact integrableOn_const ((measure_mono (hVU i)).trans_lt hUb.measure_lt_top).ne
  rw [← hint, ← integral_congr_ae hae, hIBP]

/-- Jensen's inequality `|U| f(ξ) ≤ ∫_U f(ξ + ∇φ)` for `f` convex, `φ ∈ Aff₀(U)` and `U` open
and bounded, without assuming `|∂U| = 0` (compare `ConvexENN.volume_mul_le_lintegral`). -/
theorem ConvexENN.volume_mul_le_lintegral_of_isOpen {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f)
    {U : Set (Sp N)} (hUb : Bornology.IsBounded U) (hUo : IsOpen U)
    (hU0 : volume U ≠ 0) {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 U) (ξ : Mat m N) :
    volume U * f ξ ≤ ∫⁻ y in U, f (ξ + fderiv ℝ φ y) := by
  classical
  obtain ⟨⟨K, hK⟩, h0, -, n, V, ζ, hVo, hVU, hVd, -, hVc, hφV⟩ := hφ
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hVt : ∀ i, volume (V i) ≠ ⊤ := fun i => ((measure_mono (hVU i)).trans_lt
    hUb.measure_lt_top).ne
  have hUV : U =ᵐ[volume] ⋃ i, V i :=
    ae_eq_set.2 ⟨hVc, by rw [sdiff_eq_empty.2 (iUnion_subset hVU), measure_empty]⟩
  -- (A) the integral on the pieces
  have hA : ∫⁻ y in U, f (ξ + fderiv ℝ φ y) = ∑ i, volume (V i) * f (ξ + ζ i) := by
    rw [setLIntegral_congr hUV, lintegral_iUnion (fun i => (hVo i).measurableSet) hVd,
      tsum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet
      (g := fun _ => f (ξ + ζ i)) fun y hy => by rw [(hφV i y hy).fderiv],
      setLIntegral_const, mul_comm]
  -- (B) `|U| = ∑ |Vᵢ|`
  have hB : volume U = ∑ i, volume (V i) := by
    rw [measure_congr hUV, measure_iUnion (fun i j hij => hVd hij)
      (fun i => (hVo i).measurableSet), tsum_fintype]
  have hzero := sum_volume_smul_eq_zero_of_isOpen hUb hUo hK h0 hVo hVU hVd hVc hφV
  -- (C) Jensen with weights `|Vᵢ| / |U|`
  set T : ℝ≥0 := (volume U).toNNReal
  have hT : (T : ℝ≥0∞) = volume U := ENNReal.coe_toNNReal hUt
  have hT0 : T ≠ 0 := by
    intro h; apply hU0; rw [← hT, h, ENNReal.coe_zero]
  set w : Fin n → ℝ≥0 := fun i => (volume (V i)).toNNReal / T
  have hTsum : T = ∑ i, (volume (V i)).toNNReal := by
    simp only [T, hB]; exact ENNReal.toNNReal_sum fun i _ => hVt i
  have hw : ∑ i, w i = 1 := by
    simp only [w]; rw [← Finset.sum_div, ← hTsum, div_self hT0]
  have hpts : ∑ i, (w i : ℝ) • (ξ + ζ i) = ξ := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    rw [show (∑ i, (w i : ℝ)) = 1 by exact_mod_cast hw, one_smul, add_eq_left]
    have : ∑ i, (w i : ℝ) • ζ i = (T : ℝ)⁻¹ • ∑ i, (volume (V i)).toReal • ζ i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]; congr 1
      simp only [w, NNReal.coe_div, ENNReal.coe_toNNReal_eq_toReal]; ring
    rw [this, hzero, smul_zero]
  have hJ := hf.map_sum_le Finset.univ w (fun i => ξ + ζ i) hw
  rw [hpts] at hJ
  rw [hA, ← hT]
  calc (T : ℝ≥0∞) * f ξ ≤ T * ∑ i, (w i : ℝ≥0∞) * f (ξ + ζ i) := by gcongr
    _ = ∑ i, volume (V i) * f (ξ + ζ i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← ENNReal.coe_mul, mul_div_cancel₀ _ hT0, ENNReal.coe_toNNReal (hVt i)]

/-- `|U| f(ξ) ≤ 𝒴 f(U,ξ)` for `f` convex and every bounded open `U`. -/
theorem ConvexENN.volume_mul_le_Yt_of_isOpen {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f)
    {U : Set (Sp N)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (ξ : Mat m N) :
    volume U * f ξ ≤ Yt (fun _ => f) U ξ := by
  by_cases hU0 : volume U = 0
  · rw [hU0, zero_mul]
    exact zero_le
  exact le_iInf₂ fun _ hφ => hf.volume_mul_le_lintegral_of_isOpen hUb hUo hU0 hφ ξ

/-! ### Lower semicontinuity of `G` -/

/-- A convex `G` with open effective domain containing `0` and blowing up radially at every point
of `∂(dom G)` is lower semicontinuous. -/
theorem ConvexENN.lowerSemicontinuous_of_isOpen_dom {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGo : IsOpen (dom G)) (hG0 : (0 : Mat m N) ∈ dom G)
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤)) :
    LowerSemicontinuous G := by
  have hcont : ∀ ξ ∈ dom G, ContinuousAt G ξ := fun ξ hξ =>
    (hG.continuousOn_interior_dom.continuousAt
      (isOpen_interior.mem_nhds (by rwa [hGo.interior_eq])))
  intro ξ₀ y hy
  by_cases hd : ξ₀ ∈ dom G
  · exact (hcont ξ₀ hd).eventually (lt_mem_nhds hy)
  have hytop : y < ⊤ := hy.trans_le le_top
  by_cases hc : ξ₀ ∈ closure (dom G)
  · have hfr : ξ₀ ∈ frontier (dom G) := ⟨hc, by rwa [hGo.interior_eq]⟩
    -- `G ≤ M` on a ball around `0`
    set M := G 0 + 1
    have hM : M ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hG0.ne, ENNReal.one_ne_top⟩
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff.1 ((hcont 0 hG0).eventually
      (gt_mem_nhds (ENNReal.lt_add_right hG0.ne one_ne_zero)))
    obtain ⟨t, htG, ht⟩ := ((hGsing ξ₀ hfr).eventually (lt_mem_nhds
      (ENNReal.add_lt_top.2 ⟨hytop, hM.lt_top⟩))).and
      (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)) |>.exists
    have h1t : 0 < 1 - t := by linarith [ht.2]
    filter_upwards [Metric.ball_mem_nhds ξ₀ (show 0 < ρ₀ * (1 - t) / t by
      have := ht.1; positivity)] with ζ hζ
    set w : Mat m N := (t / (1 - t)) • (ξ₀ - ζ)
    have hw : dist w 0 < ρ₀ := by
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by have := ht.1; positivity)]
      rw [mem_ball, dist_comm, dist_eq_norm] at hζ
      calc t / (1 - t) * ‖ξ₀ - ζ‖ < t / (1 - t) * (ρ₀ * (1 - t) / t) := by
            gcongr
            exact div_pos ht.1 h1t
        _ = ρ₀ := by have := ht.1.ne'; field_simp
    have hGw : G w ≤ M := (hball hw).le
    set τ : ℝ≥0 := ⟨t, ht.1.le⟩
    have hτ1 : τ ≤ 1 := by
      change (t : ℝ) ≤ 1
      exact ht.2.le
    have hconv := hG ζ w τ hτ1
    have hτc : ((1 - τ : ℝ≥0) : ℝ) = 1 - t := by
      rw [NNReal.coe_sub hτ1]
      rfl
    have hpt : (τ : ℝ) • ζ + ((1 - τ : ℝ≥0) : ℝ) • w = t • ξ₀ := by
      rw [hτc, show (τ : ℝ) = t from rfl, smul_smul, mul_div_cancel₀ _ h1t.ne', smul_sub]
      abel
    rw [hpt] at hconv
    have hle : G (t • ξ₀) ≤ G ζ + M := by
      calc G (t • ξ₀) ≤ τ * G ζ + (1 - τ : ℝ≥0) * G w := hconv
        _ ≤ 1 * G ζ + 1 * M := by
          gcongr
          · exact_mod_cast hτ1
          · exact_mod_cast tsub_le_self
        _ = G ζ + M := by rw [one_mul, one_mul]
    exact (ENNReal.add_lt_add_iff_right hM).1 (htG.trans_le hle)
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with ζ hζ
    have : G ζ = ⊤ := by
      by_contra h
      exact hζ (subset_closure (lt_top_iff_ne_top.2 h))
    rw [this]
    exact hytop

/-- The radial singularity on `∂(dom G)` extends to every `ξ ∉ dom G` when `dom G` is open
(off `closure (dom G)`, `G(tξ) = ∞` for `t` close to `1`). -/
theorem tendsto_top_of_not_mem_dom {G : Mat m N → ℝ≥0∞} (hGo : IsOpen (dom G))
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    {ξ : Mat m N} (hξ : ξ ∉ dom G) : Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤) := by
  by_cases hc : ξ ∈ closure (dom G)
  · exact hGsing ξ ⟨hc, by rwa [hGo.interior_eq]⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_smul_nhdsLT_one ξ).eventually
    (isClosed_closure.isOpen_compl.mem_nhds hc)] with t ht
  by_contra h
  exact ht (subset_closure (lt_top_iff_ne_top.2 (Ne.symm h)))

/-! ### Theorem `th:product` -/

/-- The product integrand `W(x,ξ) = a(x) H(ξ)` of Theorem `th:product`. -/
noncomputable def prodW (a : Sp N → ℝ) (H : Mat m N → ℝ≥0∞) : Sp N → Mat m N → ℝ≥0∞ :=
  fun x ξ => ENNReal.ofReal (a x) * H ξ

/-- **Theorem `th:product` (i).** For `a` lower semicontinuous with `1 ≤ a ≤ A` and `H` upper
semicontinuous: for a.e. `x`, `𝒴_loc W(x,·) = 𝒵_aff W(x,·) = a(x) 𝒵_aff H`, and `𝒴_loc W(x,·)`
is upper semicontinuous. -/
theorem th_product_i [NeZero N] {a : Sp N → ℝ} {A : ℝ} {H : Mat m N → ℝ≥0∞}
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (halsc : LowerSemicontinuous a)
    (hHusc : UpperSemicontinuous H) :
    ∀ᵐ x, Ytloc (prodW a H) x = Zaff (prodW a H x) ∧
      (∀ ξ, Zaff (prodW a H x) ξ = ENNReal.ofReal (a x) * Zaff H ξ) ∧
      UpperSemicontinuous (Ytloc (prodW a H) x) := by
  have hsum : (fun x ξ => ∑ i : Fin 1, ENNReal.ofReal ((fun _ => a) i x) *
      (fun _ => H) i ξ) = prodW a H := by
    funext x ξ
    simp [prodW]
  have h := lem_sumosc (ν := 1) (a := fun _ => a) (H := fun _ => H) one_pos
    (fun _ x => ha x) (fun _ => halsc) (fun _ => hHusc)
  rw [hsum] at h
  filter_upwards [h] with x hx
  have e : (fun ξ => ∑ _i : Fin 1, ENNReal.ofReal (a x) * H ξ) = prodW a H x := by
    funext ξ
    simp [prodW]
  rw [e] at hx
  refine ⟨hx.1, fun ξ => ?_, hx.2.2⟩
  have h0 : ENNReal.ofReal (a x) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith [(ha x).1]
  exact congrFun (Zaff_const_mul H h0 ENNReal.ofReal_ne_top) ξ

/-- `W = aH` has the set growth (H3) with `α = 1` and `β = A γ`. -/
theorem prodW_setGrowth {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} {a : Sp N → ℝ} {A : ℝ}
    (hG : ConvexENN G) (hGH : ∀ ξ, G ξ ≤ H ξ) (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (ξ : Mat m N) (U : Set (Sp N)) (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ((1 : ℝ≥0) : ℝ≥0∞) * volume U * G ξ ≤ Yt (prodW a H) U ξ ∧
      Yt (prodW a H) U ξ ≤ ((A.toNNReal * γ : ℝ≥0) : ℝ≥0∞) * volume U * (1 + G ξ) := by
  constructor
  · rw [ENNReal.coe_one, one_mul]
    refine (hG.volume_mul_le_Yt_of_isOpen hUo hUb ξ).trans (Yt_mono (fun y ζ => ?_) U ξ)
    calc G ζ ≤ H ζ := hGH ζ
      _ = 1 * H ζ := (one_mul _).symm
      _ ≤ ENNReal.ofReal (a y) * H ζ := by
        gcongr
        exact ENNReal.one_le_ofReal.2 (ha y).1
  · refine (iInf₂_le (0 : Sp N → Tgt m) (zero_mem_Aff0 hUo)).trans ?_
    have h0 : ∀ y, fderiv ℝ (0 : Sp N → Tgt m) y = 0 := fun y => fderiv_const_apply 0
    simp only [h0, add_zero]
    calc ∫⁻ y in U, prodW a H y ξ ≤ ∫⁻ _ in U, ((A.toNNReal * γ : ℝ≥0) : ℝ≥0∞) * (1 + G ξ) := by
          refine lintegral_mono fun y => ?_
          simp only [prodW, ENNReal.coe_mul]
          rw [mul_assoc]
          gcongr
          · rw [ENNReal.ofReal]
            exact_mod_cast Real.toNNReal_le_toNNReal (ha y).2
          · exact hHG ξ
      _ = ((A.toNNReal * γ : ℝ≥0) : ℝ≥0∞) * volume U * (1 + G ξ) := by
          rw [setLIntegral_const]
          ring

/-- `W = aH` is radially nonincreasing, hence `𝒴_loc W` is ru-usc (with any constant). -/
theorem prodW_Ytloc_ruusc {H : Mat m N → ℝ≥0∞} {a : Sp N → ℝ}
    (hHrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ) (c : ℝ≥0) :
    RUUSCWith c (Ytloc (prodW a H)) := by
  refine RUUSCWith.Ytloc fun η _ => ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with t ht x ξ _
  calc prodW a H x (t • ξ) ≤ prodW a H x ξ := by
        simp only [prodW]
        gcongr
        exact hHrad t ht.1.le ht.2.le ξ
    _ ≤ prodW a H x ξ + η * (c + prodW a H x ξ) := le_self_add

/-- **Theorem `th:product` (ii)**, all hypotheses of Theorem `main-Ggrowth` except (H4) and the
exact measurability (H6) of `𝒴_loc W`:
(H1) `G` convex, lower semicontinuous, `0 ∈ int(dom G)`; `G`, `W` Borel measurable;
(H2) `W` periodic; (H3) with `α = 1`, `β = A γ`; (H5) `𝒴_loc W` ru-usc; (H6) up to modification
on a null set of `x`; (H7); and (H8), the latter under the measurability of `𝒴_loc W`
(hypothesis `hYm`, used by `prop_Z3suff`).

Not proved: the literal (H6) `Measurable (uncurry (𝒴_loc W))` (only its a.e. form). The
hypothesis `γ ≥ 1` of the paper is replaced by `0 < γ`. -/
theorem th_product_ii [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} {a : Sp N → ℝ} {A : ℝ}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) (hG0 : (0 : Mat m N) ∈ dom G)
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hγ : 0 < γ) (hHusc : UpperSemicontinuous H) (hGH : ∀ ξ, G ξ ≤ H ξ)
    (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (hHrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ)
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (halsc : LowerSemicontinuous a)
    (haper : ∀ (z : Fin N → ℤ) x, a (x + fun i => (z i : ℝ)) = a x) :
    (LowerSemicontinuous G ∧ (0 : Mat m N) ∈ interior (dom G) ∧ Measurable G ∧
      Measurable (uncurry (prodW a H))) ∧
    IsPeriodic (prodW a H) ∧
    (∃ α β : ℝ≥0, 0 < α ∧ 0 < β ∧ ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      (α : ℝ≥0∞) * volume U * G ξ ≤ Yt (prodW a H) U ξ ∧
        Yt (prodW a H) U ξ ≤ β * volume U * (1 + G ξ)) ∧
    RUUSC (Ytloc (prodW a H)) ∧
    (∃ W' : Sp N → Mat m N → ℝ≥0∞, Measurable (uncurry W') ∧
      ∀ᵐ x, ∀ ξ, Ytloc (prodW a H) x ξ = W' x ξ) ∧
    (∀ᵐ x, ∀ ξ, Ytloc (prodW a H) x ξ ≤ prodW a H x ξ) ∧
    (Measurable (uncurry (Ytloc (prodW a H))) →
      ∀ ξ, Zaff (Haff (Ytloc (prodW a H))) ξ ≤
        radial (Hp (ENNReal.ofReal p) (Ytloc (prodW a H))) ξ) := by
  have hGlsc := hG.lowerSemicontinuous_of_isOpen_dom hGo hG0 hGsing
  have hA : 1 ≤ A := (ha 0).1.trans (ha 0).2
  have hper : IsPeriodic (prodW a H) := fun z x ξ => by simp only [prodW, haper z x]
  have hset := prodW_setGrowth (γ := γ) hG hGH hHG ha
  have hi := th_product_i ha halsc hHusc
  have hprod := (lem_product hG hGo hHusc hGH hHG hHrad)
  refine ⟨⟨hGlsc, by rwa [hGo.interior_eq], hGlsc.measurable,
    (ENNReal.measurable_ofReal.comp (halsc.measurable.comp measurable_fst)).mul
      (hHusc.measurable.comp measurable_snd)⟩, hper,
    ⟨1, A.toNNReal * γ, one_pos, mul_pos (Real.toNNReal_pos.2 (by linarith)) hγ, hset⟩,
    ⟨1, one_pos, prodW_Ytloc_ruusc hHrad 1⟩, ?_, ?_, fun hYm ξ => ?_⟩
  · refine ⟨fun x ξ => ENNReal.ofReal (a x) * Zaff H ξ,
      (ENNReal.measurable_ofReal.comp (halsc.measurable.comp measurable_fst)).mul
        (hprod.2.2.2.2.2.comp measurable_snd), ?_⟩
    filter_upwards [hi] with x hx ξ
    rw [hx.1, hx.2.1]
  · filter_upwards [hi] with x hx ξ
    rw [hx.1, hx.2.1]
    simp only [prodW]
    gcongr
    exact (hprod.1 ξ).2
  · exact prop_Z3suff (p := p) hG hGlsc hGo (fun ξ hξ => tendsto_top_of_not_mem_dom hGo hGsing hξ)
      one_pos hper hset hYm (hi.mono fun x hx => hx.2.2) ξ

/-- `ℋ_p` only depends on the a.e. class of the integrand in `x`. -/
theorem Hp_congr_ae {p : ℝ≥0∞} {L L' : Sp N → Mat m N → ℝ≥0∞}
    (h : ∀ᵐ x, ∀ ξ, L x ξ = L' x ξ) : Hp p L = Hp p L' := by
  funext ξ
  simp only [Hp, Ytp]
  congr 1
  funext k
  congr 1
  refine iInf_congr fun φ => iInf_congr fun _ => lintegral_congr_ae ?_
  exact ae_restrict_of_ae (h.mono fun x hx => hx _)

/-- **Theorem `th:product` (iii).** If moreover `c₀ |ξ|ᵖ ≤ G(ξ)`, then (H4) holds and, under the
measurability of `𝒴_loc W` (H6, assumed: only its a.e. form is proved in `th_product_ii`),
`∫_Ω a(x/ε) H(∇u)` Γ-converges to `∫_Ω \widehat{ℋ(a 𝒵_aff H)}(∇u)`. -/
theorem th_product_iii [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : (N : ℝ) < p)
    {Ω : Set (Sp N)} (hΩ : StandingDomain Ω)
    {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} {a : Sp N → ℝ} {A : ℝ}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) (hG0 : (0 : Mat m N) ∈ dom G)
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hγ : 0 < γ) (hHusc : UpperSemicontinuous H) (hGH : ∀ ξ, G ξ ≤ H ξ)
    (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (hHrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ)
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (halsc : LowerSemicontinuous a)
    (haper : ∀ (z : Fin N → ℤ) x, a (x + fun i => (z i : ℝ)) = a x)
    {c₀ : ℝ≥0} (hc₀ : 0 < c₀) (hcoer : ∀ ξ, ENNReal.ofReal (c₀ * ‖ξ‖ ^ p) ≤ G ξ)
    (hYm : Measurable (uncurry (Ytloc (prodW a H)))) :
    IsCoercive p c₀ (Ytloc (prodW a H)) ∧
      Whom p (prodW a H) =
        radial (Hp (ENNReal.ofReal p) (fun x ξ => ENNReal.ofReal (a x) * Zaff H ξ)) ∧
      GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun (prodW a H))
        (intHom (Whom p (prodW a H))) := by
  obtain ⟨⟨hGlsc, hG0i, hGm, hWm⟩, hper, hset, hru, -, hle, hZ8⟩ :=
    th_product_ii (p := p) hG hGo hG0 hGsing hγ hHusc hGH hHG hHrad ha halsc haper
  obtain ⟨α, β, hα, hβ, hset'⟩ := hset
  have hgr := HasGGrowth.Ytloc (prodW_setGrowth (γ := γ) hG hGH hHG ha)
  have hcoerW : IsCoercive p c₀ (Ytloc (prodW a H)) := fun x ξ => by
    refine (hcoer ξ).trans ?_
    simpa using (hgr x ξ).1
  have hW : Hypotheses p G (prodW a H) :=
    { measurable_G := hGm
      measurable_W := hWm
      convex := hG
      lsc := hGlsc
      zero_mem_interior := hG0i
      periodic := hper
      setGrowth := ⟨α, β, hα, hβ, hset'⟩
      coercive := ⟨c₀, hc₀, hcoerW⟩
      ruusc := hru
      measurable_Ytloc := hYm
      Ytloc_le := hle
      Zaff_Haff_le := hZ8 hYm }
  refine ⟨hcoerW, ?_, main_Ggrowth_final_unconditional p hp hΩ hW⟩
  have hi := th_product_i ha halsc hHusc
  simp only [Whom]
  rw [Hp_congr_ae (hi.mono fun x hx ξ => by rw [hx.1, hx.2.1])]

end Homogenization
