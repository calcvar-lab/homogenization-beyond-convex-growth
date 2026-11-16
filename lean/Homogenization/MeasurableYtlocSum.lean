import Homogenization.MeasurableYtloc
import Homogenization.Scaling

/-!
# Exact measurability (H6) of `𝒴_loc W` for `W = ∑ₖ aₖ(x) Hₖ(ξ)`

`measurable_Ytloc_sumW`: for `aₖ` measurable with values in `[η, Λ]` (`η > 0`) and `Hₖ` upper
semicontinuous, `(x,ξ) ↦ 𝒴_loc W(x,ξ)` is jointly Borel measurable, without modification on a
null set of `x`. No finiteness of `Hₖ` is required, unlike `prodW_measurable_Ytloc`, whose proof
reduces the `limsup` to rational radii and fails when `W(·,ξ) ≡ ∞` while `𝒴 W(Q_ρ(x),ξ) < ∞`
(e.g. `W_v` at matrices with `v(ξ) = 0`).

Proof:
* `cellAvg_eq_iInf_unit`: after translation and dilation, the normalized cell energy is an
  infimum over `φ ∈ Aff₀(Q_1)` of `∑ᵢ ∑ₖ (∫_{Vᵢ} aₖ(ρw + x) dw) Hₖ(ξ + ζᵢ)`, where the
  coefficients are continuous in `(ρ, x)` for `ρ > 0` (`continuous_setLIntegral_comp_smul_add`,
  dominated convergence, `|∂Vᵢ| = 0`). Hence joint upper semicontinuity in `(ρ, x, ξ)`
  (`upperSemicontinuous_cellAvg_sumW`).
* `measurable_iSup_Ioo_of_usc`: the supremum over `ρ ∈ ]0,δ[` of a function jointly upper
  semicontinuous on `[r₀, r₁] × X` is measurable (projection of closed sets along a compact
  factor).
* `Ytloc_eq_iInf_iSup`: `𝒴_loc W = inf_n sup_{ρ ∈ ]0,1/(n+1)[}` of the normalized cell energies.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {m N : ℕ}
/-- The normalized cell energy on `Q_ρ(x)` as an affine problem on the unit cell:
`𝒴 W(Q_ρ(x),ξ)/|Q_ρ(x)| = inf_{φ ∈ Aff₀(Q_1)} ∫_{Q_1} W(ρw + x, ξ + ∇φ(w)) dw`. -/
theorem cellAvg_eq_iInf_unit (W : Sp N → Mat m N → ℝ≥0∞) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N)
    (ξ : Mat m N) :
    cellAvg W ρ x ξ = ⨅ φ ∈ (Aff0 (cube 1 (0 : Sp N)) : Set (Sp N → Tgt m)),
      ∫⁻ w in cube 1 0, W (ρ • w + x) (ξ + fderiv ℝ φ w) := by
  have hε : 0 < ρ⁻¹ := inv_pos.2 hρ
  have h := iInf_rescale (fun y => W (y + x)) hε (isOpen_cube 1 (0 : Sp N)).measurableSet ξ
  simp only [inv_inv] at h
  rw [h, preimage_smul_cube hε, smul_zero, one_div, inv_inv,
    ← preimage_add_cube ρ x, Yt_translate, cellAvg, volume_cube, div_eq_mul_inv, mul_comm,
    inv_pow, ← ENNReal.ofReal_pow hρ.le, ENNReal.ofReal_inv_of_pos (pow_pos hρ N)]



/-- Dominated convergence for the dilated and translated indicators `1_V((y - x)/ρ) a(y)`,
at `ρ₀ > 0`, for `V` bounded open with `|∂V| = 0` and `a` measurable bounded above. -/
theorem tendsto_lintegral_indicator_dil {a : Sp N → ℝ} (ham : Measurable a) {A : ℝ}
    (haA : ∀ y, a y ≤ A) {V : Set (Sp N)} (hVo : IsOpen V) (hVb : Bornology.IsBounded V)
    (hVf : volume (frontier V) = 0) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (x₀ : Sp N) :
    Tendsto (fun p : ℝ × Sp N =>
      ∫⁻ y, {y | p.1⁻¹ • (y + -p.2) ∈ V}.indicator (fun y => ENNReal.ofReal (a y)) y)
      (𝓝 (ρ₀, x₀))
      (𝓝 (∫⁻ y, {y | ρ₀⁻¹ • (y + -x₀) ∈ V}.indicator (fun y => ENNReal.ofReal (a y)) y)) := by
  obtain ⟨R, hR⟩ := hVb.subset_closedBall 0
  set R' := max R 0
  have hR' : V ⊆ Metric.closedBall 0 R' := hR.trans (Metric.closedBall_subset_closedBall
    (le_max_left _ _))
  set B : Set (Sp N) := Metric.closedBall 0 (2 * ρ₀ * R' + ‖x₀‖ + 1)
  have hcont : ∀ y : Sp N, ContinuousAt (fun p : ℝ × Sp N => p.1⁻¹ • (y + -p.2)) (ρ₀, x₀) :=
    fun y => (continuous_fst.continuousAt.inv₀ hρ₀.ne').smul
      (continuous_const.add continuous_snd.neg).continuousAt
  have hmeasS : ∀ p : ℝ × Sp N, MeasurableSet {y : Sp N | p.1⁻¹ • (y + -p.2) ∈ V} := fun p =>
    (show Measurable fun y : Sp N => p.1⁻¹ • (y + -p.2) from
      (measurable_const_smul _).comp (measurable_id.add_const _)) hVo.measurableSet
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator fun _ => ENNReal.ofReal A)
    (Eventually.of_forall fun p => (ham.ennreal_ofReal).indicator (hmeasS p)) ?_ ?_ ?_
  · have hU : ∀ᶠ p : ℝ × Sp N in 𝓝 (ρ₀, x₀), p.1 ∈ Ioo (ρ₀ / 2) (2 * ρ₀) ∧
        p.2 ∈ Metric.ball x₀ 1 :=
      (continuous_fst.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))).and
        (continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds x₀ one_pos))
    filter_upwards [hU] with p hp
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ {y : Sp N | p.1⁻¹ • (y + -p.2) ∈ V}
    · have hp1 : 0 < p.1 := by linarith [hp.1.1]
      have hyB : y ∈ B := by
        have h1 := hR' hy
        simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hp1] at h1
        have h1' : ‖y + -p.2‖ ≤ p.1 * R' := by
          rw [inv_mul_le_iff₀ hp1] at h1; exact h1
        have h2 : p.1 * R' ≤ 2 * ρ₀ * R' :=
          mul_le_mul_of_nonneg_right hp.1.2.le (le_max_right _ _)
        have h3 : ‖y‖ ≤ ‖y + -p.2‖ + ‖p.2‖ := by
          calc ‖y‖ = ‖(y + -p.2) + p.2‖ := by rw [neg_add_cancel_right]
            _ ≤ _ := norm_add_le _ _
        have h4 : ‖p.2‖ ≤ ‖x₀‖ + 1 := by
          have := norm_le_norm_add_norm_sub' p.2 x₀
          have h5 := hp.2
          rw [Metric.mem_ball, dist_eq_norm] at h5
          linarith
        simp only [B, Metric.mem_closedBall, dist_zero_right]
        linarith
      rw [indicator_of_mem hy, indicator_of_mem hyB]
      exact ENNReal.ofReal_le_ofReal (haA y)
    · rw [indicator_of_notMem hy]
      exact zero_le
  · rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet, setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  · have hnull : volume {y : Sp N | ρ₀⁻¹ • (y + -x₀) ∈ frontier V} = 0 := by
      change volume ((· + -x₀) ⁻¹' ((ρ₀⁻¹ • ·) ⁻¹' frontier V)) = 0
      rw [measure_preimage_add_right, Measure.addHaar_preimage_smul _ (inv_ne_zero hρ₀.ne'), hVf,
        mul_zero]
    refine measure_mono_null (fun y hy => ?_) hnull
    simp only [Set.mem_ofPred_eq] at hy ⊢
    by_contra hyf
    apply hy
    by_cases hyV : ρ₀⁻¹ • (y + -x₀) ∈ V
    · have hev : ∀ᶠ p : ℝ × Sp N in 𝓝 (ρ₀, x₀), p.1⁻¹ • (y + -p.2) ∈ V :=
        (hcont y).eventually (hVo.mem_nhds hyV)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with p hp
      rw [indicator_of_mem (show y ∈ {y : Sp N | p.1⁻¹ • (y + -p.2) ∈ V} from hp),
        indicator_of_mem (show y ∈ {y : Sp N | ρ₀⁻¹ • (y + -x₀) ∈ V} from hyV)]
    · have hyc : ρ₀⁻¹ • (y + -x₀) ∉ closure V := fun h =>
        hyf ⟨h, by rwa [hVo.interior_eq]⟩
      have hev : ∀ᶠ p : ℝ × Sp N in 𝓝 (ρ₀, x₀), p.1⁻¹ • (y + -p.2) ∉ closure V :=
        (hcont y).eventually (isClosed_closure.isOpen_compl.mem_nhds hyc)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with p hp
      rw [indicator_of_notMem (show y ∉ {y : Sp N | p.1⁻¹ • (y + -p.2) ∈ V} from
          fun h => hp (subset_closure h)),
        indicator_of_notMem (show y ∉ {y : Sp N | ρ₀⁻¹ • (y + -x₀) ∈ V} from hyV)]


/-- `(ρ, x) ↦ ∫_V a(ρw + x) dw` is continuous on `[r₀, r₁] × ℝᴺ` for `r₀ > 0`, `V` bounded open
with `|∂V| = 0` and `a` measurable bounded above. -/
theorem continuous_setLIntegral_comp_smul_add {a : Sp N → ℝ} (ham : Measurable a) {A : ℝ}
    (haA : ∀ y, a y ≤ A) {V : Set (Sp N)} (hVo : IsOpen V) (hVb : Bornology.IsBounded V)
    (hVf : volume (frontier V) = 0) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) :
    Continuous fun q : Icc r₀ r₁ × Sp N =>
      ∫⁻ w in V, ENNReal.ofReal (a ((q.1 : ℝ) • w + q.2)) := by
  have hpos : ∀ q : Icc r₀ r₁ × Sp N, 0 < (q.1 : ℝ) := fun q => lt_of_lt_of_le hr₀ q.1.2.1
  have e : (fun q : Icc r₀ r₁ × Sp N => ∫⁻ w in V, ENNReal.ofReal (a ((q.1 : ℝ) • w + q.2))) =
      fun q => ENNReal.ofReal |((q.1 : ℝ) ^ N)⁻¹| *
        ∫⁻ y, {y | (q.1 : ℝ)⁻¹ • (y + -q.2) ∈ V}.indicator (fun y => ENNReal.ofReal (a y)) y := by
    funext q
    exact setLIntegral_comp_smul_add (fun y => ENNReal.ofReal (a y)) (hpos q) q.2
      hVo.measurableSet
  rw [e, continuous_iff_continuousAt]
  intro q
  have hc : Continuous fun q : Icc r₀ r₁ × Sp N => ENNReal.ofReal |((q.1 : ℝ) ^ N)⁻¹| :=
    ENNReal.continuous_ofReal.comp (continuous_abs.comp
      (((continuous_subtype_val.comp continuous_fst).pow N).inv₀ fun q => (pow_pos (hpos q) N).ne'))
  set F : ℝ × Sp N → ℝ≥0∞ := fun p =>
    ∫⁻ y, {y | p.1⁻¹ • (y + -p.2) ∈ V}.indicator (fun y => ENNReal.ofReal (a y)) y with hF
  set g : Icc r₀ r₁ × Sp N → ℝ × Sp N := fun q => ((q.1 : ℝ), q.2) with hg
  have hgc : Continuous g := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hI : Tendsto (F ∘ g) (𝓝 q) (𝓝 (F (g q))) :=
    (tendsto_lintegral_indicator_dil ham haA hVo hVb hVf (hpos q) q.2).comp (hgc.tendsto q)
  exact ENNReal.Tendsto.mul (hc.tendsto q)
    (Or.inl (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (pow_pos (hpos q) N).ne'))).ne') hI
    (Or.inr ENNReal.ofReal_ne_top)


/-- The sum integrand `∑ₖ aₖ(x) Hₖ(ξ)` of Lemma `lem:sumosc`. -/
noncomputable def sumW {ν : ℕ} (a : Fin ν → Sp N → ℝ) (H : Fin ν → Mat m N → ℝ≥0∞) :
    Sp N → Mat m N → ℝ≥0∞ :=
  fun x ξ => ∑ k, ENNReal.ofReal (a k x) * H k ξ

/-- For `W = ∑ₖ aₖ(x) Hₖ(ξ)` (`aₖ` measurable with values in `[η,Λ]`, `η > 0`, `Hₖ` upper
semicontinuous), the normalized cell energy is jointly upper semicontinuous in
`(ρ, x, ξ) ∈ [r₀, r₁] × ℝᴺ × 𝕄` for `r₀ > 0`: an infimum over `φ ∈ Aff₀(Q_1)` of finite sums
`∑ᵢ ∑ₖ (∫_{Vᵢ} aₖ(ρw + x) dw) Hₖ(ξ + ζᵢ)`. -/
theorem upperSemicontinuous_cellAvg_sumW {ν : ℕ} {a : Fin ν → Sp N → ℝ}
    {H : Fin ν → Mat m N → ℝ≥0∞} {η Λ : ℝ} (hη : 0 < η) (ha : ∀ k x, η ≤ a k x ∧ a k x ≤ Λ)
    (ham : ∀ k, Measurable (a k)) (hH : ∀ k, UpperSemicontinuous (H k)) {r₀ r₁ : ℝ}
    (hr₀ : 0 < r₀) :
    UpperSemicontinuous fun q : Icc r₀ r₁ × (Sp N × Mat m N) =>
      cellAvg (sumW a H) q.1 q.2.1 q.2.2 := by
  have hpos : ∀ q : Icc r₀ r₁ × (Sp N × Mat m N), 0 < (q.1 : ℝ) :=
    fun q => lt_of_lt_of_le hr₀ q.1.2.1
  have e : (fun q : Icc r₀ r₁ × (Sp N × Mat m N) => cellAvg (sumW a H) q.1 q.2.1 q.2.2) =
      fun q => ⨅ φ ∈ (Aff0 (cube 1 (0 : Sp N)) : Set (Sp N → Tgt m)),
        ∫⁻ w in cube 1 0, sumW a H ((q.1 : ℝ) • w + q.2.1) (q.2.2 + fderiv ℝ φ w) := by
    funext q
    exact cellAvg_eq_iInf_unit _ (hpos q) _ _
  rw [e]
  refine upperSemicontinuous_iInf fun φ => upperSemicontinuous_iInf fun hφ => ?_
  obtain ⟨K, n, V, ζ, -, -, hVo, hVU, hVd, hVf, hVc, hφV⟩ := Aff0.data hφ
  have hsplit : (fun q : Icc r₀ r₁ × (Sp N × Mat m N) =>
      ∫⁻ w in cube 1 0, sumW a H ((q.1 : ℝ) • w + q.2.1) (q.2.2 + fderiv ℝ φ w)) =
      fun q => ∑ i, ∑ k, (∫⁻ w in V i, ENNReal.ofReal (a k ((q.1 : ℝ) • w + q.2.1))) *
        H k (q.2.2 + ζ i) := by
    funext q
    rw [lintegral_eq_sum_pieces_fintype hVo hVU hVd hVc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet
      (g := fun w => ∑ k, ENNReal.ofReal (a k ((q.1 : ℝ) • w + q.2.1)) * H k (q.2.2 + ζ i))
      (fun w hw => by simp only [sumW, (hφV i w hw).fderiv])]
    have hmk : ∀ k, Measurable fun w : Sp N => ENNReal.ofReal (a k ((q.1 : ℝ) • w + q.2.1)) :=
      fun k => ((ham k).comp ((measurable_const_smul _).add_const _)).ennreal_ofReal
    rw [lintegral_finsetSum _ fun k _ => (hmk k).mul_const _]
    exact Finset.sum_congr rfl fun k _ => lintegral_mul_const _ (hmk k)
  rw [hsplit]
  refine upperSemicontinuous_sum fun i _ => upperSemicontinuous_sum fun k _ => ?_
  have hVb : Bornology.IsBounded (V i) := (isBounded_cube 1 (0 : Sp N)).subset (hVU i)
  by_cases hV0 : volume (V i) = 0
  · have h0 : ∀ q : Icc r₀ r₁ × (Sp N × Mat m N),
        ∫⁻ w in V i, ENNReal.ofReal (a k ((q.1 : ℝ) • w + q.2.1)) = 0 := fun q => by
      rw [Measure.restrict_eq_zero.2 hV0, lintegral_zero_measure]
    simp only [h0, zero_mul]
    exact upperSemicontinuous_const
  have hfr : volume (frontier (V i)) = 0 := by
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null (hVf i) (volume_frontier_cube 1 (0 : Sp N)))
    by_cases hyQ : y ∈ cube 1 (0 : Sp N)
    · exact Or.inl ⟨hyQ, hy⟩
    · refine Or.inr ⟨closure_mono (hVU i) hy.1, ?_⟩
      rwa [(isOpen_cube 1 0).interior_eq]
  have hcont := continuous_setLIntegral_comp_smul_add (ham k) (fun y => (ha k y).2) (hVo i) hVb hfr
    (r₁ := r₁) hr₀
  have hmul := upperSemicontinuous_mul_of_continuous ((hH k).comp (continuous_add_const (ζ i)))
    hcont (fun q => ?_) (fun q => ?_)
  · exact hmul.comp ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))
  · refine (lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hη).ne' hV0) ?_).ne'
    calc ENNReal.ofReal η * volume (V i) = ∫⁻ _ in V i, ENNReal.ofReal η := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ w in V i, ENNReal.ofReal (a k ((q.1 : ℝ) • w + q.2)) :=
          lintegral_mono fun w => ENNReal.ofReal_le_ofReal (ha k _).1
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Λ))
      (hVb.measure_lt_top (μ := volume)).ne) ?_
    calc ∫⁻ w in V i, ENNReal.ofReal (a k ((q.1 : ℝ) • w + q.2)) ≤ ∫⁻ _ in V i, ENNReal.ofReal Λ :=
          lintegral_mono fun w => ENNReal.ofReal_le_ofReal (ha k _).2
      _ = ENNReal.ofReal Λ * volume (V i) := setLIntegral_const _ _


/-- If `F` is jointly upper semicontinuous on `[r₀, r₁] × X` for every `r₀ > 0`, then
`x ↦ sup_{ρ ∈ ]0,δ[} F(ρ,x)` is Borel measurable: its strict superlevel sets are countable unions
of projections of closed subsets of `[r₀, r₁] × X`, which are closed since `[r₀, r₁]` is
compact. -/
theorem measurable_iSup_Ioo_of_usc {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (F : ℝ → X → ℝ≥0∞)
    (hF : ∀ r₀ r₁ : ℝ, 0 < r₀ → UpperSemicontinuous fun q : Icc r₀ r₁ × X => F q.1 q.2)
    {δ : ℝ} (hδ : 0 < δ) : Measurable fun x => ⨆ ρ ∈ Ioo 0 δ, F ρ x := by
  refine measurable_of_Ioi fun c => ?_
  set C : ℚ → ℕ → Set X := fun r k => Prod.snd ''
    ((fun q : Icc (δ / (k + 2)) (δ - δ / (k + 2)) × X => F q.1 q.2) ⁻¹'
      Ici ((Real.toNNReal r : ℝ≥0∞)))
  have hC : ∀ r k, IsClosed (C r k) := fun r k =>
    isClosedMap_snd_of_compactSpace _
      ((hF _ _ (by positivity)).isClosed_preimage _)
  have e : (fun x => ⨆ ρ ∈ Ioo 0 δ, F ρ x) ⁻¹' Ioi c =
      ⋃ (r : ℚ) (_ : c < (Real.toNNReal r : ℝ≥0∞)), ⋃ k : ℕ, C r k := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_iUnion, C, mem_image, Prod.exists, exists_eq_right,
      mem_Ici]
    constructor
    · intro h
      obtain ⟨ρ, h1⟩ := lt_iSup_iff.1 h
      obtain ⟨hρ, h2⟩ := lt_iSup_iff.1 h1
      obtain ⟨r, -, hcr, hrF⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h2
      obtain ⟨k, hk⟩ := exists_nat_gt (δ / min ρ (δ - ρ))
      have hm : 0 < min ρ (δ - ρ) := lt_min hρ.1 (by linarith [hρ.2])
      have hk2 : δ / (k + 2) ≤ min ρ (δ - ρ) := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hm] at hk
        nlinarith
      refine ⟨r, hcr, k, ⟨ρ, ?_, ?_⟩, hrF.le⟩
      · exact hk2.trans (min_le_left _ _)
      · linarith [hk2.trans (min_le_right _ _)]
    · rintro ⟨r, hcr, k, ⟨ρ, hρI⟩, hF'⟩
      have hd : 0 < δ / (k + 2) := by positivity
      refine lt_of_lt_of_le hcr (hF'.trans ?_)
      exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ Ioo 0 δ) => F ρ x) ρ
        ⟨hd.trans_le hρI.1, by linarith [hρI.2]⟩ le_rfl
  rw [e]
  exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun k => (hC r k).measurableSet


/-- `𝒴_loc W(x,ξ) = inf_n sup_{ρ ∈ ]0, 1/(n+1)[} 𝒴 W(Q_ρ(x),ξ)/|Q_ρ(x)|`. -/
theorem Ytloc_eq_iInf_iSup (W : Sp N → Mat m N → ℝ≥0∞) (x : Sp N) (ξ : Mat m N) :
    Ytloc W x ξ = ⨅ n : ℕ, ⨆ ρ ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), cellAvg W ρ x ξ := by
  have hb : (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ => True) (fun n => Ioo 0 (1 / ((n : ℝ) + 1))) :=
    (nhdsGT_basis (0 : ℝ)).to_hasBasis
      (fun δ hδ => by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        exact ⟨n, trivial, Ioo_subset_Ioo_right hn.le⟩)
      (fun n _ => ⟨1 / ((n : ℝ) + 1), by positivity, subset_rfl⟩)
  change limsup (fun ρ => cellAvg W ρ x ξ) (𝓝[>] 0) = _
  rw [hb.limsup_eq_iInf_iSup]
  exact iInf_congr fun n => iInf_pos trivial

/-- **(H6) for a sum `∑ₖ aₖ(x) Hₖ(ξ)`**: `(x,ξ) ↦ 𝒴_loc W(x,ξ)` is jointly Borel measurable,
without modification on a null set (Lemma `lem:measurability`). -/
theorem measurable_Ytloc_sumW {ν : ℕ} {a : Fin ν → Sp N → ℝ}
    {H : Fin ν → Mat m N → ℝ≥0∞} {η Λ : ℝ} (hη : 0 < η) (ha : ∀ k x, η ≤ a k x ∧ a k x ≤ Λ)
    (ham : ∀ k, Measurable (a k)) (hH : ∀ k, UpperSemicontinuous (H k)) :
    Measurable (uncurry (Ytloc (sumW a H))) := by
  have e : uncurry (Ytloc (sumW a H)) = fun p : Sp N × Mat m N =>
      ⨅ n : ℕ, ⨆ ρ ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), cellAvg (sumW a H) ρ p.1 p.2 := by
    funext p
    exact Ytloc_eq_iInf_iSup _ p.1 p.2
  rw [e]
  have hF : ∀ r₀ r₁ : ℝ, 0 < r₀ → UpperSemicontinuous fun q : Icc r₀ r₁ × (Sp N × Mat m N) =>
      cellAvg (sumW a H) q.1 q.2.1 q.2.2 :=
    fun r₀ r₁ hr₀ => upperSemicontinuous_cellAvg_sumW hη ha ham hH hr₀
  refine Measurable.iInf fun n => ?_
  have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact measurable_iSup_Ioo_of_usc (X := Sp N × Mat m N)
    (fun ρ p => cellAvg (sumW a H) ρ p.1 p.2) hF hn


end Homogenization
