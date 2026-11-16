import Homogenization.Mollify

/-!
# Continuity of dilations and mollifications in `Lᵖ(ℝᴺ)`

Step 1 towards proving the cited `CitedAffineApprox` ([oah-jpm11, Proposition 3.15]); that
statement is not proved here.
* `eLpNorm_comp_smul`: `‖F(r ·)‖_p = |r|^{-N/p} ‖F‖_p`;
* `tendsto_eLpNorm_comp_smul_sub`: `‖g(r ·) - g‖_p → 0` as `r → 1`, for `g ∈ Lᵖ`, `1 ≤ p < ∞`;
* `eLpNorm_bump_convolution_le`: convolution with a normalized bump is a contraction of `Lᵖ`;
* `tendsto_eLpNorm_bump_convolution_sub`: `‖φᵢ ⋆ g - g‖_p → 0` when the bump radii tend to `0`.
Both limits are proved by density of continuous compactly supported functions
(`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), the continuous case following from uniform
continuity and a common bounded support.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution

namespace Homogenization

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- `‖F(r ·)‖_p = |r|^{-N/p} ‖F‖_p`. -/
theorem eLpNorm_comp_smul {p : ℝ≥0∞} (hp : p ≠ ⊤) {F : Sp N → E}
    (hF : AEStronglyMeasurable F volume) {r : ℝ} (hr : r ≠ 0) :
    eLpNorm (fun x => F (r • x)) p volume =
      ENNReal.ofReal |(r ^ N)⁻¹| ^ (1 / p).toReal • eLpNorm F p volume := by
  have hmap : Measure.map (fun x : Sp N => r • x) volume =
      ENNReal.ofReal |(r ^ N)⁻¹| • volume := by
    rw [Measure.map_addHaar_smul _ hr, finrank_Sp]
  have h := eLpNorm_map_measure (p := p) (f := fun x : Sp N => r • x) (g := F)
    (by rw [hmap]; exact hF.smul_measure _) (measurable_const_smul r).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_top hp] at h
  exact h.symm

/-- For `c` continuous with compact support, `‖c(r ·) - c‖_p → 0` as `r → 1`. -/
theorem tendsto_eLpNorm_comp_smul_sub_of_continuous {p : ℝ≥0∞} {c : Sp N → E}
    (hc : Continuous c) (hcs : HasCompactSupport c) :
    Tendsto (fun r : ℝ => eLpNorm (fun x => c (r • x) - c x) p volume) (𝓝 1) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  set R' := max R 0
  have hR' : tsupport c ⊆ closedBall 0 R' :=
    hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hzero : ∀ y, R' < ‖y‖ → c y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR' h; rw [mem_closedBall, dist_zero_right] at this; linarith
  set B : Set (Sp N) := closedBall 0 (2 * R')
  have hVB : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  set V : ℝ≥0∞ := volume B ^ p.toReal⁻¹
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hVB
  have hUC := hcs.uniformContinuous_of_continuous hc
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hV hε.ne'
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuous_iff.1 hUC η hη
  have hnear : ∀ᶠ r : ℝ in 𝓝 1, |r - 1| < min (1 / 2) (δ / (2 * R' + 1)) := by
    have := Metric.ball_mem_nhds (1 : ℝ) (lt_min (by norm_num : (0:ℝ) < 1 / 2)
      (div_pos hδ (by positivity : (0 : ℝ) < 2 * R' + 1)))
    filter_upwards [this] with r hr
    rwa [Metric.mem_ball, Real.dist_eq] at hr
  filter_upwards [hnear] with r hr
  have hr1 : |r - 1| < 1 / 2 := lt_of_lt_of_le hr (min_le_left _ _)
  have hr2 : |r - 1| < δ / (2 * R' + 1) := lt_of_lt_of_le hr (min_le_right _ _)
  have hsupp : support (fun x => c (r • x) - c x) ⊆ B := by
    intro x hx
    by_contra hxB
    rw [mem_closedBall, dist_zero_right, not_le] at hxB
    apply hx
    have hR0 : 0 ≤ R' := le_max_right _ _
    have hrx : R' < ‖r • x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have : 1 / 2 < |r| := by
        have := abs_sub_abs_le_abs_sub 1 r; rw [abs_sub_comm] at this
        simp only [abs_one] at this; linarith
      nlinarith [norm_nonneg x]
    simp only [hzero _ hrx, hzero x (by linarith), sub_zero]
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  refine (eLpNorm_le_of_ae_bound (C := η) (Eventually.of_forall fun x => ?_)).trans ?_
  · by_cases hxB : ‖x‖ ≤ 2 * R'
    · have hd : dist (r • x) x < δ := by
        rw [dist_eq_norm, show r • x - x = (r - 1) • x by rw [sub_smul, one_smul], norm_smul,
          Real.norm_eq_abs]
        calc |r - 1| * ‖x‖ ≤ |r - 1| * (2 * R' + 1) := by gcongr; linarith
          _ < δ / (2 * R' + 1) * (2 * R' + 1) := by
              gcongr
          _ = δ := div_mul_cancel₀ δ (by have := le_max_right R 0; positivity)
      rw [← dist_eq_norm]; exact (hδU hd).le
    · have hR0 : 0 ≤ R' := le_max_right _ _
      rw [not_le] at hxB
      have hrx : R' < ‖r • x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        have : 1 / 2 < |r| := by
          have := abs_sub_abs_le_abs_sub 1 r; rw [abs_sub_comm] at this
          simp only [abs_one] at this; linarith
        nlinarith [norm_nonneg x]
      simp only [hzero _ hrx, hzero x (by linarith), sub_zero, norm_zero]
      exact η.2
  · rw [Measure.restrict_apply_univ, ENNReal.ofReal_coe_nnreal, mul_comm]
    exact hηε.le

/-- **Continuity of dilations in `Lᵖ(ℝᴺ)`**: `‖g(r ·) - g‖_p → 0` as `r → 1`, `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_comp_smul_sub [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) {g : Sp N → E}
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    Tendsto (fun r : ℝ => eLpNorm (fun x => g (r • x) - g x) (ENNReal.ofReal p) volume) (𝓝 1)
      (𝓝 0) := by
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨hp1⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun _ => hεt ▸ le_top
  set δ : ℝ≥0∞ := ε / 4
  have hδ : δ ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨c, hcs, hgc, hcc, -⟩ := hg.exists_hasCompactSupport_eLpNorm_sub_le hpT hδ
  -- the dilation factor tends to `1`
  have hfac : ∀ᶠ r : ℝ in 𝓝 1, ENNReal.ofReal |(r ^ N)⁻¹| ^ (1 / ENNReal.ofReal p).toReal ≤ 2 := by
    have hcont : ContinuousAt (fun r : ℝ =>
        ENNReal.ofReal |(r ^ N)⁻¹| ^ (1 / ENNReal.ofReal p).toReal) 1 := by
      refine (ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).continuousAt.comp ?_
      exact (continuous_abs.continuousAt).comp ((continuousAt_id.pow N).inv₀ (by simp))
    have h1 : (fun r : ℝ => ENNReal.ofReal |(r ^ N)⁻¹| ^ (1 / ENNReal.ofReal p).toReal) 1 = 1 := by
      simp
    have := hcont.eventually (gt_mem_nhds (show _ < (2 : ℝ≥0∞) by rw [h1]; norm_num))
    exact this.mono fun r hr => hr.le
  have hpos : ∀ᶠ r : ℝ in 𝓝 1, r ≠ 0 := eventually_ne_nhds one_ne_zero
  have hcpart := (ENNReal.tendsto_nhds_zero.1 (tendsto_eLpNorm_comp_smul_sub_of_continuous
    (p := ENNReal.ofReal p) hcc hcs)) δ (pos_iff_ne_zero.2 hδ)
  filter_upwards [hfac, hpos, hcpart] with r hr hr0 hrc
  have hm1 : AEStronglyMeasurable (fun x => (g - c) (r • x)) volume :=
    (hg.1.sub hcc.aestronglyMeasurable).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume hr0)
  have hm2 : AEStronglyMeasurable (fun x => c (r • x) - c x) volume :=
    (hcc.comp (continuous_const_smul r)).aestronglyMeasurable.sub hcc.aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (c - g) volume := hcc.aestronglyMeasurable.sub hg.1
  have e : (fun x => g (r • x) - g x) =
      (fun x => (g - c) (r • x)) + (fun x => c (r • x) - c x) + (c - g) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; abel
  rw [e]
  calc eLpNorm ((fun x => (g - c) (r • x)) + (fun x => c (r • x) - c x) + (c - g))
        (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => (g - c) (r • x)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => c (r • x) - c x) (ENNReal.ofReal p) volume +
          eLpNorm (c - g) (ENNReal.ofReal p) volume := by
        refine (eLpNorm_add_le (hm1.add hm2) hm3 hp1).trans ?_
        gcongr
        exact eLpNorm_add_le hm1 hm2 hp1
    _ ≤ 2 * δ + δ + δ := by
        gcongr
        · rw [eLpNorm_comp_smul hpT (hg.1.sub hcc.aestronglyMeasurable) hr0, smul_eq_mul]
          exact mul_le_mul' hr hgc
        · rw [← eLpNorm_neg, neg_sub]; exact hgc
    _ = ε := by
        simp only [δ]
        rw [show (2 : ℝ≥0∞) * (ε / 4) + ε / 4 + ε / 4 = 4 * (ε / 4) by ring]
        exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- Convolution with a normalized bump is a contraction of `Lᵖ(ℝᴺ)`. -/
theorem eLpNorm_bump_convolution_le [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ} (hp : 1 ≤ p)
    {g : Sp N → E} (hg : MemLp g (ENNReal.ofReal p) volume) (η : ContDiffBump (0 : Sp N)) :
    eLpNorm (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (ENNReal.ofReal p)
      volume ≤ eLpNorm g (ENNReal.ofReal p) volume := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]
  exact ENNReal.rpow_le_rpow (W1p0.convolution_lintegral_norm_rpow_le hp hg η)
    (by positivity)

/-- For `c` continuous with compact support, `‖φᵢ ⋆ c - c‖_p → 0` when the bump radii tend to
`0`. -/
theorem tendsto_eLpNorm_bump_convolution_sub_of_continuous [NormedSpace ℝ E]
    [CompleteSpace E] {p : ℝ≥0∞} {c : Sp N → E} (hc : Continuous c) (hcs : HasCompactSupport c)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : Sp N)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] c - c)
      p volume) l (𝓝 0) := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have hzero : ∀ y, R < ‖y‖ → c y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR h; rw [mem_closedBall, dist_zero_right] at this; linarith
  set B : Set (Sp N) := closedBall 0 (R + 1)
  have hVB : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  set V : ℝ≥0∞ := volume B ^ p.toReal⁻¹
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hVB
  have hUC := hcs.uniformContinuous_of_continuous hc
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hV hε.ne'
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuous_iff.1 hUC η hη
  filter_upwards [hφ.eventually (gt_mem_nhds (lt_min hδ one_pos))] with i hi
  have hr1 : (φ i).rOut < 1 := lt_of_lt_of_le hi (min_le_right _ _)
  have hrδ : (φ i).rOut < δ := lt_of_lt_of_le hi (min_le_left _ _)
  have hmc : AEStronglyMeasurable c volume := hc.aestronglyMeasurable
  have hsupp : support ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] c - c) ⊆
      B := by
    intro x hx
    by_contra hxB
    rw [mem_closedBall, dist_zero_right, not_le] at hxB
    apply hx
    have hcx : c x = 0 := hzero x (by linarith)
    have h0 := (φ i).dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := 0) hmc
      fun y hy => by
        rw [mem_ball, dist_eq_norm] at hy
        have : R < ‖y‖ := by
          have h1 := norm_sub_norm_le x y
          rw [norm_sub_rev] at h1
          linarith
        rw [hzero y this, hcx, dist_self]
    rw [dist_le_zero] at h0
    simp only [Pi.sub_apply, h0, sub_self]
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  refine (eLpNorm_le_of_ae_bound (C := η) (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Pi.sub_apply, ← dist_eq_norm]
    exact (φ i).dist_normed_convolution_le hmc fun y hy =>
      (hδU (lt_trans (mem_ball.1 hy) hrδ)).le
  · rw [Measure.restrict_apply_univ, ENNReal.ofReal_coe_nnreal, mul_comm]
    exact hηε.le

/-- **Mollifiers converge in `Lᵖ(ℝᴺ)`**: `‖φᵢ ⋆ g - g‖_p → 0` when the bump radii tend to `0`,
for `g ∈ Lᵖ`, `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_bump_convolution_sub [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ}
    (hp : 1 ≤ p) {g : Sp N → E} (hg : MemLp g (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : Sp N)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g - g)
      (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun _ => hεt ▸ le_top
  set δ : ℝ≥0∞ := ε / 3
  have hδ : δ ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨c, hcs, hgc, hcc, hcLp⟩ := hg.exists_hasCompactSupport_eLpNorm_sub_le hpT hδ
  have hcpart := (ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_bump_convolution_sub_of_continuous (p := ENNReal.ofReal p) hcc hcs hφ))
    δ (pos_iff_ne_zero.2 hδ)
  filter_upwards [hcpart] with i hi
  set K := fun h : Sp N → E => (φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h
  have hgcLp : MemLp (g - c) (ENNReal.ofReal p) volume := hg.sub hcLp
  have hloc : ∀ h : Sp N → E, MemLp h (ENNReal.ofReal p) volume → LocallyIntegrable h volume :=
    fun h hh => hh.locallyIntegrable hp1
  have hex : ∀ h : Sp N → E, MemLp h (ENNReal.ofReal p) volume →
      ConvolutionExists ((φ i).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    fun h hh => (φ i).hasCompactSupport_normed.convolutionExists_left _
      (φ i).continuous_normed (hloc h hh)
  have hcont : ∀ h : Sp N → E, MemLp h (ENNReal.ofReal p) volume → Continuous (K h) :=
    fun h hh => (φ i).hasCompactSupport_normed.continuous_convolution_left _
      (φ i).continuous_normed (hloc h hh)
  have hsplit : K g = K (g - c) + K c := by
    have := (hex _ hgcLp).distrib_add (hex _ hcLp)
    rwa [sub_add_cancel] at this
  have e : K g - g = K (g - c) + (K c - c) + (c - g) := by
    rw [hsplit]; abel
  rw [e]
  have hm1 := (hcont _ hgcLp).aestronglyMeasurable (μ := volume)
  have hm2 := ((hcont _ hcLp).sub hcc).aestronglyMeasurable (μ := volume)
  have hm3 : AEStronglyMeasurable (c - g) volume := hcc.aestronglyMeasurable.sub hg.1
  calc eLpNorm (K (g - c) + (K c - c) + (c - g)) (ENNReal.ofReal p) volume
      ≤ eLpNorm (K (g - c)) (ENNReal.ofReal p) volume +
          eLpNorm (K c - c) (ENNReal.ofReal p) volume +
          eLpNorm (c - g) (ENNReal.ofReal p) volume := by
        refine (eLpNorm_add_le (hm1.add hm2) hm3 hp1).trans ?_
        gcongr
        exact eLpNorm_add_le hm1 hm2 hp1
    _ ≤ δ + δ + δ := by
        gcongr
        · exact (eLpNorm_bump_convolution_le hp hgcLp _).trans hgc
        · rw [← eLpNorm_neg, neg_sub]; exact hgc
    _ = ε := by
        simp only [δ]
        rw [show ε / 3 + ε / 3 + ε / 3 = 3 * (ε / 3) by ring]
        exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end Homogenization
