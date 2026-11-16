import Homogenization.HomothetyMollify
import Homogenization.USCIneq

/-!
# Local mollification with control of a non-convex energy

Step 3 towards proving the cited `CitedAffineApprox` ([oah-jpm11, Proposition 3.15]); that
statement is not proved here.

`limsup_lintegral_mollSeq_le`: let `φ` (locally integrable) have weak gradient `g` (measurable,
locally integrable) on an open set `U`, `Ω` open of finite measure with `closedBall z δ ⊆ U` for
every `z ∈ Ω`, `g ∈ S` a.e. with `S` closed convex inside `int(dom G)`, `1_U G(g)` integrable,
and `L ≤ β(1 + G)` continuous on `int(dom G)` (`L` itself need not be convex).
Then the mollifications `ηₙ ⋆ φ` (`mollSeq`) have gradients in `S` on `Ω` and
`limsup ∫_Ω L(∇(ηₙ ⋆ φ)) ≤ ∫_Ω L(g)`.

Proof: `∇(ηₙ ⋆ φ) = ηₙ ⋆ g` on `Ω` (`fderiv_convolution_eq_convolution_grad_local`);
`L(ηₙ ⋆ g) ≤ β(1 + G(ηₙ ⋆ g)) ≤ β(1 + ηₙ ⋆ G(g))` by Jensen for the convex `G`
(`ConvexENN.bump_convolution_le_ofReal`); the dominating functions converge in `L¹`
(`tendsto_eLpNorm_bump_convolution_sub`, `tendsto_setLIntegral_ofReal_of_eLpNorm`) and a.e.; the
reverse Fatou lemma `limsup_lintegral_le_of_dominating` and the continuity of `L` on `int(dom G)`
conclude.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution Pointwise

namespace Homogenization

variable {N m : ℕ}

/-- `ofReal(η ⋆ F)(z) = ∫ η(z - y) F(y) dy` as a lower integral, for `F` integrable and
nonnegative. -/
theorem ofReal_bump_convolution_eq_lintegral (η : ContDiffBump (0 : Sp N)) {F : Sp N → ℝ}
    (hF : Integrable F volume) (hF0 : ∀ y, 0 ≤ F y) (z : Sp N) :
    ENNReal.ofReal ((η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) z) =
      ∫⁻ y, ENNReal.ofReal (η.normed volume (z - y) * F y) := by
  have hk0 : ∀ y, 0 ≤ η.normed volume (z - y) := fun y => ContDiffBump.nonneg_normed _ _
  have hint : Integrable (fun y => η.normed volume (z - y) * F y) volume := by
    have := hF.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((η.continuous_normed).comp (continuous_const.sub continuous_id))
      ((η.hasCompactSupport_normed (μ := volume)).comp_homeomorph (Homeomorph.subLeft z))
    simpa [smul_eq_mul] using this
  rw [convolution_eq_swap, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => mul_nonneg (hk0 y) (hF0 y))]
  rfl

/-- Jensen for `G` along a local mollification: if `g ∈ S ⊆ int(dom G)` a.e. and the bump around
`z` sits inside `U`, then `G((η ⋆ g)(z)) ≤ ofReal (η ⋆ F)(z)` with `F = 1_U G(g)`. -/
theorem ConvexENN.bump_convolution_le_ofReal {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGm : Measurable G) {S : Set (Mat m N)} (hSc : IsClosed S) (hSconv : Convex ℝ S)
    (hSint : S ⊆ interior (dom G)) {U : Set (Sp N)} (η : ContDiffBump (0 : Sp N))
    {g : Sp N → Mat m N} (hgm : Measurable g) (hg : LocallyIntegrable g volume)
    (hgS : ∀ᵐ y ∂volume, g y ∈ S)
    (hF : Integrable (U.indicator fun y => (G (g y)).toReal) volume) {z : Sp N}
    (hball : closedBall z η.rOut ⊆ U) :
    G ((η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) z) ≤
      ENNReal.ofReal ((η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (U.indicator fun y => (G (g y)).toReal)) z) := by
  rw [ofReal_bump_convolution_eq_lintegral η hF
    (fun y => by by_cases hy : y ∈ U <;> simp [hy, ENNReal.toReal_nonneg]) z]
  have heq : (fun y => ENNReal.ofReal (η.normed volume (z - y)) * G (g y)) =ᵐ[volume]
      fun y => ENNReal.ofReal (η.normed volume (z - y) *
        U.indicator (fun y => (G (g y)).toReal) y) := by
    filter_upwards [hgS] with y hy
    have hfin : G (g y) ≠ ⊤ := (show g y ∈ dom G from interior_subset (hSint hy)).ne
    by_cases hk : η.normed volume (z - y) = 0
    · simp [hk]
    · have hyU : y ∈ U := by
        apply hball
        have : z - y ∈ support (η.normed volume) := hk
        rw [ContDiffBump.support_normed_eq, mem_ball, dist_zero_right] at this
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact this.le
      rw [indicator_of_mem hyU, ENNReal.ofReal_mul (ContDiffBump.nonneg_normed _ _),
        ENNReal.ofReal_toReal hfin]
  rw [← lintegral_congr_ae heq]
  by_cases hfin : ∫⁻ y, ENNReal.ofReal (η.normed volume (z - y)) * G (g y) < ⊤
  · exact (hG.bump_convolution_le hGm hSc hSconv hSint η hgm hg hgS z hfin).2
  · rw [not_lt, top_le_iff] at hfin; rw [hfin]; exact le_top

/-- `ofReal a ≤ ofReal b + ‖a - b‖ₑ`. -/
theorem ofReal_le_ofReal_add_enorm_sub (a b : ℝ) :
    ENNReal.ofReal a ≤ ENNReal.ofReal b + ‖a - b‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal a ≤ ENNReal.ofReal (b + |a - b|) :=
        ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a - b)])
    _ ≤ _ := ENNReal.ofReal_add_le

/-- `L¹` convergence implies convergence of `∫_Ω ofReal hₙ`. -/
theorem tendsto_setLIntegral_ofReal_of_eLpNorm {h : ℕ → Sp N → ℝ} {F : Sp N → ℝ}
    (hF : Integrable F volume) (hh : ∀ n, AEStronglyMeasurable (h n) volume)
    (hconv : Tendsto (fun n => eLpNorm (h n - F) 1 volume) atTop (𝓝 0)) (Ω : Set (Sp N)) :
    Tendsto (fun n => ∫⁻ z in Ω, ENNReal.ofReal (h n z)) atTop
      (𝓝 (∫⁻ z in Ω, ENNReal.ofReal (F z))) := by
  set A := ∫⁻ z in Ω, ENNReal.ofReal (F z)
  have hA : A ≠ ⊤ := (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hF.lintegral_lt_top).ne
  set e : ℕ → ℝ≥0∞ := fun n => eLpNorm (h n - F) 1 volume
  have hdiff : ∀ n, ∫⁻ z in Ω, ‖h n z - F z‖ₑ ≤ e n := fun n => by
    simp only [e, eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply]
    exact setLIntegral_le_lintegral _ _
  have hm : ∀ n, AEMeasurable (fun z => ‖h n z - F z‖ₑ) (volume.restrict Ω) := fun n =>
    ((hh n).sub hF.1).enorm.restrict
  have hup : ∀ n, ∫⁻ z in Ω, ENNReal.ofReal (h n z) ≤ A + e n := fun n => by
    calc ∫⁻ z in Ω, ENNReal.ofReal (h n z)
        ≤ ∫⁻ z in Ω, (ENNReal.ofReal (F z) + ‖h n z - F z‖ₑ) :=
          lintegral_mono fun z => ofReal_le_ofReal_add_enorm_sub _ _
      _ = A + ∫⁻ z in Ω, ‖h n z - F z‖ₑ := lintegral_add_right' _ (hm n)
      _ ≤ A + e n := by gcongr; exact hdiff n
  have hlow : ∀ n, A ≤ (∫⁻ z in Ω, ENNReal.ofReal (h n z)) + e n := fun n => by
    calc A ≤ ∫⁻ z in Ω, (ENNReal.ofReal (h n z) + ‖h n z - F z‖ₑ) :=
          lintegral_mono fun z => by
            have := ofReal_le_ofReal_add_enorm_sub (F z) (h n z)
            rwa [← enorm_neg, neg_sub] at this
      _ = (∫⁻ z in Ω, ENNReal.ofReal (h n z)) + ∫⁻ z in Ω, ‖h n z - F z‖ₑ :=
          lintegral_add_right' _ (hm n)
      _ ≤ _ := by gcongr; exact hdiff n
  have hupper : Tendsto (fun n => A + e n) atTop (𝓝 A) := by
    have := tendsto_const_nhds (x := A) |>.add hconv; rwa [add_zero] at this
  have hlower : Tendsto (fun n => A - e n) atTop (𝓝 A) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := A)) hconv (Or.inl hA)
    rwa [tsub_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
    (fun n => tsub_le_iff_right.2 (hlow n)) hup

/-- The mollifications `ηₙ ⋆ φ` with bumps of radius `δ/(n+2)`. -/
noncomputable def mollSeq {δ : ℝ} (hδ : 0 < δ) (φ : Sp N → Tgt m) (n : ℕ) : Sp N → Tgt m :=
  (halfBump (N := N) (show 0 < δ / ((n : ℝ) + 2) by positivity)).normed volume
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ

/-- **Local mollification with energy control.** Let `φ` (locally integrable) have weak gradient
`g` (measurable, locally integrable) on an open `U`, `Ω` open of finite measure with
`closedBall z δ ⊆ U` for `z ∈ Ω`, `g ∈ S` a.e. with `S` closed
convex inside `int(dom G)`, `G` convex lower semicontinuous, `L ≤ β(1 + G)` continuous on
`int(dom G)`, and `1_U G(g)` integrable. Then `∇(ηₙ ⋆ φ) ∈ S` on `Ω` and
`limsup ∫_Ω L(∇(ηₙ ⋆ φ)) ≤ ∫_Ω L(g)`. -/
theorem limsup_lintegral_mollSeq_le {U Ω : Set (Sp N)} (hΩ : IsOpen Ω)
    (hΩv : volume Ω ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) (hΩU : ∀ z ∈ Ω, closedBall z δ ⊆ U)
    {φ : Sp N → Tgt m} {g : Sp N → Mat m N} (hφ : LocallyIntegrable φ volume)
    (hgm : Measurable g) (hg : LocallyIntegrable g volume) (hweak : HasWeakGrad U φ g)
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    {S : Set (Mat m N)} (hSc : IsClosed S) (hSconv : Convex ℝ S)
    (hSint : S ⊆ interior (dom G)) (hgS : ∀ᵐ y ∂volume, g y ∈ S)
    {L : Mat m N → ℝ≥0∞} (hLc : ContinuousOn L (interior (dom G))) {β : ℝ≥0}
    (hLG : ∀ ξ, L ξ ≤ β * (1 + G ξ))
    (hF : Integrable (U.indicator fun y => (G (g y)).toReal) volume) :
    (∀ n, ∀ z ∈ Ω, fderiv ℝ (mollSeq hδ φ n) z ∈ S) ∧
      limsup (fun n => ∫⁻ z in Ω, L (fderiv ℝ (mollSeq hδ φ n) z)) atTop ≤
        ∫⁻ z in Ω, L (g z) := by
  have hGm : Measurable G := hGlsc.measurable
  set r : ℕ → ℝ := fun n => δ / ((n : ℝ) + 2)
  have hr : ∀ n, 0 < r n := fun n => by positivity
  set η : ℕ → ContDiffBump (0 : Sp N) := fun n => halfBump (hr n)
  have hrδ : ∀ n, (η n).rOut ≤ δ := fun n => by
    change δ / ((n : ℝ) + 2) ≤ δ
    rw [div_le_iff₀ (by positivity)]; nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hball : ∀ n, ∀ z ∈ Ω, closedBall z (η n).rOut ⊆ U := fun n z hz =>
    (closedBall_subset_closedBall (hrδ n)).trans (hΩU z hz)
  have hder : ∀ n, ∀ z ∈ Ω, fderiv ℝ (mollSeq hδ φ n) z =
      ((η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) z := fun n z hz =>
    fderiv_convolution_eq_convolution_grad_local (φg := (φ, g)) hφ hg hweak (η n) (hball n z hz)
  have hval : ∀ n, ∀ z ∈ Ω, fderiv ℝ (mollSeq hδ φ n) z ∈ S := fun n z hz => by
    rw [hder n z hz]; exact bump_convolution_mem hSc hSconv (η n) hg hgS z
  refine ⟨hval, ?_⟩
  -- a measurable version of `L`
  classical
  set L' : Mat m N → ℝ≥0∞ := (interior (dom G)).piecewise L fun _ => 0
  have hL'm : Measurable L' :=
    hLc.measurable_piecewise continuousOn_const isOpen_interior.measurableSet
  have hL'eq : ∀ ξ ∈ interior (dom G), L' ξ = L ξ := fun ξ hξ => piecewise_eq_of_mem _ _ _ hξ
  have hL'le : ∀ ξ, L' ξ ≤ L ξ := fun ξ => by
    by_cases hξ : ξ ∈ interior (dom G)
    · rw [hL'eq ξ hξ]
    · simp [L', piecewise_eq_of_notMem _ _ _ hξ]
  set F : Sp N → ℝ := U.indicator fun y => (G (g y)).toReal
  set c : ℕ → Sp N → Mat m N :=
    fun n => (η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  set h : ℕ → Sp N → ℝ :=
    fun n => (η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  have hcc : ∀ n, Continuous (c n) := fun n =>
    (η n).hasCompactSupport_normed.continuous_convolution_left _ (η n).continuous_normed hg
  have hhc : ∀ n, Continuous (h n) := fun n =>
    (η n).hasCompactSupport_normed.continuous_convolution_left _ (η n).continuous_normed
      hF.locallyIntegrable
  -- the integrands
  set f : ℕ → Sp N → ℝ≥0∞ := fun n z => L' (c n z)
  set gg : ℕ → Sp N → ℝ≥0∞ := fun n z => β * (1 + ENNReal.ofReal (h n z))
  set f₀ : Sp N → ℝ≥0∞ := fun z => L' (g z)
  set g₀ : Sp N → ℝ≥0∞ := fun z => β * (1 + ENNReal.ofReal (F z))
  have hrOut : Tendsto (fun n => (η n).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hK : ∀ᶠ n in atTop, (η n).rOut ≤ 2 * (η n).rIn :=
    Eventually.of_forall fun n => by simp [η, halfBump]; linarith [hr n]
  have hcae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hrOut hK hg
  have hhae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hrOut hK
    hF.locallyIntegrable
  -- reverse Fatou
  have key := limsup_lintegral_le_of_dominating (μ := volume.restrict Ω) (f := f) (g := gg)
    (f₀ := f₀) (g₀ := g₀)
    (fun n => (hL'm.comp (hcc n).measurable).aemeasurable)
    (fun n => (measurable_const.mul (measurable_const.add
      (hhc n).measurable.ennreal_ofReal)).aemeasurable)
    (hL'm.comp hgm).aemeasurable
    (fun n => by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
      have hS := hval n z hz
      rw [hder n z hz] at hS
      calc f n z ≤ L (c n z) := hL'le _
        _ ≤ β * (1 + G (c n z)) := hLG _
        _ ≤ gg n z := by
          change β * (1 + G (c n z)) ≤ β * (1 + ENNReal.ofReal (h n z))
          gcongr
          exact hG.bump_convolution_le_ofReal hGm hSc hSconv hSint (η n) hgm hg hgS hF
            (hball n z hz))
    (by
      filter_upwards [ae_restrict_mem hΩ.measurableSet, ae_restrict_of_ae hgS] with z hz hzS
      have hfin : G (g z) ≠ ⊤ := (show g z ∈ dom G from interior_subset (hSint hzS)).ne
      have hFz : ENNReal.ofReal (F z) = G (g z) := by
        simp only [F, indicator_of_mem (hΩU z hz (mem_closedBall_self hδ.le)),
          ENNReal.ofReal_toReal hfin]
      calc f₀ z ≤ L (g z) := hL'le _
        _ ≤ β * (1 + G (g z)) := hLG _
        _ = g₀ z := by simp only [g₀, hFz])
    (by
      simp only [g₀]
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        lintegral_add_left measurable_const, setLIntegral_const, one_mul]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hΩv,
        (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hF.lintegral_lt_top).ne⟩))
    (by
      have hL1 : Tendsto (fun n => eLpNorm (h n - F) 1 volume) atTop (𝓝 0) := by
        have := tendsto_eLpNorm_bump_convolution_sub (p := 1) le_rfl
          (by rw [ENNReal.ofReal_one]; exact memLp_one_iff_integrable.2 hF) hrOut
        rwa [ENNReal.ofReal_one] at this
      have hlim := tendsto_setLIntegral_ofReal_of_eLpNorm hF
        (fun n => (hhc n).aestronglyMeasurable) hL1 Ω
      have e : ∀ k : Sp N → ℝ, ∫⁻ z in Ω, β * (1 + ENNReal.ofReal (k z)) =
          β * (volume Ω + ∫⁻ z in Ω, ENNReal.ofReal (k z)) := fun k => by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_add_left measurable_const,
          setLIntegral_const, one_mul]
      simp only [gg, g₀, e]
      exact ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hlim) (Or.inr ENNReal.coe_ne_top))
    (by
      filter_upwards [ae_restrict_of_ae hhae] with z hz
      have : Tendsto (fun n => gg n z) atTop (𝓝 (g₀ z)) :=
        ENNReal.Tendsto.const_mul (tendsto_const_nhds.add
          ((ENNReal.continuous_ofReal.tendsto _).comp hz)) (Or.inr ENNReal.coe_ne_top)
      exact this.liminf_eq.ge)
    (by
      filter_upwards [ae_restrict_of_ae hcae, ae_restrict_of_ae hgS] with z hz hzS
      have hcont : ContinuousAt L' (g z) := by
        have h1 : ContinuousAt L (g z) :=
          hLc.continuousAt (isOpen_interior.mem_nhds (hSint hzS))
        refine h1.congr ?_
        filter_upwards [isOpen_interior.mem_nhds (hSint hzS)] with ξ hξ
        exact (hL'eq ξ hξ).symm
      exact (hcont.tendsto.comp hz).limsup_eq.le)
  -- back to `L`
  have hlhs : ∀ n, ∫⁻ z in Ω, L (fderiv ℝ (mollSeq hδ φ n) z) = ∫⁻ z in Ω, f n z := fun n => by
    refine setLIntegral_congr_fun hΩ.measurableSet fun z hz => ?_
    rw [hder n z hz]
    exact (hL'eq _ (hSint (by rw [← hder n z hz]; exact hval n z hz))).symm
  have hrhs : ∫⁻ z in Ω, f₀ z ≤ ∫⁻ z in Ω, L (g z) := lintegral_mono fun z => hL'le _
  simp only [hlhs]
  exact key.trans hrhs

end Homogenization
