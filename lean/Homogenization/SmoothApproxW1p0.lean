import Homogenization.Mollify

/-!
# Smooth approximation of `W^{1,p}_0` functions with convex energy convergence

Step 2 of the proof of `lemme_approx_convex_zero` for cubes (`approxConvexZero_cube`), which
replaces the former cited hypothesis `CitedApproxConvexZero`. `exists_smooth_approx_W1p0`: for
`Q = cube ρ 0`, `Ψ` convex, lower semicontinuous
with `0 ∈ int(dom Ψ)`, and `u ∈ W^{1,p}_0(Q)` with `∫_Q Ψ(∇u) < ∞`, there are `fₙ` of class
`C¹` with compact support in `Q`, gradients in `tₙ · cl(dom Ψ) ⊆ int(dom Ψ)` (`tₙ < 1`),
`∇fₙ → ∇u` a.e. on `Q` and `∫_Q Ψ(∇fₙ) → ∫_Q Ψ(∇u)`.

Construction: `fₙ(x) = tₙ sₙ (ηₙ ⋆ u)(x / sₙ)` (`contrMoll`), `ηₙ` a normalized bump of radius
`rₙ → 0`, `sₙ = ρ/(ρ + 3rₙ)`, `tₙ → 1` (used in the proof, not stated in the conclusion).
* `fderiv_contrMoll_eq_conv`: `∇fₙ(x) = (ηₙ ⋆ tₙ∇u)(x/sₙ)`;
* `bump_convolution_mem`, `ConvexENN.bump_convolution_le`: the convolution stays in the closed
  convex set `tₙ · cl(dom Ψ)`, and Jensen's inequality `Ψ(η ⋆ V) ≤ η ⋆ Ψ(V)` (Mathlib's
  `Convex.integral_mem`, `ConvexOn.map_integral_le` for the probability `η(x - z) dz`);
* `lintegral_contrMoll_le`: change of variables, Jensen and Tonelli (`lintegral_bump_conv_le`)
  give `∫_Q Ψ(∇fₙ) ≤ tₙ(∫_Q Ψ(∇u) + Ψ(0)|Qₙ \ Q|) + (1 - tₙ)Ψ(0)|Qₙ|`;
* `ae_tendsto_bump_convolution_moving`: mollifiers evaluated at the moving points `x/sₙ`
  converge a.e. (moving-center Lebesgue differentiation), hence `∇fₙ → ∇u` a.e.; Fatou and lower
  semicontinuity give the reverse energy inequality.

The `Aff₀` approximation of the `fₙ` (step 1, `PwAffineInterp.lean`) and the removal of the cited
hypothesis (step 3) are not done in this file.
-/

open MeasureTheory Filter Topology Set Function Metric ContinuousLinearMap
open scoped ENNReal NNReal Convolution Pointwise

namespace Homogenization

variable {N : ℕ}

/-- **Mollifiers evaluated at moving points.** For `g` locally integrable, at a.e. `x₀`, the
convolutions of `g` with normalized bumps of radii `→ 0` (bounded ratio `rOut/rIn`), evaluated at
points `w i` with `‖w i - x₀‖ ≤ K' rOut`, converge to `g x₀` (moving-center Lebesgue
differentiation, `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`). -/
theorem ae_tendsto_bump_convolution_moving {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : Sp N → E} (hg : LocallyIntegrable g volume)
    (K K' : ℝ) :
    ∀ᵐ x₀ ∂volume, ∀ {ι : Type} {l : Filter ι} (φ : ι → ContDiffBump (0 : Sp N))
      (w : ι → Sp N), Tendsto (fun i => (φ i).rOut) l (𝓝 0) →
      (∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) →
      (∀ᶠ i in l, x₀ ∈ closedBall (w i) (K' * (φ i).rOut)) →
      Tendsto (fun i => ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] g) (w i)) l (𝓝 (g x₀)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hg K'] with
    x₀ h₀ ι l φ w hφ h'φ hw
  simp only [convolution_eq_swap, lsmul_apply]
  have hφ' : Tendsto (fun i => (φ i).rOut) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hφ, Eventually.of_forall fun i => (φ i).rOut_pos⟩
  have := h₀ w (fun i => (φ i).rOut) hφ' hw
  apply tendsto_integral_smul_of_tendsto_average_norm_sub (K ^ (Module.finrank ℝ (Sp N))) this
  · filter_upwards with i using hg.integrableOn_isCompact (isCompact_closedBall _ _)
  · apply tendsto_const_nhds.congr (fun i => ?_)
    rw [← integral_neg_eq_self]
    simp only [sub_neg_eq_add, integral_add_left_eq_self, ContDiffBump.integral_normed]
  · filter_upwards with i
    change support ((ContDiffBump.normed (φ i) volume) ∘ (fun y => w i - y)) ⊆
      closedBall (w i) (φ i).rOut
    simp only [support_comp_eq_preimage, ContDiffBump.support_normed_eq]
    intro x hx
    simp only [mem_preimage, mem_ball, dist_zero_right] at hx
    simpa [dist_eq_norm_sub'] using hx.le
  · filter_upwards [h'φ] with i hi x
    rw [abs_of_nonneg (ContDiffBump.nonneg_normed _ _),
      Measure.addHaar_real_closedBall_center]
    exact (φ i).normed_le_div_measure_closedBall_rOut _ _ hi _

variable {m : ℕ}

/-- The probability measure `η(x - z) dz` and the convolution as its barycenter. -/
theorem exists_bump_probability (η : ContDiffBump (0 : Sp N)) {V : Sp N → Mat m N}
    (hV : LocallyIntegrable V volume) (x : Sp N) :
    ∃ μ : Measure (Sp N), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ Integrable V μ ∧
      (η.normed volume ⋆[lsmul ℝ ℝ, volume] V) x = ∫ z, V z ∂μ ∧
      ∀ F : Sp N → ℝ≥0∞, Measurable F →
        ∫⁻ z, F z ∂μ = ∫⁻ z, ENNReal.ofReal (η.normed volume (x - z)) * F z := by
  set k : Sp N → ℝ := fun z => η.normed volume (x - z)
  have hk0 : ∀ z, 0 ≤ k z := fun z => ContDiffBump.nonneg_normed _ _
  have hkc : Continuous k := (η.continuous_normed).comp (continuous_const.sub continuous_id)
  have hkcs : HasCompactSupport k :=
    (η.hasCompactSupport_normed (μ := volume)).comp_homeomorph (Homeomorph.subLeft x)
  set f : Sp N → ℝ≥0 := fun z => Real.toNNReal (k z)
  have hfm : Measurable f := hkc.measurable.real_toNNReal
  have hk1 : ∫ z, k z = 1 := by
    rw [← integral_neg_eq_self]
    simp only [k, sub_neg_eq_add, integral_add_left_eq_self, ContDiffBump.integral_normed]
  have hkint : Integrable k volume := hkc.integrable_of_hasCompactSupport hkcs
  refine ⟨volume.withDensity fun z => (f z : ℝ≥0∞), ⟨?_⟩, withDensity_absolutelyContinuous _ _,
    ?_, ?_, fun F hF => ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have := ofReal_integral_eq_lintegral_ofReal hkint (Eventually.of_forall hk0)
    rw [hk1, ENNReal.ofReal_one] at this
    rw [this]
    rfl
  · rw [integrable_withDensity_iff_integrable_smul hfm]
    have := hV.integrable_smul_left_of_hasCompactSupport hkc hkcs
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [f, NNReal.smul_def, Real.coe_toNNReal _ (hk0 z)]
  · rw [convolution_eq_swap, integral_withDensity_eq_integral_smul hfm]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [lsmul_apply, f, NNReal.smul_def, Real.coe_toNNReal _ (hk0 z), k]
  · exact lintegral_withDensity_eq_lintegral_mul volume hfm.coe_nnreal_ennreal hF

/-- The convolution of `V` with a normalized bump stays in any closed convex set containing the
values of `V` a.e. -/
theorem bump_convolution_mem {S : Set (Mat m N)} (hSc : IsClosed S) (hSconv : Convex ℝ S)
    (η : ContDiffBump (0 : Sp N)) {V : Sp N → Mat m N} (hV : LocallyIntegrable V volume)
    (hVS : ∀ᵐ z ∂volume, V z ∈ S) (x : Sp N) :
    (η.normed volume ⋆[lsmul ℝ ℝ, volume] V) x ∈ S := by
  obtain ⟨μ, hμ, hac, hVint, hconv, -⟩ := exists_bump_probability η hV x
  rw [hconv]
  exact hSconv.integral_mem hSc (hac.ae_le hVS) hVint

/-- **Jensen for a normalized bump convolution.** Let `Ψ` be convex with values in `[0,∞]`, `S`
closed convex with `S ⊆ int(dom Ψ)`, and `V` measurable, locally integrable with values in `S`
a.e. Then `(η ⋆ V)(x) ∈ S` and `Ψ((η ⋆ V)(x)) ≤ ∫ η(x - z) Ψ(V z) dz`, provided the right-hand
side is finite. -/
theorem ConvexENN.bump_convolution_le {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ)
    (hΨm : Measurable Ψ)
    {S : Set (Mat m N)} (hSc : IsClosed S) (hSconv : Convex ℝ S)
    (hSint : S ⊆ interior (dom Ψ)) (η : ContDiffBump (0 : Sp N)) {V : Sp N → Mat m N}
    (hVm : Measurable V) (hV : LocallyIntegrable V volume) (hVS : ∀ᵐ z ∂volume, V z ∈ S)
    (x : Sp N)
    (hfin : ∫⁻ z, ENNReal.ofReal (η.normed volume (x - z)) * Ψ (V z) < ⊤) :
    (η.normed volume ⋆[lsmul ℝ ℝ, volume] V) x ∈ S ∧
      Ψ ((η.normed volume ⋆[lsmul ℝ ℝ, volume] V) x) ≤
        ∫⁻ z, ENNReal.ofReal (η.normed volume (x - z)) * Ψ (V z) := by
  set k : Sp N → ℝ := fun z => η.normed volume (x - z)
  have hk0 : ∀ z, 0 ≤ k z := fun z => ContDiffBump.nonneg_normed _ _
  have hkc : Continuous k := (η.continuous_normed).comp (continuous_const.sub continuous_id)
  have hkcs : HasCompactSupport k := by
    have := (η.hasCompactSupport_normed (μ := volume)).comp_homeomorph
      ((Homeomorph.subLeft x))
    exact this
  set f : Sp N → ℝ≥0 := fun z => Real.toNNReal (k z)
  have hfm : Measurable f := hkc.measurable.real_toNNReal
  set μ : Measure (Sp N) := volume.withDensity fun z => (f z : ℝ≥0∞)
  have hk1 : ∫ z, k z = 1 := by
    rw [← integral_neg_eq_self]
    simp only [k, sub_neg_eq_add, integral_add_left_eq_self, ContDiffBump.integral_normed]
  have hkint : Integrable k volume := hkc.integrable_of_hasCompactSupport hkcs
  have : IsProbabilityMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have := ofReal_integral_eq_lintegral_ofReal hkint (Eventually.of_forall hk0)
    rw [hk1, ENNReal.ofReal_one] at this
    rw [this]
    rfl
  have hconv : (η.normed volume ⋆[lsmul ℝ ℝ, volume] V) x = ∫ z, V z ∂μ := by
    rw [convolution_eq_swap, integral_withDensity_eq_integral_smul hfm]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [lsmul_apply, f, NNReal.smul_def, Real.coe_toNNReal _ (hk0 z), k]
  have hVint : Integrable V μ := by
    rw [integrable_withDensity_iff_integrable_smul hfm]
    have := hV.integrable_smul_left_of_hasCompactSupport hkc hkcs
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [f, NNReal.smul_def, Real.coe_toNNReal _ (hk0 z)]
  have hac : μ ≪ volume := withDensity_absolutelyContinuous _ _
  have hVSμ : ∀ᵐ z ∂μ, V z ∈ S := hac.ae_le hVS
  have hmem : ∫ z, V z ∂μ ∈ S := hSconv.integral_mem hSc hVSμ hVint
  refine ⟨hconv ▸ hmem, ?_⟩
  set g : Mat m N → ℝ := fun ζ => (Ψ ζ).toReal
  have hSdom : S ⊆ dom Ψ := hSint.trans interior_subset
  have hgconv : ConvexOn ℝ S g := hΨ.convexOn_toReal_dom.subset hSdom hSconv
  have hgcont : ContinuousOn g S := by
    refine (ENNReal.continuousOn_toReal.comp (hΨ.continuousOn_interior_dom.mono hSint)
      fun ζ hζ => ?_)
    exact (hSdom hζ : Ψ ζ < ⊤).ne
  have hlin : ∫⁻ z, Ψ (V z) ∂μ = ∫⁻ z, ENNReal.ofReal (k z) * Ψ (V z) := by
    have := lintegral_withDensity_eq_lintegral_mul volume hfm.coe_nnreal_ennreal (hΨm.comp hVm)
    exact this
  have hfin' : ∫⁻ z, Ψ (V z) ∂μ ≠ ⊤ := by rw [hlin]; exact hfin.ne
  have hgi : Integrable (g ∘ V) μ :=
    integrable_toReal_of_lintegral_ne_top (hΨm.comp hVm).aemeasurable hfin'
  have hjensen := hgconv.map_integral_le hgcont hSc hVSμ hVint hgi
  have hfinV : ∀ᵐ z ∂μ, Ψ (V z) < ⊤ := hVSμ.mono fun z hz => hSdom hz
  have hint : ∫ z, g (V z) ∂μ = (∫⁻ z, Ψ (V z) ∂μ).toReal :=
    integral_toReal (hΨm.comp hVm).aemeasurable hfinV
  rw [hint] at hjensen
  rw [hconv, ← hlin, ← ENNReal.ofReal_toReal (hSdom hmem : Ψ _ < ⊤).ne,
    ← ENNReal.ofReal_toReal hfin']
  exact ENNReal.ofReal_le_ofReal hjensen

/-- The bump of outer radius `r` and inner radius `r/2`. -/
noncomputable def halfBump {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : Sp N) :=
  ⟨r / 2, r, half_pos hr, half_lt_self hr⟩

/-- Contraction of a mollification: `f(x) = t s (η ⋆ u)(x / s)`. -/
noncomputable def contrMoll (η : ContDiffBump (0 : Sp N)) (u : Sp N → Tgt m) (t s : ℝ) :
    Sp N → Tgt m :=
  fun x => (t * s) • (η.normed volume ⋆[lsmul ℝ ℝ, volume] u) (s⁻¹ • x)

/-- `contrMoll` is smooth. -/
theorem contDiff_contrMoll (η : ContDiffBump (0 : Sp N)) {u : Sp N → Tgt m}
    (hu : LocallyIntegrable u volume) (t s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (contrMoll η u t s) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (η.normed volume ⋆[lsmul ℝ ℝ, volume] u) :=
    η.hasCompactSupport_normed.contDiff_convolution_left _ η.contDiff_normed hu
  exact (contDiff_const (c := t * s)).smul (hv.comp (contDiff_const_smul s⁻¹))

/-- The gradient of `contrMoll`: `∇f(x) = t (η ⋆ ∇u)(x / s)` for `u ∈ W^{1,p}_0` of a cube. -/
theorem fderiv_contrMoll {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    (η : ContDiffBump (0 : Sp N)) (t : ℝ) {s : ℝ} (hs : s ≠ 0) (x : Sp N) :
    fderiv ℝ (contrMoll η u.1 t s) x =
      t • (η.normed volume ⋆[lsmul ℝ ℝ, volume] u.2) (s⁻¹ • x) := by
  set v := η.normed volume ⋆[lsmul ℝ ℝ, volume] u.1
  have e : contrMoll η u.1 t s = t • fun z => (s⁻¹)⁻¹ • v (s⁻¹ • z) := by
    funext z
    simp only [contrMoll, Pi.smul_apply, inv_inv, v]
    rw [smul_smul]
  rw [e, fderiv_const_smul_field, Pi.smul_apply, fderiv_rescale v (inv_ne_zero hs),
    W1p0.fderiv_convolution_eq_convolution_grad hp hu]

/-- Support of `contrMoll`: inside `cube (s (ρ + 2 rOut)) 0` for `u` vanishing off `cube ρ 0`. -/
theorem support_contrMoll_subset {ρ : ℝ} {u : Sp N → Tgt m} (hzero : ∀ y ∉ cube ρ 0, u y = 0)
    (η : ContDiffBump (0 : Sp N)) (t : ℝ) {s : ℝ} (hs : 0 < s) :
    support (contrMoll η u t s) ⊆ cube (s * (ρ + 2 * η.rOut)) 0 := by
  intro x hx
  have h1 : s⁻¹ • x ∈ support (η.normed volume ⋆[lsmul ℝ ℝ, volume] u) := by
    intro h0; apply hx; simp only [contrMoll, h0, smul_zero]
  have h2 := W1p0.convolution_support_subset_enlarged_cube hzero η h1
  have hpre := preimage_smul_cube (inv_pos.2 hs) (ρ + 2 * η.rOut) (0 : Sp N)
  have hx' : x ∈ (s⁻¹ • ·) ⁻¹' cube (ρ + 2 * η.rOut) (0 : Sp N) := h2
  rw [hpre, smul_zero, div_inv_eq_mul, mul_comm] at hx'
  exact hx'

/-- The weak gradient of `u ∈ W^{1,p}_0(Q)` vanishes a.e. off `Q` (`Q` a cube). -/
theorem W1p0.grad_ae_eq_zero_off_cube {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0)) :
    ∀ᵐ z ∂volume, z ∉ cube ρ (0 : Sp N) → u.2 z = 0 := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  have hB : IsOpen (closure (cube ρ (0 : Sp N)))ᶜ := isClosed_closure.isOpen_compl
  have hzero : u.1 =ᵐ[volume.restrict (closure (cube ρ (0 : Sp N)))ᶜ] 0 :=
    (ae_restrict_iff' hB.measurableSet).2 (Eventually.of_forall fun z hz =>
      hu.1 z fun h => hz (subset_closure h))
  have h := HasWeakGrad.eq_zero_on_open hB hzero hu.2.2.1 hu.2.2.2
  have hfr : ∀ᵐ z ∂volume, z ∉ frontier (cube ρ (0 : Sp N)) := by
    rw [ae_iff]; simpa using volume_frontier_cube ρ (0 : Sp N)
  filter_upwards [h, hfr] with z hz hzf hzQ
  refine hz fun hcl => hzf ⟨hcl, ?_⟩
  rwa [(isOpen_cube ρ 0).interior_eq]

/-- If `∫_Q Ψ(∇u) < ∞` and `Ψ(0) < ∞`, then `∇u ∈ dom Ψ` a.e. on `ℝᴺ`. -/
theorem W1p0.ae_mem_dom {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    {Ψ : Mat m N → ℝ≥0∞} (hΨm : Measurable Ψ) (hΨ0 : Ψ 0 < ⊤)
    (hE : ∫⁻ z in cube ρ 0, Ψ (u.2 z) < ⊤) : ∀ᵐ z ∂volume, u.2 z ∈ dom Ψ := by
  have hm : AEMeasurable (fun z => Ψ (u.2 z)) (volume.restrict (cube ρ (0 : Sp N))) :=
    hΨm.comp_aemeasurable (hu.2.2.1.aestronglyMeasurable.aemeasurable.restrict)
  have h1 := ae_lt_top' hm hE.ne
  have h1' : ∀ᵐ z ∂volume, z ∈ cube ρ (0 : Sp N) → Ψ (u.2 z) < ⊤ :=
    (ae_restrict_iff' (isOpen_cube ρ 0).measurableSet).1 h1
  filter_upwards [h1', W1p0.grad_ae_eq_zero_off_cube hp hu] with z hz hz'
  by_cases hzQ : z ∈ cube ρ (0 : Sp N)
  · exact hz hzQ
  · change Ψ (u.2 z) < ⊤
    rw [hz' hzQ]; exact hΨ0

/-- The measurable modification of the contracted gradient, `V = t ∇u`. -/
noncomputable def contrGrad {p : ℝ} {ρ : ℝ} {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0)) (t : ℝ) : Sp N → Mat m N :=
  fun z => t • hu.2.2.1.aestronglyMeasurable.mk u.2 z

/-- `contrGrad` is measurable. -/
theorem measurable_contrGrad {p ρ : ℝ} {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0)) (t : ℝ) : Measurable (contrGrad hu t) :=
  (hu.2.2.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable).const_smul t

/-- `contrGrad hu t = t ∇u` a.e. -/
theorem contrGrad_ae_eq {p ρ : ℝ} {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0)) (t : ℝ) :
    contrGrad hu t =ᵐ[volume] fun z => t • u.2 z := by
  filter_upwards [hu.2.2.1.aestronglyMeasurable.ae_eq_mk] with z hz
  simp only [contrGrad, ← hz]

/-- `contrGrad` is locally integrable. -/
theorem locallyIntegrable_contrGrad {p ρ : ℝ} (hp : 1 ≤ p)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    (t : ℝ) : LocallyIntegrable (contrGrad hu t) volume := by
  have h1 : LocallyIntegrable u.2 volume :=
    hu.2.2.1.locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hp)
  exact (h1.smul t).congr (contrGrad_ae_eq hu t).symm

/-- `∇(contrMoll)(x) = (η ⋆ V)(x / s)` with `V = t ∇u`. -/
theorem fderiv_contrMoll_eq_conv {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    (η : ContDiffBump (0 : Sp N)) (t : ℝ) {s : ℝ} (hs : s ≠ 0) (x : Sp N) :
    fderiv ℝ (contrMoll η u.1 t s) x =
      (η.normed volume ⋆[lsmul ℝ ℝ, volume] contrGrad hu t) (s⁻¹ • x) := by
  rw [fderiv_contrMoll hp hu η t hs x, convolution_eq_swap, convolution_eq_swap,
    ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [contrGrad_ae_eq hu t] with z hz
  simp only [lsmul_apply, hz, smul_comm t]

/-- `∫_K Ψ(t ∇u) ≤ t (∫_Q Ψ(∇u) + Ψ(0) |K \ Q|) + (1 - t) Ψ(0) |K|`. -/
theorem lintegral_contrGrad_le {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ) {t : ℝ≥0} (ht1 : t ≤ 1) {K : Set (Sp N)}
    (hK : MeasurableSet K) :
    ∫⁻ z in K, Ψ (contrGrad hu t z) ≤
      t * ((∫⁻ z in cube ρ 0, Ψ (u.2 z)) + Ψ 0 * volume (K \ cube ρ 0)) +
        (1 - t : ℝ≥0) * Ψ 0 * volume K := by
  have hpt : ∀ z, Ψ (contrGrad hu t z) ≤
      t * Ψ (hu.2.2.1.aestronglyMeasurable.mk u.2 z) + (1 - t : ℝ≥0) * Ψ 0 := by
    intro z
    have := hΨ (hu.2.2.1.aestronglyMeasurable.mk u.2 z) 0 t ht1
    simpa [contrGrad] using this
  have hmk : ∫⁻ z in K, Ψ (hu.2.2.1.aestronglyMeasurable.mk u.2 z) =
      ∫⁻ z in K, Ψ (u.2 z) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hu.2.2.1.aestronglyMeasurable.ae_eq_mk] with z hz
    rw [hz]
  have hzero := W1p0.grad_ae_eq_zero_off_cube hp hu
  have hsplit : ∫⁻ z in K, Ψ (u.2 z) ≤
      (∫⁻ z in cube ρ 0, Ψ (u.2 z)) + Ψ 0 * volume (K \ cube ρ 0) := by
    rw [← lintegral_inter_add_sdiff _ K (isOpen_cube ρ (0 : Sp N)).measurableSet]
    refine add_le_add ?_ (le_of_eq ?_)
    · exact lintegral_mono_set inter_subset_right
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun_ae (hK.diff (isOpen_cube ρ 0).measurableSet) ?_
    filter_upwards [hzero] with z hz hzK
    rw [hz hzK.2]
  calc ∫⁻ z in K, Ψ (contrGrad hu t z)
      ≤ ∫⁻ z in K, (t * Ψ (hu.2.2.1.aestronglyMeasurable.mk u.2 z) + (1 - t : ℝ≥0) * Ψ 0) :=
        lintegral_mono fun z => hpt z
    _ = t * (∫⁻ z in K, Ψ (u.2 z)) + (1 - t : ℝ≥0) * Ψ 0 * volume K := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          hmk, setLIntegral_const]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hsplit) le_rfl

/-- The closed convex set `t · cl(dom Ψ) ⊆ int(dom Ψ)` for `t ∈ [0,1[`. -/
theorem ConvexENN.smul_closure_dom {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ)
    (h0 : (0 : Mat m N) ∈ interior (dom Ψ)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IsClosed (t • closure (dom Ψ)) ∧ Convex ℝ (t • closure (dom Ψ)) ∧
      t • closure (dom Ψ) ⊆ interior (dom Ψ) := by
  refine ⟨isClosed_closure.smul₀ t, hΨ.convex_dom.closure.smul t, ?_⟩
  rintro _ ⟨ξ, hξ, rfl⟩
  exact hΨ.smul_mem_interior_dom h0 hξ ht0 ht1

/-- `V = t ∇u` takes values in `t · cl(dom Ψ)` a.e. -/
theorem contrGrad_ae_mem {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    {Ψ : Mat m N → ℝ≥0∞} (hΨm : Measurable Ψ) (hΨ0 : Ψ 0 < ⊤)
    (hE : ∫⁻ z in cube ρ 0, Ψ (u.2 z) < ⊤) (t : ℝ) :
    ∀ᵐ z ∂volume, contrGrad hu t z ∈ t • closure (dom Ψ) := by
  filter_upwards [W1p0.ae_mem_dom hp hu hΨm hΨ0 hE, contrGrad_ae_eq hu t] with z hz hz'
  rw [hz']
  exact smul_mem_smul_set (subset_closure hz)

/-- `∫_{C} ∫ η(y - z) F(z) dz dy ≤ ∫_{C'} F` when the `rOut`-neighbourhood of `C` lies in `C'`:
here `C = cube a 0`, `C' = cube (a + 2 rOut) 0`. -/
theorem lintegral_bump_conv_le (η : ContDiffBump (0 : Sp N)) {F : Sp N → ℝ≥0∞}
    (hF : Measurable F) (a : ℝ) :
    ∫⁻ y in cube a 0, ∫⁻ z, ENNReal.ofReal (η.normed volume (y - z)) * F z ≤
      ∫⁻ z in cube (a + 2 * η.rOut) 0, F z := by
  have hk : Measurable fun q : Sp N × Sp N => ENNReal.ofReal (η.normed volume (q.1 - q.2)) :=
    ENNReal.measurable_ofReal.comp ((η.continuous_normed).comp
      (continuous_fst.sub continuous_snd)).measurable
  rw [lintegral_lintegral_swap ((hk.mul (hF.comp measurable_snd)).aemeasurable)]
  rw [← lintegral_indicator (isOpen_cube _ _).measurableSet]
  refine lintegral_mono fun z => ?_
  have hkz : Measurable fun y : Sp N => ENNReal.ofReal (η.normed volume (y - z)) :=
    ENNReal.measurable_ofReal.comp ((η.continuous_normed).comp
      (continuous_id.sub continuous_const)).measurable
  rw [lintegral_mul_const _ hkz]
  by_cases hz : z ∈ cube (a + 2 * η.rOut) (0 : Sp N)
  · rw [indicator_of_mem hz]
    refine mul_le_of_le_one_left (zero_le) ?_
    calc ∫⁻ y in cube a 0, ENNReal.ofReal (η.normed volume (y - z))
        ≤ ∫⁻ y, ENNReal.ofReal (η.normed volume (y - z)) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ y, ENNReal.ofReal (η.normed volume y) :=
          lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (η.normed volume y)) z
      _ = 1 := by
          rw [← ofReal_integral_eq_lintegral_ofReal (η.integrable_normed)
            (Eventually.of_forall fun y => ContDiffBump.nonneg_normed _ _),
            ContDiffBump.integral_normed, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]
    have h0 : ∀ y ∈ cube a (0 : Sp N), η.normed volume (y - z) = 0 := by
      intro y hy
      rw [← notMem_support, ContDiffBump.support_normed_eq, mem_ball, dist_zero_right, not_lt]
      simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, Pi.zero_apply, zero_sub,
        zero_add, not_forall, not_and_or, not_lt] at hz hy
      obtain ⟨i, hi⟩ := hz
      have hyi := hy i
      have hr := η.rOut_pos
      refine le_trans ?_ (norm_le_pi_norm (y - z) i)
      rw [Pi.sub_apply, Real.norm_eq_abs]
      rcases hi with hi | hi
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    rw [setLIntegral_congr_fun (isOpen_cube _ _).measurableSet (g := fun _ => 0)
      (fun y hy => by simp [h0 y hy]), lintegral_zero, zero_mul]

/-- **Energy bound for `contrMoll`.** With `s = ρ/(ρ+3r)`,
`∫_Q Ψ(∇f) ≤ t (∫_Q Ψ(∇u) + Ψ(0)|Q₅ \ Q|) + (1-t) Ψ(0) |Q₅|`, `Q₅ = cube (ρ + 5r) 0`. -/
theorem lintegral_contrMoll_le {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ} (hρ : 0 < ρ)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ) (hΨm : Measurable Ψ)
    (h0 : (0 : Mat m N) ∈ interior (dom Ψ)) (hE : ∫⁻ z in cube ρ 0, Ψ (u.2 z) < ⊤)
    {t : ℝ≥0} (ht1 : t < 1) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (contrMoll (halfBump hr) u.1 t (ρ / (ρ + 3 * r))) x) ≤
      t * ((∫⁻ z in cube ρ 0, Ψ (u.2 z)) +
          Ψ 0 * volume (cube (ρ + 5 * r) (0 : Sp N) \ cube ρ 0)) +
        (1 - t : ℝ≥0) * Ψ 0 * volume (cube (ρ + 5 * r) (0 : Sp N)) := by
  set s : ℝ := ρ / (ρ + 3 * r)
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  set η := halfBump (N := N) hr
  have hηr : η.rOut = r := rfl
  set V := contrGrad hu t
  have hΨ0 : Ψ 0 < ⊤ := (interior_subset h0 : (0 : Mat m N) ∈ dom Ψ)
  obtain ⟨hSc, hSconv, hSint⟩ := hΨ.smul_closure_dom h0 (t := t) t.2 (by exact_mod_cast ht1)
  have hVS := contrGrad_ae_mem hp hu hΨm hΨ0 hE t
  have hVloc := locallyIntegrable_contrGrad hp hu t
  have hVm := measurable_contrGrad hu t
  set F : Sp N → ℝ≥0∞ := fun y => Ψ ((η.normed volume ⋆[lsmul ℝ ℝ, volume] V) y)
  -- change of variables
  have hcv : ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (contrMoll η u.1 t s) x) ≤
      ∫⁻ y in cube (ρ + 3 * r) 0, F y := by
    have hpre : (s⁻¹ • ·) ⁻¹' cube (ρ + 3 * r) (0 : Sp N) = cube ρ 0 := by
      rw [preimage_smul_cube (inv_pos.2 hs), smul_zero, div_inv_eq_mul]
      congr 1
      simp only [s]; field_simp
    have h := setLIntegral_comp_smul (inv_ne_zero hs.ne')
      (isOpen_cube (ρ + 3 * r) (0 : Sp N)).measurableSet F
    rw [hpre] at h
    calc ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (contrMoll η u.1 t s) x)
        = ∫⁻ x in cube ρ 0, F (s⁻¹ • x) := by
          refine setLIntegral_congr_fun (isOpen_cube _ _).measurableSet fun x _ => ?_
          simp only [F, V]
          rw [fderiv_contrMoll_eq_conv hp hu η t hs.ne' x]
      _ = ENNReal.ofReal |((s⁻¹) ^ N)⁻¹| * ∫⁻ y in cube (ρ + 3 * r) 0, F y := h
      _ ≤ 1 * ∫⁻ y in cube (ρ + 3 * r) 0, F y := by
          gcongr
          rw [inv_pow, inv_inv, abs_of_pos (pow_pos hs N)]
          exact ENNReal.ofReal_le_one.2 (pow_le_one₀ hs.le hs1)
      _ = _ := one_mul _
  -- Jensen
  have hjen : ∀ y, F y ≤ ∫⁻ z, ENNReal.ofReal (η.normed volume (y - z)) * Ψ (V z) := by
    intro y
    by_cases hfin : ∫⁻ z, ENNReal.ofReal (η.normed volume (y - z)) * Ψ (V z) < ⊤
    · exact (hΨ.bump_convolution_le hΨm hSc hSconv hSint η hVm hVloc hVS y hfin).2
    · rw [not_lt, top_le_iff] at hfin; rw [hfin]; exact le_top
  calc ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (contrMoll η u.1 t s) x)
      ≤ ∫⁻ y in cube (ρ + 3 * r) 0, F y := hcv
    _ ≤ ∫⁻ y in cube (ρ + 3 * r) 0, ∫⁻ z, ENNReal.ofReal (η.normed volume (y - z)) * Ψ (V z) :=
        lintegral_mono fun y => hjen y
    _ ≤ ∫⁻ z in cube (ρ + 3 * r + 2 * η.rOut) 0, Ψ (V z) :=
        lintegral_bump_conv_le η (hΨm.comp hVm) _
    _ = ∫⁻ z in cube (ρ + 5 * r) 0, Ψ (V z) := by rw [hηr]; ring_nf
    _ ≤ _ := lintegral_contrGrad_le hp hu hΨ ht1.le (isOpen_cube _ _).measurableSet

/-- `contrMoll` has compact support inside `cube ρ 0`. -/
theorem tsupport_contrMoll_subset {ρ : ℝ} (hρ : 0 < ρ) {u : Sp N → Tgt m}
    (hzero : ∀ y ∉ cube ρ 0, u y = 0) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasCompactSupport (contrMoll (halfBump hr) u t (ρ / (ρ + 3 * r))) ∧
      tsupport (contrMoll (halfBump hr) u t (ρ / (ρ + 3 * r))) ⊆ cube ρ 0 := by
  set s : ℝ := ρ / (ρ + 3 * r)
  have hs : 0 < s := by positivity
  set c : ℝ := s * (ρ + 2 * (halfBump (N := N) hr).rOut)
  have hc : c < ρ := by
    simp only [c, s, halfBump]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hsupp := support_contrMoll_subset hzero (halfBump hr) t hs
  have hcl : tsupport (contrMoll (halfBump hr) u t s) ⊆
      Set.pi univ fun i => Icc ((0 : Sp N) i - c / 2) ((0 : Sp N) i + c / 2) :=
    closure_minimal (hsupp.trans (cube_subset_pi_Icc c 0))
      (isClosed_set_pi fun _ _ => isClosed_Icc)
  refine ⟨IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc)
    (isClosed_tsupport _) hcl, hcl.trans fun y hy i _ => ?_⟩
  have := hy i (mem_univ i)
  simp only [Pi.zero_apply, zero_sub, zero_add, mem_Icc] at this
  simp only [Pi.zero_apply, zero_sub, zero_add, mem_Ioo]
  constructor <;> linarith [this.1, this.2]

/-- **Smooth approximation with energy convergence (step 2).** For `Q = cube ρ 0`,
`Ψ` convex, lower semicontinuous with `0 ∈ int(dom Ψ)`, and `u ∈ W^{1,p}_0(Q)` with
`∫_Q Ψ(∇u) < ∞`, there are `fₙ` of class `C¹`, with compact support in `Q`, gradients in
`tₙ · cl(dom Ψ)` (`tₙ < 1`), `∇fₙ → ∇u` a.e. on `Q`, and `∫_Q Ψ(∇fₙ) → ∫_Q Ψ(∇u)`. -/
theorem exists_smooth_approx_W1p0 {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ} (hρ : 0 < ρ)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ) (hΨlsc : LowerSemicontinuous Ψ)
    (h0 : (0 : Mat m N) ∈ interior (dom Ψ)) (hE : ∫⁻ z in cube ρ 0, Ψ (u.2 z) < ⊤) :
    ∃ (f : ℕ → Sp N → Tgt m) (t : ℕ → ℝ≥0), (∀ n, t n < 1) ∧ (∀ n, ContDiff ℝ 1 (f n)) ∧
      (∀ n, HasCompactSupport (f n)) ∧ (∀ n, tsupport (f n) ⊆ cube ρ 0) ∧
      (∀ n x, fderiv ℝ (f n) x ∈ (t n : ℝ) • closure (dom Ψ)) ∧
      (∀ᵐ x ∂volume.restrict (cube ρ 0),
        Tendsto (fun n => fderiv ℝ (f n) x) atTop (𝓝 (u.2 x))) ∧
      Tendsto (fun n => ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x)) atTop
        (𝓝 (∫⁻ x in cube ρ 0, Ψ (u.2 x))) := by
  have hΨm : Measurable Ψ := hΨlsc.measurable
  have hΨ0 : Ψ 0 < ⊤ := (interior_subset h0 : (0 : Mat m N) ∈ dom Ψ)
  set r : ℕ → ℝ := fun n => ρ / ((n : ℝ) + 2)
  have hr : ∀ n, 0 < r n := fun n => by positivity
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hr0 : Tendsto r atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have htR0 : ∀ n : ℕ, 0 ≤ 1 - 1 / ((n : ℝ) + 2) := fun n => by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set t : ℕ → ℝ≥0 := fun n => Real.toNNReal (1 - 1 / ((n : ℝ) + 2))
  have htcoe : ∀ n, (t n : ℝ) = 1 - 1 / ((n : ℝ) + 2) := fun n => Real.coe_toNNReal _ (htR0 n)
  have ht1 : ∀ n, t n < 1 := fun n => by
    rw [← NNReal.coe_lt_coe, htcoe, NNReal.coe_one]
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have ht : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    rw [sub_zero] at this
    exact this.congr fun n => (htcoe n).symm
  set s : ℕ → ℝ := fun n => ρ / (ρ + 3 * r n)
  have hs : ∀ n, 0 < s n := fun n => by have := hr n; positivity
  set f : ℕ → Sp N → Tgt m := fun n => contrMoll (halfBump (hr n)) u.1 (t n) (s n)
  have hloc1 : LocallyIntegrable u.1 volume :=
    hu.2.1.locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hp)
  have hloc2 : LocallyIntegrable u.2 volume :=
    hu.2.2.1.locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hp)
  have hfd : ∀ n x, fderiv ℝ (f n) x =
      (t n : ℝ) • ((halfBump (hr n)).normed volume ⋆[lsmul ℝ ℝ, volume] u.2)
        ((s n)⁻¹ • x) := fun n x => fderiv_contrMoll hp hu _ _ (hs n).ne' x
  -- a.e. convergence of the gradients
  have hae : ∀ᵐ x ∂volume.restrict (cube ρ 0),
      Tendsto (fun n => fderiv ℝ (f n) x) atTop (𝓝 (u.2 x)) := by
    have hJ := ae_tendsto_bump_convolution_moving hloc2 2 3
    filter_upwards [ae_restrict_of_ae hJ, ae_restrict_mem (isOpen_cube ρ (0 : Sp N)).measurableSet]
      with x hx hxQ
    have hxρ : ‖x‖ ≤ ρ := by
      refine (pi_norm_le_iff_of_nonneg hρ.le).2 fun i => ?_
      have := hxQ i (mem_univ i)
      simp only [Pi.zero_apply, zero_sub, zero_add, mem_Ioo] at this
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
    have hconv := hx (fun n => halfBump (hr n)) (fun n => (s n)⁻¹ • x) hr0
      (Eventually.of_forall fun n => by simp [halfBump]; linarith [hr n])
      (Eventually.of_forall fun n => by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsinv : (s n)⁻¹ = 1 + 3 * r n / ρ := by
          simp only [s]; field_simp
        have e : x - (s n)⁻¹ • x = -((3 * r n / ρ) • x) := by
          rw [hsinv, add_smul, one_smul]; abel
        rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by have := hr n; positivity)]
        change 3 * r n / ρ * ‖x‖ ≤ 3 * r n
        rw [div_mul_eq_mul_div, div_le_iff₀ hρ]
        nlinarith [hr n])
    have := ht.smul hconv
    rw [one_smul] at this
    exact this.congr fun n => (hfd n x).symm
  -- energy convergence
  set E := ∫⁻ z in cube ρ 0, Ψ (u.2 z)
  set B : ℕ → ℝ≥0∞ := fun n => (t n : ℝ≥0∞) *
      (E + Ψ 0 * volume (cube (ρ + 5 * r n) (0 : Sp N) \ cube ρ 0)) +
    ((1 - t n : ℝ≥0) : ℝ≥0∞) * Ψ 0 * volume (cube (ρ + 5 * r n) (0 : Sp N))
  have hupper : ∀ n, ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x) ≤ B n := fun n =>
    lintegral_contrMoll_le hp hρ hu hΨ hΨm h0 hE (ht1 n) (hr n)
  have hvolC : Tendsto (fun n => volume (cube (ρ + 5 * r n) (0 : Sp N))) atTop
      (𝓝 (volume (cube ρ (0 : Sp N)))) := by
    simp only [volume_cube]
    have h1 : Tendsto (fun n => ρ + 5 * r n) atTop (𝓝 (ρ + 5 * 0)) :=
      tendsto_const_nhds.add (hr0.const_mul 5)
    rw [mul_zero, add_zero] at h1
    exact ENNReal.Tendsto.pow ((ENNReal.continuous_ofReal.tendsto ρ).comp h1)
  have hQfin : volume (cube ρ (0 : Sp N)) ≠ ⊤ := (isBounded_cube _ _).measure_lt_top.ne
  have hvolD : Tendsto (fun n => volume (cube (ρ + 5 * r n) (0 : Sp N) \ cube ρ 0)) atTop
      (𝓝 0) := by
    have hsub : ∀ n, cube ρ (0 : Sp N) ⊆ cube (ρ + 5 * r n) 0 := fun n =>
      SubaddCube.cube_subset_cube (by linarith [hr n]) 0
    have h := ENNReal.Tendsto.sub hvolC (tendsto_const_nhds (x := volume (cube ρ (0 : Sp N))))
      (Or.inr hQfin)
    rw [tsub_self] at h
    refine h.congr fun n => ?_
    rw [measure_sdiff (hsub n) (isOpen_cube _ _).measurableSet.nullMeasurableSet hQfin]
  have htN : Tendsto t atTop (𝓝 1) := by
    rw [← NNReal.tendsto_coe]; simpa using ht
  have htE : Tendsto (fun n => (t n : ℝ≥0∞)) atTop (𝓝 1) := by
    have := ENNReal.tendsto_coe.2 htN; simpa using this
  have h1tE : Tendsto (fun n => ((1 - t n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    have h : Tendsto (fun n => (1 - t n : ℝ≥0)) atTop (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub htN
    rw [tsub_self] at h
    have := ENNReal.tendsto_coe.2 h; simpa using this
  have hB : Tendsto B atTop (𝓝 E) := by
    have h1 : Tendsto (fun n => E + Ψ 0 * volume (cube (ρ + 5 * r n) (0 : Sp N) \ cube ρ 0))
        atTop (𝓝 (E + Ψ 0 * 0)) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hvolD (Or.inr hΨ0.ne))
    rw [mul_zero, add_zero] at h1
    have h2 := ENNReal.Tendsto.mul htE (Or.inr hE.ne) h1 (Or.inr ENNReal.one_ne_top)
    rw [one_mul] at h2
    have h3 : Tendsto (fun n => ((1 - t n : ℝ≥0) : ℝ≥0∞) * Ψ 0) atTop (𝓝 (0 * Ψ 0)) :=
      ENNReal.Tendsto.mul_const h1tE (Or.inr hΨ0.ne)
    rw [zero_mul] at h3
    have h4 := ENNReal.Tendsto.mul h3 (Or.inr hQfin) hvolC (Or.inr ENNReal.zero_ne_top)
    rw [zero_mul] at h4
    have := h2.add h4
    rwa [add_zero] at this
  have hlimsup : limsup (fun n => ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x)) atTop ≤ E :=
    (limsup_le_limsup (Eventually.of_forall hupper)).trans hB.limsup_eq.le
  have hliminf : E ≤ liminf (fun n => ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x)) atTop := by
    calc E ≤ ∫⁻ x in cube ρ 0, liminf (fun n => Ψ (fderiv ℝ (f n) x)) atTop := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with x hx
          refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
          exact le_liminf_of_le (by isBoundedDefault)
            ((hx.eventually (hΨlsc _ y hy)).mono fun _ h => h.le)
      _ ≤ _ := lintegral_liminf_le fun n => hΨm.comp (measurable_fderiv ℝ (f n))
  have hS := fun n => hΨ.smul_closure_dom h0 (t := t n) (t n).2 (by exact_mod_cast ht1 n)
  refine ⟨f, t, ht1, fun n => ?_, fun n => (tsupport_contrMoll_subset hρ hu.1 (hr n) _).1,
    fun n => (tsupport_contrMoll_subset hρ hu.1 (hr n) _).2, fun n x => ?_, hae,
    tendsto_of_le_liminf_of_limsup_le hliminf hlimsup⟩
  · exact (contDiff_contrMoll _ hloc1 _ _).of_le (by exact_mod_cast le_top)
  · rw [fderiv_contrMoll_eq_conv hp hu _ _ (hs n).ne' x]
    exact bump_convolution_mem (hS n).1 (hS n).2.1 _ (locallyIntegrable_contrGrad hp hu _)
      (contrGrad_ae_mem hp hu hΨm hΨ0 hE _) _

end Homogenization
