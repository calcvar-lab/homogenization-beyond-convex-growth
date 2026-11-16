import Homogenization.Poincare
import Homogenization.Jensen
import Homogenization.UpperBound
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth approximation preparatory results

This file records convolution facts for a `W1p0` pair. It proves the pointwise derivative identity
between the mollification and the convolution of the weak gradient, localization of the convolution
support in an enlarged cube, and almost-everywhere convergence of both components for shrinking
normalized bumps. It also proves contraction of the global `Lᵖ` energy under convolution and
Poincaré's inequality for arbitrary `W1p0` pairs on cubes. It does not prove `Lᵖ` convergence of
general correction sequences with a uniform bound on their gradient energies.
-/

open MeasureTheory
open Filter
open TopologicalSpace
open Set Function
open scoped ENNReal Convolution Topology

namespace Homogenization

variable {N m : ℕ}

/-- The `p`th power of a norm is convex when `p ≥ 1`. -/
theorem convexOn_univ_norm_rpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ) (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun z : E => ‖z‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hpow := (convexOn_rpow hp).2 (norm_nonneg u) (norm_nonneg v) ha hb hab
  have hnorm : ‖a • u + b • v‖ ≤ a * ‖u‖ + b * ‖v‖ := by
    calc
      ‖a • u + b • v‖ ≤ ‖a • u‖ + ‖b • v‖ := norm_add_le _ _
      _ = a * ‖u‖ + b * ‖v‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hmono := Real.monotoneOn_rpow_Ici_of_exponent_nonneg
    (le_trans (by positivity) hp)
  have hpow' : (a * ‖u‖ + b * ‖v‖) ^ p ≤ a * ‖u‖ ^ p + b * ‖v‖ ^ p := by
    simpa [smul_eq_mul] using hpow
  have hmono' : ‖a • u + b • v‖ ^ p ≤ (a * ‖u‖ + b * ‖v‖) ^ p :=
    hmono (norm_nonneg _) (Set.mem_Ici.mpr (by positivity)) hnorm
  exact hmono'.trans hpow'

/-- Jensen's inequality for the `p`th power of the norm, in a form used for probability
measures obtained by normalizing the mollifier. -/
theorem norm_rpow_integral_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → E} {p : ℝ} (hp : 1 ≤ p) (hf : Integrable f μ)
    (hfp : Integrable (fun y => ‖f y‖ ^ p) μ) :
    ‖∫ y, f y ∂μ‖ ^ p ≤ ∫ y, ‖f y‖ ^ p ∂μ := by
  have hcont : Continuous (fun z : E => ‖z‖ ^ p) :=
    (Real.continuous_rpow_const (le_trans (by norm_num) hp)).comp continuous_norm
  exact (convexOn_univ_norm_rpow p hp).map_integral_le hcont.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hf hfp

/-- Jensen's estimate at a point for convolution with a normalized bump. The probability measure
is the measure with density `η.normed`; normalization, integrability of the translated function,
and integrability of its `p`th norm power all follow from the bump and the global `MemLp` bound. -/
theorem W1p0.convolution_norm_rpow_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ} (hp : 1 ≤ p)
    {g : Sp N → E} (hg : MemLp g (ENNReal.ofReal p) volume)
    (η : ContDiffBump (0 : Sp N)) (x : Sp N) :
    ‖((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x‖ₑ ^ p ≤
      ∫⁻ y, ‖g (x - y)‖ₑ ^ p ∂(volume.withDensity
        (fun y => ENNReal.ofReal (η.normed volume y))) := by
  let k : Sp N → ℝ := η.normed volume
  let d : Sp N → ℝ≥0∞ := fun y => ENNReal.ofReal (k y)
  let ν : Measure (Sp N) := volume.withDensity d
  have hkcont : Continuous k := η.continuous_normed
  have hknonneg : ∀ y, 0 ≤ k y := η.nonneg_normed
  have hdmeas : Measurable d := ENNReal.measurable_ofReal.comp hkcont.measurable
  have hdlt : ∀ᵐ y ∂volume, d y < ⊤ :=
    Eventually.of_forall fun y => ENNReal.ofReal_lt_top
  have hp0 : 0 < p := by linarith
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp)
  have hpENN0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hνmass : ν Set.univ = 1 := by
    change (volume.withDensity d) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal η.integrable_normed
      (Eventually.of_forall hknonneg)]
    simp [η.integral_normed]
  let : IsProbabilityMeasure ν := ⟨hνmass⟩
  have hgLoc : LocallyIntegrable g volume := hg.locallyIntegrable hpENN
  have hconvInt := η.hasCompactSupport_normed.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hkcont hgLoc x
  have hshift : MemLp (fun y => g (x - y)) (ENNReal.ofReal p) volume :=
    hg.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hbase : Integrable (fun y => ‖g (x - y)‖ ^ p) volume := by
    simpa [ENNReal.toReal_ofReal hp0.le] using
      hshift.integrable_norm_rpow hpENN0 ENNReal.ofReal_ne_top
  have hkbdd : BddAbove (Set.range fun y => |k y|) :=
    hkcont.abs.bddAbove_range_of_hasCompactSupport η.hasCompactSupport_normed.norm
  let C : ℝ := ⨆ y, |k y|
  have hC : ∀ y, |k y| ≤ C := fun y => le_ciSup hkbdd y
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg (k 0)) (hC 0)
  have hweighted : Integrable (fun y => k y * ‖g (x - y)‖ ^ p) volume := by
    have hdom : Integrable (fun y => C * ‖g (x - y)‖ ^ p) volume := hbase.const_mul C
    apply hdom.mono'
    · exact hkcont.aestronglyMeasurable.mul hbase.aestronglyMeasurable
    · filter_upwards with y
      have hkn : 0 ≤ k y := hknonneg y
      have hFn : 0 ≤ ‖g (x - y)‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
      have hkC : k y ≤ C := (le_abs_self _).trans (hC y)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hkn hFn)]
      exact mul_le_mul_of_nonneg_right hkC hFn
  have hfi : Integrable (fun y => g (x - y)) ν := by
    rw [integrable_withDensity_iff_integrable_smul' hdmeas hdlt]
    simpa [d, k, ENNReal.toReal_ofReal (hknonneg _)] using hconvInt.integrable
  have hfp : Integrable (fun y => ‖g (x - y)‖ ^ p) ν := by
    rw [integrable_withDensity_iff_integrable_smul' hdmeas hdlt]
    simpa [d, k, ENNReal.toReal_ofReal (hknonneg _), smul_eq_mul] using hweighted
  have hconv_eq :
      ((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x =
        ∫ y, g (x - y) ∂ν := by
    rw [MeasureTheory.convolution_def]
    simpa [ν, d, k, ENNReal.toReal_ofReal (hknonneg _)] using
      (integral_withDensity_eq_integral_toReal_smul hdmeas hdlt
        (fun y => g (x - y))).symm
  have hJ := norm_rpow_integral_le hp hfi hfp
  have hJ' : ENNReal.ofReal (‖∫ y, g (x - y) ∂ν‖ ^ p) ≤
      ENNReal.ofReal (∫ y, ‖g (x - y)‖ ^ p ∂ν) :=
    ENNReal.ofReal_le_ofReal (by simpa [hconv_eq] using hJ)
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le] at hJ'
  rw [ofReal_integral_eq_lintegral_ofReal hfp
    (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg (g (x - y))) _)] at hJ'
  have hrhs : (∫⁻ y, ENNReal.ofReal (‖g (x - y)‖ ^ p) ∂ν) =
      ∫⁻ y, ‖g (x - y)‖ₑ ^ p ∂ν := by
    apply lintegral_congr
    intro y
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ← ofReal_norm]
  rw [hrhs] at hJ'
  simpa [← ofReal_norm, hconv_eq] using hJ'

/-- Convolution by a normalized bump is a contraction for the global `Lᵖ` energy. The pointwise
Jensen estimate is integrated using Tonelli and translation invariance of volume. -/
theorem W1p0.convolution_lintegral_norm_rpow_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ} (hp : 1 ≤ p)
    {g : Sp N → E} (hg : MemLp g (ENNReal.ofReal p) volume)
    (η : ContDiffBump (0 : Sp N)) :
    ∫⁻ x, ‖((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x‖ₑ ^ p ≤
      ∫⁻ x, ‖g x‖ₑ ^ p := by
  calc
    ∫⁻ x, ‖((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x‖ₑ ^ p ≤
        ∫⁻ x, ∫⁻ y, ‖g (x - y)‖ₑ ^ p ∂(volume.withDensity
          (fun y => ENNReal.ofReal (η.normed volume y))) :=
      lintegral_mono fun x => W1p0.convolution_norm_rpow_le hp hg η x
    _ = ∫⁻ y, ∫⁻ x, ‖g (x - y)‖ₑ ^ p ∂volume ∂(volume.withDensity
          (fun y => ENNReal.ofReal (η.normed volume y))) := by
      let ν : Measure (Sp N) := volume.withDensity
        (fun y => ENNReal.ofReal (η.normed volume y))
      have hmeas : AEMeasurable (Function.uncurry fun x y : Sp N => ‖g (x - y)‖ₑ ^ p)
          (volume.prod ν) := by
        have hqmp : Measure.QuasiMeasurePreserving (fun z : Sp N × Sp N => z.1 - z.2)
            (volume.prod ν) volume := by
          refine MeasureTheory.QuasiMeasurePreserving.prod_of_left (by fun_prop)
            (Eventually.of_forall fun y => ?_)
          simpa [Function.comp_def, sub_eq_add_neg, add_comm] using
            (volume.measurePreserving_neg.quasiMeasurePreserving).comp
              (quasiMeasurePreserving_sub_left_of_right_invariant volume y)
        exact (hg.aestronglyMeasurable.enorm.pow_const p).mono_ac hqmp.absolutelyContinuous
          |>.comp_measurable (by fun_prop)
      rw [lintegral_lintegral_swap hmeas]
    _ = ∫⁻ y, ∫⁻ x, ‖g x‖ₑ ^ p ∂volume ∂(volume.withDensity
          (fun y => ENNReal.ofReal (η.normed volume y))) := by
      apply lintegral_congr
      intro y
      let F : Sp N → ℝ≥0∞ := fun z => ‖g z‖ₑ ^ p
      calc
        ∫⁻ x, F (x - y) ∂volume = ∫⁻ x, F (-(y - x)) ∂volume := by
          apply lintegral_congr_ae
          filter_upwards with x
          simp [F, sub_eq_add_neg]
        _ = ∫⁻ x, F (-x) ∂volume := by
          rw [← (volume.measurePreserving_sub_left y).lintegral_comp_emb
            (MeasurableEquiv.subLeft y).measurableEmbedding (fun z => F (-z))]
        _ = ∫⁻ x, F x ∂volume := by
          rw [← volume.measurePreserving_neg.lintegral_comp_emb
            measurableEmbedding_neg F]
    _ = ∫⁻ x, ‖g x‖ₑ ^ p := by
      have hprob : (volume.withDensity (fun y => ENNReal.ofReal (η.normed volume y)))
          Set.univ = 1 := by
        rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
        rw [← ofReal_integral_eq_lintegral_ofReal η.integrable_normed
          (Eventually.of_forall fun y => η.nonneg_normed y)]
        simp [η.integral_normed]
      rw [lintegral_const, hprob]
      simp

/-- The function component of a `W1p0` pair has compactly supported smooth approximants in the
global `Lᵖ` norm when `1 ≤ p < ∞`. This is only an approximation of the function: it does not
identify the derivatives of the approximants with approximations of the weak-gradient component.
The result is Mathlib's `MemLp.exist_eLpNorm_sub_le` applied to the global `MemLp` field in
`W1p0`. -/
theorem W1p0.exists_smooth_compact_approx_function {p : ℝ} (hp : 1 ≤ p)
    {ρ : ℝ} {x : Sp N} {φg : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (h : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Sp N → Tgt m, HasCompactSupport ψ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      eLpNorm (φg.1 - ψ) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ε := by
  rcases h with ⟨_, hφ, _, _⟩
  exact hφ.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top
    (by simpa using (ENNReal.ofReal_le_ofReal hp)) hε

/-- Testing the global weak-gradient identity against a translated normalized bump gives the
integration-by-parts identity needed to identify the derivative of a mollification. This is the
distributional part of the convolution argument; no pointwise or a.e. gradient statement is
asserted here. -/
theorem HasWeakGrad.bump_test_identity {φ : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hweak : HasWeakGrad (Set.univ : Set (Sp N)) φ g)
    (η : ContDiffBump (0 : Sp N)) (x v : Sp N) :
    ∫ y, fderiv ℝ (η.normed volume) (x - y) v • φ y =
      ∫ y, η.normed volume (x - y) • g y v := by
  let k : Sp N → ℝ := η.normed volume
  let ψ : Sp N → ℝ := fun y => k (x - y)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := η.contDiff_normed
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    change ContDiff ℝ (⊤ : ℕ∞) (k ∘ fun y : Sp N => x - y)
    exact hk.comp (contDiff_const.sub contDiff_id)
  have hψcs : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x η.rOut)
    intro y hy
    have hy' : ψ y ≠ 0 := by
      simp only [Function.mem_support] at hy
      exact hy
    have hys : k (x - y) ≠ 0 := by simpa only [ψ] using hy'
    have hball : x - y ∈ Metric.ball (0 : Sp N) η.rOut := by
      have : x - y ∈ Function.support k := by
        simpa only [Function.mem_support] using hys
      simpa [k, η.support_normed_eq] using this
    rw [Metric.mem_closedBall, dist_eq_norm_sub']
    simpa [norm_sub_rev] using (Metric.mem_ball.mp hball).le
  have htest : ∀ y, fderiv ℝ ψ y v = -(fderiv ℝ k (x - y) v) := by
    intro y
    have hsub : HasFDerivAt (fun z : Sp N => x - z)
        (-ContinuousLinearMap.id ℝ (Sp N)) y := by
      exact (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x
    have hkd : HasFDerivAt k (fderiv ℝ k (x - y)) (x - y) :=
      (hk.differentiable (by simp) (x - y)).hasFDerivAt
    have hc := hkd.comp y hsub
    have := congrArg (fun A : Sp N →L[ℝ] ℝ => A v) hc.fderiv
    change fderiv ℝ (k ∘ fun z : Sp N => x - z) y v = _
    simpa [ContinuousLinearMap.comp_apply] using this
  have hts : tsupport ψ ⊆ (Set.univ : Set (Sp N)) := Set.subset_univ _
  have h := hweak ψ hψ hψcs hts v
  rw [show (fun y => fderiv ℝ ψ y v • φ y) =
      fun y => -(fderiv ℝ k (x - y) v • φ y) by
        funext y
        rw [htest y, neg_smul]] at h
  rw [integral_neg] at h
  exact neg_injective h

/-- The derivative of the normalized-bump convolution of a global `W1p0` function is its
normalized-bump convolution with the weak gradient. The proof uses the preceding translated-bump
test identity and the derivative formula for convolution with a compactly supported smooth kernel.
-/
theorem W1p0.fderiv_convolution_eq_convolution_grad {p : ℝ} (hp : 1 ≤ p)
    {ρ : ℝ} {x : Sp N} {φg : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (h : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x)) (η : ContDiffBump (0 : Sp N))
    (z : Sp N) :
    fderiv ℝ (((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1)) z =
      ((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.2) z := by
  rcases h with ⟨_, hφ, hgrad, hweak⟩
  let k : Sp N → ℝ := η.normed volume
  have hkcd : ContDiff ℝ (1 : ℕ∞) k := by
    exact (η.contDiff_normed (μ := volume) (n := ⊤)).of_le
      (show (↑(1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)
  have hkcs : HasCompactSupport k := η.hasCompactSupport_normed
  have hφloc : LocallyIntegrable φg.1 volume := by
    apply hφ.locallyIntegrable
    simpa using (ENNReal.ofReal_le_ofReal hp)
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp)
  have hgLoc : LocallyIntegrable φg.2 volume := hgrad.locallyIntegrable hpENN
  have hderiv := hkcs.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hkcd hφloc z
  have hderiv' := hderiv.fderiv
  ext v i
  have htest := HasWeakGrad.bump_test_identity hweak η z v
  let F : Sp N → Tgt m := fun y => fderiv ℝ k y v • φg.1 (z - y)
  have hchange :
      ∫ y, fderiv ℝ k y v • φg.1 (z - y) =
        ∫ y, fderiv ℝ k (z - y) v • φg.1 y := by
    simpa only [F, sub_sub_cancel] using
      (integral_sub_left_eq_self F volume z).symm
  have hvec := hchange.trans htest
  have hdkcs : HasCompactSupport (fderiv ℝ k) := hkcs.fderiv ℝ
  have hdkcont : Continuous (fderiv ℝ k) := hkcd.continuous_fderiv (by norm_num)
  have hdkconv := hdkcs.convolutionExists_left
    (ContinuousLinearMap.precompL (Sp N) (ContinuousLinearMap.lsmul ℝ ℝ)) hdkcont hφloc z
  have hdkInt : Integrable
      (fun y => (ContinuousLinearMap.precompL (Sp N) (ContinuousLinearMap.lsmul ℝ ℝ)
        (fderiv ℝ k y)) (φg.1 (z - y))) volume := hdkconv.integrable
  have hgconv := hkcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (η.continuous_normed (μ := volume)) hgLoc z
  have hgInt : Integrable (fun y => k y • φg.2 (z - y)) volume := hgconv.integrable
  have hleft :
      (fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1) z) v =
        ∫ y, fderiv ℝ k y v • φg.1 (z - y) := by
    rw [hderiv', MeasureTheory.convolution_def,
      ContinuousLinearMap.integral_apply hdkInt]
    apply integral_congr_ae
    filter_upwards with y
    simp [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  have hright :
      ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.2) z) v =
        ∫ y, k (z - y) • φg.2 y v := by
    rw [MeasureTheory.convolution_lsmul, ContinuousLinearMap.integral_apply hgInt]
    simpa only [smul_apply, sub_sub_cancel] using
      (integral_sub_left_eq_self
        (fun y => k y • (φg.2 (z - y)) v) volume z).symm
  rw [hleft, hright]
  exact congrArg (fun w : Tgt m => w i) hvec

/-- If a function vanishes off a cube, convolution with a normalized bump is supported in the
cube enlarged on each side by the outer radius. This is the support localization needed to apply
`poincare_cube` to mollifications. -/
theorem W1p0.convolution_support_subset_enlarged_cube
    {ρ : ℝ} {x : Sp N} {φ : Sp N → Tgt m}
    (hzero : ∀ y ∉ cube ρ x, φ y = 0) (η : ContDiffBump (0 : Sp N)) :
    Function.support ((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ) ⊆
      cube (ρ + 2 * η.rOut) x := by
  let k : Sp N → ℝ := η.normed volume
  have hk : Function.support k = Metric.ball 0 η.rOut := by
    exact η.support_normed_eq
  have hφ : Function.support φ ⊆ cube ρ x := by
    intro y hy
    by_contra hyc
    have : φ y = 0 := hzero y hyc
    exact hy this
  have hconv := MeasureTheory.support_convolution_subset
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (f := k) (g := φ)
  intro z hz
  rcases Set.mem_add.mp (hconv hz) with ⟨a, ha, b, hb, hab⟩
  have hb' : b ∈ cube ρ x := hφ hb
  have hbpi := Set.mem_pi.mp hb'
  have ha' : a ∈ Metric.ball (0 : Sp N) η.rOut := by
    rwa [hk] at ha
  rw [cube, Set.mem_pi]
  intro i _
  have hai : |a i| < η.rOut := by
    have hi := norm_le_pi_norm a i
    simpa only [Real.norm_eq_abs] using hi.trans_lt (by simpa using ha')
  have hbi := hbpi i (Set.mem_univ i)
  have hbx : |b i - x i| < ρ / 2 := by
    rw [abs_lt]
    constructor <;> linarith [hbi.1, hbi.2]
  have hsum : |a i + (b i - x i)| < η.rOut + ρ / 2 := by
    calc
      |a i + (b i - x i)| ≤ |a i| + |b i - x i| := abs_add_le _ _
      _ < η.rOut + ρ / 2 := add_lt_add hai hbx
  have hsum' := abs_lt.mp hsum
  constructor
  · rw [← hab]
    change x i - (ρ + 2 * η.rOut) / 2 < a i + b i
    nlinarith
  · rw [← hab]
    change a i + b i < x i + (ρ + 2 * η.rOut) / 2
    nlinarith

/-- A normalized bump convolution of a `W1p0` function is globally Lipschitz and vanishes off
the corresponding enlarged cube. Smoothness follows by differentiating the compactly supported
kernel; compact support follows from the support inclusion above and boundedness of cubes. -/
theorem W1p0.exists_lipschitz_convolution {p : ℝ} (hp : 1 ≤ p)
    {ρ : ℝ} {x : Sp N} {φg : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (h : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x)) (η : ContDiffBump (0 : Sp N)) :
    ∃ K : NNReal,
      LipschitzWith K ((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1) ∧
      ∀ y ∉ cube (ρ + 2 * η.rOut) x,
        ((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1) y = 0 := by
  rcases h with ⟨hzero, hφ, _, _⟩
  let k : Sp N → ℝ := η.normed volume
  have hkcd : ContDiff ℝ (⊤ : ℕ∞) k := η.contDiff_normed
  have hkcs : HasCompactSupport k := η.hasCompactSupport_normed
  have hφloc : LocallyIntegrable φg.1 volume := by
    apply hφ.locallyIntegrable
    simpa using (ENNReal.ofReal_le_ofReal hp)
  have hcd : ContDiff ℝ (⊤ : ℕ∞)
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1) :=
    hkcs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hkcd hφloc
  have hsupport := W1p0.convolution_support_subset_enlarged_cube hzero η
  have hcs : HasCompactSupport (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1) :=
    HasCompactSupport.intro (isBounded_cube (ρ + 2 * η.rOut) x).isCompact_closure fun y hy => by
      by_contra hne
      exact hy (subset_closure (hsupport hne))
  obtain ⟨K, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hcd (by simp)
  exact ⟨K, hLip, fun y hy => by
    by_contra hne
    exact hy (hsupport hne)⟩

/-- A sequence of normalized bump convolutions converges almost everywhere to the function
component of a `W1p0` pair, provided the bump supports shrink with uniformly bounded ratio of
outer to inner radius. This is the pointwise convergence input for a Fatou argument; it does not
assert convergence of the weak gradients or an `Lᵖ` contraction estimate. -/
theorem W1p0.ae_tendsto_convolution_function {p : ℝ} (hp : 1 ≤ p)
    {ρ : ℝ} {x : Sp N} {φg : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (h : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x))
    (η : ℕ → ContDiffBump (0 : Sp N))
    (hη : Tendsto (fun n => (η n).rOut) atTop (𝓝 0))
    (hη' : ∀ᶠ n in atTop, (η n).rOut ≤ 2 * (η n).rIn) :
    ∀ᵐ y ∂volume,
      Tendsto (fun n => ((η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        φg.1) y) atTop (𝓝 (φg.1 y)) := by
  rcases h with ⟨_, hφ, _, _⟩
  have hloc : LocallyIntegrable φg.1 volume := by
    apply hφ.locallyIntegrable
    simpa using (ENNReal.ofReal_le_ofReal hp)
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hη hη' hloc

/-- The weak-gradient component of a `W1p0` pair also converges almost everywhere under shrinking
normalized bump convolution. Together with `fderiv_convolution_eq_convolution_grad`, this gives
almost-everywhere convergence of the pointwise derivatives of the smooth mollifications to the
weak gradient. No `Lᵖ` convergence is asserted. -/
theorem W1p0.ae_tendsto_convolution_weak_gradient {p : ℝ} (hp : 1 ≤ p)
    {ρ : ℝ} {x : Sp N} {φg : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (h : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x))
    (η : ℕ → ContDiffBump (0 : Sp N))
    (hη : Tendsto (fun n => (η n).rOut) atTop (𝓝 0))
    (hη' : ∀ᶠ n in atTop, (η n).rOut ≤ 2 * (η n).rIn) :
    ∀ᵐ y ∂volume,
      Tendsto (fun n => ((η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        φg.2) y) atTop (𝓝 (φg.2 y)) := by
  rcases h with ⟨_, _, hgrad, _⟩
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp)
  have hloc : LocallyIntegrable φg.2 volume := hgrad.locallyIntegrable hpENN
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hη hη' hloc

/-- The pointwise derivatives of the smooth mollifications converge almost everywhere to the
weak gradient. This combines the convolution derivative identity with differentiation of
locally-integrable functions; it is pointwise a.e. convergence, not `Lᵖ` convergence. -/
theorem W1p0.ae_tendsto_fderiv_convolution {p : ℝ} (hp : 1 ≤ p)
    {ρ : ℝ} {x : Sp N} {φg : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (h : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x))
    (η : ℕ → ContDiffBump (0 : Sp N))
    (hη : Tendsto (fun n => (η n).rOut) atTop (𝓝 0))
    (hη' : ∀ᶠ n in atTop, (η n).rOut ≤ 2 * (η n).rIn) :
    ∀ᵐ y ∂volume,
      Tendsto (fun n => fderiv ℝ
        ((η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1) y)
        atTop (𝓝 (φg.2 y)) := by
  have hgrad := W1p0.ae_tendsto_convolution_weak_gradient hp h η hη hη'
  filter_upwards [hgrad] with y hy
  apply Filter.Tendsto.congr' _ hy
  filter_upwards with n
  exact (W1p0.fderiv_convolution_eq_convolution_grad hp h (η n) y).symm

/-- Poincaré's inequality on a cube for every `W1p0` pair. The proof mollifies the function,
applies the Lipschitz cube inequality on the slightly enlarged cube, uses contraction for the
gradient energy, then passes to the limit by Fatou. -/
theorem poincare_cube_W1p0 [NeZero N] {p ρ : ℝ} (hp : 1 ≤ p)
    {x : Sp N} {φg : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (h : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x)) :
    ∫⁻ y, ‖φg.1 y‖ₑ ^ p ≤
      m * ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p := by
  rcases h with ⟨hzero, hφ, hgrad, hweak⟩
  have hp0 : 0 < p := by linarith
  by_cases hρ : 0 < ρ
  · let η : ℕ → ContDiffBump (0 : Sp N) := fun n =>
      ⟨1 / (n + 1 : ℝ), 2 / (n + 1 : ℝ), by positivity, by
        have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
        exact (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) hn)⟩
    have hη : Tendsto (fun n => (η n).rOut) atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
        apply Filter.tendsto_atTop.2
        intro b
        filter_upwards [Filter.eventually_ge_atTop b] with n hn
        exact le_trans hn (Nat.le_add_right n 1)
      have h' := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hn
      convert h' using 1
      funext n
      simp [η, Nat.cast_add]
    have hη' : ∀ᶠ n in atTop, (η n).rOut ≤ 2 * (η n).rIn := by
      filter_upwards with n
      simp [η, div_eq_mul_inv]
    have hconv := W1p0.ae_tendsto_convolution_function hp
      (show (φg : (Sp N → Tgt m) × (Sp N → Mat m N)) ∈
        W1p0 (ENNReal.ofReal p) (cube ρ x) from ⟨hzero, hφ, hgrad, hweak⟩)
      η hη hη'
    let f : ℕ → Sp N → Tgt m := fun n =>
      ((η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1)
    have hfatou := lintegral_liminf_le (μ := volume) (u := atTop) (fun n => by
      obtain ⟨K, hK, _⟩ := W1p0.exists_lipschitz_convolution hp
        (show (φg : (Sp N → Tgt m) × (Sp N → Mat m N)) ∈
          W1p0 (ENNReal.ofReal p) (cube ρ x) from ⟨hzero, hφ, hgrad, hweak⟩) (η n)
      exact ((hK.continuous.enorm).measurable.pow_const p))
    have hpoint : ∀ᵐ y ∂volume,
        Filter.liminf (fun n => ‖f n y‖ₑ ^ p) atTop = ‖φg.1 y‖ₑ ^ p := by
      filter_upwards [hconv] with y hy
      have hcont : Continuous (fun z : Tgt m => ‖z‖ ^ p) :=
        (Real.continuous_rpow_const hp0.le).comp continuous_norm
      have ht := hcont.continuousAt.tendsto.comp hy
      have ht' : Tendsto (fun n => ENNReal.ofReal (‖f n y‖ ^ p)) atTop
          (𝓝 (ENNReal.ofReal (‖φg.1 y‖ ^ p))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
      have heq (n : ℕ) : ‖f n y‖ₑ ^ p = ENNReal.ofReal (‖f n y‖ ^ p) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
      have hlim : Filter.liminf (fun n => ENNReal.ofReal (‖f n y‖ ^ p)) atTop =
          ENNReal.ofReal (‖φg.1 y‖ ^ p) := ht'.liminf_eq
      rw [show (fun n => ‖f n y‖ₑ ^ p) = fun n => ENNReal.ofReal (‖f n y‖ ^ p) from
        funext heq, hlim]
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    have hfatou' : ∫⁻ y, ‖φg.1 y‖ₑ ^ p ≤
        Filter.liminf (fun n => ∫⁻ y, ‖f n y‖ₑ ^ p) atTop := by
      calc
        ∫⁻ y, ‖φg.1 y‖ₑ ^ p = ∫⁻ y, Filter.liminf (fun n => ‖f n y‖ₑ ^ p) atTop :=
          lintegral_congr_ae (hpoint.mono fun y hy => hy.symm)
        _ ≤ Filter.liminf (fun n => ∫⁻ y, ‖f n y‖ₑ ^ p) atTop := hfatou
    have hbound (n : ℕ) : ∫⁻ y, ‖f n y‖ₑ ^ p ≤
        m * ENNReal.ofReal (ρ + 2 * (η n).rOut) ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p := by
      obtain ⟨K, hK, hzeroConv⟩ := W1p0.exists_lipschitz_convolution hp
        (show (φg : (Sp N → Tgt m) × (Sp N → Mat m N)) ∈
          W1p0 (ENNReal.ofReal p) (cube ρ x) from ⟨hzero, hφ, hgrad, hweak⟩) (η n)
      have hP := poincare_cube hp hK hzeroConv
      have hderiv := W1p0.fderiv_convolution_eq_convolution_grad hp
        (show (φg : (Sp N → Tgt m) × (Sp N → Mat m N)) ∈
          W1p0 (ENNReal.ofReal p) (cube ρ x) from ⟨hzero, hφ, hgrad, hweak⟩) (η n)
      have hcontract := W1p0.convolution_lintegral_norm_rpow_le hp hgrad (η n)
      have hcontract' : ∫⁻ y, ‖fderiv ℝ (f n) y‖ₑ ^ p ≤
          ∫⁻ y, ‖φg.2 y‖ₑ ^ p :=
        (lintegral_congr fun y => by rw [hderiv y]).trans_le hcontract
      calc
        ∫⁻ y, ‖f n y‖ₑ ^ p ≤
            ((m : ℝ≥0∞) * ENNReal.ofReal (ρ + 2 * (η n).rOut) ^ p) *
              ∫⁻ y, ‖fderiv ℝ (f n) y‖ₑ ^ p := by
          simpa [f, mul_assoc] using hP
        _ ≤ ((m : ℝ≥0∞) * ENNReal.ofReal (ρ + 2 * (η n).rOut) ^ p) *
              ∫⁻ y, ‖φg.2 y‖ₑ ^ p :=
          mul_le_mul_of_nonneg_left hcontract' (by positivity)
        _ = (m : ℝ≥0∞) * ENNReal.ofReal (ρ + 2 * (η n).rOut) ^ p *
              ∫⁻ y, ‖φg.2 y‖ₑ ^ p := by ring
    have hEfinite : (∫⁻ y, ‖φg.2 y‖ₑ ^ p) ≠ ⊤ := by
      have hpENN0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
      have hInt' := hgrad.integrable_norm_rpow hpENN0 ENNReal.ofReal_ne_top
      have hInt : Integrable (fun y => ‖φg.2 y‖ ^ p) volume := by
        simpa [ENNReal.toReal_ofReal hp0.le] using hInt'
      have hEq : (∫⁻ y, ‖φg.2 y‖ₑ ^ p) =
          ENNReal.ofReal (∫ y, ‖φg.2 y‖ ^ p) := by
        calc
          ∫⁻ y, ‖φg.2 y‖ₑ ^ p = ∫⁻ y, ENNReal.ofReal (‖φg.2 y‖ ^ p) := by
            apply lintegral_congr
            intro y
            rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ← ofReal_norm]
          _ = ENNReal.ofReal (∫ y, ‖φg.2 y‖ ^ p) :=
            (ofReal_integral_eq_lintegral_ofReal hInt
              (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)).symm
      rw [hEq]
      exact ENNReal.ofReal_ne_top
    let c : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((ρ + 2 * (η n).rOut) ^ p)
    have hc : Tendsto c atTop (𝓝 (ENNReal.ofReal ρ ^ p)) := by
      have hr : Tendsto (fun n : ℕ => ρ + 2 * (η n).rOut) atTop (𝓝 ρ) := by
        have := hη.const_mul 2
        simpa [η] using tendsto_const_nhds.add this
      have hpow : Continuous (fun z : ℝ => z ^ p) := Real.continuous_rpow_const hp0.le
      have hlim := (ENNReal.continuous_ofReal.comp hpow).continuousAt.tendsto.comp hr
      change Tendsto (fun n => ENNReal.ofReal ((ρ + 2 * (η n).rOut) ^ p)) atTop
        (𝓝 (ENNReal.ofReal (ρ ^ p))) at hlim
      simpa only [← ENNReal.ofReal_rpow_of_nonneg hρ.le hp0.le] using hlim
    have hprod : Tendsto (fun n => c n * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) atTop
        (𝓝 (ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p)) := by
      have hcfinite : ENNReal.ofReal ρ ^ p ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
      exact (ENNReal.tendsto_mul (a := ENNReal.ofReal ρ ^ p)
        (b := ∫⁻ y, ‖φg.2 y‖ₑ ^ p) (Or.inr hEfinite) (Or.inr hcfinite)).comp
        (hc.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫⁻ y, ‖φg.2 y‖ₑ ^ p)
          atTop (𝓝 (∫⁻ y, ‖φg.2 y‖ₑ ^ p))))
    have hlim : Filter.liminf (fun n => c n * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) atTop =
        ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p := hprod.liminf_eq
    have hlimBound : Filter.liminf (fun n => ∫⁻ y, ‖f n y‖ₑ ^ p) atTop ≤
        Filter.liminf (fun n => m * c n * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => by
        have hb := hbound n
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le] at hb
        simpa [c, mul_assoc] using hb)
    have hmlim : Filter.liminf (fun n => m * c n * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) atTop =
        m * (ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) := by
      have hmfinite : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
      have htargetFinite : ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
          hEfinite
      have := (ENNReal.tendsto_mul (a := (m : ℝ≥0∞))
        (b := ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p)
        (Or.inr htargetFinite) (Or.inr hmfinite)).comp
          ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (m : ℝ≥0∞)) atTop (𝓝 (m : ℝ≥0∞))).prodMk_nhds hprod)
      change Tendsto (fun n => (m : ℝ≥0∞) * (c n * ∫⁻ y, ‖φg.2 y‖ₑ ^ p)) atTop
        (𝓝 ((m : ℝ≥0∞) * (ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p))) at this
      simpa [mul_assoc] using this.liminf_eq
    calc
      ∫⁻ y, ‖φg.1 y‖ₑ ^ p ≤ Filter.liminf (fun n => ∫⁻ y, ‖f n y‖ₑ ^ p) atTop := hfatou'
      _ ≤ m * (ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) := by
        calc
          _ ≤ Filter.liminf (fun n => m * c n * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) atTop := hlimBound
          _ = m * (ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p) := hmlim
      _ = m * ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖φg.2 y‖ₑ ^ p := by ring
  · have hcube : cube ρ x = ∅ := by
      ext y
      rw [cube, Set.mem_pi]
      simp only [Set.mem_univ, Set.mem_empty_iff_false, iff_false]
      intro hy
      have hN : 0 < N := NeZero.pos N
      have hmem := hy ⟨0, hN⟩ trivial
      linarith [hmem.1, hmem.2]
    have hzeroAll : ∀ y, φg.1 y = 0 := fun y => hzero y (by simp [hcube])
    simp [hzeroAll, ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hρ),
      ENNReal.zero_rpow_of_pos hp0]

/-- Poincaré on a finite union of pairwise disjoint cubes for arbitrary `W1p0` correctors.
The estimate controls the correction on the union by its weak gradient there, with the largest
cube side `R`. It provides no uniform bound on the gradient energies of a family of corrections,
no `Lᵖ` convergence as `R → 0`, and no connection to `GammaLimsup`. -/
theorem finiteW1p0_cube_correction_poincare [NeZero N] {n : ℕ} {p R : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (ρ : Fin n → ℝ) (x : Fin n → Sp N)
    (hρR : ∀ i, ρ i ≤ R)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i)))
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j))) :
    let U : Set (Sp N) := ⋃ i, cube (ρ i) (x i)
    ∫⁻ y in U, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
      (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
        ∫⁻ y in U, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
  classical
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 (Fact.out : 1 ≤ ENNReal.ofReal p)
  have hp0 : 0 < p := by linarith
  let Q : Fin n → Set (Sp N) := fun i => cube (ρ i) (x i)
  let U : Set (Sp N) := ⋃ i, Q i
  have hQo : ∀ i, IsOpen (Q i) := fun i => isOpen_cube _ _
  have hpieces {F : Sp N → ℝ≥0∞} :
      ∫⁻ y in U, F y = ∑ i, ∫⁻ y in Q i, F y := by
    apply lintegral_eq_sum_pieces_fintype hQo (fun i => subset_iUnion Q i) hQd ?_ F
    simp [Q]
  have hfun_local : ∀ i y, y ∈ Q i → (finiteCubeCorrection v).1 y = (v i).1 y := by
    intro i y hy
    simp only [finiteCubeCorrection, Prod.fst_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · intro j hj hji
      have hyj : y ∉ Q j := fun hmem => (Set.disjoint_left.mp (hQd hji)) hmem hy
      exact (hv j).1 y hyj
  have hgrad_local := fun i =>
    finiteCubeCorrectionGrad_ae_eq_on hQo hQd hv i
  have hlocal_est : ∀ i,
      (∫⁻ y in Q i, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) ≤
        (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
    intro i
    have hfun : (∫⁻ y in Q i, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) =
        ∫⁻ y in Q i, ‖(v i).1 y‖ₑ ^ p := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hQo i).measurableSet] with y hy
      exact congrArg (fun z : Tgt m => ‖z‖ₑ ^ p) (hfun_local i y hy)
    have hgrad : (∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p) =
        ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := by
      apply lintegral_congr_ae
      filter_upwards [hgrad_local i] with y hy
      exact congrArg (fun z : Mat m N => ‖z‖ₑ ^ p) hy
    have hφall : ∫⁻ y, ‖(v i).1 y‖ₑ ^ p =
        ∫⁻ y in Q i, ‖(v i).1 y‖ₑ ^ p := by
      rw [← lintegral_indicator (hQo i).measurableSet]
      apply lintegral_congr_ae
      filter_upwards [] with y
      by_cases hmem : y ∈ Q i
      · simp [hmem]
      · simpa [hmem, (hv i).1 y hmem] using
          (ENNReal.zero_rpow_of_pos hp0 : (0 : ℝ≥0∞) ^ p = 0)
    have hgradall : ∫⁻ y, ‖(v i).2 y‖ₑ ^ p =
        ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := by
      rw [← lintegral_indicator (hQo i).measurableSet]
      apply lintegral_congr_ae
      have hoff := W1p0.ae_grad_eq_zero_off (hQo i)
        (volume_frontier_cube _ _) (hv i)
      filter_upwards [hoff] with y hy
      by_cases hmem : y ∈ Q i
      · simp [hmem]
      · rw [hy hmem, indicator_of_notMem hmem]
        rw [enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero]
        exact ENNReal.zero_rpow_of_pos hp0
    have hP := poincare_cube_W1p0 hp (hv i)
    rw [hφall, hgradall] at hP
    rw [hfun, hgrad]
    calc
      ∫⁻ y in Q i, ‖(v i).1 y‖ₑ ^ p ≤
          (m : ℝ≥0∞) * ENNReal.ofReal (ρ i) ^ p *
            ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := hP
      _ ≤ (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
            ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := by
          gcongr
          exact hρR i
  change (∫⁻ y in U, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) ≤
    (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
      ∫⁻ y in U, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p
  rw [hpieces, hpieces]
  calc
    (∑ i, ∫⁻ y in Q i, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) ≤
        ∑ i, ((m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p) :=
      Finset.sum_le_sum fun i hi => hlocal_est i
    _ = (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∑ i, ∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
      rw [Finset.mul_sum]

/-- Global finite-union Poincaré for arbitrary `W1p0` cube correctors, obtained from
`finiteW1p0_cube_correction_poincare` and the fact that both correction components are supported
on the cube union (the gradient support statement holds almost everywhere). This supplies no
uniform gradient-energy bound, no `Lᵖ` convergence as `R → 0`, and no connection to
`GammaLimsup`. -/
theorem finiteW1p0_cube_correction_global_poincare [NeZero N] {n : ℕ} {p R : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (ρ : Fin n → ℝ) (x : Fin n → Sp N)
    (hρR : ∀ i, ρ i ≤ R)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i)))
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j))) :
    ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
      (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
        ∫⁻ y, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
  have hEq := finiteCubeCorrection_lintegral_eq_on_union ρ x v hv
  rw [hEq.1, hEq.2]
  exact finiteW1p0_cube_correction_poincare ρ x hρR v hv hQd

/-- Coercivity bounds the global `Lᵖ` energy of a single cube corrector from its Dirichlet
energy and the `Lᵖ` energy of the background field on that cube. The estimate is uniform in the
scale `ε` once these two energy terms are bounded. The explicit `AEMeasurable` assumption on the
background power is used only to split its integral from the corrector term. This does not bound
the Dirichlet energy itself for a chosen corrector. -/
theorem W1p0.grad_lintegral_le_of_dirichlet_energy_le
    {p : ℝ} (hp : (1 : ℝ) ≤ p) {W : Sp N → Mat m N → ENNReal} {c₀ : NNReal}
    (hW : IsCoercive p c₀ W) (hc₀ : 0 < c₀) (ε : ℝ) (D : Sp N → Mat m N)
    (ρ : ℝ) (x : Sp N) (φg : (Sp N → Tgt m) × (Sp N → Mat m N))
    (hφ : φg ∈ W1p0 (ENNReal.ofReal p) (cube ρ x)) (E : ℝ≥0∞)
    (henergy : ∫⁻ y in cube ρ x, W (ε⁻¹ • y) (D y + φg.2 y) ≤ E)
    (hD : AEMeasurable (fun y => ‖D y‖ₑ ^ p) (volume.restrict (cube ρ x))) :
    ∫⁻ y, ‖φg.2 y‖ₑ ^ p ≤ 2 ^ (p - 1) *
      ((c₀ : ℝ≥0∞)⁻¹ * E + ∫⁻ y in cube ρ x, ‖D y‖ₑ ^ p) := by
  have hp0 : 0 < p := by linarith
  have hcubeOpen : IsOpen (cube ρ x) := isOpen_cube _ _
  have hpoint : ∀ y, ‖φg.2 y‖ₑ ^ p ≤
      2 ^ (p - 1) * (‖D y + φg.2 y‖ₑ ^ p + ‖D y‖ₑ ^ p) := by
    intro y
    have hnorm : ‖φg.2 y‖ₑ ≤ ‖D y + φg.2 y‖ₑ + ‖D y‖ₑ := by
      have h := nnnorm_sub_le (D y + φg.2 y) (D y)
      rw [add_sub_cancel_left] at h
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_add]
      exact ENNReal.coe_le_coe.2 h
    exact (ENNReal.rpow_le_rpow hnorm hp0.le).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)
  have hcoercive : (∫⁻ y in cube ρ x, ‖D y + φg.2 y‖ₑ ^ p) ≤
      (c₀ : ℝ≥0∞)⁻¹ * E := by
    calc
      ∫⁻ y in cube ρ x, ‖D y + φg.2 y‖ₑ ^ p ≤
          ∫⁻ y in cube ρ x, (c₀ : ℝ≥0∞)⁻¹ *
            W (ε⁻¹ • y) (D y + φg.2 y) := by
        exact lintegral_mono fun y =>
          hW.enorm_rpow_le hp0.le hc₀ (ε⁻¹ • y) (D y + φg.2 y)
      _ = (c₀ : ℝ≥0∞)⁻¹ *
          ∫⁻ y in cube ρ x, W (ε⁻¹ • y) (D y + φg.2 y) := by
        rw [lintegral_const_mul' _ _ (by
          apply ENNReal.inv_ne_top.mpr
          exact ENNReal.coe_ne_zero.mpr hc₀.ne')]
      _ ≤ (c₀ : ℝ≥0∞)⁻¹ * E := by gcongr
  have hgradSupport : ∫⁻ y, ‖φg.2 y‖ₑ ^ p =
      ∫⁻ y in cube ρ x, ‖φg.2 y‖ₑ ^ p := by
    rw [← lintegral_indicator hcubeOpen.measurableSet]
    apply lintegral_congr_ae
    have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
    have hoff := W1p0.ae_grad_eq_zero_off hcubeOpen (volume_frontier_cube ρ x) hφ
    filter_upwards [hoff] with y hy
    by_cases hmem : y ∈ cube ρ x
    · simp [hmem]
    · rw [hy hmem, indicator_of_notMem hmem]
      simp [enorm_eq_nnnorm, hp0]
  calc
    ∫⁻ y, ‖φg.2 y‖ₑ ^ p = ∫⁻ y in cube ρ x, ‖φg.2 y‖ₑ ^ p := hgradSupport
    _ ≤ ∫⁻ y in cube ρ x,
          2 ^ (p - 1) * (‖D y + φg.2 y‖ₑ ^ p + ‖D y‖ₑ ^ p) := by
        exact lintegral_mono fun y => hpoint y
    _ = 2 ^ (p - 1) *
          ((∫⁻ y in cube ρ x, ‖D y + φg.2 y‖ₑ ^ p) +
            ∫⁻ y in cube ρ x, ‖D y‖ₑ ^ p) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          ENNReal.ofNat_ne_top), lintegral_add_right' _ hD]
    _ ≤ 2 ^ (p - 1) *
          ((c₀ : ℝ≥0∞)⁻¹ * E + ∫⁻ y in cube ρ x, ‖D y‖ₑ ^ p) := by
        gcongr

/-- For finitely many pairwise disjoint cube correctors with bounded individual Dirichlet
energies, coercivity and global Poincaré give an `Lᵖ` bound on their sum. The bound is uniform in
`R` whenever `∑ i, E i` is bounded. This proves no bound on `∑ i, E i` itself, constructs no
Vitali covering or recovery sequence, and gives no connection to `GammaLimsup`; Proposition
2.1(ii) remains unproved. -/
theorem finiteW1p0_cube_correction_lintegral_le_of_energy_le [NeZero N]
    {n : ℕ} {p R : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (ρ : Fin n → ℝ) (x : Fin n → Sp N) (hρR : ∀ i, ρ i ≤ R)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i)))
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j)))
    {W : Sp N → Mat m N → ENNReal} {c₀ : NNReal} (hW : IsCoercive p c₀ W)
    (hc₀ : 0 < c₀) (ε : ℝ) (D : Sp N → Mat m N) (E : Fin n → ℝ≥0∞)
    (henergy : ∀ i, ∫⁻ y in cube (ρ i) (x i),
      W (ε⁻¹ • y) (D y + (v i).2 y) ≤ E i)
    (hD : AEMeasurable (fun y => ‖D y‖ₑ ^ p)
      (volume.restrict (⋃ i, cube (ρ i) (x i)))) :
    ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
      (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
        (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * ∑ i, E i +
          ∫⁻ y in ⋃ i, cube (ρ i) (x i), ‖D y‖ₑ ^ p)) := by
  classical
  let Q : Fin n → Set (Sp N) := fun i => cube (ρ i) (x i)
  let U : Set (Sp N) := ⋃ i, Q i
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 (Fact.out : 1 ≤ ENNReal.ofReal p)
  have hp0 : 0 < p := by linarith
  have hQo : ∀ i, IsOpen (Q i) := fun i => isOpen_cube _ _
  have hpieces {F : Sp N → ℝ≥0∞} :
      ∫⁻ y in U, F y = ∑ i, ∫⁻ y in Q i, F y := by
    apply lintegral_eq_sum_pieces_fintype hQo (fun i => subset_iUnion Q i) hQd ?_ F
    simp [Q]
  have hDpieces : (∑ i, ∫⁻ y in Q i, ‖D y‖ₑ ^ p) =
      ∫⁻ y in U, ‖D y‖ₑ ^ p := by
    rw [← hpieces]
  have hlocal : ∀ i, ∫⁻ y, ‖(v i).2 y‖ₑ ^ p ≤
      2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * E i +
        ∫⁻ y in Q i, ‖D y‖ₑ ^ p) := by
    intro i
    exact W1p0.grad_lintegral_le_of_dirichlet_energy_le hp hW hc₀ ε D
      (ρ i) (x i) (v i) (hv i) (E i) (henergy i)
      (hD.mono_measure (Measure.restrict_mono (subset_iUnion Q i) le_rfl))
  have hEq := finiteCubeCorrection_lintegral_eq_on_union ρ x v hv
  have hgradSum : ∫⁻ y, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p =
      ∑ i, ∫⁻ y, ‖(v i).2 y‖ₑ ^ p := by
    rw [hEq.2, hpieces]
    calc
      (∑ i, ∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p) =
          ∑ i, ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            apply lintegral_congr_ae
            filter_upwards [finiteCubeCorrectionGrad_ae_eq_on hQo hQd hv i] with y hy
            exact congrArg (fun z : Mat m N => ‖z‖ₑ ^ p) hy
      _ = ∑ i, ∫⁻ y, ‖(v i).2 y‖ₑ ^ p := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            rw [← lintegral_indicator (hQo i).measurableSet]
            apply lintegral_congr_ae
            have hoff := W1p0.ae_grad_eq_zero_off (hQo i)
              (volume_frontier_cube _ _) (hv i)
            filter_upwards [hoff] with y hy
            by_cases hmem : y ∈ Q i
            · simp [hmem]
            · rw [hy hmem, indicator_of_notMem hmem]
              simp [enorm_eq_nnnorm, hp0]
  have hP := finiteW1p0_cube_correction_global_poincare ρ x hρR v hv hQd
  rw [hEq.1] at hP
  calc
    ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p =
        ∫⁻ y in U, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p := hEq.1
    _ ≤
        (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∫⁻ y, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := hP
    _ = (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∑ i, ∫⁻ y, ‖(v i).2 y‖ₑ ^ p := by rw [hgradSum]
    _ ≤ (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∑ i, (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * E i +
            ∫⁻ y in Q i, ‖D y‖ₑ ^ p)) := by
        gcongr with i
        exact hlocal i
    _ = (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * ∑ i, E i +
            ∫⁻ y in U, ‖D y‖ₑ ^ p)) := by
        congr 1
        calc
          ∑ i, 2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * E i +
              ∫⁻ y in Q i, ‖D y‖ₑ ^ p) =
              2 ^ (p - 1) * ∑ i, ((c₀ : ℝ≥0∞)⁻¹ * E i +
                ∫⁻ y in Q i, ‖D y‖ₑ ^ p) := by rw [← Finset.mul_sum]
          _ = 2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * ∑ i, E i +
                ∑ i, ∫⁻ y in Q i, ‖D y‖ₑ ^ p) := by
                  congr 1
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = 2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * ∑ i, E i +
                ∫⁻ y in U, ‖D y‖ₑ ^ p) := by rw [hDpieces]

/-! The local and finite-union near-minimizer results below provide energy control for chosen
correctors. They do not construct Vitali coverings, control the remainder outside the cubes, take
a diagonal in `ε` and the radius, connect to `GammaLimsup`, or construct a recovery sequence. -/

/-- If the Dirichlet infimum is finite, a zero-boundary competitor has energy at most any
strictly positive ENNReal tolerance above it. The infimum need not be attained. This does not
construct a Vitali covering, control the remainder outside the cubes, take a diagonal in `ε` and
the radius, connect to `GammaLimsup`, or provide a recovery sequence; Proposition 2.1(ii) is not
proved. -/
theorem mDirichlet_exists_near_optimal {p : ℝ≥0∞} (W : Sp N → Mat m N → ℝ≥0∞)
    (ε : ℝ) (D : Sp N → Mat m N) (A : Set (Sp N))
    (hfinite : mDirichlet p W ε D A ≠ ⊤) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ φg ∈ (W1p0 p A : Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
      ∫⁻ y in A, W (ε⁻¹ • y) (D y + φg.2 y) ≤ mDirichlet p W ε D A + δ := by
  have hlt : mDirichlet p W ε D A < mDirichlet p W ε D A + δ :=
    ENNReal.lt_add_right hfinite hδ.ne'
  unfold mDirichlet at hlt ⊢
  obtain ⟨φg, hφg⟩ := exists_lt_of_ciInf_lt hlt
  obtain ⟨hmem, henergy⟩ := (iInf_lt_iff).mp hφg
  exact ⟨φg, hmem, henergy.le⟩

/-- A finite family of pairwise disjoint cubes admits zero-boundary correctors with each local
energy within `δ` of its Dirichlet infimum. Their total energy is bounded by the growth integral
on the union plus `n * δ`. This gives no Vitali covering, no remainder control outside the cubes,
no diagonal in `ε` and the radius, no connection to `GammaLimsup`, and no recovery sequence;
Proposition 2.1(ii) remains unproved. -/
theorem finite_cube_near_optimal_correctors [NeZero N] {n : ℕ}
    (ρ : Fin n → ℝ) (x : Fin n → Sp N)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j)))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (G : Mat m N → ℝ≥0∞)
    (α β : NNReal) (W : Sp N → Mat m N → ℝ≥0∞)
    (hGrowth : HasGGrowth G α β W) (ε : ℝ) (D : Sp N → Mat m N)
    (hGDmeas : Measurable (fun y => G (D y)))
    (hGint : ∫⁻ y in ⋃ i, cube (ρ i) (x i), G (D y) < ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N),
      (∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i))) ∧
      (∀ i, ∫⁻ y in cube (ρ i) (x i),
        W (ε⁻¹ • y) (D y + (v i).2 y) ≤
          mDirichlet (ENNReal.ofReal p) W ε D (cube (ρ i) (x i)) + δ) ∧
    (∑ i, ∫⁻ y in cube (ρ i) (x i),
        W (ε⁻¹ • y) (D y + (v i).2 y) ≤
        (∫⁻ y in ⋃ i, cube (ρ i) (x i), (β : ℝ≥0∞) * (1 + G (D y))) + n * δ) := by
  classical
  let Q : Fin n → Set (Sp N) := fun i => cube (ρ i) (x i)
  let U : Set (Sp N) := ⋃ i, Q i
  have hQo : ∀ i, IsOpen (Q i) := fun i => isOpen_cube _ _
  have hpieces {F : Sp N → ℝ≥0∞} :
      ∫⁻ y in U, F y = ∑ i, ∫⁻ y in Q i, F y := by
    apply lintegral_eq_sum_pieces_fintype hQo (fun i => subset_iUnion Q i) hQd ?_ F
    simp [Q]
  have hlocalFinite : ∀ i, mDirichlet (ENNReal.ofReal p) W ε D (Q i) ≠ ⊤ := by
    intro i
    have hGlocal : ∫⁻ y in Q i, G (D y) < ⊤ := by
      apply lt_of_le_of_lt ?_ hGint
      exact lintegral_mono_set (subset_iUnion Q i)
    have hbound := mDirichlet_le_growthDensity (p := ENNReal.ofReal p) G W ε D (Q i) hGrowth hGDmeas
      (lt_top_iff_ne_top.mpr (volume_cube_ne_top (ρ i) (x i))) hGlocal
    exact (lt_top_iff_ne_top.mp (hbound.1.trans_lt hbound.2))
  choose v hv henergy using fun i =>
    mDirichlet_exists_near_optimal (p := ENNReal.ofReal p) W ε D (Q i)
      (hlocalFinite i) hδ
  refine ⟨v, hv, henergy, ?_⟩
  have hsumBound :
      (∑ i, ∫⁻ y in Q i, W (ε⁻¹ • y) (D y + (v i).2 y)) ≤
        (∑ i, ∫⁻ y in Q i, (β : ℝ≥0∞) * (1 + G (D y))) + n * δ := by
    calc
      (∑ i, ∫⁻ y in Q i, W (ε⁻¹ • y) (D y + (v i).2 y)) ≤
        ∑ i, ((∫⁻ y in Q i, (β : ℝ≥0∞) * (1 + G (D y))) + δ) :=
        Finset.sum_le_sum fun i hi => by
          have hm := (mDirichlet_le_growthDensity (p := ENNReal.ofReal p) G W ε D (Q i)
            hGrowth hGDmeas
            (lt_top_iff_ne_top.mpr (volume_cube_ne_top (ρ i) (x i))) (by
              apply lt_of_le_of_lt ?_ hGint
              exact lintegral_mono_set (subset_iUnion Q i))).1
          exact (henergy i).trans (by
            simpa [add_comm] using add_le_add_right hm δ)
      _ = (∑ i, ∫⁻ y in Q i, (β : ℝ≥0∞) * (1 + G (D y))) + n * δ := by
        rw [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
  have hsumGrowth :
      (∑ i, ∫⁻ y in Q i, (β : ℝ≥0∞) * (1 + G (D y))) =
        ∫⁻ y in U, (β : ℝ≥0∞) * (1 + G (D y)) := by
    symm
    exact hpieces
  rw [hsumGrowth] at hsumBound
  simpa [Q, U] using hsumBound

/-- The near-optimal disjoint-cube correctors satisfy the global `Lᵖ` estimate obtained from
coercivity and finite-union Poincaré, with total energy bounded by the growth integral and `n * δ`.
This gives no Vitali covering, no control outside the cubes, no diagonal in `ε` and radius, no
connection to `GammaLimsup`, and no recovery sequence; Proposition 2.1(ii) remains unproved. -/
theorem finite_cube_near_optimal_correction_lintegral_le [NeZero N]
    {n : ℕ} {p R : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (ρ : Fin n → ℝ) (x : Fin n → Sp N)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j)))
    (hρR : ∀ i, ρ i ≤ R) (G : Mat m N → ℝ≥0∞)
    {α β : NNReal} (W : Sp N → Mat m N → ℝ≥0∞)
    (hGrowth : HasGGrowth G α β W) {c₀ : NNReal} (hW : IsCoercive p c₀ W)
    (hc₀ : 0 < c₀) (ε : ℝ) (D : Sp N → Mat m N)
    (hGDmeas : Measurable (fun y => G (D y)))
    (hGint : ∫⁻ y in ⋃ i, cube (ρ i) (x i), G (D y) < ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ)
    (hD : AEMeasurable (fun y => ‖D y‖ₑ ^ p)
      (volume.restrict (⋃ i, cube (ρ i) (x i)))) :
    ∃ v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N),
      (∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i))) ∧
      (∀ i, ∫⁻ y in cube (ρ i) (x i),
        W (ε⁻¹ • y) (D y + (v i).2 y) ≤
          mDirichlet (ENNReal.ofReal p) W ε D (cube (ρ i) (x i)) + δ) ∧
      ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
        (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ *
            ((∫⁻ y in ⋃ i, cube (ρ i) (x i),
              (β : ℝ≥0∞) * (1 + G (D y))) + n * δ) +
            ∫⁻ y in ⋃ i, cube (ρ i) (x i), ‖D y‖ₑ ^ p)) := by
  obtain ⟨v, hv, henergy, hsum⟩ := finite_cube_near_optimal_correctors
    ρ x hQd (p := p) G (α := α) (β := β) W hGrowth ε D hGDmeas hGint hδ
  refine ⟨v, hv, henergy, ?_⟩
  let E : Fin n → ℝ≥0∞ := fun i =>
    ∫⁻ y in cube (ρ i) (x i), W (ε⁻¹ • y) (D y + (v i).2 y)
  have h := finiteW1p0_cube_correction_lintegral_le_of_energy_le
    ρ x hρR v hv hQd hW hc₀ ε D E (by intro i; exact le_rfl) hD
  exact h.trans (by
    dsimp [E]
    gcongr)

end Homogenization
