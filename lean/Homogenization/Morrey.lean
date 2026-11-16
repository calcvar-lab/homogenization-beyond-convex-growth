import Homogenization.LocalMollifyEnergy
import Homogenization.SumOsc
import Homogenization.DensityZaff
import Homogenization.LowerBound

/-!
# Morrey's inequality and the cited result (b)

* `morrey_C1_cube`: Morrey's inequality on a cube for `C¹` functions, `p > N`, by averaging the
  fundamental theorem of calculus along segments and Hölder on the homothetic cubes
  `y + t(Q - y)` (no polar coordinates).
* `morrey_weak_cube`: the same, a.e., for weakly differentiable `φ ∈ Lᵖ` with an affine
  correction, by mollification.
* `ae_tendsto_cube_enorm_sub_rpow`: `Lᵖ` Lebesgue points on cubes.
* `W1p.ae_tendsto_affine_remainder`: a.e. differentiability of `W^{1,p}`, `p > N`, with the
  tangent map `u(x) + ∇u(x)(· - x)` (eq. `difflowerbound`);
* `citedSobolevDiff_holds`: the cited result (b) `CitedSobolevDiff` holds.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution

namespace Homogenization

variable {N m : ℕ}

/-- Fundamental theorem of calculus along the segment `[y, w]`, in `enorm` form. -/
theorem enorm_sub_le_lintegral_fderiv {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f) (y w : Sp N) :
    ‖f w - f y‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (homothety y t w)‖ₑ * ‖w - y‖ₑ := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hh : Continuous fun t : ℝ => homothety y t w := by unfold homothety; fun_prop
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (homothety y t w))
      (fderiv ℝ f (homothety y t w) (w - y)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => homothety y t w) (w - y) t := by
      simpa [homothety] using ((hasDerivAt_id t).smul_const (w - y)).const_add y
    exact (hd _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ => fderiv ℝ f (homothety y t w) (w - y) :=
    ((hf.continuous_fderiv one_ne_zero).comp hh).clm_apply continuous_const
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 1)
  have h0 : homothety y 0 w = y := by simp [homothety]
  have h1 : homothety y 1 w = w := by simp [homothety]
  simp only [h0, h1, intervalIntegral.integral_of_le zero_le_one] at hint
  rw [← hint]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t => ?_)
  exact ContinuousLinearMap.le_opENorm _ _

/-- The homothety of center `y` and ratio `t > 0` maps `Q_r(c)` into `Q_{tr}(y + t(c - y))`. -/
theorem homothety_mem_cube {r t : ℝ} (ht : 0 < t) {c y w : Sp N} (hw : w ∈ cube r c) :
    homothety y t w ∈ cube (t * r) (homothety y t c) := by
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, homothety, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hw ⊢
  intro i
  obtain ⟨h1, h2⟩ := hw i
  constructor <;> nlinarith

/-- For `y ∈ Q_r(c)` and `t ≤ 1`, the homothetic cube `Q_{tr}(y + t(c - y))` lies in `Q_r(c)`. -/
theorem cube_homothety_subset {r t : ℝ} (ht1 : t ≤ 1) {c y : Sp N} (hy : y ∈ cube r c) :
    cube (t * r) (homothety y t c) ⊆ cube r c := by
  intro z hz
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, homothety, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hy hz ⊢
  intro i
  obtain ⟨a1, a2⟩ := hz i
  obtain ⟨b1, b2⟩ := hy i
  have h1t : 0 ≤ 1 - t := by linarith
  constructor <;> nlinarith [mul_nonneg h1t (by linarith : (0 : ℝ) ≤ y i - (c i - r / 2)),
    mul_nonneg h1t (by linarith : (0 : ℝ) ≤ c i + r / 2 - y i)]

/-- Two points of `Q_r(c)` are at sup-distance at most `r`. -/
theorem norm_sub_le_of_mem_cube [NeZero N] {r : ℝ} {c y w : Sp N} (hy : y ∈ cube r c)
    (hw : w ∈ cube r c) :
    ‖w - y‖ ≤ r := by
  have hr : 0 ≤ r := by
    by_contra h
    rw [cube_eq_empty_of_nonpos (by linarith) c] at hy
    exact hy
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy hw
  obtain ⟨a1, a2⟩ := hy i
  obtain ⟨b1, b2⟩ := hw i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Exponent bookkeeping: `t^{-N} ((tr)^N)^{1 - 1/p} = t^{-N/p} r^{N - N/p}`. -/
theorem morrey_rpow_aux {p t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (t ^ N)⁻¹ * ((t * r) ^ N) ^ (1 - 1 / p) = t ^ (-((N : ℝ) / p)) * r ^ ((N : ℝ) - N / p) := by
  rw [mul_pow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast t N,
    ← Real.rpow_natCast r N, ← Real.rpow_mul ht.le, ← Real.rpow_mul hr.le,
    ← Real.rpow_neg ht.le, ← mul_assoc, ← Real.rpow_add ht]
  congr 2 <;> ring

/-- `∫₀¹ t^{-a} dt = 1/(1 - a)` for `a < 1`. -/
theorem lintegral_Ioc_rpow_neg {a : ℝ} (ha : a < 1) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-a)) = ENNReal.ofReal (1 / (1 - a)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-a)) (Ioc 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -a) (by linarith)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _),
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith)),
    Real.one_rpow, Real.zero_rpow (by linarith)]
  congr 1
  ring

/-- Change of variables along the homothety of center `y ∈ Q` and ratio `t ∈ (0,1]`, followed by
Hölder on the image cube `y + t(Q - y) ⊆ Q`. -/
theorem setLIntegral_fderiv_homothety_le {p : ℝ} (hp : 1 ≤ p) {f : Sp N → Tgt m}
    (hf : ContDiff ℝ 1 f) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (ht1 : t ≤ 1) {c y : Sp N}
    (hy : y ∈ cube r c) :
    ∫⁻ w in cube r c, ‖fderiv ℝ f (homothety y t w)‖ₑ ≤
      ENNReal.ofReal (t ^ (-((N : ℝ) / p)) * r ^ ((N : ℝ) - N / p)) *
        eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict (cube r c)) := by
  set Qt := cube (t * r) (homothety y t c)
  set E := eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict (cube r c))
  have hcont := hf.continuous_fderiv one_ne_zero
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hs : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hp
  calc ∫⁻ w in cube r c, ‖fderiv ℝ f (homothety y t w)‖ₑ
      ≤ ∫⁻ w in homothety y t ⁻¹' Qt, ‖fderiv ℝ f (homothety y t w)‖ₑ :=
        lintegral_mono_set fun w hw => homothety_mem_cube ht hw
    _ = ENNReal.ofReal |(t ^ N)⁻¹| * ∫⁻ z in Qt, ‖fderiv ℝ f z‖ₑ :=
        setLIntegral_comp_homothety (fun z => ‖fderiv ℝ f z‖ₑ) ht y
          (isOpen_cube _ _).measurableSet
    _ ≤ ENNReal.ofReal ((t ^ N)⁻¹) * (E * volume Qt ^ (1 - 1 / p)) := by
        rw [abs_of_nonneg (by positivity)]
        gcongr
        have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict Qt) hp1
          hcont.aestronglyMeasurable
        rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ, ENNReal.toReal_one,
          ENNReal.toReal_ofReal (by linarith), div_one] at h
        refine h.trans ?_
        gcongr
        exact eLpNorm_mono_measure _
          (Measure.restrict_mono (cube_homothety_subset ht1 hy) le_rfl)
    _ = ENNReal.ofReal (t ^ (-((N : ℝ) / p)) * r ^ ((N : ℝ) - N / p)) * E := by
        rw [volume_cube, ← ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hs, ← morrey_rpow_aux ht hr,
          ENNReal.ofReal_mul (by positivity)]
        ring

/-- **Morrey, integrated form, for `C¹` functions on a cube.** For `y ∈ Q = Q_r(c)` and `p > N`,
`∫_Q |f(w) - f(y)| dw ≤ r · r^{N - N/p} / (1 - N/p) · ‖∇f‖_{Lᵖ(Q)}`. -/
theorem setLIntegral_enorm_sub_le [NeZero N] {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f) {r : ℝ} (hr : 0 < r) {c y : Sp N}
    (hy : y ∈ cube r c) :
    ∫⁻ w in cube r c, ‖f w - f y‖ₑ ≤
      ENNReal.ofReal (r * (r ^ ((N : ℝ) - N / p) * (1 / (1 - N / p)))) *
        eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict (cube r c)) := by
  set E := eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict (cube r c))
  have hcont := hf.continuous_fderiv one_ne_zero
  have hh : Continuous (fun q : Sp N × ℝ => homothety y q.2 q.1) := by
    unfold homothety; fun_prop
  have hh1 : ∀ t : ℝ, Continuous (fun w : Sp N => homothety y t w) := by
    intro t; unfold homothety; fun_prop
  have hNp1 : (N : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hNp
  calc ∫⁻ w in cube r c, ‖f w - f y‖ₑ
      ≤ ∫⁻ w in cube r c, ∫⁻ t in Ioc (0 : ℝ) 1,
          ‖fderiv ℝ f (homothety y t w)‖ₑ * ENNReal.ofReal r := by
        refine setLIntegral_mono' (isOpen_cube _ _).measurableSet fun w hw =>
          (enorm_sub_le_lintegral_fderiv hf y w).trans (lintegral_mono fun t => ?_)
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_sub_le_of_mem_cube hy hw)
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ w in cube r c,
          ‖fderiv ℝ f (homothety y t w)‖ₑ * ENNReal.ofReal r :=
        lintegral_lintegral_swap ((hcont.comp hh).measurable.enorm.mul_const _).aemeasurable
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-((N : ℝ) / p))) *
          (ENNReal.ofReal (r ^ ((N : ℝ) - N / p)) * E * ENNReal.ofReal r) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        rw [lintegral_mul_const _ (show Measurable fun w => ‖fderiv ℝ f (homothety y t w)‖ₑ from
          (hcont.comp (hh1 t)).measurable.enorm)]
        calc (∫⁻ w in cube r c, ‖fderiv ℝ f (homothety y t w)‖ₑ) * ENNReal.ofReal r
            ≤ ENNReal.ofReal (t ^ (-((N : ℝ) / p)) * r ^ ((N : ℝ) - N / p)) * E *
                ENNReal.ofReal r := by
              gcongr
              exact setLIntegral_fderiv_homothety_le hp hf hr ht.1 ht.2 hy
          _ = _ := by rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _)]; ring
    _ = ENNReal.ofReal (1 / (1 - N / p)) *
          (ENNReal.ofReal (r ^ ((N : ℝ) - N / p)) * E * ENNReal.ofReal r) := by
        rw [lintegral_mul_const _
          (show Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-((N : ℝ) / p)))
          from (measurable_id.pow_const _).ennreal_ofReal),
          lintegral_Ioc_rpow_neg hNp1]
    _ = _ := by
        rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_mul (by positivity)]
        ring

/-- **Morrey's inequality for `C¹` functions on a cube.** For `p > N` and `y, z ∈ Q = Q_r(c)`,
`|f(y) - f(z)| ≤ 2/(1 - N/p) · r^{1 - N/p} ‖∇f‖_{Lᵖ(Q)}`. -/
theorem morrey_C1_cube [NeZero N] {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f) {r : ℝ} (hr : 0 < r) {c y z : Sp N}
    (hy : y ∈ cube r c) (hz : z ∈ cube r c) :
    ‖f y - f z‖ₑ ≤ ENNReal.ofReal (2 / (1 - N / p) * r ^ (1 - (N : ℝ) / p)) *
      eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict (cube r c)) := by
  set E := eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict (cube r c))
  set X : ℝ := r * (r ^ ((N : ℝ) - N / p) * (1 / (1 - N / p)))
  have hfm : Measurable f := hf.continuous.measurable
  have hQ : volume (cube r c) = ENNReal.ofReal (r ^ N) := by
    rw [volume_cube, ENNReal.ofReal_pow hr.le]
  have hQ0 : ENNReal.ofReal (r ^ N) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hmain : ‖f y - f z‖ₑ * ENNReal.ofReal (r ^ N) ≤ 2 * (ENNReal.ofReal X * E) := by
    rw [← hQ, ← setLIntegral_const]
    calc ∫⁻ _ in cube r c, ‖f y - f z‖ₑ
        ≤ ∫⁻ w in cube r c, (‖f w - f y‖ₑ + ‖f w - f z‖ₑ) := by
          refine lintegral_mono fun w => ?_
          rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
          exact edist_triangle_left _ _ _
      _ = (∫⁻ w in cube r c, ‖f w - f y‖ₑ) + ∫⁻ w in cube r c, ‖f w - f z‖ₑ :=
          lintegral_add_left (hfm.sub_const _).enorm _
      _ ≤ ENNReal.ofReal X * E + ENNReal.ofReal X * E :=
          add_le_add (setLIntegral_enorm_sub_le hp hNp hf hr hy)
            (setLIntegral_enorm_sub_le hp hNp hf hr hz)
      _ = 2 * (ENNReal.ofReal X * E) := (two_mul _).symm
  have h := (ENNReal.le_div_iff_mul_le (Or.inl hQ0) (Or.inl ENNReal.ofReal_ne_top)).2 hmain
  refine h.trans (le_of_eq ?_)
  have hreal : 2 * X / r ^ N = 2 / (1 - N / p) * r ^ (1 - (N : ℝ) / p) := by
    have h1 : r * r ^ ((N : ℝ) - N / p) = r ^ (1 + ((N : ℝ) - N / p)) := by
      rw [Real.rpow_add hr, Real.rpow_one]
    have h2 : r ^ (1 - (N : ℝ) / p) = r ^ (1 + ((N : ℝ) - N / p)) / r ^ N := by
      rw [← Real.rpow_natCast r N, ← Real.rpow_sub hr]; ring_nf
    rw [h2, ← h1]
    simp only [X]
    ring
  have e2 : ENNReal.ofReal (2 * X) = 2 * ENNReal.ofReal X := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [← hreal, ENNReal.ofReal_div_of_pos (by positivity), e2, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Morrey's inequality for weakly differentiable functions, with an affine correction.** Let
`φ, g ∈ Lᵖ(ℝᴺ)` with `g` a weak gradient of `φ` on `U`, and `Q = Q_r(c)` with
`closedBall z δ ⊆ U` for `z ∈ Q`. For `p > N`, every `ξ` and `x₀`, and a.e. `y, z ∈ Q`,
`|(φ(y) - ξ(y - x₀)) - (φ(z) - ξ(z - x₀))| ≤ 2/(1 - N/p) · r^{1 - N/p} ‖g - ξ‖_{Lᵖ(Q)}`.
Proof: Morrey for the mollifications `ηₙ ⋆ φ` (`morrey_C1_cube`), then `n → ∞`. -/
theorem morrey_weak_cube [NeZero N] {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {U : Set (Sp N)} {φ : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hφ : MemLp φ (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hweak : HasWeakGrad U φ g) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) {c : Sp N}
    (hU : ∀ z ∈ cube r c, closedBall z δ ⊆ U) (ξ : Mat m N) (x₀ : Sp N) :
    ∀ᵐ y ∂(volume.restrict (cube r c)), ∀ᵐ z ∂(volume.restrict (cube r c)),
      ‖(φ y - ξ (y - x₀)) - (φ z - ξ (z - x₀))‖ₑ ≤
        ENNReal.ofReal (2 / (1 - N / p) * r ^ (1 - (N : ℝ) / p)) *
          eLpNorm (fun w => g w - ξ) (ENNReal.ofReal p) (volume.restrict (cube r c)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hφl : LocallyIntegrable φ volume := hφ.locallyIntegrable hp1
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable hp1
  have hQm : MeasurableSet (cube r c) := (isOpen_cube r c).measurableSet
  set C : ℝ≥0∞ := ENNReal.ofReal (2 / (1 - N / p) * r ^ (1 - (N : ℝ) / p))
  set B : ℝ≥0∞ := eLpNorm (fun w => g w - ξ) (ENNReal.ofReal p) (volume.restrict (cube r c))
  set η : ℕ → ContDiffBump (0 : Sp N) := fun n =>
    halfBump (show 0 < δ / ((n : ℝ) + 2) by positivity)
  have hrOut : Tendsto (fun n => (η n).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hK : ∀ᶠ n in atTop, (η n).rOut ≤ 2 * (η n).rIn :=
    Eventually.of_forall fun n => by
      simp only [η, halfBump]; linarith [show 0 < δ / ((n : ℝ) + 2) by positivity]
  have hrδ : ∀ n, (η n).rOut ≤ δ := fun n => by
    change δ / ((n : ℝ) + 2) ≤ δ
    rw [div_le_iff₀ (by positivity)]; nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hφae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hrOut hK hφl
  set u : ℕ → Sp N → Tgt m := fun n =>
    (η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ
  set v : ℕ → Sp N → Mat m N := fun n =>
    (η n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  set A : Sp N → Tgt m := fun w => ξ (w - x₀)
  have hAd : ∀ w, HasFDerivAt A ξ w := fun w => by
    have h := ξ.hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const x₀)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hA : ContDiff ℝ 1 A := ξ.contDiff.comp (contDiff_id.sub contDiff_const)
  have hu : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    (η n).hasCompactSupport_normed.contDiff_convolution_left _ (η n).contDiff_normed hφl
  have hder : ∀ n, ∀ w ∈ cube r c, fderiv ℝ (u n - A) w = v n w - ξ := by
    intro n w hw
    rw [fderiv_sub ((hu n).differentiable one_ne_zero w) (hAd w).differentiableAt,
      (hAd w).fderiv]
    congr 1
    exact fderiv_convolution_eq_convolution_grad_local (φg := (φ, g)) hφl hgl hweak (η n)
      ((closedBall_subset_closedBall (hrδ n)).trans (hU w hw))
  have hmor : ∀ n, ∀ y ∈ cube r c, ∀ z ∈ cube r c,
      ‖(u n - A) y - (u n - A) z‖ₑ ≤
        C * eLpNorm (fun w => v n w - ξ) (ENNReal.ofReal p) (volume.restrict (cube r c)) := by
    intro n y hy z hz
    refine (morrey_C1_cube hp hNp ((hu n).sub hA) hr hy hz).trans (le_of_eq ?_)
    congr 1
    exact eLpNorm_congr_ae (ae_restrict_of_forall_mem hQm (hder n))
  have hvc : ∀ n, Continuous (v n) := fun n =>
    (η n).hasCompactSupport_normed.continuous_convolution_left _ (η n).continuous_normed hgl
  have hbound : ∀ n, eLpNorm (fun w => v n w - ξ) (ENNReal.ofReal p) (volume.restrict (cube r c))
      ≤ eLpNorm (v n - g) (ENNReal.ofReal p) volume + B := by
    intro n
    have he : (fun w => v n w - ξ) = (v n - g) + fun w => g w - ξ := by
      funext w; simp
    rw [he]
    refine (eLpNorm_add_le ((hvc n).aestronglyMeasurable.sub hg.1).restrict
      (hg.1.sub aestronglyMeasurable_const).restrict hp1).trans ?_
    gcongr
    · exact Measure.restrict_le_self
    · exact le_rfl
  have hconv : Tendsto (fun n => eLpNorm (v n - g) (ENNReal.ofReal p) volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_bump_convolution_sub hp hg hrOut
  have hrhs : Tendsto (fun n => C * (eLpNorm (v n - g) (ENNReal.ofReal p) volume + B)) atTop
      (𝓝 (C * B)) := by
    have := ENNReal.Tendsto.const_mul (hconv.add (tendsto_const_nhds (x := B)))
      (Or.inr (ENNReal.ofReal_ne_top (r := 2 / (1 - N / p) * r ^ (1 - (N : ℝ) / p))))
    rwa [zero_add] at this
  filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hφae] with y hyQ hy
  filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hφae] with z hzQ hz
  have hlim : Tendsto (fun n => ‖(u n - A) y - (u n - A) z‖ₑ) atTop
      (𝓝 ‖(φ y - A y) - (φ z - A z)‖ₑ) :=
    ((hy.sub_const (A y)).sub (hz.sub_const (A z))).enorm
  exact le_of_tendsto_of_tendsto' hlim hrhs fun n =>
    (hmor n y hyQ z hzQ).trans (by gcongr; exact hbound n)

/-- **`Lᵖ` Lebesgue points on cubes.** If `F ∈ Lᵖ_loc`, `1 ≤ p`, then at a.e. `x`,
`(∫_{Q_ρ(x)} |F - F(x)|ᵖ) / |Q_ρ(x)| → 0` as `ρ → 0⁺`. -/
theorem ae_tendsto_cube_enorm_sub_rpow [NeZero N] {E : Type*} [NormedAddCommGroup E]
    [TopologicalSpace.SeparableSpace E] {p : ℝ} (hp : 1 ≤ p) {F : Sp N → E}
    (hF : ∀ K : Set (Sp N), IsCompact K → MemLp F (ENNReal.ofReal p) (volume.restrict K)) :
    ∀ᵐ x, Tendsto (fun ρ : ℝ => (∫⁻ z in cube ρ x, ‖F z - F x‖ₑ ^ p) / volume (cube ρ x))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq E
  have hp0 : 0 < p := by linarith
  have h2 : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  have hloc : ∀ k, LocallyIntegrable (fun z => ‖F z - q k‖ ^ p) volume := by
    intro k
    rw [locallyIntegrable_iff]
    intro K hK
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    have h := ((hF K hK).sub (memLp_const (q k))).integrable_norm_rpow
      (by simp; linarith) ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp0.le] at h
    exact h
  have hall := ae_all_iff.2 fun k => ae_tendsto_setLIntegral_affMap_div (hloc k)
  filter_upwards [hall] with x hx
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set T : ℝ≥0∞ → ℝ≥0∞ := fun t => 2 ^ (p - 1) * (t ^ p + t ^ p)
  have hT : Tendsto T (𝓝 0) (𝓝 0) := by
    have hc : Continuous T :=
      (ENNReal.continuous_const_mul h2).comp
        (ENNReal.continuous_rpow_const.add ENNReal.continuous_rpow_const)
    have := hc.tendsto 0
    simpa [T, ENNReal.zero_rpow_of_pos hp0] using this
  obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.1
    (show F x ∈ closure (range q) by rw [hq.closure_range]; exact mem_univ _)
  have hd : Tendsto (fun j => ‖F x - w j‖ₑ) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := F x)).sub hwlim).enorm
    simpa using this
  obtain ⟨j, hj⟩ := ((hT.comp hd).eventually (gt_mem_nhds hε)).exists
  obtain ⟨k, hk⟩ := hw j
  rw [Function.comp_apply, ← hk] at hj
  set c : ℝ≥0∞ := ‖q k - F x‖ₑ ^ p
  have hA := hx k (cube 1 0) (isOpen_cube 1 0) (isBounded_cube 1 0)
    ⟨0, self_mem_cube one_pos 0⟩
  have hlim : Tendsto (fun ρ : ℝ => 2 ^ (p - 1) *
      ((∫⁻ y in affMap ρ x ⁻¹' cube 1 0, ENNReal.ofReal (‖F y - q k‖ ^ p)) /
        volume (affMap ρ x ⁻¹' cube 1 0) + c)) (𝓝[>] 0) (𝓝 (T ‖F x - q k‖ₑ)) := by
    have := ENNReal.Tendsto.const_mul (hA.add (tendsto_const_nhds (x := c))) (Or.inr h2)
    convert this using 2
    simp only [T, c]
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm, enorm_sub_rev (F x)]
  filter_upwards [hlim.eventually (gt_mem_nhds hj), self_mem_nhdsWithin] with ρ hρε hρ
  refine le_trans ?_ hρε.le
  rw [preimage_affMap_cube hρ x]
  have hV0 := volume_cube_ne_zero' hρ x
  have hVt := volume_cube_ne_top ρ x
  calc (∫⁻ z in cube ρ x, ‖F z - F x‖ₑ ^ p) / volume (cube ρ x)
      ≤ (∫⁻ z in cube ρ x, 2 ^ (p - 1) * (ENNReal.ofReal (‖F z - q k‖ ^ p) + c)) /
          volume (cube ρ x) := by
        gcongr with z
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
        calc ‖F z - F x‖ₑ ^ p ≤ (‖F z - q k‖ₑ + ‖q k - F x‖ₑ) ^ p := by
              gcongr
              rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
              exact edist_triangle _ _ _
          _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ = 2 ^ (p - 1) * ((∫⁻ z in cube ρ x, ENNReal.ofReal (‖F z - q k‖ ^ p)) /
          volume (cube ρ x) + c) := by
        rw [lintegral_const_mul' _ _ h2, lintegral_add_right _ measurable_const,
          setLIntegral_const, mul_div_assoc, ENNReal.add_div,
          ENNReal.mul_div_cancel_right hV0 hVt]

/-- Concentric cubes are nested. -/
theorem cube_subset_cube_of_le {r ρ : ℝ} (h : r ≤ ρ) (x : Sp N) : cube r x ⊆ cube ρ x := by
  intro z hz
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hz ⊢
  intro i
  obtain ⟨h1, h2⟩ := hz i
  constructor <;> linarith

/-- An a.e. oscillation bound `|v(y) - v(z)| ≤ M` on `Q_ρ(x)` and the Lebesgue-point property of
`v` at `x` with value `a` give `|v(y) - a| ≤ M`. -/
theorem enorm_sub_le_of_ae_osc [NeZero N] {v : Sp N → Tgt m} {a : Tgt m} {x y : Sp N} {ρ : ℝ}
    (hρ : 0 < ρ) {M : ℝ≥0∞}
    (hy : ∀ᵐ z ∂(volume.restrict (cube ρ x)), ‖v y - v z‖ₑ ≤ M)
    (hleb : Tendsto (fun r : ℝ => (∫⁻ z in cube r x, ‖v z - a‖ₑ) / volume (cube r x))
      (𝓝[>] 0) (𝓝 0)) :
    ‖v y - a‖ₑ ≤ M := by
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖v y - a‖ₑ ≤ M + (∫⁻ z in cube r x, ‖v z - a‖ₑ) / volume (cube r x) := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    have hyr := ae_restrict_of_ae_restrict_of_subset (cube_subset_cube_of_le hr.2.le x) hy
    have hV0 := volume_cube_ne_zero' hr.1 x
    have hVt := volume_cube_ne_top r x
    calc ‖v y - a‖ₑ = (‖v y - a‖ₑ * volume (cube r x)) / volume (cube r x) :=
          (ENNReal.mul_div_cancel_right hV0 hVt).symm
      _ = (∫⁻ _ in cube r x, ‖v y - a‖ₑ) / volume (cube r x) := by rw [setLIntegral_const]
      _ ≤ (∫⁻ z in cube r x, (M + ‖v z - a‖ₑ)) / volume (cube r x) := by
          refine ENNReal.div_le_div_right (lintegral_mono_ae (hyr.mono fun z hz => ?_)) _
          calc ‖v y - a‖ₑ ≤ ‖v y - v z‖ₑ + ‖v z - a‖ₑ := by
                rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
                exact edist_triangle _ _ _
            _ ≤ M + ‖v z - a‖ₑ := by gcongr
      _ = M + (∫⁻ z in cube r x, ‖v z - a‖ₑ) / volume (cube r x) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, ENNReal.add_div,
            ENNReal.mul_div_cancel_right hV0 hVt]
  have hlim := (tendsto_const_nhds (x := M)).add hleb
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim hev

/-- Lebesgue point of `φ` at `x` ⇒ Lebesgue point of `φ - ξ(· - x)` at `x`, same value. -/
theorem tendsto_cube_enorm_sub_affine [NeZero N] {φ : Sp N → Tgt m} {x : Sp N} (ξ : Mat m N)
    (hφ : Tendsto (fun r : ℝ => (∫⁻ z in cube r x, ‖φ z - φ x‖ₑ) / volume (cube r x))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => (∫⁻ z in cube r x, ‖(φ z - ξ (z - x)) - φ x‖ₑ) / volume (cube r x))
      (𝓝[>] 0) (𝓝 0) := by
  have hr0 : Tendsto (fun r : ℝ => ‖ξ‖ₑ * ENNReal.ofReal r) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (enorm_ne_top (x := ξ)))
  have hup := hφ.add hr0
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  have hV0 := volume_cube_ne_zero' hr x
  have hVt := volume_cube_ne_top r x
  calc (∫⁻ z in cube r x, ‖(φ z - ξ (z - x)) - φ x‖ₑ) / volume (cube r x)
      ≤ (∫⁻ z in cube r x, (‖φ z - φ x‖ₑ + ‖ξ‖ₑ * ENNReal.ofReal r)) / volume (cube r x) := by
        refine ENNReal.div_le_div_right (setLIntegral_mono' (isOpen_cube r x).measurableSet
          fun z hz => ?_) _
        rw [show (φ z - ξ (z - x)) - φ x = (φ z - φ x) - ξ (z - x) by abel]
        refine (enorm_sub_le).trans (add_le_add le_rfl ((ContinuousLinearMap.le_opENorm _ _).trans
          ?_))
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_sub_le_of_mem_cube (self_mem_cube hr x) hz)
    _ = (∫⁻ z in cube r x, ‖φ z - φ x‖ₑ) / volume (cube r x) + ‖ξ‖ₑ * ENNReal.ofReal r := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, ENNReal.add_div,
          ENNReal.mul_div_cancel_right hV0 hVt]

/-- Morrey on `Q_ρ(x) ⊆ ball x (R/2)`, `ball x R ⊆ Ω`, combined with the Lebesgue-point property
of `φ` at `x`: `‖φ - φ(x) - g(x)(· - x)‖_{L^∞(Q_ρ(x))} ≤ C ρ^{1-N/p} ‖g - g(x)‖_{Lᵖ(Q_ρ(x))}`. -/
theorem eLpNorm_top_affine_le [NeZero N] {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {Ω : Set (Sp N)} {φ : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hφ : MemLp φ (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hweak : HasWeakGrad Ω φ g) {x : Sp N} {R ρ : ℝ} (hball : ball x R ⊆ Ω) (hρ : 0 < ρ)
    (hρR : ρ < R)
    (hv : Tendsto (fun r : ℝ => (∫⁻ z in cube r x, ‖(φ z - g x (z - x)) - φ x‖ₑ) /
      volume (cube r x)) (𝓝[>] 0) (𝓝 0)) :
    eLpNorm (fun y => (φ y - g x (y - x)) - φ x) ⊤ (volume.restrict (cube ρ x)) ≤
      ENNReal.ofReal (2 / (1 - N / p) * ρ ^ (1 - (N : ℝ) / p)) *
        eLpNorm (fun w => g w - g x) (ENNReal.ofReal p) (volume.restrict (cube ρ x)) := by
  have hQball : cube ρ x ⊆ ball x (R / 2) := by
    rw [cube_eq_ball hρ x]; exact ball_subset_ball (by linarith)
  have hU : ∀ z ∈ cube ρ x, closedBall z (R / 4) ⊆ Ω := by
    intro z hz w hw
    apply hball
    have h1 := mem_ball.1 (hQball hz)
    have h2 := mem_closedBall.1 hw
    rw [mem_ball]
    linarith [dist_triangle w z x]
  have hmor := morrey_weak_cube hp hNp hφ hg hweak hρ (by linarith : 0 < R / 4) hU (g x) x
  rw [eLpNorm_exponent_top]
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [hmor] with y hy
  exact enorm_sub_le_of_ae_osc (v := fun w => φ w - g x (w - x)) (a := φ x) hρ hy hv

/-- Scaling identity: `ρ⁻¹ · C ρ^{1-N/p} I^{1/p} = C (I / ρ^N)^{1/p}`. -/
theorem morrey_scaling_eq {p ρ C : ℝ} (hp0 : 0 < p) (hρ : 0 < ρ) (hC : 0 ≤ C) (I : ℝ≥0∞) :
    ENNReal.ofReal ρ⁻¹ * (ENNReal.ofReal (C * ρ ^ (1 - (N : ℝ) / p)) * I ^ (1 / p)) =
      ENNReal.ofReal C * (I / ENNReal.ofReal ρ ^ N) ^ (1 / p) := by
  have hρN : 0 < ρ ^ ((N : ℝ) / p) := by positivity
  have hrp : ρ ^ (1 - (N : ℝ) / p) = ρ / ρ ^ ((N : ℝ) / p) := by
    rw [Real.rpow_sub hρ, Real.rpow_one]
  have hrp' : (ρ ^ N) ^ (1 / p) = ρ ^ ((N : ℝ) / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le, mul_one_div]
  calc ENNReal.ofReal ρ⁻¹ * (ENNReal.ofReal (C * ρ ^ (1 - (N : ℝ) / p)) * I ^ (1 / p))
      = ENNReal.ofReal (ρ⁻¹ * (C * ρ ^ (1 - (N : ℝ) / p))) * I ^ (1 / p) := by
        rw [← mul_assoc, ENNReal.ofReal_mul (inv_nonneg.2 hρ.le)]
    _ = ENNReal.ofReal (C * ((ρ ^ N) ^ (1 / p))⁻¹) * I ^ (1 / p) := by
        congr 2
        rw [hrp, hrp']
        field_simp
    _ = ENNReal.ofReal C * (I / ENNReal.ofReal ρ ^ N) ^ (1 / p) := by
        rw [ENNReal.div_rpow_of_nonneg _ _ (by positivity), ← ENNReal.ofReal_pow hρ.le,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ENNReal.ofReal_mul hC,
          ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.div_eq_inv_mul, mul_assoc]

/-- **A.e. differentiability of `W^{1,p}` functions, `p > N`** (eq. `difflowerbound` of the
paper), with the tangent map `u_x = u(x) + ∇u(x)(· - x)` of the given representative: for a.e.
`x ∈ Ω`, `ρ⁻¹ ‖u - u_x‖_{L^∞(Q_ρ(x))} → 0`. At such `x` (an `L¹` Lebesgue point of `u` and an
`Lᵖ` Lebesgue point of `∇u`), Morrey's inequality on `Q_ρ(x)` (`morrey_weak_cube`) applied to
`u - ∇u(x)(· - x)` gives `ρ⁻¹ ‖u - u_x‖_{L^∞(Q_ρ(x))} ≤ C (⨍_{Q_ρ(x)} |∇u - ∇u(x)|ᵖ)^{1/p} → 0`. -/
theorem W1p.ae_tendsto_affine_remainder [NeZero N] {p : ℝ} (hNp : (N : ℝ) < p)
    {Ω : Set (Sp N)} (hΩ : IsOpen Ω) (u : W1p N m (ENNReal.ofReal p) Ω) :
    ∀ᵐ x ∂(volume.restrict Ω),
      Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
          eLpNorm (fun y => u.toFun y - affineMap (u.toFun x) (u.grad x) x y) ⊤
            (volume.restrict (cube ρ x)))
        (𝓝[>] 0) (𝓝 0) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hp : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hφ : MemLp (Ω.indicator u.toFun) (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict (f := u.toFun) hΩm).2 u.memLp
  have hg : MemLp (Ω.indicator u.grad) (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict (f := u.grad) hΩm).2 u.memLp_grad
  have hφK : ∀ K : Set (Sp N), IsCompact K →
      MemLp (Ω.indicator u.toFun) (ENNReal.ofReal 1) (volume.restrict K) := fun K hK => by
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact (hφ.restrict K).mono_exponent (ENNReal.ofReal_le_ofReal hp)
  filter_upwards [ae_restrict_mem hΩm,
    ae_restrict_of_ae (ae_tendsto_cube_enorm_sub_rpow hp fun K _ => hg.restrict K),
    ae_restrict_of_ae (ae_tendsto_cube_enorm_sub_rpow le_rfl hφK)] with x hxΩ hgx hφx
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hΩ x hxΩ
  have hgx' : Ω.indicator u.grad x = u.grad x := indicator_of_mem hxΩ _
  have hφx' : Ω.indicator u.toFun x = u.toFun x := indicator_of_mem hxΩ _
  have hφx1 : Tendsto (fun r : ℝ => (∫⁻ z in cube r x,
      ‖Ω.indicator u.toFun z - Ω.indicator u.toFun x‖ₑ) / volume (cube r x))
      (𝓝[>] 0) (𝓝 0) := by simpa using hφx
  have hv := tendsto_cube_enorm_sub_affine (Ω.indicator u.grad x) hφx1
  set C : ℝ := 2 / (1 - N / p)
  have hC : 0 ≤ C := div_nonneg (by norm_num) (by rw [sub_nonneg, div_le_one hp0]; linarith)
  have key : ∀ ρ : ℝ, 0 < ρ → ρ < R →
      ENNReal.ofReal ρ⁻¹ * eLpNorm (fun y => u.toFun y - affineMap (u.toFun x) (u.grad x) x y) ⊤
        (volume.restrict (cube ρ x)) ≤ ENNReal.ofReal C *
          ((∫⁻ z in cube ρ x, ‖Ω.indicator u.grad z - Ω.indicator u.grad x‖ₑ ^ p) /
            volume (cube ρ x)) ^ (1 / p) := by
    intro ρ hρ hρR
    have hQΩ : cube ρ x ⊆ Ω := by
      rw [cube_eq_ball hρ x]; exact (ball_subset_ball (by linarith)).trans hball
    have hcongr : (fun y => u.toFun y - affineMap (u.toFun x) (u.grad x) x y) =ᵐ[volume.restrict
        (cube ρ x)] fun y => (Ω.indicator u.toFun y - Ω.indicator u.grad x (y - x)) -
          Ω.indicator u.toFun x := by
      filter_upwards [ae_restrict_mem (isOpen_cube ρ x).measurableSet] with y hy
      simp only [affineMap, indicator_of_mem (hQΩ hy), hgx', hφx']
      abel
    rw [eLpNorm_congr_ae hcongr]
    refine (mul_le_mul' le_rfl (eLpNorm_top_affine_le hp hNp hφ hg u.weak.indicator hball hρ
      hρR hv)).trans (le_of_eq ?_)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le, volume_cube, ← morrey_scaling_eq hp0 hρ hC]
  have hlimR : Tendsto (fun ρ : ℝ => ENNReal.ofReal C *
      ((∫⁻ z in cube ρ x, ‖Ω.indicator u.grad z - Ω.indicator u.grad x‖ₑ ^ p) /
        volume (cube ρ x)) ^ (1 / p)) (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul
      (((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hgx)
      (Or.inr (ENNReal.ofReal_ne_top (r := C)))
    simpa [ENNReal.zero_rpow_of_pos (inv_pos.2 hp0)] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimR
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with ρ hρ
  exact key ρ hρ.1 hρ.2

/-- **Cited result (b) proved**: `CitedSobolevDiff` holds, with `a = u(x)`
(`W1p.ae_tendsto_affine_remainder`). -/
theorem citedSobolevDiff_holds [NeZero N] (p : ℝ) : CitedSobolevDiff N m p :=
  fun hNp _ hΩ u => (W1p.ae_tendsto_affine_remainder hNp hΩ u).mono fun x hx => ⟨u.toFun x, hx⟩

end Homogenization
