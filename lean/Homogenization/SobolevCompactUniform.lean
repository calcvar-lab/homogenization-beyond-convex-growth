import Homogenization.SobolevCompact

/-!
# The cited result (a): uniform convergence on Lipschitz domains

* Morrey's inequality on open convex sets (`morrey_C1_convex`, `morrey_weak_convex`) and the
  resulting sup bound on a convex set (`ae_enorm_le_of_convex`);
* uniform convergence from a cover of `S` by convex sets, uniform in the scale
  (`eventually_ae_enorm_le_of_convex_cover`);
* such covers: truncated cones in the coordinates of a Lipschitz chart (`coneSet`,
  `exists_cone_cover_of_chart`) and cubes inside a compact subset
  (`exists_cube_cover_of_compact`);
* `citedSobolevCompact_holds`: the cited result (a) `CitedSobolevCompact` holds, (a1) by the
  above and (a2) by `W1p.grad_mem_of_tendsto` (`SobolevCompact.lean`).
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution

namespace Homogenization

variable {N m : ℕ}

/-- For `C` convex and `y ∈ C`, `t ∈ (0,1]`, the homothetic copy `y + t(C - y)` lies in `C`. -/
theorem homothety_inv_preimage_subset {C : Set (Sp N)} (hC : Convex ℝ C) {y : Sp N}
    (hy : y ∈ C) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : homothety y t⁻¹ ⁻¹' C ⊆ C := by
  intro z hz
  have h := hC.add_smul_sub_mem hy hz ⟨ht.le, ht1⟩
  convert h using 1
  simp [homothety, smul_smul, mul_inv_cancel₀ ht.ne']

/-- `y + t(w - y)` lies in `y + t(C - y)` for `w ∈ C`. -/
theorem mem_preimage_homothety_inv {y : Sp N} {t : ℝ} (ht : 0 < t) {C : Set (Sp N)}
    {w : Sp N} (hw : w ∈ C) : homothety y t w ∈ homothety y t⁻¹ ⁻¹' C := by
  simpa [homothety, smul_smul, inv_mul_cancel₀ ht.ne'] using hw

/-- `|y + t(C - y)| = tᴺ |C|`. -/
theorem volume_homothety_inv_preimage {C : Set (Sp N)} (hCm : MeasurableSet C) (y : Sp N)
    {t : ℝ} (ht : 0 < t) :
    volume (homothety y t⁻¹ ⁻¹' C) = ENNReal.ofReal (t ^ N) * volume C := by
  have h := setLIntegral_comp_homothety (fun _ => (1 : ℝ≥0∞)) (inv_pos.2 ht) y hCm
  simp only [setLIntegral_const, one_mul] at h
  rw [h, inv_pow, inv_inv, abs_of_pos (by positivity)]

/-- Change of variables along the homothety of center `y ∈ C` and ratio `t ∈ (0,1]`, then Hölder
on `y + t(C - y) ⊆ C`, for an open convex `C`. -/
theorem setLIntegral_fderiv_homothety_le_convex {p : ℝ} (hp : 1 ≤ p) {f : Sp N → Tgt m}
    (hf : ContDiff ℝ 1 f) {C : Set (Sp N)} (hCo : IsOpen C) (hC : Convex ℝ C) {y : Sp N}
    (hy : y ∈ C) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∫⁻ w in C, ‖fderiv ℝ f (homothety y t w)‖ₑ ≤
      ENNReal.ofReal (t ^ (-((N : ℝ) / p))) * volume C ^ (1 - 1 / p) *
        eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict C) := by
  set Ct := homothety y t⁻¹ ⁻¹' C
  set E := eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict C)
  have hcont := hf.continuous_fderiv one_ne_zero
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hs : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hp
  have hhc : Continuous (homothety (N := N) y t⁻¹) := by unfold homothety; fun_prop
  have hCtm : MeasurableSet Ct := (hCo.preimage hhc).measurableSet
  calc ∫⁻ w in C, ‖fderiv ℝ f (homothety y t w)‖ₑ
      ≤ ∫⁻ w in homothety y t ⁻¹' Ct, ‖fderiv ℝ f (homothety y t w)‖ₑ :=
        lintegral_mono_set fun w hw => mem_preimage_homothety_inv ht hw
    _ = ENNReal.ofReal |(t ^ N)⁻¹| * ∫⁻ z in Ct, ‖fderiv ℝ f z‖ₑ :=
        setLIntegral_comp_homothety (fun z => ‖fderiv ℝ f z‖ₑ) ht y hCtm
    _ ≤ ENNReal.ofReal ((t ^ N)⁻¹) * (E * volume Ct ^ (1 - 1 / p)) := by
        rw [abs_of_nonneg (by positivity)]
        gcongr
        have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict Ct) hp1
          hcont.aestronglyMeasurable
        rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ, ENNReal.toReal_one,
          ENNReal.toReal_ofReal (by linarith), div_one] at h
        refine h.trans ?_
        gcongr
        exact eLpNorm_mono_measure _
          (Measure.restrict_mono (homothety_inv_preimage_subset hC hy ht ht1) le_rfl)
    _ = ENNReal.ofReal (t ^ (-((N : ℝ) / p))) * volume C ^ (1 - 1 / p) * E := by
        rw [volume_homothety_inv_preimage hCo.measurableSet y ht,
          ENNReal.mul_rpow_of_nonneg _ _ hs, ENNReal.ofReal_rpow_of_nonneg (by positivity) hs]
        have hreal : (t ^ N)⁻¹ * (t ^ N) ^ (1 - 1 / p) = t ^ (-((N : ℝ) / p)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le,
            ← Real.rpow_add ht]
          ring_nf
        rw [← hreal, ENNReal.ofReal_mul (by positivity)]
        ring

/-- **Morrey, integrated form, on an open convex set** `C` with `‖w - y‖ ≤ d` on `C`:
`∫_C |f(w) - f(y)| dw ≤ d/(1 - N/p) · |C|^{1 - 1/p} ‖∇f‖_{Lᵖ(C)}`. -/
theorem setLIntegral_enorm_sub_le_convex {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f) {C : Set (Sp N)} (hCo : IsOpen C)
    (hC : Convex ℝ C) {y : Sp N} (hy : y ∈ C) {d : ℝ} (hd : ∀ w ∈ C, ‖w - y‖ ≤ d) :
    ∫⁻ w in C, ‖f w - f y‖ₑ ≤
      ENNReal.ofReal (d * (1 / (1 - N / p))) * volume C ^ (1 - 1 / p) *
        eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict C) := by
  set E := eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict C)
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd y hy)
  have hcont := hf.continuous_fderiv one_ne_zero
  have hh : Continuous (fun q : Sp N × ℝ => homothety y q.2 q.1) := by
    unfold homothety; fun_prop
  have hh1 : ∀ t : ℝ, Continuous (fun w : Sp N => homothety y t w) := by
    intro t; unfold homothety; fun_prop
  have hNp1 : (N : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hNp
  calc ∫⁻ w in C, ‖f w - f y‖ₑ
      ≤ ∫⁻ w in C, ∫⁻ t in Ioc (0 : ℝ) 1,
          ‖fderiv ℝ f (homothety y t w)‖ₑ * ENNReal.ofReal d := by
        refine setLIntegral_mono' hCo.measurableSet fun w hw =>
          (enorm_sub_le_lintegral_fderiv hf y w).trans (lintegral_mono fun t => ?_)
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hd w hw)
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ w in C,
          ‖fderiv ℝ f (homothety y t w)‖ₑ * ENNReal.ofReal d :=
        lintegral_lintegral_swap ((hcont.comp hh).measurable.enorm.mul_const _).aemeasurable
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-((N : ℝ) / p))) *
          (volume C ^ (1 - 1 / p) * E * ENNReal.ofReal d) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        rw [lintegral_mul_const _ (show Measurable fun w => ‖fderiv ℝ f (homothety y t w)‖ₑ from
          (hcont.comp (hh1 t)).measurable.enorm)]
        calc (∫⁻ w in C, ‖fderiv ℝ f (homothety y t w)‖ₑ) * ENNReal.ofReal d
            ≤ ENNReal.ofReal (t ^ (-((N : ℝ) / p))) * volume C ^ (1 - 1 / p) * E *
                ENNReal.ofReal d := by
              gcongr
              exact setLIntegral_fderiv_homothety_le_convex hp hf hCo hC hy ht.1 ht.2
          _ = _ := by ring
    _ = ENNReal.ofReal (1 / (1 - N / p)) *
          (volume C ^ (1 - 1 / p) * E * ENNReal.ofReal d) := by
        rw [lintegral_mul_const _
          (show Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-((N : ℝ) / p)))
          from (measurable_id.pow_const _).ennreal_ofReal),
          lintegral_Ioc_rpow_neg hNp1]
    _ = _ := by
        rw [ENNReal.ofReal_mul hd0]
        ring

/-- **Morrey's inequality for `C¹` functions on an open convex set** `C` of finite positive
measure and diameter `≤ d`: for `y, z ∈ C`,
`|f(y) - f(z)| ≤ 2d/(1 - N/p) · |C|^{-1/p} ‖∇f‖_{Lᵖ(C)}`. -/
theorem morrey_C1_convex {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f) {C : Set (Sp N)} (hCo : IsOpen C)
    (hC : Convex ℝ C) (hC0 : volume C ≠ 0) (hCt : volume C ≠ ⊤) {d : ℝ}
    (hd : ∀ w ∈ C, ∀ w' ∈ C, ‖w - w'‖ ≤ d) {y z : Sp N} (hy : y ∈ C) (hz : z ∈ C) :
    ‖f y - f z‖ₑ ≤ ENNReal.ofReal (2 * (d * (1 / (1 - N / p)))) * volume C ^ (-(1 / p)) *
      eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict C) := by
  set E := eLpNorm (fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict C)
  set X : ℝ := d * (1 / (1 - N / p))
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd y hy y hy)
  have hX : 0 ≤ X := mul_nonneg hd0 (by
    have : (N : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hNp
    rw [one_div]; exact inv_nonneg.2 (by linarith))
  have hfm : Measurable f := hf.continuous.measurable
  have hA : ∀ y' ∈ C, ∫⁻ w in C, ‖f w - f y'‖ₑ ≤
      ENNReal.ofReal X * volume C ^ (1 - 1 / p) * E := fun y' hy' =>
    setLIntegral_enorm_sub_le_convex hp hNp hf hCo hC hy' fun w hw => hd w hw y' hy'
  have hmain : ‖f y - f z‖ₑ * volume C ≤
      2 * (ENNReal.ofReal X * volume C ^ (1 - 1 / p) * E) := by
    rw [← setLIntegral_const]
    calc ∫⁻ _ in C, ‖f y - f z‖ₑ
        ≤ ∫⁻ w in C, (‖f w - f y‖ₑ + ‖f w - f z‖ₑ) := by
          refine lintegral_mono fun w => ?_
          rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
          exact edist_triangle_left _ _ _
      _ = (∫⁻ w in C, ‖f w - f y‖ₑ) + ∫⁻ w in C, ‖f w - f z‖ₑ :=
          lintegral_add_left (hfm.sub_const _).enorm _
      _ ≤ ENNReal.ofReal X * volume C ^ (1 - 1 / p) * E +
            ENNReal.ofReal X * volume C ^ (1 - 1 / p) * E := add_le_add (hA y hy) (hA z hz)
      _ = 2 * (ENNReal.ofReal X * volume C ^ (1 - 1 / p) * E) := (two_mul _).symm
  have h := (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCt)).2 hmain
  refine h.trans (le_of_eq ?_)
  have hpow : volume C ^ (1 - 1 / p) / volume C = volume C ^ (-(1 / p)) := by
    rw [show -(1 / p) = (1 - 1 / p) - 1 by ring, ENNReal.rpow_sub (1 - 1 / p) 1 hC0 hCt,
      ENNReal.rpow_one]
  have e2 : ENNReal.ofReal (2 * X) = 2 * ENNReal.ofReal X := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [e2, ← hpow]
  simp only [div_eq_mul_inv]
  ring

/-- **Morrey's inequality for weakly differentiable functions on an open convex set** `C` with
`closedBall z δ ⊆ U` for `z ∈ C`: for a.e. `y, z ∈ C`,
`|φ(y) - φ(z)| ≤ 2d/(1 - N/p) · |C|^{-1/p} ‖g‖_{Lᵖ(C)}`. -/
theorem morrey_weak_convex {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {U : Set (Sp N)} {φ : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hφ : MemLp φ (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hweak : HasWeakGrad U φ g) {C : Set (Sp N)} (hCo : IsOpen C) (hC : Convex ℝ C)
    (hC0 : volume C ≠ 0) (hCt : volume C ≠ ⊤) {d δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ w ∈ C, ∀ w' ∈ C, ‖w - w'‖ ≤ d) (hU : ∀ z ∈ C, closedBall z δ ⊆ U) :
    ∀ᵐ y ∂(volume.restrict C), ∀ᵐ z ∂(volume.restrict C),
      ‖φ y - φ z‖ₑ ≤ ENNReal.ofReal (2 * (d * (1 / (1 - N / p)))) * volume C ^ (-(1 / p)) *
        eLpNorm g (ENNReal.ofReal p) (volume.restrict C) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hφl : LocallyIntegrable φ volume := hφ.locallyIntegrable hp1
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable hp1
  have hQm : MeasurableSet C := hCo.measurableSet
  set Cst : ℝ≥0∞ := ENNReal.ofReal (2 * (d * (1 / (1 - N / p)))) * volume C ^ (-(1 / p))
  have hCst : Cst ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero hC0 hCt)
  set B : ℝ≥0∞ := eLpNorm g (ENNReal.ofReal p) (volume.restrict C)
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
  have hu : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    (η n).hasCompactSupport_normed.contDiff_convolution_left _ (η n).contDiff_normed hφl
  have hder : ∀ n, ∀ w ∈ C, fderiv ℝ (u n) w = v n w := fun n w hw =>
    fderiv_convolution_eq_convolution_grad_local (φg := (φ, g)) hφl hgl hweak (η n)
      ((closedBall_subset_closedBall (hrδ n)).trans (hU w hw))
  have hmor : ∀ n, ∀ y ∈ C, ∀ z ∈ C,
      ‖u n y - u n z‖ₑ ≤ Cst * eLpNorm (v n) (ENNReal.ofReal p) (volume.restrict C) := by
    intro n y hy z hz
    refine (morrey_C1_convex hp hNp (hu n) hCo hC hC0 hCt hd hy hz).trans (le_of_eq ?_)
    congr 1
    exact eLpNorm_congr_ae (ae_restrict_of_forall_mem hQm (hder n))
  have hvc : ∀ n, Continuous (v n) := fun n =>
    (η n).hasCompactSupport_normed.continuous_convolution_left _ (η n).continuous_normed hgl
  have hbound : ∀ n, eLpNorm (v n) (ENNReal.ofReal p) (volume.restrict C)
      ≤ eLpNorm (v n - g) (ENNReal.ofReal p) volume + B := by
    intro n
    have h1 : AEStronglyMeasurable (v n - g) (volume.restrict C) :=
      ((hvc n).aestronglyMeasurable.sub hg.1).restrict
    have h2 : AEStronglyMeasurable g (volume.restrict C) := hg.1.restrict
    have hadd := eLpNorm_add_le (f := v n - g) (g := g) (μ := volume.restrict C)
      (p := ENNReal.ofReal p) h1 h2 hp1
    rw [sub_add_cancel] at hadd
    refine hadd.trans ?_
    gcongr
    exact Measure.restrict_le_self
  have hconv : Tendsto (fun n => eLpNorm (v n - g) (ENNReal.ofReal p) volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_bump_convolution_sub hp hg hrOut
  have hrhs : Tendsto (fun n => Cst * (eLpNorm (v n - g) (ENNReal.ofReal p) volume + B)) atTop
      (𝓝 (Cst * B)) := by
    have := ENNReal.Tendsto.const_mul (hconv.add (tendsto_const_nhds (x := B))) (Or.inr hCst)
    rwa [zero_add] at this
  filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hφae] with y hyQ hy
  filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hφae] with z hzQ hz
  have hlim : Tendsto (fun n => ‖u n y - u n z‖ₑ) atTop (𝓝 ‖φ y - φ z‖ₑ) :=
    (hy.sub hz).enorm
  exact le_of_tendsto_of_tendsto' hlim hrhs fun n =>
    (hmor n y hyQ z hzQ).trans (by gcongr; exact hbound n)

/-- **Sup bound on a convex set.** Under the hypotheses of `morrey_weak_convex`, for a.e.
`y ∈ C`, `|φ(y)| ≤ |C|^{-1/p} (‖φ‖_{Lᵖ(C)} + 2d/(1 - N/p) ‖g‖_{Lᵖ(C)})`. -/
theorem ae_enorm_le_of_convex {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {U : Set (Sp N)} {φ : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hφ : MemLp φ (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hweak : HasWeakGrad U φ g) {C : Set (Sp N)} (hCo : IsOpen C) (hC : Convex ℝ C)
    (hC0 : volume C ≠ 0) (hCt : volume C ≠ ⊤) {d δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ w ∈ C, ∀ w' ∈ C, ‖w - w'‖ ≤ d) (hU : ∀ z ∈ C, closedBall z δ ⊆ U) :
    ∀ᵐ y ∂(volume.restrict C), ‖φ y‖ₑ ≤ volume C ^ (-(1 / p)) *
      (eLpNorm φ (ENNReal.ofReal p) (volume.restrict C) +
        ENNReal.ofReal (2 * (d * (1 / (1 - N / p)))) *
          eLpNorm g (ENNReal.ofReal p) (volume.restrict C)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hQm : MeasurableSet C := hCo.measurableSet
  set M : ℝ≥0∞ := ENNReal.ofReal (2 * (d * (1 / (1 - N / p)))) * volume C ^ (-(1 / p)) *
    eLpNorm g (ENNReal.ofReal p) (volume.restrict C)
  set Eφ := eLpNorm φ (ENNReal.ofReal p) (volume.restrict C)
  have hmor := morrey_weak_convex hp hNp hφ hg hweak hCo hC hC0 hCt hδ hd hU
  filter_upwards [hmor] with y hy
  have hint : ∫⁻ z in C, ‖φ z‖ₑ ≤ Eφ * volume C ^ (1 - 1 / p) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict C) hp1
      hφ.1.restrict
    rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ, ENNReal.toReal_one,
      ENNReal.toReal_ofReal (by linarith), div_one] at h
    exact h
  have hmain : ‖φ y‖ₑ * volume C ≤ M * volume C + Eφ * volume C ^ (1 - 1 / p) := by
    rw [← setLIntegral_const]
    calc ∫⁻ _ in C, ‖φ y‖ₑ ≤ ∫⁻ z in C, (M + ‖φ z‖ₑ) := by
          refine lintegral_mono_ae (hy.mono fun z hz => ?_)
          calc ‖φ y‖ₑ ≤ ‖φ y - φ z‖ₑ + ‖φ z‖ₑ := by
                simpa using enorm_add_le (φ y - φ z) (φ z)
            _ ≤ M + ‖φ z‖ₑ := by gcongr
      _ = M * volume C + ∫⁻ z in C, ‖φ z‖ₑ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
      _ ≤ M * volume C + Eφ * volume C ^ (1 - 1 / p) := by gcongr
  have h := (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCt)).2 hmain
  refine h.trans (le_of_eq ?_)
  have hpow : volume C ^ (1 - 1 / p) / volume C = volume C ^ (-(1 / p)) := by
    rw [show -(1 / p) = (1 - 1 / p) - 1 by ring, ENNReal.rpow_sub (1 - 1 / p) 1 hC0 hCt,
      ENNReal.rpow_one]
  rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hC0 hCt, mul_div_assoc, hpow]
  simp only [M]
  ring

/-- Scaling: `(a s^N)^{-1/p} · 2 (A s)/(1 - N/p) → 0` as `s → 0⁺` when `p > N`. -/
theorem tendsto_cover_scale {p a A : ℝ} (hNp : (N : ℝ) < p) (ha : 0 < a) :
    Tendsto (fun s : ℝ => (a * s ^ N) ^ (-(1 / p)) * (2 * (A * s * (1 / (1 - N / p)))))
      (𝓝[>] 0) (𝓝 0) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg N) hNp
  have he : 0 < 1 - (N : ℝ) / p := by
    have : (N : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact hNp
    linarith
  have hlim : Tendsto (fun s : ℝ => s ^ (1 - (N : ℝ) / p)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 - (N : ℝ) / p) (Or.inr he.le)).tendsto
    rw [Real.zero_rpow he.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := hlim.const_mul (a ^ (-(1 / p)) * (2 * (A * (1 / (1 - N / p)))))
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : 0 < s := hs
  rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hs.le,
    show (1 - (N : ℝ) / p) = 1 + (N : ℝ) * (-(1 / p)) by ring, Real.rpow_add hs, Real.rpow_one]
  ring

/-- **Uniform convergence from a uniform convex cover.** Let `φₙ → 0` in `Lᵖ`, with weak
gradients `gₙ` on `Ω` bounded in `Lᵖ` by `B < ∞`, `p > N`. Assume that at every scale
`s ∈ (0, s₀]`, every `y ∈ S` lies in an open convex `C`, `δ`-inside `Ω`, of diameter `≤ A s` and
measure `≥ a sᴺ`. Then `‖φₙ‖_{L^∞(S)} → 0`. -/
theorem eventually_ae_enorm_le_of_convex_cover {p : ℝ} (hp : 1 ≤ p) (hNp : (N : ℝ) < p)
    {Ω S : Set (Sp N)} {φ : ℕ → Sp N → Tgt m} {g : ℕ → Sp N → Mat m N}
    (hφ : ∀ n, MemLp (φ n) (ENNReal.ofReal p) volume)
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) volume) (hweak : ∀ n, HasWeakGrad Ω (φ n) (g n))
    (hφlim : Tendsto (fun n => eLpNorm (φ n) (ENNReal.ofReal p) volume) atTop (𝓝 0))
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hgB : ∀ n, eLpNorm (g n) (ENNReal.ofReal p) volume ≤ B)
    {A a s₀ : ℝ} (ha : 0 < a) (hs₀ : 0 < s₀)
    (hcover : ∀ s, 0 < s → s ≤ s₀ → ∀ y ∈ S, ∃ C : Set (Sp N), IsOpen C ∧ Convex ℝ C ∧
      y ∈ C ∧ volume C ≠ ⊤ ∧ ENNReal.ofReal (a * s ^ N) ≤ volume C ∧
      (∀ w ∈ C, ∀ w' ∈ C, ‖w - w'‖ ≤ A * s) ∧ ∃ δ > 0, ∀ z ∈ C, closedBall z δ ⊆ Ω) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ᵐ y ∂(volume.restrict S), ‖φ n y‖ₑ ≤ ε := by
  intro ε hε
  have hp0 : 0 < p := by linarith
  set K : ℝ → ℝ := fun s => 2 * (A * s * (1 / (1 - N / p)))
  set cs : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (a * s ^ N) ^ (-(1 / p))
  have hQ : Tendsto (fun s : ℝ => cs s * (ENNReal.ofReal (K s) * B)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const
      ((ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_cover_scale (A := A) hNp ha))
      (Or.inr hB)
    rw [Function.comp_def, ENNReal.ofReal_zero, zero_mul] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : 0 < s := hs
    simp only [cs, K, ENNReal.ofReal_rpow_of_pos (show 0 < a * s ^ N by positivity)]
    rw [← mul_assoc (ENNReal.ofReal ((a * s ^ N) ^ (-(1 / p)))),
      ← ENNReal.ofReal_mul (by positivity)]
  obtain ⟨s, hsQ, hsI⟩ := ((hQ.eventually (gt_mem_nhds hε)).and (Ioc_mem_nhdsGT hs₀)).exists
  have hs : 0 < s := hsI.1
  have hcs : cs s ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero
    (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity) ENNReal.ofReal_ne_top
  have hF : Tendsto (fun n => cs s * (eLpNorm (φ n) (ENNReal.ofReal p) volume +
      ENNReal.ofReal (K s) * B)) atTop (𝓝 (cs s * (ENNReal.ofReal (K s) * B))) := by
    have := ENNReal.Tendsto.const_mul (hφlim.add (tendsto_const_nhds
      (x := ENNReal.ofReal (K s) * B))) (Or.inr hcs)
    rwa [zero_add] at this
  choose! Cy hCo hCc hyC hCt hCvol hCd hCδ using hcover s hs hsI.2
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : S => Cy y) fun y => hCo y y.2
  filter_upwards [hF.eventually (gt_mem_nhds hsQ)] with n hn
  have hsub : S ⊆ ⋃ y ∈ T, Cy (y : Sp N) := by
    rw [hTU]
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hyC y hy⟩
  refine ae_restrict_of_ae_restrict_of_subset hsub ?_
  rw [ae_restrict_biUnion_iff _ hTc]
  intro y _
  have hy := y.2
  obtain ⟨δ, hδ, hδΩ⟩ := hCδ y hy
  have hvol0 : volume (Cy y) ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (hCvol y hy)).ne'
    rw [ENNReal.ofReal_pos]; positivity
  filter_upwards [ae_enorm_le_of_convex hp hNp (hφ n) (hg n) (hweak n) (hCo y hy) (hCc y hy)
    hvol0 (hCt y hy) hδ (hCd y hy) hδΩ] with z hz
  refine hz.trans (le_trans ?_ hn.le)
  have hpow : volume (Cy y) ^ (-(1 / p)) ≤ cs s := by
    simp only [cs]
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    gcongr
    exact hCvol y hy
  refine mul_le_mul' hpow (add_le_add ?_ (mul_le_mul' le_rfl ?_))
  · exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hgB n)

/-! ### Truncated cones in the coordinates of a Lipschitz chart -/

/-- The projection `ζ ↦ (0, ζ₁, …, ζ_{N-1})` killing the vertical coordinate `0`. -/
noncomputable def dropFirst [NeZero N] : Sp N →L[ℝ] Sp N :=
  ContinuousLinearMap.pi fun i => if i = 0 then 0 else ContinuousLinearMap.proj i

/-- Coordinates of `dropFirst`. -/
theorem dropFirst_apply [NeZero N] (ζ : Sp N) (i : Fin N) :
    dropFirst ζ i = if i = 0 then 0 else ζ i := by
  by_cases hi : i = 0 <;> simp [dropFirst, hi]

/-- `dropFirst ζ = update ζ 0 0`. -/
theorem dropFirst_eq_update [NeZero N] (ζ : Sp N) : dropFirst ζ = update ζ 0 0 := by
  funext i
  rw [dropFirst_apply]
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

/-- The open truncated cone `{τ - s < ζ₀, ζ₀ + κ ‖ζ'‖ < τ}` with vertex `τ e₀`, opening
downwards. -/
def coneSet [NeZero N] (κ τ s : ℝ) : Set (Sp N) :=
  {ζ | τ - s < ζ 0 ∧ ζ 0 + κ * ‖dropFirst ζ‖ < τ}

/-- Its closed version. -/
def coneSetClosed [NeZero N] (κ τ s : ℝ) : Set (Sp N) :=
  {ζ | τ - s ≤ ζ 0 ∧ ζ 0 + κ * ‖dropFirst ζ‖ ≤ τ}

/-- The cone is open. -/
theorem isOpen_coneSet [NeZero N] (κ τ s : ℝ) : IsOpen (coneSet (N := N) κ τ s) := by
  have hc : Continuous fun ζ : Sp N => ζ 0 := continuous_apply 0
  exact (isOpen_lt continuous_const hc).inter
    (isOpen_lt (hc.add (continuous_const.mul dropFirst.continuous.norm)) continuous_const)

/-- The closed cone is closed. -/
theorem isClosed_coneSetClosed [NeZero N] (κ τ s : ℝ) :
    IsClosed (coneSetClosed (N := N) κ τ s) := by
  have hc : Continuous fun ζ : Sp N => ζ 0 := continuous_apply 0
  exact (isClosed_le continuous_const hc).inter
    (isClosed_le (hc.add (continuous_const.mul dropFirst.continuous.norm)) continuous_const)

/-- The open cone lies in the closed one. -/
theorem coneSet_subset_closed [NeZero N] (κ τ s : ℝ) :
    coneSet (N := N) κ τ s ⊆ coneSetClosed κ τ s := fun _ h => ⟨h.1.le, h.2.le⟩

/-- The cone is convex. -/
theorem convex_coneSet [NeZero N] {κ : ℝ} (hκ : 0 ≤ κ) (τ s : ℝ) :
    Convex ℝ (coneSet (N := N) κ τ s) := by
  have h1 : Convex ℝ {ζ : Sp N | τ - s < ζ 0} :=
    convex_halfSpace_gt (f := fun ζ : Sp N => ζ 0) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _
  have hF : ConvexOn ℝ univ (fun ζ : Sp N => ζ 0 + κ * ‖dropFirst ζ‖) := by
    have hl : ConvexOn ℝ univ (fun ζ : Sp N => ζ 0) :=
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) 0).convexOn convex_univ
    have hn : ConvexOn ℝ univ (fun ζ : Sp N => ‖dropFirst ζ‖) := by
      have := (convexOn_norm (E := Sp N) convex_univ).comp_linearMap
        (dropFirst (N := N) : Sp N →ₗ[ℝ] Sp N)
      simpa [Function.comp_def] using this
    exact hl.add (hn.smul hκ)
  have h2 := hF.convex_lt τ
  have : coneSet (N := N) κ τ s = {ζ : Sp N | τ - s < ζ 0} ∩
      {ζ | ζ ∈ univ ∧ ζ 0 + κ * ‖dropFirst ζ‖ < τ} := by
    ext ζ; simp [coneSet]
  rw [this]
  exact h1.inter h2

/-- Points of the closed cone (with `κ ≥ 1`, `0 ≤ τ ≤ s`) have norm `≤ s`. -/
theorem norm_le_of_mem_coneSetClosed [NeZero N] {κ τ s : ℝ} (hκ : 1 ≤ κ) (hτ : 0 ≤ τ)
    (hτs : τ ≤ s) {ζ : Sp N} (hζ : ζ ∈ coneSetClosed κ τ s) : ‖ζ‖ ≤ s := by
  obtain ⟨h1, h2⟩ := hζ
  have hP0 : 0 ≤ ‖dropFirst ζ‖ := norm_nonneg _
  have hP : ‖dropFirst ζ‖ ≤ s := by nlinarith
  have hs : 0 ≤ s := by linarith
  refine (pi_norm_le_iff_of_nonneg hs).2 fun i => ?_
  by_cases hi : i = 0
  · subst hi
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  · have := norm_le_pi_norm (dropFirst ζ) i
    rw [dropFirst_apply, if_neg hi] at this
    linarith

/-- `0` lies in the cone when `0 < τ < s`. -/
theorem zero_mem_coneSet [NeZero N] {κ τ s : ℝ} (hτ : 0 < τ) (hτs : τ < s) :
    (0 : Sp N) ∈ coneSet κ τ s := by
  simp only [coneSet, mem_ofPred_eq, Pi.zero_apply, map_zero, norm_zero, mul_zero, add_zero]
  exact ⟨by linarith, hτ⟩

/-- A cube of side `s/(2κ)` inside the cone (`κ ≥ 1`, `0 < s`). -/
theorem cube_subset_coneSet [NeZero N] {κ τ s : ℝ} (hκ : 1 ≤ κ) (hs : 0 < s) :
    cube (s / (2 * κ)) (Pi.single 0 (τ - 3 * s / 4) : Sp N) ⊆ coneSet κ τ s := by
  intro ζ hζ
  have hκ0 : 0 < κ := by linarith
  have hr : s / (2 * κ) / 2 ≤ s / 4 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hcoord : ∀ i, |ζ i - (Pi.single 0 (τ - 3 * s / 4) : Sp N) i| < s / (2 * κ) / 2 := by
    intro i
    have := hζ i (mem_univ i)
    rw [mem_Ioo] at this
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have h0 := hcoord 0
  simp only [Pi.single_eq_same] at h0
  rw [abs_lt] at h0
  have hP : ‖dropFirst ζ‖ < s / (2 * κ) / 2 := by
    rw [pi_norm_lt_iff (by positivity)]
    intro i
    rw [dropFirst_apply]
    by_cases hi : i = 0
    · rw [if_pos hi, norm_zero]; positivity
    · rw [if_neg hi, Real.norm_eq_abs]
      have := hcoord i
      rwa [Pi.single_eq_of_ne hi, sub_zero] at this
  have hκP : κ * ‖dropFirst ζ‖ < s / 4 := by
    have : κ * (s / (2 * κ) / 2) = s / 4 := by field_simp; ring
    nlinarith
  exact ⟨by linarith, by linarith⟩

/-- **Cones from a Lipschitz chart.** Near a boundary point `x₀` with chart `(T, g, K, U)` (as in
`HasLipschitzBoundary`), there are `R, a, s₀ > 0` and `A` such that, at every scale `s ∈ (0, s₀]`,
every `y ∈ Ω ∩ B(x₀, R)` lies in an open convex set `C`, `δ`-inside `Ω`, of diameter `≤ A s` and
measure `≥ a sᴺ`: the preimage of a truncated cone `coneSet` under `y' ↦ T(y' - y)`, with vertex
slightly above `y`. -/
theorem exists_cone_cover_of_chart [NeZero N] {Ω : Set (Sp N)} (hΩ : IsOpen Ω) {x₀ : Sp N}
    (T : Sp N ≃L[ℝ] Sp N) (g : Sp N → ℝ) (K : ℝ≥0) (U : Set (Sp N)) (hU : U ∈ 𝓝 x₀)
    (hg : LipschitzWith K g) (hg0 : ∀ z, g z = g (update z 0 0))
    (hchart : ∀ y ∈ U, (y ∈ Ω ↔ T (y - x₀) 0 < g (T (y - x₀)))) :
    ∃ R > 0, ∃ A a s₀ : ℝ, 0 < a ∧ 0 < s₀ ∧ ∀ s, 0 < s → s ≤ s₀ → ∀ y ∈ Ω ∩ ball x₀ R,
      ∃ C : Set (Sp N), IsOpen C ∧ Convex ℝ C ∧ y ∈ C ∧ volume C ≠ ⊤ ∧
        ENNReal.ofReal (a * s ^ N) ≤ volume C ∧ (∀ w ∈ C, ∀ w' ∈ C, ‖w - w'‖ ≤ A * s) ∧
        ∃ δ > 0, ∀ z ∈ C, closedBall z δ ⊆ Ω := by
  obtain ⟨R₀, hR₀, hR₀U⟩ := Metric.mem_nhds_iff.1 hU
  set M : ℝ := ‖(T.symm : Sp N →L[ℝ] Sp N)‖
  have hM : 0 ≤ M := norm_nonneg _
  set κ : ℝ := (K : ℝ) + 1
  have hκ : 1 ≤ κ := by simp [κ]
  set D : ℝ := LinearMap.det (T.symm : Sp N →ₗ[ℝ] Sp N)
  have hD : D ≠ 0 := (LinearEquiv.isUnit_det' T.symm.toLinearEquiv).ne_zero
  refine ⟨R₀ / 2, half_pos hR₀, 2 * M, |D| * (1 / (2 * κ)) ^ N, R₀ / (4 * (M + 1)),
    by positivity, by positivity, ?_⟩
  intro s hs hss₀ y ⟨hyΩ, hyR⟩
  have hgP : ∀ z, g z = g (dropFirst z) := fun z => by rw [dropFirst_eq_update]; exact hg0 z
  set z : Sp N := T (y - x₀)
  have hyU : y ∈ U := hR₀U (ball_subset_ball (by linarith) hyR)
  have hz : z 0 < g z := (hchart y hyU).1 hyΩ
  set τ : ℝ := min (g z - z 0) s / 2
  have hτ0 : 0 < τ := by have := lt_min (sub_pos.2 hz) hs; positivity
  have hτs : τ ≤ s / 2 := by have := min_le_right (g z - z 0) s; simp only [τ]; linarith
  have hτg : τ < g z - z 0 := by
    have := min_le_left (g z - z 0) s; simp only [τ]; linarith [sub_pos.2 hz]
  set Φ : Sp N → Sp N := fun y' => T (y' - y)
  have hΦc : Continuous Φ := T.continuous.comp (continuous_id.sub continuous_const)
  set C : Set (Sp N) := Φ ⁻¹' coneSet κ τ s
  set Dc : Set (Sp N) := Φ ⁻¹' coneSetClosed κ τ s
  have hCD : C ⊆ Dc := preimage_mono (coneSet_subset_closed κ τ s)
  -- points of `Dc` are `M s`-close to `y`
  have hclose : ∀ y' ∈ Dc, ‖y' - y‖ ≤ M * s := by
    intro y' hy'
    have h1 := norm_le_of_mem_coneSetClosed hκ hτ0.le (by linarith) hy'
    have h2 : y' - y = T.symm (Φ y') := by simp [Φ]
    rw [h2]
    exact ((T.symm : Sp N →L[ℝ] Sp N).le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 hM)
  have hMs : M * s < R₀ / 4 := by
    have h1 : M * s ≤ M * (R₀ / (4 * (M + 1))) := mul_le_mul_of_nonneg_left hss₀ hM
    have h2 : M * (R₀ / (4 * (M + 1))) < R₀ / 4 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  -- `Dc ⊆ Ω`
  have hDΩ : Dc ⊆ Ω := by
    intro y' hy'
    have hy'U : y' ∈ U := by
      apply hR₀U
      rw [mem_ball, dist_eq_norm]
      have := hclose y' hy'
      have hyx : ‖y - x₀‖ < R₀ / 2 := by rw [← dist_eq_norm]; exact hyR
      calc ‖y' - x₀‖ = ‖(y' - y) + (y - x₀)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y' - y‖ + ‖y - x₀‖ := norm_add_le _ _
        _ < R₀ := by linarith
    rw [hchart y' hy'U]
    have hsplit : T (y' - x₀) = Φ y' + z := by
      simp only [Φ, z, ← map_add, sub_add_sub_cancel]
    obtain ⟨_, h2⟩ := hy'
    have hgl : g z - K * ‖dropFirst (Φ y')‖ ≤ g (Φ y' + z) := by
      have := hg.dist_le_mul (dropFirst (Φ y' + z)) (dropFirst z)
      rw [Real.dist_eq, dist_eq_norm, ← map_sub, add_sub_cancel_right, ← hgP, ← hgP] at this
      have := neg_abs_le (g (Φ y' + z) - g z)
      linarith
    rw [hsplit, Pi.add_apply]
    have hK : (K : ℝ) * ‖dropFirst (Φ y')‖ ≤ κ * ‖dropFirst (Φ y')‖ :=
      mul_le_mul_of_nonneg_right (by simp [κ]) (norm_nonneg _)
    linarith
  have hDc : IsCompact Dc := by
    refine Metric.isCompact_of_isClosed_isBounded ((isClosed_coneSetClosed κ τ s).preimage hΦc)
      ((Metric.isBounded_closedBall (x := y) (r := M * s)).subset fun y' hy' => ?_)
    rw [mem_closedBall, dist_eq_norm]; exact hclose y' hy'
  obtain ⟨δ, hδ, hδD⟩ := hDc.exists_cthickening_subset_open hΩ hDΩ
  refine ⟨C, (isOpen_coneSet κ τ s).preimage hΦc, ?_, ?_, ?_, ?_, ?_, δ, hδ, ?_⟩
  · -- convexity
    have h1 := (convex_coneSet (N := N) (by linarith : (0 : ℝ) ≤ κ) τ s).linear_preimage
      (T : Sp N →ₗ[ℝ] Sp N)
    have h2 := h1.translate_preimage_right (-y)
    have hset : C = (fun x => -y + x) ⁻¹' ((T : Sp N →ₗ[ℝ] Sp N) ⁻¹' coneSet κ τ s) := by
      ext y'
      change T (y' - y) ∈ coneSet κ τ s ↔ T (-y + y') ∈ coneSet κ τ s
      rw [neg_add_eq_sub]
    rw [hset]
    exact h2
  · -- `y ∈ C`
    change Φ y ∈ coneSet κ τ s
    simpa [Φ] using zero_mem_coneSet (N := N) (κ := κ) hτ0 (by linarith)
  · -- finite measure
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := y) (r := M * s)).ne
      (measure_mono fun y' hy' => ?_)
    rw [mem_closedBall, dist_eq_norm]; exact hclose y' (hCD hy')
  · -- measure lower bound
    have hpre : C = (fun y' => y' + (-y)) ⁻¹' (T ⁻¹' coneSet κ τ s) := by
      ext y'; simp [C, Φ, sub_eq_add_neg]
    rw [hpre, measure_preimage_add_right, Measure.addHaar_preimage_continuousLinearEquiv]
    calc ENNReal.ofReal (|D| * (1 / (2 * κ)) ^ N * s ^ N)
        = ENNReal.ofReal |D| * volume (cube (s / (2 * κ))
            (Pi.single 0 (τ - 3 * s / 4) : Sp N)) := by
          rw [volume_cube, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul
            (abs_nonneg _)]
          congr 1
          rw [div_pow, div_pow, one_pow]
          ring
      _ ≤ _ := by
          gcongr
          exact cube_subset_coneSet hκ hs
  · -- diameter
    intro w hw w' hw'
    have h1 := hclose w (hCD hw)
    have h2 := hclose w' (hCD hw')
    calc ‖w - w'‖ = ‖(w - y) - (w' - y)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖w - y‖ + ‖w' - y‖ := norm_sub_le _ _
      _ ≤ 2 * M * s := by linarith
  · -- margin
    intro w hw
    exact (closedBall_subset_cthickening (hCD hw) δ).trans hδD

/-- **Cubes inside a compact subset.** For `K ⊆ Ω` compact, at every small scale `s` every
`y ∈ K` lies in the cube `Q_s(y)`, `δ`-inside `Ω`, of diameter `≤ s` and measure `sᴺ`. -/
theorem exists_cube_cover_of_compact [NeZero N] {Ω K : Set (Sp N)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ s₀ > 0, ∀ s, 0 < s → s ≤ s₀ → ∀ y ∈ K,
      ∃ C : Set (Sp N), IsOpen C ∧ Convex ℝ C ∧ y ∈ C ∧ volume C ≠ ⊤ ∧
        ENNReal.ofReal (1 * s ^ N) ≤ volume C ∧ (∀ w ∈ C, ∀ w' ∈ C, ‖w - w'‖ ≤ 1 * s) ∧
        ∃ δ > 0, ∀ z ∈ C, closedBall z δ ⊆ Ω := by
  obtain ⟨δ₀, hδ₀, hδ₀Ω⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨δ₀, hδ₀, fun s hs hsδ y hy => ⟨cube s y, isOpen_cube s y, ?_, self_mem_cube hs y,
    volume_cube_ne_top s y, ?_, ?_, δ₀ / 2, half_pos hδ₀, ?_⟩⟩
  · rw [cube_eq_ball hs y]; exact convex_ball y (s / 2)
  · rw [one_mul, volume_cube, ENNReal.ofReal_pow hs.le]
  · intro w hw w' hw'
    rw [one_mul]
    exact norm_sub_le_of_mem_cube hw' hw
  · intro z hz w hw
    apply hδ₀Ω
    apply closedBall_subset_cthickening hy δ₀
    rw [cube_eq_ball hs y, mem_ball] at hz
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w z y]

/-- **Cited result (a) proved: `CitedSobolevCompact`.** (a2) is `W1p.grad_mem_of_tendsto`.
(a1): the differences `wₙ = uₙ - v` tend to `0` in `Lᵖ(Ω)` with gradients bounded in `Lᵖ`;
`Ω` is covered, uniformly in the scale `s`, by open convex sets `δ`-inside `Ω` of diameter
`≲ s` and measure `≳ sᴺ` (cubes away from `∂Ω`, `exists_cube_cover_of_compact`; cones in
finitely many Lipschitz charts near the compact `∂Ω`, `exists_cone_cover_of_chart`), and
`eventually_ae_enorm_le_of_convex_cover` (Morrey on convex sets) gives `‖wₙ‖_{L^∞(Ω)} → 0`. -/
theorem citedSobolevCompact_holds [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    CitedSobolevCompact N m p := by
  intro hNp Ω hΩo hΩb hLip u v hu hgrad
  refine ⟨?_, fun K hK hKc hn => W1p.grad_mem_of_tendsto hΩo hu hK hKc hn⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 hp1
  have hp0 : 0 < p := by linarith
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  obtain ⟨Cg, hCg, hCgn⟩ := hgrad
  set φ : ℕ → Sp N → Tgt m := fun n => Ω.indicator ((u n).toFun - v.toFun)
  set g : ℕ → Sp N → Mat m N := fun n => Ω.indicator ((u n).grad - v.grad)
  have hφ : ∀ n, MemLp (φ n) (ENNReal.ofReal p) volume := fun n =>
    (memLp_indicator_iff_restrict (f := (u n).toFun - v.toFun) hΩm).2 ((u n).memLp.sub v.memLp)
  have hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) volume := fun n =>
    (memLp_indicator_iff_restrict (f := (u n).grad - v.grad) hΩm).2
      ((u n).memLp_grad.sub v.memLp_grad)
  have hweak : ∀ n, HasWeakGrad Ω (φ n) (g n) := by
    intro n
    have h := HasWeakGrad.add hΩo hΩb (u n).memLp (u n).memLp_grad
      (v.memLp.const_smul (-1 : ℝ)) (v.memLp_grad.const_smul (-1 : ℝ)) (u n).weak
      (v.weak.const_smul (-1))
    change HasWeakGrad Ω (Ω.indicator ((u n).toFun - v.toFun)) (Ω.indicator ((u n).grad - v.grad))
    convert h.indicator using 2 <;> funext y <;> simp [sub_eq_add_neg]
  have hφlim : Tendsto (fun n => eLpNorm (φ n) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine (tendsto_iff_edist_tendsto_0.1 hu).congr fun n => ?_
    rw [W1p.edist_def]
    exact (eLpNorm_indicator_eq_eLpNorm_restrict hΩm).symm
  -- the uniform gradient bound
  set B : ℝ≥0∞ := Cg ^ (1 / p) + eLpNorm v.grad (ENNReal.ofReal p) (volume.restrict Ω)
  have hB : B ≠ ⊤ := ENNReal.add_ne_top.2
    ⟨ENNReal.rpow_ne_top_of_nonneg (by positivity) hCg.ne, v.memLp_grad.eLpNorm_ne_top⟩
  have hgB : ∀ n, eLpNorm (g n) (ENNReal.ofReal p) volume ≤ B := by
    intro n
    change eLpNorm (Ω.indicator ((u n).grad - v.grad)) (ENNReal.ofReal p) volume ≤ B
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (f := (u n).grad - v.grad) hΩm]
    refine (eLpNorm_sub_le (u n).memLp_grad.1 v.memLp_grad.1 hp1).trans (add_le_add ?_ le_rfl)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
    gcongr
    exact hCgn n
  -- the geometric cover
  have hfr : IsCompact (frontier Ω) :=
    hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hchart : ∀ x ∈ frontier Ω, ∃ R > 0, ∃ A a s₀ : ℝ, 0 < a ∧ 0 < s₀ ∧
      ∀ s, 0 < s → s ≤ s₀ → ∀ y ∈ Ω ∩ ball x R,
      ∃ C : Set (Sp N), IsOpen C ∧ Convex ℝ C ∧ y ∈ C ∧ volume C ≠ ⊤ ∧
        ENNReal.ofReal (a * s ^ N) ≤ volume C ∧ (∀ w ∈ C, ∀ w' ∈ C, ‖w - w'‖ ≤ A * s) ∧
        ∃ δ > 0, ∀ z ∈ C, closedBall z δ ⊆ Ω := by
    intro x hx
    obtain ⟨T, g₀, K, U, hU, hg₀, hg0, hch⟩ := hLip x hx
    exact exists_cone_cover_of_chart hΩo T g₀ K U hU hg₀ hg0 hch
  choose! R hR A a s₀ ha hs₀ hcov using hchart
  obtain ⟨t, htfr, hcovt⟩ := hfr.elim_nhds_subcover (fun x => ball x (R x))
    fun x hx => ball_mem_nhds x (hR x hx)
  set V : Set (Sp N) := ⋃ x ∈ t, ball x (R x)
  have hVo : IsOpen V := isOpen_biUnion fun x _ => isOpen_ball
  set Kint : Set (Sp N) := closure Ω ∩ Vᶜ
  have hKint : IsCompact Kint :=
    hΩb.isCompact_closure.of_isClosed_subset (isClosed_closure.inter hVo.isClosed_compl)
      inter_subset_left
  have hKintΩ : Kint ⊆ Ω := by
    intro y ⟨hy1, hy2⟩
    rw [closure_eq_self_union_frontier] at hy1
    rcases hy1 with hy | hy
    · exact hy
    · exact absurd (hcovt hy) hy2
  obtain ⟨si, hsi, hcovi⟩ := exists_cube_cover_of_compact hΩo hKint hKintΩ
  have hΩsub : Ω ⊆ Kint ∪ ⋃ x ∈ t, Ω ∩ ball x (R x) := by
    intro y hy
    by_cases hyV : y ∈ V
    · right
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyV
      exact mem_iUnion₂.2 ⟨x, hx, hy, hyx⟩
    · left; exact ⟨subset_closure hy, hyV⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hint := eventually_ae_enorm_le_of_convex_cover hp hNp hφ hg hweak hφlim hB hgB
    one_pos hsi hcovi ε hε
  have hbd : ∀ x ∈ t, ∀ᶠ n in atTop,
      ∀ᵐ y ∂(volume.restrict (Ω ∩ ball x (R x))), ‖φ n y‖ₑ ≤ ε := fun x hx =>
    eventually_ae_enorm_le_of_convex_cover hp hNp hφ hg hweak hφlim hB hgB
      (ha x (htfr x hx)) (hs₀ x (htfr x hx)) (hcov x (htfr x hx)) ε hε
  filter_upwards [hint, (Filter.eventually_all_finset t).2 hbd] with n hn1 hn2
  have hae : ∀ᵐ y ∂(volume.restrict Ω), ‖φ n y‖ₑ ≤ ε := by
    refine ae_restrict_of_ae_restrict_of_subset hΩsub ?_
    rw [ae_restrict_union_iff]
    refine ⟨hn1, ?_⟩
    rw [ae_restrict_biUnion_finset_iff]
    exact hn2
  rw [eLpNorm_exponent_top]
  refine essSup_le_of_ae_le ε ?_
  filter_upwards [hae, ae_restrict_mem hΩm] with y hy hyΩ
  simpa [φ, indicator_of_mem hyΩ] using hy

end Homogenization
