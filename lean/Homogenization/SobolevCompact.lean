import Homogenization.Morrey

/-!
# The cited result (a): compactness in `W^{1,p}`

Step 1, (a2): closed convex gradient constraints pass to `Lᵖ` limits
(`W1p.grad_mem_of_tendsto`), for any open `Ω`, without bound on the gradients.

(a1), the uniform convergence on a bounded Lipschitz domain, and `CitedSobolevCompact` itself
(`citedSobolevCompact_holds`) are proved in `SobolevCompactUniform.lean`.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution

namespace Homogenization

variable {N m : ℕ}

/-- The convolution at `x` with a bump only sees `V` on `closedBall x rOut`. -/
theorem convolution_congr_on_ball (η : ContDiffBump (0 : Sp N)) {Ω : Set (Sp N)}
    {V W : Sp N → Mat m N} {x : Sp N} (hball : closedBall x η.rOut ⊆ Ω)
    (hVW : ∀ y ∈ Ω, V y = W y) :
    (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) x =
      (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] W) x := by
  simp only [convolution_def]
  congr 1
  funext t
  by_cases ht : η.normed volume t = 0
  · simp [ht]
  · have htb : t ∈ ball (0 : Sp N) η.rOut := by
      rw [← η.support_normed_eq (μ := volume)]; exact ht
    rw [hVW (x - t) (hball ?_)]
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact (mem_ball_zero_iff.1 htb).le

/-- `(η ⋆ g)(x) w = ∫ ∂_w η(x - y) φ(y) dy` when `g` is a weak gradient of `φ` on
`Ω ⊇ closedBall x rOut`. -/
theorem convolution_grad_apply_eq {Ω : Set (Sp N)} {φ : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hg : LocallyIntegrable g volume) (hweak : HasWeakGrad Ω φ g) (η : ContDiffBump (0 : Sp N))
    {x : Sp N} (hball : closedBall x η.rOut ⊆ Ω) (w : Sp N) :
    (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x w =
      ∫ y, fderiv ℝ (η.normed volume) (x - y) w • φ y := by
  have hgInt : Integrable (fun y => η.normed volume y • g (x - y)) volume :=
    (η.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      η.continuous_normed hg x).integrable
  rw [HasWeakGrad.bump_test_identity_local hweak η hball w, MeasureTheory.convolution_lsmul,
    ContinuousLinearMap.integral_apply hgInt]
  simpa only [smul_apply, sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y => η.normed volume y • (g (x - y)) w) volume x).symm

/-- Integrals against a continuous kernel supported in a ball are continuous for `Lᵖ`
convergence. -/
theorem tendsto_integral_smul_of_eLpNorm {p : ℝ} (hp : 1 ≤ p) {c : Sp N → ℝ}
    (hc : Continuous c) {x : Sp N} {r : ℝ} (hcs : ∀ y, c y ≠ 0 → y ∈ closedBall x r)
    {Φ : ℕ → Sp N → Tgt m} {Ψ : Sp N → Tgt m} (hΦ : ∀ n, MemLp (Φ n) (ENNReal.ofReal p) volume)
    (hΨ : MemLp Ψ (ENNReal.ofReal p) volume)
    (hlim : Tendsto (fun n => eLpNorm (Φ n - Ψ) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, c y • Φ n y) atTop (𝓝 (∫ y, c y • Ψ y)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hcsupp : HasCompactSupport c :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x r) fun y hy => hcs y hy
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcsupp
  set B := closedBall x r
  have hBm : MeasurableSet B := isClosed_closedBall.measurableSet
  have hBt : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  set V : ℝ≥0∞ := volume B ^ (1 - 1 / p)
  have hVt : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
    (by rw [sub_nonneg, div_le_one (by linarith)]; exact hp) hBt
  have hint : ∀ f : Sp N → Tgt m, MemLp f (ENNReal.ofReal p) volume →
      Integrable (fun y => c y • f y) volume := fun f hf =>
    (hf.locallyIntegrable hp1).integrable_smul_left_of_hasCompactSupport hc hcsupp
  rw [tendsto_iff_edist_tendsto_0]
  have hbound : ∀ n, edist (∫ y, c y • Φ n y) (∫ y, c y • Ψ y) ≤
      ENNReal.ofReal M * (eLpNorm (Φ n - Ψ) (ENNReal.ofReal p) volume * V) := by
    intro n
    have hsub := hint _ ((hΦ n).sub hΨ)
    rw [edist_eq_enorm_sub, ← integral_sub (hint _ (hΦ n)) (hint _ hΨ)]
    have he : (fun y => c y • Φ n y - c y • Ψ y) = fun y => c y • (Φ n - Ψ) y := by
      funext y; simp [smul_sub]
    rw [he]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hsupp : support (fun y => ‖c y • (Φ n - Ψ) y‖ₑ) ⊆ B := by
      intro y hy
      by_contra hyB
      apply hy
      have : c y = 0 := by
        by_contra hc0; exact hyB (hcs y hc0)
      simp [this]
    rw [← setLIntegral_eq_of_support_subset hsupp]
    calc ∫⁻ y in B, ‖c y • (Φ n - Ψ) y‖ₑ
        ≤ ∫⁻ y in B, ENNReal.ofReal M * ‖(Φ n - Ψ) y‖ₑ := by
          refine lintegral_mono fun y => ?_
          rw [enorm_smul, ← ofReal_norm]
          gcongr
          exact hM y
      _ = ENNReal.ofReal M * eLpNorm (Φ n - Ψ) 1 (volume.restrict B) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal M * (eLpNorm (Φ n - Ψ) (ENNReal.ofReal p) volume * V) := by
          gcongr
          have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B) hp1
            ((hΦ n).1.sub hΨ.1).restrict
          rw [Measure.restrict_apply_univ, ENNReal.toReal_one,
            ENNReal.toReal_ofReal (by linarith), div_one] at h
          refine h.trans ?_
          gcongr
          exact Measure.restrict_le_self
  have hup : Tendsto (fun n => ENNReal.ofReal M *
      (eLpNorm (Φ n - Ψ) (ENNReal.ofReal p) volume * V)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const hlim (Or.inr hVt))
      (Or.inr (ENNReal.ofReal_ne_top (r := M)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le) hbound

/-- **(a2) Closed convex gradient constraints pass to `Lᵖ` limits.** If `uₙ → v` in `Lᵖ(Ω)` and
`∇uₙ ∈ K` a.e. in `Ω` for a closed convex `K`, then `∇v ∈ K` a.e. in `Ω`. No bound on the
gradients and no regularity of `Ω` is needed: at `x ∈ Ω`, `(η ⋆ ∇uₙ)(x) ∈ K` (barycenter), it
equals `∫ ∇η(x - y) uₙ(y) dy` (weak gradient), which tends to `(η ⋆ ∇v)(x)`; then `η → δ` at
Lebesgue points of `∇v`. -/
theorem W1p.grad_mem_of_tendsto {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩ : IsOpen Ω) {u : ℕ → W1p N m (ENNReal.ofReal p) Ω} {v : W1p N m (ENNReal.ofReal p) Ω}
    (hu : Tendsto u atTop (𝓝 v)) {K : Set (Mat m N)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hn : ∀ n, ∀ᵐ x ∂(volume.restrict Ω), (u n).grad x ∈ K) :
    ∀ᵐ x ∂(volume.restrict Ω), v.grad x ∈ K := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 hp1
  rcases K.eq_empty_or_nonempty with hKe | ⟨k₀, hk₀⟩
  · filter_upwards [hn 0] with x hx
    simp [hKe] at hx
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  set G : ℕ → Sp N → Mat m N := fun n => Ω.indicator (u n).grad
  set Gv : Sp N → Mat m N := Ω.indicator v.grad
  set Φ : ℕ → Sp N → Tgt m := fun n => Ω.indicator (u n).toFun
  set Ψ : Sp N → Tgt m := Ω.indicator v.toFun
  have hGv : MemLp Gv (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict (f := v.grad) hΩm).2 v.memLp_grad
  have hGl : ∀ n, LocallyIntegrable (G n) volume := fun n =>
    ((memLp_indicator_iff_restrict (f := (u n).grad) hΩm).2 (u n).memLp_grad).locallyIntegrable
      hp1
  have hΦ : ∀ n, MemLp (Φ n) (ENNReal.ofReal p) volume := fun n =>
    (memLp_indicator_iff_restrict (f := (u n).toFun) hΩm).2 (u n).memLp
  have hΨ : MemLp Ψ (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict (f := v.toFun) hΩm).2 v.memLp
  have hlim : Tendsto (fun n => eLpNorm (Φ n - Ψ) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine (tendsto_iff_edist_tendsto_0.1 hu).congr fun n => ?_
    rw [W1p.edist_def, ← eLpNorm_indicator_eq_eLpNorm_restrict hΩm]
    congr 1
    ext1 y
    by_cases hy : y ∈ Ω <;> simp [Φ, Ψ, hy]
  have hkey : ∀ (η : ContDiffBump (0 : Sp N)) (x : Sp N), closedBall x η.rOut ⊆ Ω →
      (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Gv) x ∈ K := by
    intro η x hball
    have hmem : ∀ n, (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G n) x ∈ K := by
      intro n
      set V : Sp N → Mat m N := Ω.piecewise (u n).grad fun _ => k₀
      have hVeq : V = G n + Ωᶜ.indicator fun _ => k₀ := by
        funext y
        by_cases hy : y ∈ Ω <;> simp [V, G, hy]
      have hV : LocallyIntegrable V volume := by
        rw [hVeq]
        exact (hGl n).add ((locallyIntegrable_const k₀).indicator hΩm.compl)
      have hVK : ∀ᵐ y ∂volume, V y ∈ K := by
        filter_upwards [(ae_restrict_iff' hΩm).1 (hn n)] with y hy
        by_cases hyΩ : y ∈ Ω
        · simpa [V, hyΩ] using hy hyΩ
        · simpa [V, hyΩ] using hk₀
      rw [convolution_congr_on_ball η hball (W := V) fun y hy => by simp [G, V, hy]]
      exact bump_convolution_mem hK hKc η hV hVK x
    set c : Sp N → Sp N → ℝ := fun w y => fderiv ℝ (η.normed volume) (x - y) w
    have hcc : ∀ w, Continuous (c w) := fun w =>
      (((η.contDiff_normed (μ := volume) (n := ⊤)).continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_id)).clm_apply continuous_const
    have hcs : ∀ w y, c w y ≠ 0 → y ∈ closedBall x η.rOut := by
      intro w y hy
      have h0 : fderiv ℝ (η.normed volume) (x - y) ≠ 0 := by
        intro h; apply hy; simp [c, h]
      have h1 := support_fderiv_subset ℝ (f := η.normed volume) h0
      rw [η.tsupport_normed_eq, mem_closedBall, dist_zero_right] at h1
      rwa [mem_closedBall, dist_comm, dist_eq_norm]
    have hw : ∀ w, Tendsto (fun n => (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        G n) x w) atTop
        (𝓝 ((η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Gv) x w)) := by
      intro w
      have e : ∀ n, (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G n) x w =
          ∫ y, c w y • Φ n y := fun n =>
        convolution_grad_apply_eq (hGl n) (u n).weak.indicator η hball w
      have ev : (η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Gv) x w =
          ∫ y, c w y • Ψ y :=
        convolution_grad_apply_eq (hGv.locallyIntegrable hp1) v.weak.indicator η hball w
      rw [funext e, ev]
      exact tendsto_integral_smul_of_eLpNorm hp (hcc w) (hcs w) hΦ hΨ hlim
    have h1 : Tendsto (fun n => matCoordEquiv m N
        ((η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G n) x)) atTop
        (𝓝 (matCoordEquiv m N
          ((η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Gv) x))) := by
      refine tendsto_pi_nhds.2 fun ⟨i, j⟩ => ?_
      simp only [matCoordEquiv_apply]
      exact ((continuous_apply i).tendsto _).comp (hw (Pi.single j 1))
    have h2 := ((matCoordEquiv m N).symm.continuous.tendsto _).comp h1
    simp only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] at h2
    exact hK.mem_of_tendsto h2 (Eventually.of_forall hmem)
  set η : ℕ → ContDiffBump (0 : Sp N) := fun j =>
    halfBump (show 0 < 1 / ((j : ℝ) + 2) by positivity)
  have hrOut : Tendsto (fun j => (η j).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hK2 : ∀ᶠ j in atTop, (η j).rOut ≤ 2 * (η j).rIn :=
    Eventually.of_forall fun j => by
      simp only [η, halfBump]; linarith [show 0 < 1 / ((j : ℝ) + 2) by positivity]
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hrOut hK2
    (hGv.locallyIntegrable hp1)
  filter_upwards [ae_restrict_mem hΩm, ae_restrict_of_ae hae] with x hx hxlim
  obtain ⟨R, hR, hRball⟩ := Metric.isOpen_iff.1 hΩ x hx
  have hev : ∀ᶠ j in atTop,
      ((η j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Gv) x ∈ K := by
    filter_upwards [hrOut.eventually (gt_mem_nhds (half_pos hR))] with j hj
    exact hkey (η j) x ((closedBall_subset_ball (by linarith)).trans hRball)
  have := hK.mem_of_tendsto hxlim hev
  simpa [Gv, indicator_of_mem hx] using this

end Homogenization
