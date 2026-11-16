import Homogenization.PwAffineInterp
import Homogenization.SmoothApproxW1p0

/-!
# Lemma `lemme_approx_convex_zero` for cubes

`approxConvexZero_cube`: for `Q = cube ρ 0`, `Ψ` convex, lower semicontinuous with
`0 ∈ int(dom Ψ)`, and `u ∈ W^{1,p}_0(Q)` (`p ≥ 1`) with `∫_Q Ψ(∇u) < ∞`, there are
`φₙ ∈ Aff₀(Q)` with `∇φₙ → ∇u` a.e. on `Q` and `∫_Q Ψ(∇φₙ) → ∫_Q Ψ(∇u)`.

This is the case of [duerinckx-gloria16, Prop. A.16] used in the paper (in the proof of
`lemmaUSC_ineq`, with `O = k₀Y`); it replaces the former cited hypothesis
`CitedApproxConvexZero`. The general statement for an arbitrary bounded Lipschitz domain, and the
conclusions `∇φₙ ∈ int(dom Ψ)` and `φₙ → u` in `W^{1,p}`, are not formalized.

Proof: `exists_smooth_approx_W1p0` (contraction, mollification, Jensen) gives smooth `fₙ` with
gradients in a compact subset of `int(dom Ψ)`; each `fₙ` is approximated in `Aff₀(Q)` by
`exists_Aff0_approx_of_contDiff` (Kuhn interpolation), the energies staying close by uniform
continuity of `Ψ` on a compact neighbourhood (`ConvexENN.exists_uniform_modulus`,
`exists_Aff0_energy_close`).
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Pointwise

namespace Homogenization

variable {N m : ℕ}

/-- If `Ψ` is convex and `K ⊆ int(dom Ψ)` is compact, then `Ψ` changes by at most `ε` under
perturbations of size `≤ δ` of points of `K`. -/
theorem ConvexENN.exists_uniform_modulus {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ)
    {K : Set (Mat m N)} (hK : IsCompact K) (hKint : K ⊆ interior (dom Ψ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ K, ∀ b, ‖b - a‖ ≤ δ →
      Ψ b ≤ Ψ a + ENNReal.ofReal ε ∧ Ψ a ≤ Ψ b + ENNReal.ofReal ε := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open isOpen_interior hKint
  have hK' : IsCompact (cthickening δ₀ K) := hK.cthickening
  have hcont : ContinuousOn (fun ζ => (Ψ ζ).toReal) (cthickening δ₀ K) :=
    ENNReal.continuousOn_toReal.comp (hΨ.continuousOn_interior_dom.mono hsub)
      fun ζ hζ => (show ζ ∈ dom Ψ from interior_subset (hsub hζ)).ne
  obtain ⟨δ₁, hδ₁, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min δ₀ (δ₁ / 2), lt_min hδ₀ (by positivity), fun a ha b hb => ?_⟩
  have haK : a ∈ cthickening δ₀ K := self_subset_cthickening K ha
  have hbK : b ∈ cthickening δ₀ K :=
    mem_cthickening_of_dist_le b a δ₀ K ha (by rw [dist_eq_norm]; exact hb.trans (min_le_left _ _))
  have hfin : ∀ ζ ∈ cthickening δ₀ K, Ψ ζ = ENNReal.ofReal (Ψ ζ).toReal := fun ζ hζ =>
    (ENNReal.ofReal_toReal (show ζ ∈ dom Ψ from interior_subset (hsub hζ)).ne).symm
  have hd := hU b hbK a haK (by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (hb.trans (min_le_right _ _)) (by linarith))
  rw [Real.dist_eq, abs_lt] at hd
  rw [hfin a haK, hfin b hbK, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le]
  exact ⟨ENNReal.ofReal_le_ofReal (by linarith), ENNReal.ofReal_le_ofReal (by linarith)⟩

/-- One `Aff₀` approximation of a smooth `f` with gradients in a compact `K ⊆ int(dom Ψ)`:
gradients within `δ` a.e. and energies within `ε |Q|`. -/
theorem exists_Aff0_energy_close {ρ : ℝ} {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ)
    {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f)
    (hfQ : tsupport f ⊆ cube ρ 0) {K : Set (Mat m N)} (hK : IsCompact K)
    (hKint : K ⊆ interior (dom Ψ)) (hfK : ∀ x, fderiv ℝ f x ∈ K) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ φ ∈ (Aff0 (cube ρ 0) : Set (Sp N → Tgt m)),
      (∀ᵐ x, ‖fderiv ℝ φ x - fderiv ℝ f x‖ ≤ δ) ∧
      (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ φ x)) ≤
        (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ f x)) + ENNReal.ofReal ε * volume (cube ρ (0 : Sp N)) ∧
      (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ f x)) ≤
        (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ φ x)) + ENNReal.ofReal ε * volume (cube ρ (0 : Sp N)) := by
  obtain ⟨δ', hδ', hmod⟩ := hΨ.exists_uniform_modulus hK hKint hε
  obtain ⟨φ, hφ, -, hgrad⟩ := exists_Aff0_approx_of_contDiff (isOpen_cube ρ 0)
    (isBounded_cube ρ 0) hf hfs hfQ (lt_min hδ hδ')
  have hpt : ∀ᵐ x, Ψ (fderiv ℝ φ x) ≤ Ψ (fderiv ℝ f x) + ENNReal.ofReal ε ∧
      Ψ (fderiv ℝ f x) ≤ Ψ (fderiv ℝ φ x) + ENNReal.ofReal ε := by
    filter_upwards [hgrad] with x hx
    exact hmod _ (hfK x) _ (hx.trans (min_le_right _ _))
  refine ⟨φ, hφ, hgrad.mono fun x hx => hx.trans (min_le_left _ _), ?_, ?_⟩
  · calc (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ φ x))
        ≤ ∫⁻ x in cube ρ 0, (Ψ (fderiv ℝ f x) + ENNReal.ofReal ε) :=
          lintegral_mono_ae (ae_restrict_of_ae (hpt.mono fun x hx => hx.1))
      _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  · calc (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ f x))
        ≤ ∫⁻ x in cube ρ 0, (Ψ (fderiv ℝ φ x) + ENNReal.ofReal ε) :=
          lintegral_mono_ae (ae_restrict_of_ae (hpt.mono fun x hx => hx.2))
      _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]

/-- **Lemma `lemme_approx_convex_zero` for cubes** (the case used in the paper). For
`Q = cube ρ 0`, `Ψ` convex, lower semicontinuous with `0 ∈ int(dom Ψ)`, and `u ∈ W^{1,p}_0(Q)`
with `∫_Q Ψ(∇u) < ∞`, there are `φₙ ∈ Aff₀(Q)` with `∇φₙ → ∇u` a.e. on `Q` and
`∫_Q Ψ(∇φₙ) → ∫_Q Ψ(∇u)`. -/
theorem approxConvexZero_cube {p : ℝ} (hp : 1 ≤ p) {ρ : ℝ} (hρ : 0 < ρ)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) (cube ρ 0))
    {Ψ : Mat m N → ℝ≥0∞} (hΨ : ConvexENN Ψ) (hΨlsc : LowerSemicontinuous Ψ)
    (h0 : (0 : Mat m N) ∈ interior (dom Ψ)) (hE : ∫⁻ z in cube ρ 0, Ψ (u.2 z) < ⊤) :
    ∃ φ : ℕ → Sp N → Tgt m, (∀ n, φ n ∈ Aff0 (cube ρ 0)) ∧
      (∀ᵐ x ∂volume.restrict (cube ρ 0),
        Tendsto (fun n => fderiv ℝ (φ n) x) atTop (𝓝 (u.2 x))) ∧
      Tendsto (fun n => ∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (φ n) x)) atTop
        (𝓝 (∫⁻ x in cube ρ 0, Ψ (u.2 x))) := by
  obtain ⟨f, t, ht1, hfC, hfcs, hfQ, hfval, hfae, hfE⟩ :=
    exists_smooth_approx_W1p0 hp hρ hu hΨ hΨlsc h0 hE
  have hstep : ∀ n : ℕ, ∃ φ ∈ (Aff0 (cube ρ 0) : Set (Sp N → Tgt m)),
      (∀ᵐ x, ‖fderiv ℝ φ x - fderiv ℝ (f n) x‖ ≤ 1 / ((n : ℝ) + 1)) ∧
      (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ φ x)) ≤ (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x)) +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) * volume (cube ρ (0 : Sp N)) ∧
      (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x)) ≤ (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ φ x)) +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) * volume (cube ρ (0 : Sp N)) := by
    intro n
    obtain ⟨M, hM⟩ := (hfC n |>.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      ((hfcs n).fderiv (𝕜 := ℝ))
    obtain ⟨hSc, -, hSint⟩ := hΨ.smul_closure_dom h0 (t := t n) (t n).2
      (by exact_mod_cast ht1 n)
    refine exists_Aff0_energy_close hΨ (hfC n) (hfcs n) (hfQ n)
      (K := ((t n : ℝ) • closure (dom Ψ)) ∩ closedBall 0 M)
      ((isCompact_closedBall 0 M).inter_left hSc) (inter_subset_left.trans hSint)
      (fun x => ⟨hfval n x, by rw [mem_closedBall, dist_zero_right]; exact hM x⟩)
      (by positivity) (by positivity)
  choose φ hφ hgrad hup hlow using hstep
  refine ⟨φ, hφ, ?_, ?_⟩
  · have hall : ∀ᵐ x ∂volume.restrict (cube ρ 0), ∀ n,
        ‖fderiv ℝ (φ n) x - fderiv ℝ (f n) x‖ ≤ 1 / ((n : ℝ) + 1) :=
      ae_all_iff.2 fun n => ae_restrict_of_ae (hgrad n)
    filter_upwards [hall, hfae] with x hx hxf
    have hdiff : Tendsto (fun n => fderiv ℝ (φ n) x - fderiv ℝ (f n) x) atTop (𝓝 0) :=
      squeeze_zero_norm hx tendsto_one_div_add_atTop_nhds_zero_nat
    have := hxf.add hdiff
    rw [add_zero] at this
    exact this.congr fun n => by abel
  · set c : ℕ → ℝ≥0∞ := fun n =>
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) * volume (cube ρ (0 : Sp N))
    have hQfin : volume (cube ρ (0 : Sp N)) ≠ ⊤ := (isBounded_cube _ _).measure_lt_top.ne
    have hc : Tendsto c atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        have := (ENNReal.continuous_ofReal.tendsto 0).comp
          tendsto_one_div_add_atTop_nhds_zero_nat
        rw [ENNReal.ofReal_zero] at this
        exact this
      have := ENNReal.Tendsto.mul_const h1 (Or.inr hQfin)
      rw [zero_mul] at this
      exact this
    have hEne : (∫⁻ x in cube ρ 0, Ψ (u.2 x)) ≠ ⊤ := hE.ne
    have hupper : Tendsto (fun n => (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x)) + c n) atTop
        (𝓝 (∫⁻ x in cube ρ 0, Ψ (u.2 x))) := by
      have := hfE.add hc; rwa [add_zero] at this
    have hlower : Tendsto (fun n => (∫⁻ x in cube ρ 0, Ψ (fderiv ℝ (f n) x)) - c n) atTop
        (𝓝 (∫⁻ x in cube ρ 0, Ψ (u.2 x))) := by
      have := ENNReal.Tendsto.sub hfE hc (Or.inl hEne); rwa [tsub_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
      (fun n => tsub_le_iff_right.2 (hlow n)) hup

end Homogenization
