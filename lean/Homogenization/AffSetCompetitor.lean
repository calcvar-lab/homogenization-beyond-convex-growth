import Homogenization.PwAffineInterp
import Homogenization.LocalMollifyEnergy
import Homogenization.Step3
import Homogenization.AffSobolev

/-!
# Piecewise affine competitors on `Ω` without boundary condition

Step 4 towards proving the cited `CitedAffineApprox` ([oah-jpm11, Proposition 3.15]); that
statement is not proved here.
* `pwInterp_isPWAffine`: for `f` Lipschitz and `h > 0`, the Kuhn interpolant is piecewise affine
  on any bounded open set;
* `exists_pwInterp_approx_of_contDiff`: uniform and a.e. gradient approximation of a `C¹`
  compactly supported function by its Kuhn interpolants;
* `exists_uniform_modulus_of_continuousOn`: uniform continuity, in `ℝ≥0∞`, of a function
  continuous and finite on an open set, near a compact subset;
* `exists_affSet_energy_close`: an element of `AffSet P Ω` uniformly close to `f` whose
  `L`-energy on `Ω` exceeds that of `f` by at most `ε |Ω|`, when the gradients of `f` on `Ω`
  lie in a compact subset of an open set where `L` is continuous and finite.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution Pointwise

namespace Homogenization

variable {N m : ℕ}

/-- For `f` Lipschitz and `h > 0`, the Kuhn interpolant is piecewise affine on any bounded open
`U` (no boundary condition). -/
theorem pwInterp_isPWAffine {U : Set (Sp N)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : Sp N → Tgt m} {K : ℝ≥0} (hf : LipschitzWith K f) {h : ℝ} (hh : 0 < h) :
    IsPWAffine U (pwInterp h f) := by
  have hLip := lipschitzWith_pwInterp hf hh
  obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
  set M : ℤ := ⌈R / h⌉ + 1
  let ι := (Fin N → (Finset.Icc (-M) M : Set ℤ)) × Equiv.Perm (Fin N)
  let kOf : ι → Fin N → ℤ := fun a i => (a.1 i : ℤ)
  let V : ι → Set (Sp N) := fun a => kuhnPiece h (kOf a) a.2 ∩ U
  let ξ : ι → Mat m N := fun a => kuhnGrad h f (kOf a) a.2
  let e := Fintype.equivFin ι
  refine ⟨⟨_, hLip.lipschitzOnWith⟩,
    Fintype.card ι, fun i => V (e.symm i), fun i => ξ (e.symm i), fun i => ?_, fun i => ?_,
    fun i j hij => ?_, fun i => ?_, ?_, fun i y hy => ?_⟩
  · exact (isOpen_kuhnPiece _ _ _).inter hUo
  · exact inter_subset_right
  · refine Set.disjoint_left.2 fun y hy hy' => hij ?_
    obtain ⟨hk, hσ⟩ := kuhnPiece_eq_of_mem hy.1 hy'.1
    apply e.symm.injective
    refine Prod.ext (funext fun l => Subtype.ext (congrFun hk l)) hσ
  · exact measure_mono_null (inter_frontier_kuhnPiece_subset hh hUo _ _) (volume_kuhnBad h)
  · refine measure_mono_null (fun x ⟨hxU, hxV⟩ => ?_) (volume_kuhnBad h)
    by_contra hbad
    obtain ⟨k, σ, hx⟩ := exists_mem_kuhnPiece hh hbad
    have hk : ∀ l, k l ∈ (Finset.Icc (-M) M : Set ℤ) := by
      intro l
      have hkl : k l = ⌊x l / h⌋ := by
        have h1 := (hx.1 l).1
        have h2 := (hx.1 l).2
        simp only [kuhnFrac] at h1 h2
        exact (Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩).symm
      have hxR : |x l| ≤ R := by
        have := hR hxU
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact (Real.norm_eq_abs (x l) ▸ norm_le_pi_norm x l).trans this
      have hc := Int.le_ceil (R / h)
      rw [abs_le] at hxR
      simp only [Finset.coe_Icc, mem_Icc, hkl, M]
      constructor
      · rw [Int.le_floor]; push_cast
        rw [le_div_iff₀ hh]
        have : -R / h ≥ -(⌈R / h⌉ : ℝ) := by rw [neg_div]; linarith
        rw [ge_iff_le, le_div_iff₀ hh] at this
        nlinarith
      · rw [Int.floor_le_iff]; push_cast
        have : x l / h ≤ R / h := div_le_div_of_nonneg_right hxR.2 hh.le
        linarith
    apply hxV
    refine mem_iUnion.2 ⟨e (fun l => ⟨k l, hk l⟩, σ), ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨hx, hxU⟩
  · exact hasFDerivAt_pwInterp_of_mem_kuhnPiece hy.1

/-- Uniform and gradient approximation of a `C¹` compactly supported `f` by its Kuhn
interpolants, with no boundary condition. -/
theorem exists_pwInterp_approx_of_contDiff {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ h > 0, (∀ x, ‖pwInterp h f x - f x‖ ≤ ε) ∧
      ∀ᵐ x, ‖fderiv ℝ (pwInterp h f) x - fderiv ℝ f x‖ ≤ ε := by
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfs one_ne_zero
  have hUC : UniformContinuous (fderiv ℝ f) :=
    (hfs.fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)
  set ε' : ℝ := ε / (N + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.uniformContinuous_iff.1 hUC ε' hε'
  set h : ℝ := min (δ' / 2) (ε / (C + 1))
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have hhδ' : h < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hhε : (C : ℝ) * h ≤ ε := by
    have h1 : h ≤ ε / (C + 1) := min_le_right _ _
    have h2 : (C : ℝ) * h ≤ (C + 1) * h := by nlinarith
    calc (C : ℝ) * h ≤ (C + 1) * h := h2
      _ ≤ (C + 1) * (ε / (C + 1)) := by gcongr
      _ = ε := by field_simp
  refine ⟨h, hh, fun x => (norm_pwInterp_sub_le hC hh x).trans hhε, ?_⟩
  have hae : ∀ᵐ x, x ∉ kuhnBad (N := N) h := by
    rw [ae_iff]; simpa using volume_kuhnBad (N := N) h
  filter_upwards [hae] with x hx
  obtain ⟨k, σ, hxP⟩ := exists_mem_kuhnPiece hh hx
  rw [(hasFDerivAt_pwInterp_of_mem_kuhnPiece hxP).fderiv]
  have hω : ∀ z, ‖z - x‖ ≤ h → ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε' := by
    intro z hz
    have := hδ'U (a := z) (b := x) (by rw [dist_eq_norm]; exact lt_of_le_of_lt hz hhδ')
    rw [dist_eq_norm] at this
    exact this.le
  calc ‖kuhnGrad h f k σ - fderiv ℝ f x‖ ≤ N * ε' :=
        norm_kuhnGrad_sub_fderiv_le (hf.differentiable one_ne_zero) hh hxP hω
    _ ≤ ε := by
        simp only [ε']
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- A function continuous and finite on an open `V` changes by at most `ε` under perturbations
of size `≤ δ` of points of a compact `K ⊆ V`. -/
theorem exists_uniform_modulus_of_continuousOn {Ψ : Mat m N → ℝ≥0∞} {V : Set (Mat m N)}
    (hVo : IsOpen V) (hΨc : ContinuousOn Ψ V) (hΨfin : ∀ ξ ∈ V, Ψ ξ ≠ ⊤)
    {K : Set (Mat m N)} (hK : IsCompact K) (hKint : K ⊆ V) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ K, ∀ b, ‖b - a‖ ≤ δ →
      Ψ b ≤ Ψ a + ENNReal.ofReal ε ∧ Ψ a ≤ Ψ b + ENNReal.ofReal ε := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hVo hKint
  have hK' : IsCompact (cthickening δ₀ K) := hK.cthickening
  have hcont : ContinuousOn (fun ζ => (Ψ ζ).toReal) (cthickening δ₀ K) :=
    ENNReal.continuousOn_toReal.comp (hΨc.mono hsub) fun ζ hζ => hΨfin ζ (hsub hζ)
  obtain ⟨δ₁, hδ₁, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min δ₀ (δ₁ / 2), lt_min hδ₀ (by positivity), fun a ha b hb => ?_⟩
  have haK : a ∈ cthickening δ₀ K := self_subset_cthickening K ha
  have hbK : b ∈ cthickening δ₀ K :=
    mem_cthickening_of_dist_le b a δ₀ K ha (by rw [dist_eq_norm]; exact hb.trans (min_le_left _ _))
  have hfin : ∀ ζ ∈ cthickening δ₀ K, Ψ ζ = ENNReal.ofReal (Ψ ζ).toReal := fun ζ hζ =>
    (ENNReal.ofReal_toReal (hΨfin ζ (hsub hζ))).symm
  have hd := hU b hbK a haK (by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (hb.trans (min_le_right _ _)) (by linarith))
  rw [Real.dist_eq, abs_lt] at hd
  rw [hfin a haK, hfin b hbK, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le]
  exact ⟨ENNReal.ofReal_le_ofReal (by linarith), ENNReal.ofReal_le_ofReal (by linarith)⟩

/-- **One piecewise affine competitor with energy control (no boundary condition).** For `Ω`
bounded open, `f` of class `C¹` with compact support, gradients of `f` on `Ω` in a compact `K`
inside an open `V` where `L` is continuous and finite: there is `φ ∈ AffSet P Ω` uniformly
`ε`-close to `f` with `∫_Ω L(∇φ) ≤ ∫_Ω L(∇f) + ε |Ω|`. -/
theorem exists_affSet_energy_close {P : ℝ≥0∞} {Ω : Set (Sp N)} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) {V : Set (Mat m N)} (hVo : IsOpen V) {L : Mat m N → ℝ≥0∞}
    (hLc : ContinuousOn L V) (hLfin : ∀ ξ ∈ V, L ξ ≠ ⊤) {K : Set (Mat m N)} (hK : IsCompact K)
    (hKV : K ⊆ V) (hfK : ∀ x ∈ Ω, fderiv ℝ f x ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : W1p N m P Ω, φ ∈ AffSet P Ω ∧ (∀ x, ‖φ.toFun x - f x‖ ≤ ε) ∧
      (∫⁻ x in Ω, L (φ.grad x)) ≤
        (∫⁻ x in Ω, L (fderiv ℝ f x)) + ENNReal.ofReal ε * volume Ω := by
  obtain ⟨δ', hδ', hmod⟩ := exists_uniform_modulus_of_continuousOn hVo hLc hLfin hK hKV hε
  obtain ⟨h, hh, hsup, hgrad⟩ := exists_pwInterp_approx_of_contDiff hf hfs (lt_min hε hδ')
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfs one_ne_zero
  have hLip := lipschitzWith_pwInterp hC hh
  let φ : W1p N m P Ω :=
    { toFun := pwInterp h f
      grad := fderiv ℝ (pwInterp h f)
      memLp := memLp_of_lipschitzWith hΩo hΩb hLip
      memLp_grad := memLp_fderiv_of_lipschitzWith hΩb hLip
      weak := LipschitzWith.hasWeakGrad hLip Ω }
  refine ⟨φ, ⟨pwInterp_isPWAffine hΩo hΩb hC hh, Eventually.of_forall fun _ => rfl⟩,
    fun x => (hsup x).trans (min_le_left _ _), ?_⟩
  have hpt : ∀ᵐ x ∂volume.restrict Ω, L (φ.grad x) ≤ L (fderiv ℝ f x) + ENNReal.ofReal ε := by
    filter_upwards [ae_restrict_of_ae hgrad, ae_restrict_mem hΩo.measurableSet] with x hx hxΩ
    exact (hmod _ (hfK x hxΩ) _ (hx.trans (min_le_right _ _))).1
  calc (∫⁻ x in Ω, L (φ.grad x))
      ≤ ∫⁻ x in Ω, (L (fderiv ℝ f x) + ENNReal.ofReal ε) := lintegral_mono_ae hpt
    _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]

end Homogenization
