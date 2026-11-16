import Homogenization.Subadditive
import Homogenization.Vitali

/-!
# Cut-off functions in `W^{1,p}` (ingredient (f) of the proof of [oah-jpm-zorgati14, Thm 1.1])

The cut-off arguments of [oah-jpm-zorgati14] (Step 2 of the lower bound, Step 3 of the upper
bound) replace a Sobolev function `u` near `x₀` by `v = ℓ + φ (u - ℓ)`, where `ℓ` is the affine
tangent map and `φ` is a cut-off between `Q_{sρ}(x₀)` and `Q_ρ(x₀)`, so that
`v - ℓ ∈ W^{1,p}_0(Q_ρ(x₀))` and `∇v = ∇ℓ + φ (∇u - ∇ℓ) + ∇φ ⊗ (u - ℓ)`.

We use **smooth** cut-offs. Then the product rule for weak gradients is immediate: for a test
function `ψ`, `ψ φ` is again a test function, so no regularization is needed. The paper only
uses `‖∇φ‖_∞ ≤ C/ρ` with `C` depending on `s` (the limits are taken in `ε`, then `ρ`, then `s`),
which a rescaled fixed bump provides.

* `cutoff hs ρ x`: smooth, `[0,1]`-valued, `= 1` on `Q_{sρ}(x)`, `= 0` off `Q_ρ(x)`,
  `tsupport ⊆ Q̄_ρ(x)`, and `‖∇ cutoff‖ ≤ C_s / ρ` (`exists_cutoff_fderiv_bound`);
* `HasWeakGrad.smul_contDiff_univ`: if `w` has weak gradient `g` on `Ω` and `tsupport φ ⊆ Ω`,
  then the zero extension of `φ • w` has weak gradient `φ • g + ∇φ ⊗ w` on `ℝᴺ`;
* `cutoff_mem_W1p0`: the corresponding pair belongs to `W^{1,p}_0(U)` when `support φ ⊆ U`.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### The cut-off functions -/

/-- The fixed bump `θ_s`: `= 1` on `Q̄_s(0)`, supported in `Q_1(0)` (sup-norm balls). -/
noncomputable def cutBump {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : ContDiffBump (0 : Sp N) :=
  ⟨s / 2, 1 / 2, by linarith [hs.1], by linarith [hs.2]⟩

/-- The cut-off `φ(y) = θ_s((y - x)/ρ)` between `Q_{sρ}(x)` and `Q_ρ(x)`. -/
noncomputable def cutoff {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ρ : ℝ) (x : Sp N) : Sp N → ℝ :=
  fun y => cutBump hs (ρ⁻¹ • (y - x))

variable {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)

theorem contDiff_cutoff (ρ : ℝ) (x : Sp N) : ContDiff ℝ (⊤ : ℕ∞) (cutoff hs ρ x) :=
  (cutBump hs).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)

theorem cutoff_nonneg (ρ : ℝ) (x y : Sp N) : 0 ≤ cutoff hs ρ x y := (cutBump hs).nonneg

theorem cutoff_le_one (ρ : ℝ) (x y : Sp N) : cutoff hs ρ x y ≤ 1 := (cutBump hs).le_one

theorem norm_smul_sub_lt_iff {ρ r : ℝ} (hρ : 0 < ρ) (x y : Sp N) :
    ‖ρ⁻¹ • (y - x)‖ < r ↔ ‖y - x‖ < ρ * r := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, inv_mul_lt_iff₀ hρ]

theorem norm_smul_sub_le_iff {ρ r : ℝ} (hρ : 0 < ρ) (x y : Sp N) :
    ‖ρ⁻¹ • (y - x)‖ ≤ r ↔ ‖y - x‖ ≤ ρ * r := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, inv_mul_le_iff₀ hρ]

/-- `φ = 1` on `Q_{sρ}(x)`. -/
theorem cutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) {y : Sp N} (hy : y ∈ cube (s * ρ) x) :
    cutoff hs ρ x y = 1 := by
  refine (cutBump hs).one_of_mem_closedBall ?_
  rw [cube_eq_ball (mul_pos hs.1 hρ)] at hy
  rw [mem_closedBall, dist_zero_right]
  change ‖ρ⁻¹ • (y - x)‖ ≤ s / 2
  rw [norm_smul_sub_le_iff hρ]
  have := mem_ball_iff_norm.1 hy
  linarith

/-- `φ = 0` off `Q_ρ(x)`. -/
theorem cutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) {y : Sp N} (hy : y ∉ cube ρ x) :
    cutoff hs ρ x y = 0 := by
  rw [cube_eq_ball hρ] at hy
  have h : ρ⁻¹ • (y - x) ∉ Function.support (cutBump hs) := by
    rw [(cutBump hs).support_eq]
    intro h
    rw [mem_ball, dist_zero_right, norm_smul_sub_lt_iff hρ] at h
    exact hy (mem_ball_iff_norm.2 (by change ‖y - x‖ < ρ * (1 / 2) at h; linarith))
  exact Function.notMem_support.1 h

theorem support_cutoff_subset {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    Function.support (cutoff hs ρ x) ⊆ cube ρ x := fun y hy => by
  by_contra h
  exact hy (cutoff_eq_zero hs hρ x h)

/-- `tsupport φ ⊆ Q̄_ρ(x)`. -/
theorem tsupport_cutoff_subset {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    tsupport (cutoff hs ρ x) ⊆ closedBall x (ρ / 2) := by
  refine closure_minimal ((support_cutoff_subset hs hρ x).trans ?_) isClosed_closedBall
  rw [cube_eq_ball hρ]
  exact ball_subset_closedBall

theorem hasCompactSupport_cutoff {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    HasCompactSupport (cutoff hs ρ x) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (ρ / 2))
    ((subset_tsupport _).trans (tsupport_cutoff_subset hs hρ x))

/-- **Gradient bound**: `‖∇φ‖ ≤ C_s / ρ`, with `C_s` independent of `ρ` and `x`. -/
theorem exists_cutoff_fderiv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ) (x y : Sp N), 0 < ρ → ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ := by
  set θ := cutBump (N := N) hs
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := θ.contDiff
  have hcont : Continuous (fderiv ℝ θ) := hθ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (θ.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max C 0, le_max_right _ _, fun ρ x y hρ => ?_⟩
  have hd : HasFDerivAt (fun z : Sp N => ρ⁻¹ • (z - x)) (ρ⁻¹ • ContinuousLinearMap.id ℝ (Sp N))
      y := ((hasFDerivAt_id y).sub_const x).const_smul ρ⁻¹
  have hcomp := ((hθ.differentiable (by simp)) (ρ⁻¹ • (y - x))).hasFDerivAt.comp y hd
  change ‖fderiv ℝ (θ ∘ fun z => ρ⁻¹ • (z - x)) y‖ ≤ _
  rw [hcomp.fderiv]
  calc ‖(fderiv ℝ θ (ρ⁻¹ • (y - x))).comp (ρ⁻¹ • ContinuousLinearMap.id ℝ (Sp N))‖
      ≤ ‖fderiv ℝ θ (ρ⁻¹ • (y - x))‖ * ‖ρ⁻¹ • ContinuousLinearMap.id ℝ (Sp N)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max C 0 * ρ⁻¹ := by
        gcongr
        · exact (hC _).trans (le_max_left _ _)
        · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
          exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
    _ = max C 0 / ρ := by rw [div_eq_mul_inv]

/-! ### The product rule with a smooth cut-off -/

section ProductRule

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}

theorem tsupport_fderiv_apply_subset {φ : Sp N → ℝ} (v : Sp N) :
    tsupport (fun y => fderiv ℝ φ y v) ⊆ tsupport φ := by
  refine (closure_mono fun y hy => ?_).trans (tsupport_fderiv_subset ℝ (f := φ))
  intro h
  exact hy (by simp [h])

/-- **Product rule.** If `w` has weak gradient `g` on `Ω` and `φ` is smooth with
`tsupport φ ⊆ Ω`, then the zero extension of `φ • w` has weak gradient `φ • g + ∇φ ⊗ w`
on `ℝᴺ`. (Compactness of
the support of `φ` follows from `tsupport φ ⊆ Ω` and the boundedness of `Ω`.) -/
theorem HasWeakGrad.smul_contDiff_univ (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {w : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hw : MemLp w (ENNReal.ofReal p) (volume.restrict Ω))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict Ω)) (hwg : HasWeakGrad Ω w g)
    {φ : Sp N → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφs : tsupport φ ⊆ Ω) :
    HasWeakGrad univ (fun y => φ y • w y)
      (fun y => φ y • g y + (fderiv ℝ φ y).smulRight (w y)) := by
  intro ψ hψ hcs _ v
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  set χ : Sp N → ℝ := fun y => ψ y * φ y with hχ_def
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hψ.mul hφ
  have hχc : HasCompactSupport χ := hcs.mul_right
  have hχs : tsupport χ ⊆ Ω := (tsupport_mul_subset_right).trans hφs
  set dφ : Sp N → ℝ := fun y => fderiv ℝ φ y v with hdφ_def
  have hdφ : ContDiff ℝ (⊤ : ℕ∞) dφ :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  set ξ : Sp N → ℝ := fun y => ψ y * dφ y with hξ_def
  have hξ : ContDiff ℝ (⊤ : ℕ∞) ξ := hψ.mul hdφ
  have hξc : HasCompactSupport ξ := hcs.mul_right
  have hξs : tsupport ξ ⊆ Ω :=
    (tsupport_mul_subset_right).trans ((tsupport_fderiv_apply_subset v).trans hφs)
  have hderiv : ∀ y, fderiv ℝ χ y v = ψ y * dφ y + φ y * fderiv ℝ ψ y v := by
    intro y
    have h := fderiv_mul (hψd y) (hφd y)
    change fderiv ℝ (ψ * φ) y v = _
    rw [h]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, hdφ_def]
  have hgv : MemLp (fun y => g y v) (ENNReal.ofReal p) (volume.restrict Ω) :=
    hg.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ (Tgt m) v)
  have hi1 := (test_integrable hΩo hΩb hw hχ hχc hχs v).1
  have hi2 := (test_integrable hΩo hΩb hw hξ hξc hξs v).2.1
  have hi3 := (test_integrable hΩo hΩb hgv hχ hχc hχs v).2.1
  change ∫ y, fderiv ℝ ψ y v • (φ y • w y) =
    -∫ y, ψ y • (φ y • g y + (fderiv ℝ φ y).smulRight (w y)) v
  have hL : (fun y => fderiv ℝ ψ y v • (φ y • w y)) =
      fun y => fderiv ℝ χ y v • w y - ξ y • w y := by
    funext y
    rw [hderiv y]
    simp only [hξ_def]
    module
  have hR : (fun y => ψ y • (φ y • g y + (fderiv ℝ φ y).smulRight (w y)) v) =
      fun y => χ y • g y v + ξ y • w y := by
    funext y
    simp only [hχ_def, hξ_def, hdφ_def, add_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
    module
  rw [hL, hR, integral_sub hi1 hi2, integral_add hi3 hi2, hwg χ hχ hχc hχs v]
  abel

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- A function in `Lᵖ(Ω)` vanishing off `Ω` is in `Lᵖ(ℝᴺ)`. -/
theorem memLp_of_restrict_of_eq_zero {E : Type*} [NormedAddCommGroup E]
    (hΩm : MeasurableSet Ω) {q : ℝ≥0∞} {F : Sp N → E} (hF : MemLp F q (volume.restrict Ω))
    (hF0 : ∀ y ∉ Ω, F y = 0) : MemLp F q volume := by
  have h := (memLp_indicator_iff_restrict hΩm).2 hF
  have heq : Ω.indicator F = F := by
    funext y
    by_cases hy : y ∈ Ω
    · exact indicator_of_mem hy F
    · rw [indicator_of_notMem hy, hF0 y hy]
  rwa [heq] at h

/-- **The cut-off competitor.** With `w`, `g` as above, `φ` smooth with compact support in `Ω`,
`φ = 0` off `U`, `|φ| ≤ 1` and `‖∇φ‖ ≤ C`, the pair `(φ w, φ g + ∇φ ⊗ w)` lies in
`W^{1,p}_0(U)`. Applied to `w = u - ℓ` this gives `v - ℓ ∈ W^{1,p}_0(Q_ρ)` for
`v = ℓ + φ (u - ℓ)`. -/
theorem cutoff_mem_W1p0 (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {w : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hw : MemLp w (ENNReal.ofReal p) (volume.restrict Ω))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict Ω)) (hwg : HasWeakGrad Ω w g)
    {φ : Sp N → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφs : tsupport φ ⊆ Ω)
    {U : Set (Sp N)} (hφU : ∀ y ∉ U, φ y = 0)
    (hφ1 : ∀ y, |φ y| ≤ 1) {C : ℝ} (hC : 0 ≤ C) (hdC : ∀ y, ‖fderiv ℝ φ y‖ ≤ C) :
    ((fun y => φ y • w y), (fun y => φ y • g y + (fderiv ℝ φ y).smulRight (w y))) ∈
      W1p0 (ENNReal.ofReal p) U := by
  have hΩm := hΩo.measurableSet
  have hφ0 : ∀ y ∉ Ω, φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hφs h)
  have hdφ0 : ∀ y ∉ Ω, fderiv ℝ φ y = 0 := fun y hy =>
    fderiv_of_notMem_tsupport ℝ fun h => hy (hφs h)
  have hφcont : Continuous φ := hφ.continuous
  have hdcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hf : MemLp (fun y => φ y • w y) (ENNReal.ofReal p) (volume.restrict Ω) :=
    hw.of_le (hφcont.aestronglyMeasurable.smul hw.1) (ae_of_all _ fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hφ1 y))
  have hg1 : MemLp (fun y => φ y • g y) (ENNReal.ofReal p) (volume.restrict Ω) :=
    hg.of_le (hφcont.aestronglyMeasurable.smul hg.1) (ae_of_all _ fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hφ1 y))
  have hg2 : MemLp (fun y => (fderiv ℝ φ y).smulRight (w y)) (ENNReal.ofReal p)
      (volume.restrict Ω) := by
    refine (hw.const_smul C).of_le ?_ (ae_of_all _ fun y => ?_)
    · exact (ContinuousLinearMap.smulRightL ℝ (Sp N) (Tgt m)).aestronglyMeasurable_comp₂
        hdcont.aestronglyMeasurable hw.1
    · rw [ContinuousLinearMap.norm_smulRight_apply, Pi.smul_apply, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hdC y) (norm_nonneg _)
  have h1 : ∀ y ∉ U, φ y • w y = 0 := fun y hy => by rw [hφU y hy, zero_smul]
  have h2 : MemLp (fun y => φ y • w y) (ENNReal.ofReal p) volume :=
    memLp_of_restrict_of_eq_zero hΩm hf fun y hy => by
      change φ y • w y = 0
      rw [hφ0 y hy, zero_smul]
  have h3 : MemLp (fun y => φ y • g y + (fderiv ℝ φ y).smulRight (w y)) (ENNReal.ofReal p)
      volume :=
    memLp_of_restrict_of_eq_zero hΩm (memLp_add' hg1 hg2) fun y hy => by
      change φ y • g y + (fderiv ℝ φ y).smulRight (w y) = 0
      rw [hφ0 y hy, hdφ0 y hy, zero_smul, zero_add]
      exact ContinuousLinearMap.ext fun z => by
        rw [ContinuousLinearMap.smulRight_apply, zero_apply, zero_smul,
          zero_apply]
  have h4 := HasWeakGrad.smul_contDiff_univ hΩo hΩb hw hg hwg hφ hφs
  exact ⟨h1, h2, h3, h4⟩

/-! ### Application to `u - ℓ`, `ℓ` affine -/

/-- The affine map `ℓ(y) = a + A (y - x₀)`. -/
def affineMap (a : Tgt m) (A : Mat m N) (x₀ : Sp N) (y : Sp N) : Tgt m := a + A (y - x₀)

theorem hasFDerivAt_affineMap (a : Tgt m) (A : Mat m N) (x₀ y : Sp N) :
    HasFDerivAt (affineMap a A x₀) A y := by
  have h := (A.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀)).const_add a
  simpa [affineMap, Function.comp_def] using h

theorem lipschitzWith_affineMap (a : Tgt m) (A : Mat m N) (x₀ : Sp N) :
    LipschitzWith ‖A‖₊ (affineMap a A x₀) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm, dist_eq_norm, affineMap, affineMap, add_sub_add_left_eq_sub, ← map_sub,
    sub_sub_sub_cancel_right]
  exact A.le_opNorm _

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- An affine map is in `Lᵖ(Ω)` on a bounded set. -/
theorem memLp_affineMap (hΩb : Bornology.IsBounded Ω) (a : Tgt m) (A : Mat m N) (x₀ : Sp N)
    (q : ℝ≥0∞) : MemLp (affineMap a A x₀) q (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn
    (lipschitzWith_affineMap a A x₀).continuous.continuousOn
  refine MemLp.of_bound (lipschitzWith_affineMap a A x₀).continuous.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' measurableSet_closure |>.2 (ae_of_all _ fun y hy => hC y hy)).filter_mono
    (Measure.restrict_mono subset_closure le_rfl |> ae_mono)

theorem hasWeakGrad_affineMap (U : Set (Sp N)) (a : Tgt m) (A : Mat m N) (x₀ : Sp N) :
    HasWeakGrad U (affineMap a A x₀) (fun _ => A) :=
  (LipschitzWith.hasWeakGrad (lipschitzWith_affineMap a A x₀) U).congr_grad_ae
    (ae_of_all _ fun y => (hasFDerivAt_affineMap a A x₀ y).fderiv)

/-- **The cut-off competitor for `u - ℓ`.** For `u ∈ W^{1,p}(Ω)`, `ℓ` affine with gradient `A`,
and the cut-off `φ` between `Q_{sρ}(x)` and `Q_ρ(x)` with `Q̄_ρ(x) ⊆ Ω`,
`(φ (u - ℓ), φ (∇u - A) + ∇φ ⊗ (u - ℓ)) ∈ W^{1,p}_0(Q_ρ(x))`, so that
`v = ℓ + φ (u - ℓ) ∈ ℓ + W^{1,p}_0(Q_ρ(x))`. -/
theorem cutoff_sub_affine_mem_W1p0 (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N) (x₀ : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N)
    (hΩx : closedBall x (ρ / 2) ⊆ Ω) :
    ((fun y => cutoff hs ρ x y • (u.toFun y - affineMap a A x₀ y)),
      (fun y => cutoff hs ρ x y • (u.grad y - A) +
        (fderiv ℝ (cutoff hs ρ x) y).smulRight (u.toFun y - affineMap a A x₀ y))) ∈
      W1p0 (ENNReal.ofReal p) (cube ρ x) := by
  have hw : MemLp (fun y => u.toFun y - affineMap a A x₀ y) (ENNReal.ofReal p)
      (volume.restrict Ω) := u.memLp.sub (memLp_affineMap hΩb a A x₀ _)
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  have hg : MemLp (fun y => u.grad y - A) (ENNReal.ofReal p) (volume.restrict Ω) :=
    u.memLp_grad.sub (memLp_const A)
  have hwg : HasWeakGrad Ω (fun y => u.toFun y - affineMap a A x₀ y) (fun y => u.grad y - A) := by
    have hneg : HasWeakGrad Ω (affineMap (-a) (-A) x₀) (fun _ => -A) :=
      hasWeakGrad_affineMap Ω (-a) (-A) x₀
    have h := HasWeakGrad.add hΩo hΩb u.memLp u.memLp_grad (memLp_affineMap hΩb (-a) (-A) x₀ _)
      (memLp_const (-A)) u.weak hneg
    have e1 : (u.toFun + affineMap (-a) (-A) x₀) = fun y => u.toFun y - affineMap a A x₀ y := by
      funext y
      simp only [Pi.add_apply, affineMap, neg_apply]
      abel
    have e2 : (u.grad + fun _ => -A) = fun y => u.grad y - A := by
      funext y
      simp only [Pi.add_apply, sub_eq_add_neg]
    rwa [e1, e2] at h
  obtain ⟨C, hC0, hC⟩ := exists_cutoff_fderiv_bound (N := N) hs
  exact cutoff_mem_W1p0 hΩo hΩb hw hg hwg (contDiff_cutoff hs ρ x)
    ((tsupport_cutoff_subset hs hρ x).trans hΩx) (fun y hy => cutoff_eq_zero hs hρ x hy)
    (fun y => by rw [abs_of_nonneg (cutoff_nonneg hs ρ x y)]; exact cutoff_le_one hs ρ x y)
    (div_nonneg hC0 hρ.le) fun y => hC ρ x y hρ

/-- On `Q_{sρ}(x)` the cut-off is identically `1`, so its gradient vanishes. -/
theorem fderiv_cutoff_eq_zero {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Sp N) {y : Sp N} (hy : y ∈ cube (s * ρ) x) : fderiv ℝ (cutoff hs ρ x) y = 0 := by
  have h : cutoff hs ρ x =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_cube _ _).mem_nhds hy] with z hz
    exact cutoff_eq_one hs hρ x hz
  rw [h.fderiv_eq, fderiv_const_apply]

end ProductRule

end Homogenization
