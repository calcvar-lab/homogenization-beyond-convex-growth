import Homogenization.Envelopes

/-!
# `Aff₀(U;ℝᵐ) ⊂ W^{1,p}_0(U;ℝᵐ)` and `ℋ_p ≤ ℋ_aff`

Inclusion (2.1) (`eq:affinclusion`) of the paper, for bounded `U`, and its consequence
`ℋ L ≤ ℋ_aff L` of Remark `lEnvelopes` (iii). The weak gradient of a Lipschitz function is its
pointwise gradient by the integration by parts formula of Mathlib's proof of Rademacher's theorem.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- A globally Lipschitz function has its pointwise (a.e.) gradient as weak gradient. -/
theorem LipschitzWith.hasWeakGrad {φ : Sp N → Tgt m} {K : ℝ≥0} (hK : LipschitzWith K φ)
    (U : Set (Sp N)) : HasWeakGrad U φ (fderiv ℝ φ) := by
  intro ψ hψ hcs _ v
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hψ (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  -- integrability of both sides
  have hφc : Continuous φ := hK.continuous
  have hF1 : Integrable (fun y => fderiv ℝ ψ y v • φ y) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).smul hφc
    · refine (hcs.fderiv (𝕜 := ℝ)).mono fun y hy => ?_
      rw [mem_support] at hy ⊢
      intro h; apply hy; rw [h]; simp
  have hF2 : Integrable (fun y => ψ y • fderiv ℝ φ y v) := by
    obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hcs
    rw [← memLp_one_iff_integrable]
    refine (hcs.smul_right (f' := fun y => fderiv ℝ φ y v)).memLp_of_bound ?_ (Cψ * (K * ‖v‖)) ?_
    · exact hψ.continuous.aestronglyMeasurable.smul
        ((measurable_fderiv_apply_const ℝ φ v).aestronglyMeasurable)
    · refine Eventually.of_forall fun y => ?_
      change ‖ψ y • fderiv ℝ φ y v‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul (hCψ y) ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hK) (norm_nonneg _)))
        (norm_nonneg _) ((norm_nonneg _).trans (hCψ y))
  funext k
  have e1 : (∫ y, fderiv ℝ ψ y v • φ y) k = ∫ y, fderiv ℝ ψ y v * φ y k :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).integral_comp_comm
      hF1).symm
  have e2 : (∫ y, ψ y • fderiv ℝ φ y v) k = ∫ y, ψ y * fderiv ℝ φ y v k :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).integral_comp_comm
      hF2).symm
  rw [Pi.neg_apply, e1, e2]
  -- Rademacher's integration by parts for the component `φ_k`
  have hfk : LipschitzWith K (fun y => φ y k) :=
    LipschitzWith.of_dist_le_mul fun x y => (dist_le_pi_dist (φ x) (φ y) k).trans
      (hK.dist_le_mul x y)
  have hIBP := hfk.integral_lineDeriv_mul_eq (μ := volume) hC hcs v
  have hL : (fun y => lineDeriv ℝ (fun y => φ y k) y v * ψ y) =ᵐ[volume]
      fun y => ψ y * fderiv ℝ φ y v k := by
    filter_upwards [hK.ae_differentiableAt (μ := volume)] with y hy
    have hd : HasFDerivAt (fun y => φ y k)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).comp (fderiv ℝ φ y)) y :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).hasFDerivAt.comp y
        hy.hasFDerivAt
    rw [(hd.hasLineDerivAt v).lineDeriv, mul_comm]
    rfl
  have hR : (fun y => lineDeriv ℝ ψ y (-v) * φ y k) = fun y => -(fderiv ℝ ψ y v * φ y k) := by
    funext y
    rw [(hψd y).lineDeriv_eq_fderiv, map_neg, neg_mul]
  rw [integral_congr_ae hL, hR, integral_neg] at hIBP
  rw [hIBP, neg_neg]

/-- **Inclusion (2.1)**: `Aff₀(U;ℝᵐ) ⊂ W^{1,p}_0(U;ℝᵐ)` for bounded `U`. -/
theorem mem_W1p0_of_mem_Aff0 {p : ℝ≥0∞} {U : Set (Sp N)} (hU : Bornology.IsBounded U)
    {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 U) : (φ, fderiv ℝ φ) ∈ W1p0 p U := by
  obtain ⟨⟨K, hK⟩, h0, -⟩ := hφ
  have hcs : HasCompactSupport φ :=
    HasCompactSupport.intro hU.isCompact_closure fun y hy => h0 y fun h => hy (subset_closure h)
  refine ⟨h0, hK.continuous.memLp_of_hasCompactSupport hcs, ?_,
    LipschitzWith.hasWeakGrad hK univ⟩
  exact (hcs.fderiv (𝕜 := ℝ)).memLp_of_bound (measurable_fderiv ℝ φ).aestronglyMeasurable K
    (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hK)

theorem Ytp_le_Yt (p : ℝ≥0∞) (L : Sp N → Mat m N → ℝ≥0∞) {U : Set (Sp N)}
    (hU : Bornology.IsBounded U) (ξ : Mat m N) : Ytp p L U ξ ≤ Yt L U ξ :=
  le_iInf₂ fun φ hφ => iInf₂_le (φ, fderiv ℝ φ) (mem_W1p0_of_mem_Aff0 hU hφ)

/-- Remark `lEnvelopes` (iii): `ℋ_p L ≤ ℋ_aff L`. -/
theorem Hp_le_Haff (p : ℝ≥0∞) (L : Sp N → Mat m N → ℝ≥0∞) : Hp p L ≤ Haff L := by
  intro ξ
  refine iInf_mono fun k => ENNReal.div_le_div_right (Ytp_le_Yt p L ?_ ξ) _
  exact (Metric.isBounded_Icc (fun i => (0 : ℝ) - ((k : ℝ) + 1) / 2)
    (fun i => (0 : ℝ) + ((k : ℝ) + 1) / 2)).subset
    fun _ hy => ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩

end Homogenization
