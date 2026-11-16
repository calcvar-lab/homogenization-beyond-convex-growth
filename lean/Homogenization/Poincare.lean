import Homogenization.AffSobolev

/-!
# Poincaré's inequality on cubes for Lipschitz functions

Used in Step 4 (e) of the proof of Theorem `main-Ggrowth`:
`∫_Q |φ|ᵖ ≤ m ρᵖ ∫_Q |∇φ|ᵖ` for `φ` Lipschitz vanishing outside a cube `Q` of side `ρ`.
(The constant `m` comes from the sup norm on `ℝᵐ`; the paper's constant `K` depends on `p, N`.)

The one-dimensional case follows from the fundamental theorem of calculus for absolutely
continuous functions and Hölder's inequality; the general case from Fubini's theorem in the first
coordinate.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

theorem enorm_le_lintegral_deriv {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {a b : ℝ}
    (h0 : ∀ t ∉ Ioo a b, f t = 0) (t : ℝ) :
    ‖f t‖ₑ ≤ ∫⁻ s in Ioc a b, ‖deriv f s‖ₑ := by
  by_cases ht : t ∈ Ioo a b
  · have hfa : f a = 0 := h0 a fun h => lt_irrefl a h.1
    have hac : AbsolutelyContinuousOnInterval f a t :=
      (hf.lipschitzOnWith (s := uIcc a t)).absolutelyContinuousOnInterval
    have h := hac.integral_deriv_eq_sub
    rw [hfa, sub_zero] at h
    rw [← h, intervalIntegral.integral_of_le ht.1.le]
    exact (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono_set (Ioc_subset_Ioc_right ht.2.le))
  · rw [h0 t ht]; simp

/-- **One-dimensional Poincaré inequality.** -/
theorem poincare_1d {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {a b : ℝ}
    (h0 : ∀ t ∉ Ioo a b, f t = 0) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ t, ‖f t‖ₑ ^ p ≤ ENNReal.ofReal (b - a) ^ p * ∫⁻ t, ‖deriv f t‖ₑ ^ p := by
  set A := ∫⁻ s in Ioc a b, ‖deriv f s‖ₑ
  set V := ENNReal.ofReal (b - a)
  have hp0 : 0 < p := by linarith
  have h1 : ∫⁻ t, ‖f t‖ₑ ^ p ≤ V * A ^ p := by
    calc ∫⁻ t, ‖f t‖ₑ ^ p = ∫⁻ t in Ioo a b, ‖f t‖ₑ ^ p := by
          rw [← lintegral_indicator measurableSet_Ioo]
          congr 1; funext t
          by_cases ht : t ∈ Ioo a b
          · simp [ht]
          · simp [ht, h0 t ht, ENNReal.zero_rpow_of_pos hp0]
      _ ≤ ∫⁻ t in Ioo a b, A ^ p :=
          lintegral_mono fun t => ENNReal.rpow_le_rpow (enorm_le_lintegral_deriv hf h0 t) hp0.le
      _ = V * A ^ p := by rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
  -- Hölder: `A ≤ (∫ |f'|ᵖ)^(1/p) |I|^(1 - 1/p)`
  set X := ∫⁻ s in Ioc a b, ‖deriv f s‖ₑ ^ p
  have h2 : A ≤ X ^ (1 / p) * V ^ (1 - 1 / p) := by
    have hmeas : AEStronglyMeasurable (deriv f) (volume.restrict (Ioc a b)) :=
      (measurable_deriv f).aestronglyMeasurable
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := ENNReal.ofReal p)
      (by simpa using hp) hmeas
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simp; linarith) ENNReal.ofReal_ne_top, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal hp0.le] at h
    simpa using h
  have hX : X ≤ ∫⁻ t, ‖deriv f t‖ₑ ^ p := setLIntegral_le_lintegral _ _
  by_cases hV : V = 0
  · rw [hV, zero_mul] at h1; exact h1.trans (zero_le)
  have hVt : V ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∫⁻ t, ‖f t‖ₑ ^ p ≤ V * A ^ p := h1
    _ ≤ V * (X ^ (1 / p) * V ^ (1 - 1 / p)) ^ p := by gcongr
    _ = V ^ p * X := by
        have e0 : (1 - 1 / p) * p = p - 1 := by field_simp
        have e1 : (X ^ (1 / p) * V ^ (1 - 1 / p)) ^ p = X * V ^ (p - 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            e0, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
        have e2 : V * V ^ (p - 1) = V ^ p := by
          conv_lhs => arg 1; rw [← ENNReal.rpow_one V]
          rw [← ENNReal.rpow_add _ _ hV hVt]; congr 1; ring
        rw [e1, mul_left_comm, e2, mul_comm]
    _ ≤ V ^ p * ∫⁻ t, ‖deriv f t‖ₑ ^ p := by gcongr

/-- The sup norm on `ℝᵐ` is controlled by the `ℓᵖ` sum of the components. -/
theorem enorm_rpow_le_sum {v : Tgt m} {p : ℝ} (hp : 0 < p) :
    ‖v‖ₑ ^ p ≤ ∑ k, ‖v k‖ₑ ^ p := by
  rcases (Finset.univ : Finset (Fin m)).eq_empty_or_nonempty with h | h
  · have : ‖v‖₊ = 0 := by rw [Pi.nnnorm_def, h, Finset.sup_empty]; rfl
    rw [enorm_eq_nnnorm, this, ENNReal.coe_zero, ENNReal.zero_rpow_of_pos hp]
    exact zero_le
  · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup _ h fun b => ‖v b‖₊
    have : ‖v‖ₑ = ‖v k‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Pi.nnnorm_def, hk]
    rw [this]
    exact Finset.single_le_sum (f := fun k => ‖v k‖ₑ ^ p) (fun _ _ => zero_le)
      (Finset.mem_univ k)

/-! ### Fubini in the first coordinate -/

section Fubini

variable {n : ℕ}

/-- The measurable equivalence `ℝⁿ⁺¹ ≃ ℝ × ℝⁿ` splitting off the first coordinate. -/
noncomputable abbrev split0 : Sp (n + 1) ≃ᵐ ℝ × Sp n :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0

theorem lintegral_split0 (F : Sp (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ x', ∫⁻ t, F (split0.symm (t, x')) := by
  have hmp : MeasurePreserving (split0 (n := n)).symm
      ((volume : Measure ℝ).prod (volume : Measure (Sp n))) (volume : Measure (Sp (n + 1))) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0).symm _
  rw [← hmp.lintegral_comp_emb split0.symm.measurableEmbedding F]
  exact lintegral_prod_symm _ (hF.comp split0.symm.measurable).aemeasurable

theorem split0_symm_add (t s : ℝ) (x' : Sp n) :
    (split0 (n := n)).symm (t + s, x') = split0.symm (t, x') + s • Pi.single 0 1 := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [split0, MeasurableEquiv.piFinSuccAbove]
  · simp [split0, MeasurableEquiv.piFinSuccAbove]

theorem split0_symm_apply_zero (t : ℝ) (x' : Sp n) : (split0 (n := n)).symm (t, x') 0 = t := by
  simp [split0, MeasurableEquiv.piFinSuccAbove]

theorem lipschitzWith_split0_symm (x' : Sp n) :
    LipschitzWith ‖(Pi.single 0 1 : Sp (n + 1))‖₊ fun t : ℝ => (split0 (n := n)).symm (t, x') := by
  have h : (fun t : ℝ => (split0 (n := n)).symm (t, x')) =
      fun t => split0.symm (0, x') + t • (Pi.single 0 1 : Sp (n + 1)) := by
    funext t; rw [← split0_symm_add, zero_add]
  rw [h]
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm, Real.norm_eq_abs]
  rfl

end Fubini

/-- **Poincaré's inequality on cubes.** -/
theorem poincare_cube [NeZero N] {p : ℝ} (hp : 1 ≤ p) {φ : Sp N → Tgt m} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) {ρ : ℝ} {x : Sp N} (h0 : ∀ y ∉ cube ρ x, φ y = 0) :
    ∫⁻ y, ‖φ y‖ₑ ^ p ≤ m * ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖fderiv ℝ φ y‖ₑ ^ p := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have hp0 : 0 < p := by linarith
  set e0 : Sp (n + 1) := Pi.single 0 1
  have he0 : ‖e0‖ = 1 := by
    rw [← coe_nnnorm, show ‖e0‖₊ = 1 by simp [e0, Pi.nnnorm_single]]; rfl
  -- componentwise estimate
  have hcomp : ∀ k : Fin m, ∫⁻ y, ‖φ y k‖ₑ ^ p ≤
      ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖lineDeriv ℝ (fun z => φ z k) y e0‖ₑ ^ p := by
    intro k
    have hφk : LipschitzWith K fun z => φ z k :=
      LipschitzWith.of_dist_le_mul fun a b => (dist_le_pi_dist (φ a) (φ b) k).trans
        (hφ.dist_le_mul a b)
    have hmeas1 : Measurable fun y => ‖φ y k‖ₑ ^ p :=
      (hφk.continuous.enorm.measurable).pow_const p
    have hmeas2 : Measurable fun y => ‖lineDeriv ℝ (fun z => φ z k) y e0‖ₑ ^ p :=
      ((measurable_lineDeriv hφk.continuous).enorm).pow_const p
    rw [lintegral_split0 _ hmeas1, lintegral_split0 _ hmeas2, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun x' => ?_
    set g : ℝ → ℝ := fun t => φ (split0.symm (t, x')) k
    have hg : LipschitzWith (K * ‖e0‖₊) g := hφk.comp (lipschitzWith_split0_symm x')
    have hg0 : ∀ t ∉ Ioo (x 0 - ρ / 2) (x 0 + ρ / 2), g t = 0 := by
      intro t ht
      have : split0.symm (t, x') ∉ cube ρ x := fun h => ht (by
        have := h 0 (mem_univ 0); rwa [split0_symm_apply_zero] at this)
      change φ (split0.symm (t, x')) k = 0
      rw [h0 _ this]; rfl
    have hderiv : ∀ t, deriv g t = lineDeriv ℝ (fun z => φ z k) (split0.symm (t, x')) e0 := by
      intro t
      have h := deriv_comp_add_const (f := g) (a := t) (x := 0)
      rw [zero_add] at h
      rw [lineDeriv, ← h]
      congr 1; funext s
      change φ (split0.symm (s + t, x')) k = _
      rw [add_comm s t, split0_symm_add]
    have := poincare_1d hg hg0 hp
    simp only [hderiv, show x 0 + ρ / 2 - (x 0 - ρ / 2) = ρ by ring] at this
    exact this
  -- a.e. identification of the line derivative
  have hline : ∀ k : Fin m, ∀ᵐ y, ‖lineDeriv ℝ (fun z => φ z k) y e0‖ₑ ^ p ≤
      ‖fderiv ℝ φ y‖ₑ ^ p := by
    intro k
    filter_upwards [hφ.ae_differentiableAt (μ := volume)] with y hy
    have hd : HasFDerivAt (fun z => φ z k)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).comp (fderiv ℝ φ y)) y :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).hasFDerivAt.comp y
        hy.hasFDerivAt
    rw [(hd.hasLineDerivAt e0).lineDeriv]
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).comp
          (fderiv ℝ φ y)) e0‖ = ‖fderiv ℝ φ y e0 k‖ := rfl
      _ ≤ ‖fderiv ℝ φ y e0‖ := norm_le_pi_norm _ k
      _ ≤ ‖fderiv ℝ φ y‖ * ‖e0‖ := (fderiv ℝ φ y).le_opNorm e0
      _ = ‖fderiv ℝ φ y‖ := by rw [he0, mul_one]
  calc ∫⁻ y, ‖φ y‖ₑ ^ p ≤ ∫⁻ y, ∑ k, ‖φ y k‖ₑ ^ p :=
        lintegral_mono fun y => enorm_rpow_le_sum hp0
    _ = ∑ k, ∫⁻ y, ‖φ y k‖ₑ ^ p := lintegral_finsetSum' _ fun k _ =>
        ((LipschitzWith.of_dist_le_mul fun a b => (dist_le_pi_dist (φ a) (φ b) k).trans
          (hφ.dist_le_mul a b) : LipschitzWith K fun z => φ z k).continuous.enorm.measurable
            |>.pow_const p).aemeasurable
    _ ≤ ∑ k : Fin m, ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖fderiv ℝ φ y‖ₑ ^ p :=
        Finset.sum_le_sum fun k _ =>
          (hcomp k).trans (mul_le_mul_right (lintegral_mono_ae (hline k)) _)
    _ = m * ENNReal.ofReal ρ ^ p * ∫⁻ y, ‖fderiv ℝ φ y‖ₑ ^ p := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end Homogenization
