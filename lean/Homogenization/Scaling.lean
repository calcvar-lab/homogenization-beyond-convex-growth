import Homogenization.Step3

/-!
# Rescaling the affine Dirichlet problem

The change of variables `y = εz`, `φ(y) = ε φ̃(y/ε)` used in Step 4 (b)–(c) of the proof of
Theorem `main-Ggrowth`:
`inf_{φ ∈ Aff₀(B)} ∫_B W(y/ε, ξ + ∇φ) dy = εᴺ 𝒴 W(ε⁻¹B, ξ)`.

The second part does the same for the Sobolev cell problem `𝒴_p` (Step 3 of the proof of the
lower bound in [oah-jpm-zorgati14]): `W1p0.rescale` dilates a competitor (`ε⁻¹ u(ε·)`, whose
weak gradient is `∇u(ε·)`), `setLIntegral_rescale_energy` changes variables in the energy, and
`Ytp_rescale_le` combines them:
`εᴺ 𝒴_p W(Q_{ρ/ε}(x₀/ε), ξ) ≤ ∫_{Q_ρ(x₀)} W(x/ε, ξ + ∇u) dx` for `u ∈ W^{1,p}_0(Q_ρ(x₀))`.
The rescaled cubes are those of `Ytp_tendsto_Hp`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

theorem finrank_Sp : Module.finrank ℝ (Sp N) = N := Module.finrank_fin_fun ℝ

/-- Change of variables `y = R z` in a lower Lebesgue integral. -/
theorem setLIntegral_comp_smul {R : ℝ} (hR : R ≠ 0) {B : Set (Sp N)} (hB : MeasurableSet B)
    (F : Sp N → ℝ≥0∞) :
    ∫⁻ z in (R • ·) ⁻¹' B, F (R • z) = ENNReal.ofReal |(R ^ N)⁻¹| * ∫⁻ y in B, F y := by
  have hpre : MeasurableSet ((R • ·) ⁻¹' B : Set (Sp N)) :=
    (measurable_const_smul R) hB
  rw [← lintegral_indicator hpre, ← lintegral_indicator hB]
  have h1 : ((R • ·) ⁻¹' B).indicator (fun z => F (R • z)) =
      fun z : Sp N => B.indicator F (MeasurableEquiv.smul₀ R hR z) := by
    funext z; rfl
  rw [h1, ← lintegral_map_equiv]
  change ∫⁻ y, B.indicator F y ∂Measure.map (fun x : Sp N => R • x) volume = _
  rw [Measure.map_addHaar_smul _ hR, lintegral_smul_measure, finrank_Sp, smul_eq_mul]

/-- `Aff₀` is invariant under the rescaling `φ ↦ a⁻¹ φ(a ·)`. -/
theorem Aff0.rescale {B : Set (Sp N)} {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 B) {a : ℝ}
    (ha : a ≠ 0) : (fun z => a⁻¹ • φ (a • z)) ∈ Aff0 ((a • ·) ⁻¹' B) := by
  obtain ⟨K, n, V, ξ, hK, h0, hVo, hVU, hVd, hVf, hVc, hφV⟩ := Aff0.data hφ
  have hLip : LipschitzWith (‖a⁻¹‖₊ * (K * ‖a‖₊)) fun z => a⁻¹ • φ (a • z) :=
    (lipschitzWith_smul a⁻¹).comp (hK.comp (lipschitzWith_smul a))
  let h : Sp N ≃ₜ Sp N := Homeomorph.smulOfNeZero a ha
  have hnull : ∀ S : Set (Sp N), volume S = 0 → volume ((a • ·) ⁻¹' S) = 0 := fun S hS => by
    rw [Measure.addHaar_preimage_smul _ ha, hS, mul_zero]
  refine ⟨⟨_, hLip⟩, fun z hz => by simp [h0 _ hz], ⟨_, hLip.lipschitzOnWith⟩, n,
    fun i => (a • ·) ⁻¹' V i, ξ, fun i => (hVo i).preimage (continuous_const_smul a),
    fun i => preimage_mono (hVU i), fun i j hij => (hVd hij).preimage _, fun i => ?_, ?_,
    fun i z hz => ?_⟩
  · have hfr : (a • ·) ⁻¹' frontier (V i) = frontier ((a • ·) ⁻¹' V i) :=
      h.preimage_frontier (V i)
    rw [← hfr, ← preimage_inter]; exact hnull _ (hVf i)
  · rw [← preimage_iUnion, ← preimage_sdiff]; exact hnull _ hVc
  · have h1 : HasFDerivAt (fun z : Sp N => a • z) (a • ContinuousLinearMap.id ℝ (Sp N)) z :=
      (hasFDerivAt_id z).const_smul a
    have h2 := ((hφV i _ hz).comp z h1).const_smul a⁻¹
    have heq : a⁻¹ • (ξ i).comp (a • ContinuousLinearMap.id ℝ (Sp N)) = ξ i := by
      ext v k
      simp [smul_smul, inv_mul_cancel₀ ha]
    exact h2.congr_fderiv heq

theorem fderiv_rescale (φ : Sp N → Tgt m) {a : ℝ} (ha : a ≠ 0) (z : Sp N) :
    fderiv ℝ (fun z => a⁻¹ • φ (a • z)) z = fderiv ℝ φ (a • z) := by
  rw [show (fun z => a⁻¹ • φ (a • z)) = a⁻¹ • (φ <| a • ·) from rfl, fderiv_const_smul_field,
    Pi.smul_apply, fderiv_comp_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- **Rescaling of the affine Dirichlet problem.** -/
theorem iInf_rescale (L : Sp N → Mat m N → ℝ≥0∞) {ε : ℝ} (hε : 0 < ε) {B : Set (Sp N)}
    (hB : MeasurableSet B) (ξ : Mat m N) :
    (⨅ φ ∈ (Aff0 B : Set (Sp N → Tgt m)), ∫⁻ y in B, L (ε⁻¹ • y) (ξ + fderiv ℝ φ y)) =
      ENNReal.ofReal (ε ^ N) * Yt L ((ε • ·) ⁻¹' B) ξ := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hc0 : ENNReal.ofReal (ε ^ N) ≠ 0 := by simp [hε, pow_pos]
  have hct : ENNReal.ofReal (ε ^ N) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpre : MeasurableSet ((ε • ·) ⁻¹' B : Set (Sp N)) := (measurable_const_smul ε) hB
  have hcancel : ENNReal.ofReal (ε ^ N) * ENNReal.ofReal |(ε ^ N)⁻¹| = 1 := by
    rw [abs_of_pos (inv_pos.2 (pow_pos hε N)), ← ENNReal.ofReal_mul (pow_pos hε N).le,
      mul_inv_cancel₀ (pow_pos hε N).ne', ENNReal.ofReal_one]
  simp only [Yt]
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_antisymm (le_iInf fun ψ => ?_) (le_iInf fun φ => ?_)
  · -- `φ(y) = ε ψ(y/ε)`
    rw [ENNReal.mul_iInf_of_ne hc0 hct]
    refine le_iInf fun hψ => ?_
    have hφ := Aff0.rescale hψ (inv_ne_zero hε0)
    rw [← preimage_comp, show ((ε • ·) ∘ (ε⁻¹ • ·) : Sp N → Sp N) = id from
      funext fun y => smul_inv_smul₀ hε0 y, preimage_id] at hφ
    refine (iInf₂_le _ hφ).trans (le_of_eq ?_)
    simp_rw [fderiv_rescale ψ (inv_ne_zero hε0)]
    have := setLIntegral_comp_smul (inv_ne_zero hε0) hpre (fun z => L z (ξ + fderiv ℝ ψ z))
    rw [← preimage_comp, show ((ε • ·) ∘ (ε⁻¹ • ·) : Sp N → Sp N) = id from
      funext fun y => smul_inv_smul₀ hε0 y, preimage_id] at this
    rw [this, inv_pow, inv_inv, abs_of_pos (pow_pos hε N)]
  · -- `ψ(z) = ε⁻¹ φ(εz)`
    refine le_iInf fun hφ => ?_
    have hψ := Aff0.rescale hφ hε0
    refine (iInf_le _ (fun z => ε⁻¹ • φ (ε • z))).trans ?_
    refine (mul_le_mul_right (iInf_le _ hψ) _).trans (le_of_eq ?_)
    simp_rw [fderiv_rescale φ hε0]
    have := setLIntegral_comp_smul hε0 hB (fun y => L (ε⁻¹ • y) (ξ + fderiv ℝ φ y))
    simp only [inv_smul_smul₀ hε0] at this
    rw [this, ← mul_assoc, hcancel, one_mul]

theorem preimage_smul_cube {ε : ℝ} (hε : 0 < ε) (ρ : ℝ) (x : Sp N) :
    (ε • ·) ⁻¹' cube ρ x = cube (ρ / ε) (ε⁻¹ • x) := by
  ext z
  simp only [cube, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ioo, Pi.smul_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  have h1 : ε⁻¹ * x i - ρ / ε / 2 = (x i - ρ / 2) / ε := by field_simp
  have h2 : ε⁻¹ * x i + ρ / ε / 2 = (x i + ρ / 2) / ε := by field_simp
  rw [h1, h2, div_lt_iff₀ hε, lt_div_iff₀ hε, mul_comm (z i) ε]

/-! The following lemmas concern the Sobolev competitor class `W1p0`.  In particular, they do
not use the affine approximation class `Aff0`: its scaling result above is a separate fact. -/

/-- A global weak gradient is transported by a dilation.  The scalar in the function is chosen
so that the weak gradient itself is simply composed with the dilation. -/
theorem HasWeakGrad.comp_smul {f : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hfg : HasWeakGrad univ f g) {ε : ℝ} (hε : ε ≠ 0) :
    HasWeakGrad univ (fun z => ε⁻¹ • f (ε • z)) (fun z => g (ε • z)) := by
  intro ψ hψ hcs _ v
  let ψ' : Sp N → ℝ := fun x => ψ (ε⁻¹ • x)
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) ψ' := by
    exact hψ.comp (contDiff_id.const_smul ε⁻¹)
  have hcs' : HasCompactSupport ψ' := hcs.comp_smul (c := ε⁻¹) (inv_ne_zero hε)
  have hweak := hfg ψ' hψ' hcs' (subset_univ _) v
  let c : ℝ := |(ε ^ N)⁻¹|
  have hc : c ≠ 0 := by
    simp [c, hε]
  have hleft :
      (∫ z, fderiv ℝ ψ z v • (ε⁻¹ • f (ε • z))) =
        c • ∫ x, fderiv ℝ ψ' x v • f x := by
    have hchange := MeasureTheory.Measure.integral_comp_smul
      (volume : Measure (Sp N)) (fun x => fderiv ℝ ψ' x v • f x) ε
    rw [finrank_Sp] at hchange
    have heq : (fun z : Sp N =>
        (fun x => fderiv ℝ ψ' x v • f x) (ε • z)) =
        fun z => fderiv ℝ ψ z v • (ε⁻¹ • f (ε • z)) := by
      funext z
      simp only [ψ', fderiv_comp_smul]
      rw [inv_smul_smul₀ hε z]
      change (ε⁻¹ * fderiv ℝ ψ z v) • f (ε • z) =
        fderiv ℝ ψ z v • (ε⁻¹ • f (ε • z))
      rw [smul_smul]
      congr 1
      ring
    rw [← heq, hchange]
  have hright :
      (∫ z, ψ z • g (ε • z) v) = c • ∫ x, ψ' x • g x v := by
    have hchange := MeasureTheory.Measure.integral_comp_smul
      (volume : Measure (Sp N)) (fun x => ψ' x • g x v) ε
    rw [finrank_Sp] at hchange
    have heq : (fun z : Sp N => (fun x => ψ' x • g x v) (ε • z)) =
        fun z => ψ z • g (ε • z) v := by
      funext z
      change ψ (ε⁻¹ • (ε • z)) • g (ε • z) v = ψ z • g (ε • z) v
      rw [inv_smul_smul₀ hε]
    rw [← heq, hchange]
  have hweak' :
      (∫ x, fderiv ℝ ψ' x v • f x) = -∫ x, ψ' x • g x v := by
    simpa [ψ'] using hweak
  have hscaled := congrArg (fun z : Tgt m => c • z) hweak'
  have hcancel := congrArg (fun z : Tgt m => c⁻¹ • z) hscaled
  have hcancel' :
      (∫ x, fderiv ℝ ψ' x v • f x) = -∫ x, ψ' x • g x v := by
    simpa [smul_smul, hc] using hcancel
  rw [hleft, hright]
  calc
    c • ∫ x, fderiv ℝ ψ' x v • f x = c • (-∫ x, ψ' x • g x v) :=
      congrArg (fun z : Tgt m => c • z) hcancel'
    _ = -(c • ∫ x, ψ' x • g x v) := by rw [smul_neg]

/-- Dilate a zero-extended Sobolev competitor.  The definition of `W1p0` is used directly:
vanishing off the inverse image, both `MemLp` conditions under the scaled Haar measure, and the
transport of the distributional weak-gradient identity. -/
theorem W1p0.rescale {p : ℝ≥0∞} {U : Set (Sp N)}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 p U)
    {ε : ℝ} (hε : ε ≠ 0) :
    ((fun z => ε⁻¹ • u.1 (ε • z)), (fun z => u.2 (ε • z))) ∈
      W1p0 p ((ε • ·) ⁻¹' U) := by
  rcases hu with ⟨hu0, huLp, huGradLp, huweak⟩
  have hmap : Measure.map (fun z : Sp N => ε • z) volume =
      ENNReal.ofReal |(ε ^ N)⁻¹| • volume := by
    rw [Measure.map_addHaar_smul _ hε, finrank_Sp]
  have hcTop : ENNReal.ofReal |(ε ^ N)⁻¹| ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfLp : MemLp (fun z => u.1 (ε • z)) p volume := by
    have h := huLp.smul_measure hcTop
    rw [← hmap] at h
    exact h.comp_of_map (measurable_const_smul ε).aemeasurable
  have hgLp : MemLp (fun z => u.2 (ε • z)) p volume := by
    have h := huGradLp.smul_measure hcTop
    rw [← hmap] at h
    exact h.comp_of_map (measurable_const_smul ε).aemeasurable
  refine ⟨?_, ?_, ?_, huweak.comp_smul hε⟩
  · intro z hz
    change ε⁻¹ • u.1 (ε • z) = 0
    rw [hu0 (ε • z) hz, smul_zero]
  · exact hfLp.const_smul ε⁻¹
  · exact hgLp

/-- The energy change of variables for a composed gradient field. The cube centered at `x₀`
becomes a cube centered at `ε⁻¹ • x₀`; no translation of the center is suppressed. -/
theorem setLIntegral_rescale_energy (L : Sp N → Mat m N → ℝ≥0∞) {ε ρ : ℝ}
    (hε : 0 < ε) (x₀ : Sp N) (ξ : Mat m N) (g : Sp N → Mat m N) :
    ∫⁻ x in cube ρ x₀, L (ε⁻¹ • x) (ξ + g x) =
      ENNReal.ofReal (ε ^ N) *
        ∫⁻ y in cube (ρ / ε) (ε⁻¹ • x₀), L y (ξ + g (ε • y)) := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hcube : (ε • ·) ⁻¹' cube ρ x₀ = cube (ρ / ε) (ε⁻¹ • x₀) :=
    preimage_smul_cube hε ρ x₀
  have hmeas : MeasurableSet (cube ρ x₀) := (isOpen_cube ρ x₀).measurableSet
  have hchange := setLIntegral_comp_smul hε0 hmeas
    (fun x => L (ε⁻¹ • x) (ξ + g x))
  have hfactor : ENNReal.ofReal (ε ^ N) * ENNReal.ofReal |(ε ^ N)⁻¹| = 1 := by
    rw [abs_of_pos (inv_pos.2 (pow_pos hε N)), ← ENNReal.ofReal_mul (pow_pos hε N).le,
      mul_inv_cancel₀ (pow_pos hε N).ne', ENNReal.ofReal_one]
  rw [hcube] at hchange
  have hchange' :
      ∫⁻ y in cube (ρ / ε) (ε⁻¹ • x₀), L y (ξ + g (ε • y)) =
        ENNReal.ofReal |(ε ^ N)⁻¹| * ∫⁻ x in cube ρ x₀, L (ε⁻¹ • x) (ξ + g x) := by
    simpa only [inv_smul_smul₀ hε0] using hchange
  calc
    ∫⁻ x in cube ρ x₀, L (ε⁻¹ • x) (ξ + g x) =
        (ENNReal.ofReal (ε ^ N) * ENNReal.ofReal |(ε ^ N)⁻¹|) *
          ∫⁻ x in cube ρ x₀, L (ε⁻¹ • x) (ξ + g x) := by rw [hfactor, one_mul]
    _ = ENNReal.ofReal (ε ^ N) *
          (ENNReal.ofReal |(ε ^ N)⁻¹| *
            ∫⁻ x in cube ρ x₀, L (ε⁻¹ • x) (ξ + g x)) := by rw [mul_assoc]
    _ = ENNReal.ofReal (ε ^ N) *
          ∫⁻ y in cube (ρ / ε) (ε⁻¹ • x₀), L y (ξ + g (ε • y)) := by
      rw [← hchange']

/-- In the affine lower-bound construction, the rescaled zero-boundary perturbation has gradient
`t ∇v (ε y) - t ∇u(x₀)`. Adding the reference slope `t ∇u(x₀)` in `Ytp` therefore gives exactly
the desired argument `t ∇v (ε y)`. -/
theorem rescaled_affine_cell_argument (ε t : ℝ) (A : Mat m N)
    (gradV : Sp N → Mat m N) (y : Sp N) :
    (t • A) + (t • gradV (ε • y) - t • A) = t • gradV (ε • y) := by
  abel

/-- **Rescaled cell problem.** A zero-boundary competitor on `Q_ρ(x₀)` with the oscillating
integrand `W(x/ε, ·)` bounds from above `εᴺ 𝒴_p W(Q_{ρ/ε}(x₀/ε), ξ)`. -/
theorem Ytp_rescale_le {p : ℝ≥0∞} (L : Sp N → Mat m N → ℝ≥0∞) {ε ρ : ℝ} (hε : 0 < ε)
    (x₀ : Sp N) (ξ : Mat m N) {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 p (cube ρ x₀)) :
    ENNReal.ofReal (ε ^ N) * Ytp p L (cube (ρ / ε) (ε⁻¹ • x₀)) ξ ≤
      ∫⁻ x in cube ρ x₀, L (ε⁻¹ • x) (ξ + u.2 x) := by
  rw [setLIntegral_rescale_energy L hε x₀ ξ u.2]
  gcongr
  have h := W1p0.rescale hu hε.ne'
  rw [preimage_smul_cube hε] at h
  exact iInf₂_le _ h

/-- Change of variables `y = ρ w + x`. -/
theorem setLIntegral_comp_smul_add (g : Sp N → ℝ≥0∞) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N)
    {V : Set (Sp N)} (hV : MeasurableSet V) :
    ∫⁻ w in V, g (ρ • w + x) = ENNReal.ofReal |(ρ ^ N)⁻¹| *
      ∫⁻ y, {y | ρ⁻¹ • (y + -x) ∈ V}.indicator g y := by
  have hρ0 : ρ ≠ 0 := hρ.ne'
  set B : Set (Sp N) := (ρ⁻¹ • ·) ⁻¹' V
  have hB : MeasurableSet B := (measurable_const_smul ρ⁻¹) hV
  have hBV : (ρ • ·) ⁻¹' B = V := by
    ext z; simp [B, inv_smul_smul₀ hρ0]
  have h1 := setLIntegral_comp_smul hρ0 hB (fun z => g (z + x))
  rw [hBV] at h1
  rw [h1]
  congr 1
  have hS : MeasurableSet ((· + -x) ⁻¹' B) := (measurable_add_const _) hB
  have e : {y | ρ⁻¹ • (y + -x) ∈ V} = (· + -x) ⁻¹' B := rfl
  rw [e, lintegral_indicator hS]
  have hmp := measurePreserving_add_right (volume : Measure (Sp N)) x
  have hemb : MeasurableEmbedding (fun y : Sp N => y + x) :=
    (MeasurableEquiv.addRight x).measurableEmbedding
  have h := hmp.setLIntegral_comp_preimage_emb hemb g ((· + -x) ⁻¹' B)
  have e2 : (fun y => y + x) ⁻¹' ((fun y => y + -x) ⁻¹' B) = B := by
    ext z; simp
  rw [e2] at h
  exact h

end Homogenization
