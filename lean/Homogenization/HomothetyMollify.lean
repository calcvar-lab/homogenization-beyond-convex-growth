import Homogenization.LpContinuity

/-!
# Homotheties and local mollification of functions with a weak gradient

Step 2 towards proving the cited `CitedAffineApprox` ([oah-jpm11, Proposition 3.15]); that
statement is not proved here.
* `HasWeakGrad.comp_add_set`, `HasWeakGrad.comp_smul_set`, `HasWeakGrad.const_smul`,
  `HasWeakGrad.comp_homothety`: weak gradients on an open set are transported by translations,
  dilations and the homothety `x ↦ x₀ + s(x - x₀)`;
* `HasWeakGrad.indicator`: extension by `0` off `U` keeps the weak-gradient identity on `U`;
* `fderiv_convolution_eq_convolution_grad_local`: `∇(η ⋆ φ)(z) = (η ⋆ ∇φ)(z)` when the closed
  ball of radius `rOut` around `z` lies in the open set where `φ` has weak gradient `∇φ`;
* `setLIntegral_comp_homothety`: `∫_{A⁻¹Ω} F(Az) dz = s^{-N} ∫_Ω F`;
* `lintegral_homothety_ruusc_le`: for `L` ru-usc, `Ω` measurable and star-shaped with respect to
  `x₀`, and `L(∇u)` finite a.e. on `Ω`,
  `∫_Ω L(s ∇u(x₀ + s(z - x₀))) dz ≤ (1 + η) s^{-N} ∫_Ω L(∇u) + η c |Ω|` for `0 < s < 1` close
  to `1`.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution

namespace Homogenization

variable {N m : ℕ}

/-- Translation of a weak-gradient identity on an open set. -/
theorem HasWeakGrad.comp_add_set {U : Set (Sp N)} {f : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hfg : HasWeakGrad U f g) (a : Sp N) :
    HasWeakGrad ((· + a) ⁻¹' U) (fun y => f (y + a)) (fun y => g (y + a)) := by
  intro ψ hψ hcs hsupp v
  let ψ' : Sp N → ℝ := fun x => ψ (x + -a)
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) ψ' := hψ.comp (contDiff_id.add contDiff_const)
  have hcs' : HasCompactSupport ψ' := hcs.comp_homeomorph (Homeomorph.addRight (-a))
  have hsupp' : tsupport ψ' ⊆ U := by
    intro x hx
    have : x + -a ∈ tsupport ψ := by
      have h := tsupport_comp_eq_preimage ψ (Homeomorph.addRight (-a))
      have hx' : x ∈ tsupport (ψ ∘ Homeomorph.addRight (-a)) := hx
      rw [h] at hx'
      exact hx'
    have := hsupp this
    simpa using this
  have hweak := hfg ψ' hψ' hcs' hsupp' v
  have hleft : (∫ y, fderiv ℝ ψ y v • f (y + a)) =
      ∫ x, fderiv ℝ ψ (x + -a) v • f x := by
    let q : Sp N → Tgt m := fun x => fderiv ℝ ψ (x + -a) v • f x
    have h := (measurePreserving_add_right (volume : Measure (Sp N)) a).integral_comp
      (MeasurableEquiv.addRight a).measurableEmbedding q
    simpa [q, add_assoc, add_comm] using h
  have hright : (∫ y, ψ y • g (y + a) v) = ∫ x, ψ (x + -a) • g x v := by
    let q : Sp N → Tgt m := fun x => ψ (x + -a) • g x v
    have h := (measurePreserving_add_right (volume : Measure (Sp N)) a).integral_comp
      (MeasurableEquiv.addRight a).measurableEmbedding q
    simpa [q, add_assoc, add_comm] using h
  have hweak' : (∫ x, fderiv ℝ ψ (x + -a) v • f x) = -∫ x, ψ (x + -a) • g x v := by
    simpa [ψ', fderiv_comp_add_right] using hweak
  rw [hleft, hweak', ← hright]

/-- Dilation of a weak-gradient identity on an open set. -/
theorem HasWeakGrad.comp_smul_set {U : Set (Sp N)} {f : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hfg : HasWeakGrad U f g) {ε : ℝ} (hε : ε ≠ 0) :
    HasWeakGrad ((ε • ·) ⁻¹' U) (fun z => ε⁻¹ • f (ε • z)) (fun z => g (ε • z)) := by
  intro ψ hψ hcs hsupp v
  let ψ' : Sp N → ℝ := fun x => ψ (ε⁻¹ • x)
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) ψ' := by
    exact hψ.comp (contDiff_id.const_smul ε⁻¹)
  have hcs' : HasCompactSupport ψ' := hcs.comp_smul (c := ε⁻¹) (inv_ne_zero hε)
  have hsupp' : tsupport ψ' ⊆ U := by
    intro x hx
    have h := tsupport_comp_eq_preimage ψ (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε))
    have hx' : x ∈ tsupport (ψ ∘ Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε)) := hx
    rw [h] at hx'
    have := hsupp hx'
    simpa [smul_inv_smul₀ hε] using this
  have hweak := hfg ψ' hψ' hcs' hsupp' v
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

/-- Scalar multiples of a weak-gradient identity. -/
theorem HasWeakGrad.const_smul {U : Set (Sp N)} {f : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hfg : HasWeakGrad U f g) (c : ℝ) : HasWeakGrad U (fun y => c • f y) (fun y => c • g y) := by
  intro ψ hψ hcs hsupp v
  have h := hfg ψ hψ hcs hsupp v
  simp only [smul_comm (fderiv ℝ ψ _ v) c, smul_apply, smul_comm (ψ _) c]
  rw [integral_smul, integral_smul, h, smul_neg]

/-- Weak gradients are transported by the homothety `x ↦ x₀ + s (x - x₀)`, `s ≠ 0`. -/
theorem HasWeakGrad.comp_homothety {U : Set (Sp N)} {f : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hfg : HasWeakGrad U f g) {s : ℝ} (hs : s ≠ 0) (x₀ : Sp N) :
    HasWeakGrad ((fun x => x₀ + s • (x - x₀)) ⁻¹' U) (fun x => f (x₀ + s • (x - x₀)))
      (fun x => s • g (x₀ + s • (x - x₀))) := by
  have h := ((hfg.comp_add_set x₀).comp_smul_set hs).comp_add_set (-x₀) |>.const_smul s
  have e1 : (fun x : Sp N => x₀ + s • (x - x₀)) ⁻¹' U =
      (· + -x₀) ⁻¹' ((s • ·) ⁻¹' ((· + x₀) ⁻¹' U)) := by
    ext x; simp [sub_eq_add_neg, add_comm]
  have e2 : (fun x : Sp N => f (x₀ + s • (x - x₀))) =
      fun x => s • (s⁻¹ • f (s • (x + -x₀) + x₀)) := by
    funext x; rw [smul_smul, mul_inv_cancel₀ hs, one_smul, sub_eq_add_neg, add_comm x₀]
  have e3 : (fun x : Sp N => s • g (x₀ + s • (x - x₀))) =
      fun x => s • g (s • (x + -x₀) + x₀) := by
    funext x; rw [sub_eq_add_neg, add_comm x₀]
  rw [e1, e2, e3]
  exact h

/-- Local form of `HasWeakGrad.bump_test_identity`: the weak-gradient identity on `U` tested
against the translated bump, when `closedBall x rOut ⊆ U`. -/
theorem HasWeakGrad.bump_test_identity_local {U : Set (Sp N)} {φ : Sp N → Tgt m}
    {g : Sp N → Mat m N} (hweak : HasWeakGrad U φ g)
    (η : ContDiffBump (0 : Sp N)) {x : Sp N} (hball : closedBall x η.rOut ⊆ U) (v : Sp N) :
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
  have hts : tsupport ψ ⊆ U := by
    refine (closure_minimal (fun y hy => ?_) isClosed_closedBall).trans hball
    have hys : k (x - y) ≠ 0 := by simpa only [ψ, Function.mem_support] using hy
    have hball' : x - y ∈ Metric.ball (0 : Sp N) η.rOut := by
      have : x - y ∈ Function.support k := by simpa only [Function.mem_support] using hys
      simpa [k, η.support_normed_eq] using this
    rw [Metric.mem_closedBall, dist_eq_norm_sub']
    simpa [norm_sub_rev] using (Metric.mem_ball.mp hball').le
  have h := hweak ψ hψ hψcs hts v
  rw [show (fun y => fderiv ℝ ψ y v • φ y) =
      fun y => -(fderiv ℝ k (x - y) v • φ y) by
        funext y
        rw [htest y, neg_smul]] at h
  rw [integral_neg] at h
  exact neg_injective h

/-- Local form of `W1p0.fderiv_convolution_eq_convolution_grad`: if `φ` has weak gradient `g` on
`U` and `closedBall z rOut ⊆ U`, then `∇(η ⋆ φ)(z) = (η ⋆ g)(z)`. -/
theorem fderiv_convolution_eq_convolution_grad_local {U : Set (Sp N)}
    {φg : (Sp N → Tgt m) × (Sp N → Mat m N)} (hφloc : LocallyIntegrable φg.1 volume)
    (hgLoc : LocallyIntegrable φg.2 volume) (hweak : HasWeakGrad U φg.1 φg.2)
    (η : ContDiffBump (0 : Sp N)) {z : Sp N} (hball : closedBall z η.rOut ⊆ U) :
    fderiv ℝ (((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.1)) z =
      ((η.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φg.2) z := by
  let k : Sp N → ℝ := η.normed volume
  have hkcd : ContDiff ℝ (1 : ℕ∞) k := by
    exact (η.contDiff_normed (μ := volume) (n := ⊤)).of_le
      (show (↑(1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)
  have hkcs : HasCompactSupport k := η.hasCompactSupport_normed
  have hderiv := hkcs.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hkcd hφloc z
  have hderiv' := hderiv.fderiv
  ext v i
  have htest := HasWeakGrad.bump_test_identity_local hweak η hball v
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

/-- Extending by `0` off `U` does not change a weak-gradient identity on `U`. -/
theorem HasWeakGrad.indicator {U : Set (Sp N)} {f : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hfg : HasWeakGrad U f g) : HasWeakGrad U (U.indicator f) (U.indicator g) := by
  intro ψ hψ hcs hsupp v
  have h := hfg ψ hψ hcs hsupp v
  have e1 : (fun y => fderiv ℝ ψ y v • U.indicator f y) = fun y => fderiv ℝ ψ y v • f y := by
    funext y
    by_cases hy : y ∈ U
    · rw [indicator_of_mem hy]
    · have hyt : y ∉ tsupport ψ := fun h => hy (hsupp h)
      rw [(HasFDerivAt.of_notMem_tsupport ℝ hyt).fderiv]
      simp
  have e2 : (fun y => ψ y • U.indicator g y v) = fun y => ψ y • g y v := by
    funext y
    by_cases hy : y ∈ U
    · rw [indicator_of_mem hy]
    · have hyt : y ∉ tsupport ψ := fun h => hy (hsupp h)
      rw [image_eq_zero_of_notMem_tsupport hyt]
      simp
  rw [e1, e2, h]

/-- The homothety `x ↦ x₀ + s (x - x₀)`. -/
def homothety (x₀ : Sp N) (s : ℝ) (x : Sp N) : Sp N := x₀ + s • (x - x₀)

/-- The homothety as an affine map. -/
theorem homothety_eq (x₀ : Sp N) (s : ℝ) (x : Sp N) :
    homothety x₀ s x = s • x + (1 - s) • x₀ := by
  simp only [homothety, smul_sub, sub_smul, one_smul]; abel

/-- Change of variables for the homothety: `∫_{A⁻¹Ω} F(A z) dz = s^{-N} ∫_Ω F`. -/
theorem setLIntegral_comp_homothety (F : Sp N → ℝ≥0∞) {s : ℝ} (hs : 0 < s) (x₀ : Sp N)
    {Ω : Set (Sp N)} (hΩ : MeasurableSet Ω) :
    ∫⁻ z in homothety x₀ s ⁻¹' Ω, F (homothety x₀ s z) =
      ENNReal.ofReal |(s ^ N)⁻¹| * ∫⁻ y in Ω, F y := by
  have hm : Measurable (homothety (N := N) x₀ s) := by
    unfold homothety; fun_prop
  simp_rw [homothety_eq]
  have hpre : homothety x₀ s ⁻¹' Ω = (fun z : Sp N => s • z + (1 - s) • x₀) ⁻¹' Ω := by
    ext z; simp [homothety_eq]
  rw [hpre, setLIntegral_comp_smul_add F hs _ (by
    exact (show Measurable fun z : Sp N => s • z + (1 - s) • x₀ by fun_prop) hΩ),
    ← lintegral_indicator hΩ]
  have hset : {y : Sp N | s⁻¹ • (y + -((1 - s) • x₀)) ∈
      (fun z : Sp N => s • z + (1 - s) • x₀) ⁻¹' Ω} = Ω := by
    ext y
    change s • (s⁻¹ • (y + -((1 - s) • x₀))) + (1 - s) • x₀ ∈ Ω ↔ y ∈ Ω
    rw [smul_inv_smul₀ hs.ne', neg_add_cancel_right]
  rw [hset]

/-- The homothety is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_homothety (x₀ : Sp N) {s : ℝ} (hs : s ≠ 0) :
    Measure.QuasiMeasurePreserving (homothety x₀ s) volume volume := by
  have h1 := Measure.quasiMeasurePreserving_smul (volume : Measure (Sp N)) hs
  have h2 := (measurePreserving_add_right (volume : Measure (Sp N))
    ((1 - s) • x₀)).quasiMeasurePreserving
  have e : homothety x₀ s = (fun z => z + (1 - s) • x₀) ∘ (fun z => s • z) := by
    funext z; simp [homothety_eq]
  rw [e]
  exact h2.comp h1

/-- **Energy of the dilated gradient.** If `Ω` is star-shaped with respect to `x₀` and `L` is
ru-usc with constant `c`, then for `s < 1` close to `1`,
`∫_Ω L(s ∇u(x₀ + s(z - x₀))) dz ≤ (1 + η) s^{-N} ∫_Ω L(∇u) + η c |Ω|`. -/
theorem lintegral_homothety_ruusc_le {Ω : Set (Sp N)} (hΩ : MeasurableSet Ω) {x₀ : Sp N}
    (hstar : ∀ s : ℝ, 0 < s → s < 1 → ∀ z ∈ Ω, homothety x₀ s z ∈ Ω)
    {L : Mat m N → ℝ≥0∞} {c : ℝ≥0} (hL : RUUSCWith c (fun _ : Sp N => L))
    {g : Sp N → Mat m N} (hfin : ∀ᵐ y ∂volume.restrict Ω, L (g y) < ⊤) {η : ℝ≥0}
    (hη : 0 < η) :
    ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s →
      ∫⁻ z in Ω, L (s • g (homothety x₀ s z)) ≤
        (1 + η) * (ENNReal.ofReal |(s ^ N)⁻¹| * ∫⁻ y in Ω, L (g y)) + η * c * volume Ω := by
  filter_upwards [hL η hη, self_mem_nhdsWithin] with s hs (hs1 : s < 1) hs0
  have hfin' : ∀ᵐ y ∂volume, y ∈ Ω → L (g y) < ⊤ := (ae_restrict_iff' hΩ).1 hfin
  have hfinA : ∀ᵐ z ∂volume, homothety x₀ s z ∈ Ω → L (g (homothety x₀ s z)) < ⊤ :=
    (quasiMeasurePreserving_homothety x₀ hs0.ne').tendsto_ae.eventually hfin'
  have hpt : ∀ᵐ z ∂volume.restrict Ω, L (s • g (homothety x₀ s z)) ≤
      (1 + η) * L (g (homothety x₀ s z)) + η * c := by
    filter_upwards [ae_restrict_of_ae hfinA, ae_restrict_mem hΩ] with z hz hzΩ
    have hA := hstar s hs0 hs1 z hzΩ
    calc L (s • g (homothety x₀ s z))
        ≤ L (g (homothety x₀ s z)) + η * (c + L (g (homothety x₀ s z))) := hs z _ (hz hA)
      _ = (1 + η) * L (g (homothety x₀ s z)) + η * c := by ring
  have hsub : Ω ⊆ homothety x₀ s ⁻¹' Ω := fun z hz => hstar s hs0 hs1 z hz
  calc ∫⁻ z in Ω, L (s • g (homothety x₀ s z))
      ≤ ∫⁻ z in Ω, ((1 + η) * L (g (homothety x₀ s z)) + η * c) := lintegral_mono_ae hpt
    _ = (1 + η) * (∫⁻ z in Ω, L (g (homothety x₀ s z))) + η * c * volume Ω := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
          setLIntegral_const]
    _ ≤ (1 + η) * (∫⁻ z in homothety x₀ s ⁻¹' Ω, L (g (homothety x₀ s z))) +
          η * c * volume Ω := by
        gcongr
    _ = _ := by rw [setLIntegral_comp_homothety (fun y => L (g y)) hs0 x₀ hΩ]

end Homogenization
