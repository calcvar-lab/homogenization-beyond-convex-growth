import Homogenization.Radial

/-!
# Effective domains and the homogenized integrand (Remark `domhw`, Proposition `lsc-of-HW` of
[oah-jpm-zorgati14])

Throughout, `G : 𝕄 → [0,∞]` is convex (`ConvexENN`) with `0 ∈ int(dom G)`, as in `CitedAHM14`.

* **Jensen's inequality for Sobolev correctors** (`ConvexENN.volume_mul_le_lintegral_W1p0`):
  `|U| G(ξ) ≤ ∫_U G(ξ + ∇φ)` for `φ ∈ W^{1,p}_0(U)` and `ξ ∈ int(dom G)`. This is the
  `W^{1,p}`-quasiconvexity (C3) of the paper, deduced here from convexity. The proof uses a
  subgradient of `G` at `ξ` (`ConvexENN.exists_subgradient`, obtained by Hahn–Banach separation
  of `(ξ, G ξ)` from the open strict epigraph over `int(dom G)`) and `∫_U ∇φ = 0`
  (`W1p0.integral_grad_eq_zero`).
* **Remark `domhw` (i)**: `α G(ξ) ≤ ℋ_p L(ξ)` on `int(dom G)` (`HasGGrowth.le_Hp`) and
  `ℋ_p L ≤ β (1 + G)` everywhere (`HasGGrowth.Hp_le`).
* **Remark `domhw` (ii)**: `t ξ ∈ int(dom G)` for `ξ ∈ cl(dom G)` and `t ∈ [0,1[`
  (`ConvexENN.smul_mem_interior_dom`).
* **Proposition `lsc-of-HW`** (`lsc_of_HW`): `ℋ_p L` and its radial envelope are ru-usc, and
  `ℋ_p L(tξ) → \widehat{ℋ_p L}(ξ)` as `t → 1⁻`, for every `ξ`.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### Convex sets and functions -/

theorem ConvexENN.convex_dom {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) : Convex ℝ (dom G) := by
  intro ξ hξ ζ hζ a b ha hb hab
  let τ : ℝ≥0 := ⟨a, ha⟩
  have hτ1 : τ ≤ 1 := by change a ≤ 1; linarith
  have h := hG ξ ζ τ hτ1
  have hb' : ((1 - τ : ℝ≥0) : ℝ) = b := by
    rw [NNReal.coe_sub hτ1, NNReal.coe_one]; change 1 - a = b; linarith
  rw [hb'] at h
  change G (a • ξ + b • ζ) < ⊤
  refine h.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hξ,
    ENNReal.mul_lt_top ENNReal.coe_lt_top hζ⟩)

/-- **Remark `domhw` (ii)**: `t ξ ∈ int(dom G)` for `ξ ∈ cl(dom G)`, `t ∈ [0,1[`. -/
theorem ConvexENN.smul_mem_interior_dom {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (h0 : (0 : Mat m N) ∈ interior (dom G)) {ξ : Mat m N} (hξ : ξ ∈ closure (dom G))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : t • ξ ∈ interior (dom G) := by
  rcases ht0.eq_or_lt with rfl | ht0
  · simpa using h0
  have hseg := hG.convex_dom.openSegment_interior_closure_subset_interior h0 hξ
  refine hseg ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
  simp

/-- A convex `G` finite on an open neighborhood of zero is bounded by a finite ENNReal constant
on a smaller closed ball. This is the local bound used for the gradient-of-cutoff term. -/
theorem ConvexENN.exists_finite_bound_closedBall_zero {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h0 : (0 : Mat m N) ∈ interior (dom G)) :
    ∃ R : ℝ, ∃ M : ℝ≥0∞, 0 < R ∧ M < ⊤ ∧ ∀ ξ, ‖ξ‖ ≤ R → G ξ ≤ M := by
  have h0nhds : interior (dom G) ∈ 𝓝 (0 : Mat m N) := isOpen_interior.mem_nhds h0
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.1 h0nhds
  let R : ℝ := r / 2
  let K : Set (Mat m N) := closedBall 0 R
  have hRK : 0 < R := by dsimp [R]; linarith
  have hKsub : K ⊆ interior (dom G) := by
    intro ξ hξ
    apply hrball
    rw [Metric.mem_ball, dist_zero_right]
    have hnorm : ‖ξ‖ ≤ R := by
      have := Metric.mem_closedBall.mp hξ
      simpa [dist_zero_right] using this
    dsimp [R] at hnorm ⊢
    exact hnorm.trans_lt (by linarith)
  have hKcompact : IsCompact K := isCompact_closedBall 0 R
  have hKnonempty : K.Nonempty := ⟨0, by simp [K, R, hRK.le]⟩
  have hcont : ContinuousOn G K := hG.continuousOn_interior_dom.mono hKsub
  obtain ⟨ξ₀, hξ₀K, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty hcont
  have hξ₀dom' : ξ₀ ∈ dom G := interior_subset (hKsub hξ₀K)
  change G ξ₀ < ⊤ at hξ₀dom'
  refine ⟨R, G ξ₀, hRK, hξ₀dom', ?_⟩
  intro ξ hξ
  apply hmax
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hξ

/-- The lower extended-growth inequality transfers finiteness of the energy to finiteness of the
convex control function, provided its coefficient is strictly positive. -/
theorem HasGGrowth.G_finite_of_L_finite {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (h : HasGGrowth G α β L) (hα : 0 < α)
    {x : Sp N} {ξ : Mat m N} (hL : L x ξ < ⊤) : G ξ < ⊤ := by
  by_contra hG
  have hGtop : G ξ = ⊤ := le_antisymm le_top (not_lt.mp hG)
  have hα0 : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
  have hmul := (h x ξ).1
  rw [hGtop, ENNReal.mul_top hα0] at hmul
  exact (not_lt_of_ge hmul) hL

/-- The real-valued restriction of `G` is convex on `dom G`. -/
theorem ConvexENN.convexOn_toReal_dom {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) :
    ConvexOn ℝ (dom G) fun ζ => (G ζ).toReal := by
  refine ⟨hG.convex_dom, fun ξ hξ ζ hζ a b ha hb hab => ?_⟩
  have hξt : G ξ ≠ ⊤ := (hξ : G ξ < ⊤).ne
  have hζt : G ζ ≠ ⊤ := (hζ : G ζ < ⊤).ne
  let τ : ℝ≥0 := ⟨a, ha⟩
  have ha1 : τ ≤ 1 := by change a ≤ 1; linarith
  have h := hG ξ ζ τ ha1
  have hb' : ((1 - τ : ℝ≥0) : ℝ) = b := by
    rw [NNReal.coe_sub ha1, NNReal.coe_one]; change 1 - a = b; linarith
  rw [hb'] at h
  have hrhs : (τ : ℝ≥0∞) * G ξ + ((1 - τ : ℝ≥0) : ℝ≥0∞) * G ζ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hξt,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hζt⟩
  have := ENNReal.toReal_mono hrhs h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hξt)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hζt), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.coe_toReal, hb'] at this
  change (G (a • ξ + b • ζ)).toReal ≤ a • (G ξ).toReal + b • (G ζ).toReal
  exact this

theorem ConvexENN.convexOn_toReal {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) :
    ConvexOn ℝ (interior (dom G)) fun ζ => (G ζ).toReal :=
  hG.convexOn_toReal_dom.subset interior_subset hG.convex_dom.interior

/-- **Subgradient** of a convex `G` at an interior point of its domain. -/
theorem ConvexENN.exists_subgradient {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) {ξ : Mat m N}
    (hξ : ξ ∈ interior (dom G)) :
    ∃ ℓ : Mat m N →L[ℝ] ℝ, ∀ ζ, ENNReal.ofReal ((G ξ).toReal + ℓ (ζ - ξ)) ≤ G ζ := by
  set g : Mat m N → ℝ := fun ζ => (G ζ).toReal with hg_def
  have hconv := hG.convexOn_toReal
  have hcont : ContinuousOn g (interior (dom G)) := by
    intro ζ hζ
    have hζd : G ζ < ⊤ := (interior_subset hζ : ζ ∈ dom G)
    exact (ENNReal.continuousAt_toReal hζd.ne).comp_continuousWithinAt
      (hG.continuousOn_interior_dom ζ hζ)
  set E : Set (Mat m N × ℝ) := {p | p.1 ∈ interior (dom G) ∧ g p.1 < p.2} with hE_def
  have hEc : Convex ℝ E := hconv.convex_strict_epigraph
  have hEo : IsOpen E := by
    have h1 : ContinuousOn (fun p : Mat m N × ℝ => g p.1 - p.2) (Prod.fst ⁻¹' interior (dom G)) :=
      (hcont.comp continuous_fst.continuousOn fun p hp => hp).sub continuous_snd.continuousOn
    have h2 := h1.isOpen_inter_preimage (isOpen_interior.preimage continuous_fst)
      (isOpen_Iio (a := (0 : ℝ)))
    convert h2 using 1
    ext p
    simp only [hE_def, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, sub_neg]
  have hxE : (ξ, g ξ) ∉ E := fun h => lt_irrefl _ h.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hEc hEo hxE
  set ℓ₀ : Mat m N →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Mat m N) ℝ) with hℓ₀
  set lam : ℝ := f (0, 1) with hlam
  have hfdec : ∀ ζ r, f (ζ, r) = ℓ₀ ζ + r * lam := by
    intro ζ r
    have h : f (ζ, r) = f (ζ, 0) + r * f (0, 1) := by
      rw [← smul_eq_mul, ← map_smul, ← map_add]
      congr 1
      ext <;> simp
    rw [h]
    rfl
  have hlam0 : lam < 0 := by
    have h := hf (ξ, g ξ + 1) ⟨hξ, by linarith⟩
    rw [hfdec, hfdec] at h
    linarith
  -- the supporting inequality on `D`
  have hsupD : ∀ ζ ∈ interior (dom G), g ξ + ((-lam)⁻¹ • ℓ₀) (ζ - ξ) ≤ g ζ := by
    intro ζ hζ
    have key : ℓ₀ ζ + g ζ * lam ≤ ℓ₀ ξ + g ξ * lam := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have h := hf (ζ, g ζ + ε / (-lam)) ⟨hζ, by
        have : 0 < ε / (-lam) := div_pos hε (by linarith)
        linarith⟩
      rw [hfdec, hfdec] at h
      have : (g ζ + ε / (-lam)) * lam = g ζ * lam - ε := by
        rw [add_mul, div_neg, neg_mul, div_mul_cancel₀ ε hlam0.ne]; ring
      linarith
    have hl : ((-lam)⁻¹ • ℓ₀) (ζ - ξ) = (ℓ₀ ζ - ℓ₀ ξ) / (-lam) := by
      rw [smul_apply, map_sub, smul_eq_mul, inv_mul_eq_div]
    have hd : (ℓ₀ ζ - ℓ₀ ξ) / (-lam) ≤ g ζ - g ξ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [hl]
    linarith
  refine ⟨(-lam)⁻¹ • ℓ₀, fun ζ => ?_⟩
  by_cases hζ : G ζ < ⊤
  · rw [← ENNReal.ofReal_toReal hζ.ne]
    refine ENNReal.ofReal_le_ofReal ?_
    -- the midpoint of `[ξ, ζ]` lies in `D`
    have hmid : (1 / 2 : ℝ) • ξ + (1 / 2 : ℝ) • ζ ∈ interior (dom G) :=
      hG.convex_dom.openSegment_interior_closure_subset_interior hξ (subset_closure hζ)
        ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have h1 := hsupD _ hmid
    have h2 := hG.convexOn_toReal_dom.2 (interior_subset hξ) hζ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hlin : ((-lam)⁻¹ • ℓ₀) ((1 / 2 : ℝ) • ξ + (1 / 2 : ℝ) • ζ - ξ) =
        (1 / 2 : ℝ) * ((-lam)⁻¹ • ℓ₀) (ζ - ξ) := by
      rw [show (1 / 2 : ℝ) • ξ + (1 / 2 : ℝ) • ζ - ξ = (1 / 2 : ℝ) • (ζ - ξ) by module,
        map_smul, smul_eq_mul]
    simp only [hg_def, smul_eq_mul] at h1 h2
    rw [hlin] at h1
    linarith
  · rw [not_lt, top_le_iff] at hζ
    rw [hζ]
    exact le_top

/-! ### Jensen's inequality for Sobolev correctors -/

theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ y, f y ∂μ) ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂μ := by
  calc ENNReal.ofReal (∫ y, f y ∂μ) ≤ ENNReal.ofReal (∫ y, max (f y) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun y => le_max_left _ _)
    _ = ∫⁻ y, ENNReal.ofReal (max (f y) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part (ae_of_all _ fun y => le_max_right _ _)
    _ = ∫⁻ y, ENNReal.ofReal (f y) ∂μ := by
        congr 1
        funext y
        rcases le_total (f y) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]

section Jensen

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-- **`∫_U ∇φ = 0`** for `φ ∈ W^{1,p}_0(U)`, `U` bounded open with `|∂U| = 0`: test the weak
gradient identity with a smooth bump equal to `1` near `Ū`. -/
theorem W1p0.integral_grad_eq_zero {U : Set (Sp N)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUf : volume (frontier U) = 0)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 (ENNReal.ofReal p) U) :
    ∫ y in U, u.2 y = 0 := by
  have hgoff := W1p0.ae_grad_eq_zero_off hUo hUf hu
  obtain ⟨R, hR⟩ := hUb.subset_ball (0 : Sp N)
  set R' := max R 0
  let ψ : ContDiffBump (0 : Sp N) := ⟨R' + 1, R' + 2, by positivity, by linarith⟩
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hUb.measure_lt_top.ne
  have hint : Integrable u.2 (volume.restrict U) :=
    (hu.2.2.1.restrict U).integrable hP.out
  have hψ1 : ∀ y ∈ U, ψ =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    intro y hy
    have hyb : y ∈ Metric.ball (0 : Sp N) (R' + 1) :=
      Metric.ball_subset_ball (by linarith [le_max_left R 0]) (hR hy)
    filter_upwards [Metric.isOpen_ball.mem_nhds hyb] with z hz
    exact ψ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.integral_apply hint, zero_apply]
  have h := hu.2.2.2 ψ ψ.contDiff ψ.hasCompactSupport (subset_univ _) v
  have hL : ∀ y, fderiv ℝ ψ y v • u.1 y = 0 := by
    intro y
    by_cases hy : y ∈ U
    · rw [(hψ1 y hy).fderiv_eq, fderiv_const_apply, zero_apply, zero_smul]
    · rw [hu.1 y hy, smul_zero]
  rw [integral_congr_ae (ae_of_all _ hL), integral_zero] at h
  have h' : ∫ y, ψ y • u.2 y v = 0 := neg_eq_zero.1 h.symm
  calc ∫ y in U, u.2 y v = ∫ y, u.2 y v :=
        setIntegral_eq_integral_of_ae_compl_eq_zero (hgoff.mono fun y hy hyU => by
          rw [hy hyU, zero_apply])
    _ = ∫ y, ψ y • u.2 y v := by
        refine integral_congr_ae (hgoff.mono fun y hy => ?_)
        dsimp only
        by_cases hyU : y ∈ U
        · rw [(hψ1 y hyU).eq_of_nhds, one_smul]
        · rw [hy hyU, zero_apply, smul_zero]
    _ = 0 := h'

/-- **Jensen's inequality** for Sobolev correctors at an interior point of `dom G`:
`|U| G(ξ) ≤ ∫_U G(ξ + ∇φ)`. -/
theorem ConvexENN.volume_mul_le_lintegral_W1p0 {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {U : Set (Sp N)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUf : volume (frontier U) = 0) {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 (ENNReal.ofReal p) U) {ξ : Mat m N} (hξ : ξ ∈ interior (dom G)) :
    volume U * G ξ ≤ ∫⁻ y in U, G (ξ + u.2 y) := by
  obtain ⟨ℓ, hℓ⟩ := hG.exists_subgradient hξ
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hUb.measure_lt_top.ne
  have hint : Integrable u.2 (volume.restrict U) := (hu.2.2.1.restrict U).integrable hP.out
  have hξt : G ξ ≠ ⊤ := (interior_subset hξ : ξ ∈ dom G).ne
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  set c := (G ξ).toReal
  have hpt : ∀ y, ENNReal.ofReal (c + ℓ (u.2 y)) ≤ G (ξ + u.2 y) := fun y => by
    simpa using hℓ (ξ + u.2 y)
  have hℓint : Integrable (fun y => ℓ (u.2 y)) (volume.restrict U) := ℓ.integrable_comp hint
  have hI : ∫ y in U, (c + ℓ (u.2 y)) = (volume U).toReal * c := by
    rw [integral_add (integrable_const c) hℓint, ContinuousLinearMap.integral_comp_comm ℓ hint,
      W1p0.integral_grad_eq_zero hUo hUb hUf hu, map_zero, add_zero, integral_const,
      smul_eq_mul, measureReal_restrict_apply_univ]
    rfl
  calc volume U * G ξ = ENNReal.ofReal ((volume U).toReal * c) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hUt,
          ENNReal.ofReal_toReal hξt]
    _ = ENNReal.ofReal (∫ y in U, (c + ℓ (u.2 y))) := by rw [hI]
    _ ≤ ∫⁻ y in U, ENNReal.ofReal (c + ℓ (u.2 y)) :=
        ofReal_integral_le_lintegral_ofReal ((integrable_const c).add hℓint)
    _ ≤ ∫⁻ y in U, G (ξ + u.2 y) := lintegral_mono hpt

/-! ### Remark `domhw` (i) and Proposition `lsc-of-HW` -/

/-- **Remark `domhw` (i), upper bound**: `ℋ_p L ≤ β (1 + G)`. -/
theorem HasGGrowth.Hp_le {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (h : HasGGrowth G α β L) (q : ℝ≥0∞) (ξ : Mat m N) : Hp q L ξ ≤ β * (1 + G ξ) := by
  refine (iInf_le _ 0).trans ?_
  simp only [Nat.cast_zero, zero_add, volume_cube_one, div_one]
  refine (Ytp_le_lintegral q L _ ξ).trans ?_
  calc ∫⁻ y in cube 1 0, L y ξ ≤ ∫⁻ _y in cube 1 (0 : Sp N), (β : ℝ≥0∞) * (1 + G ξ) :=
        lintegral_mono fun y => (h y ξ).2
    _ = β * (1 + G ξ) := by rw [setLIntegral_const, volume_cube_one, mul_one]

/-- **Remark `domhw` (i), lower bound** on `int(dom G)`: `α G ≤ ℋ_p L`. -/
theorem HasGGrowth.le_Hp {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (h : HasGGrowth G α β L) {ξ : Mat m N}
    (hξ : ξ ∈ interior (dom G)) : (α : ℝ≥0∞) * G ξ ≤ Hp (ENNReal.ofReal p) L ξ := by
  refine le_iInf fun k => ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [ENNReal.le_div_iff_mul_le (Or.inl (volume_cube_pos hk 0).ne')
    (Or.inl (volume_cube_ne_top _ 0))]
  refine le_iInf₂ fun u hu => ?_
  have hJ := hG.volume_mul_le_lintegral_W1p0 (isOpen_cube _ _) (isBounded_cube _ _)
    (volume_frontier_cube _ _) hu hξ
  calc (α : ℝ≥0∞) * G ξ * volume (cube ((k : ℝ) + 1) (0 : Sp N))
      = α * (volume (cube ((k : ℝ) + 1) (0 : Sp N)) * G ξ) := by ring
    _ ≤ α * ∫⁻ y in cube ((k : ℝ) + 1) 0, G (ξ + u.2 y) := by gcongr
    _ = ∫⁻ y in cube ((k : ℝ) + 1) 0, α * G (ξ + u.2 y) :=
        (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
    _ ≤ ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ξ + u.2 y) := lintegral_mono fun y => (h y _).1

/-- **Remark `domhw` (i)**, inclusion `dom G ⊆ dom ℋ_p L` (from the upper bound). On
`int(dom G)` both functions are finite, and `HasGGrowth.le_Hp` gives the lower bound. -/
theorem HasGGrowth.dom_subset_dom_Hp {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (h : HasGGrowth G α β L) (q : ℝ≥0∞) :
    dom G ⊆ dom (Hp q L) := fun ξ hξ =>
  (h.Hp_le q ξ).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hξ⟩))

end Jensen

/-- **Proposition `lsc-of-HW`**: if `L` is ru-usc, then `ℋ_p L` and its radial envelope are
ru-usc, and `ℋ_p L(tξ) → \widehat{ℋ_p L}(ξ)` as `t → 1⁻`, for every `ξ`. -/
theorem lsc_of_HW {q : ℝ≥0∞} {L : Sp N → Mat m N → ℝ≥0∞} (hL : RUUSC L) :
    RUUSC (fun _ => Hp q L) ∧ RUUSC (fun _ => radial (Hp q L)) ∧
      ∀ ξ : Mat m N, Tendsto (fun t : ℝ => Hp q L (t • ξ)) (𝓝[<] 1) (𝓝 (radial (Hp q L) ξ)) := by
  obtain ⟨c, hc, h⟩ := hL
  exact ⟨⟨c, hc, h.Hp⟩, ⟨c, hc, h.Hp.radial⟩, fun ξ => h.Hp.tendsto_radial ξ⟩

end Homogenization
