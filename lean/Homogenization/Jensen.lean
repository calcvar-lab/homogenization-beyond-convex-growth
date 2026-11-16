import Homogenization.Envelopes

/-!
# Convex integrands are invariant under `𝒵_aff` and `ℋ_aff`

This is the argument of the proof of Lemma `lem:consequences` (iii): for `f` convex and
`φ ∈ Aff₀(U)`, `∫_U ∇φ = 0`, hence by Jensen's inequality `|U| f(ξ) ≤ ∫_U f(ξ + ∇φ)`. Consequently
`𝒵_aff f = f`, `ℋ_aff f = f`, and the `G`-growth propagates to `ℋ_aff L` and `𝒵_aff ℋ_aff L`.

The identity `∫ ∇φ = 0` is obtained from the integration by parts formula for Lipschitz functions
(`LipschitzWith.integral_lineDeriv_mul_eq`, from Mathlib's proof of Rademacher's theorem). This is
exactly where the Lipschitz requirement in `IsPWAffine` is needed (see the module docstring of
`Homogenization.Basic`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### Finite Jensen inequality for `[0,∞]`-valued convex functions -/

theorem ConvexENN.map_sum_le {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f) {ι : Type*}
    (t : Finset ι) (w : ι → ℝ≥0) (x : ι → Mat m N) (hw : ∑ i ∈ t, w i = 1) :
    f (∑ i ∈ t, (w i : ℝ) • x i) ≤ ∑ i ∈ t, (w i : ℝ≥0∞) * f (x i) := by
  classical
  induction t using Finset.induction_on generalizing w with
  | empty => simp at hw
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hw ⊢
    rw [Finset.sum_insert ha]
    set S := ∑ i ∈ s, w i with hS
    by_cases hS0 : S = 0
    · have hz : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff.1 hS0)
      have ha1 : w a = 1 := by rw [hS0, add_zero] at hw; exact hw
      have h1 : ∑ i ∈ s, (w i : ℝ) • x i = 0 :=
        Finset.sum_eq_zero fun i hi => by simp [hz i hi]
      have h2 : ∑ i ∈ s, (w i : ℝ≥0∞) * f (x i) = 0 :=
        Finset.sum_eq_zero fun i hi => by simp [hz i hi]
      simp [h1, h2, ha1]
    · set w' : ι → ℝ≥0 := fun i => w i / S
      have hw' : ∑ i ∈ s, w' i = 1 := by
        simp only [w']; rw [← Finset.sum_div, div_self hS0]
      have hwa : w a = 1 - S := eq_tsub_of_add_eq hw
      have hS1 : S ≤ 1 := by rw [← hw]; exact le_add_self
      set y := ∑ i ∈ s, (w' i : ℝ) • x i
      have hy : ∑ i ∈ s, (w i : ℝ) • x i = (S : ℝ) • y := by
        simp only [y, Finset.smul_sum, smul_smul, w']
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; push_cast; field_simp
      have hconv := hf (x a) y (w a) (by rw [hwa]; exact tsub_le_self)
      have h1a : (1 - w a : ℝ≥0) = S := by rw [hwa]; exact tsub_tsub_cancel_of_le hS1
      rw [h1a] at hconv
      rw [hy]
      refine hconv.trans (add_le_add le_rfl ?_)
      calc (S : ℝ≥0∞) * f y ≤ S * ∑ i ∈ s, (w' i : ℝ≥0∞) * f (x i) := by gcongr; exact ih w' hw'
        _ = ∑ i ∈ s, (w i : ℝ≥0∞) * f (x i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, ← ENNReal.coe_mul]
          simp only [w', mul_div_cancel₀ _ hS0]

/-- Jensen's inequality for the three terms produced by the cut-off formula.  This is the
pointwise convexity estimate needed before applying the upper `G`-growth bound to a cut-off
gradient.  The coefficients are allowed to vanish, which is important on the inner cube and at
the edge of the cut-off. -/
theorem ConvexENN.weighted_three_le {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f)
    (a b c : ℝ≥0) (habc : a + b + c = 1) (x y z : Mat m N) :
    f ((a : ℝ) • x + (b : ℝ) • y + (c : ℝ) • z) ≤
      (a : ℝ≥0∞) * f x + (b : ℝ≥0∞) * f y + (c : ℝ≥0∞) * f z := by
  classical
  let w : Fin 3 → ℝ≥0 := fun i => if i = 0 then a else if i = 1 then b else c
  let v : Fin 3 → Mat m N := fun i => if i = 0 then x else if i = 1 then y else z
  have hw : ∑ i ∈ Finset.univ, w i = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [w, ↓reduceIte]
    simpa [add_assoc] using habc
  have hj := hf.map_sum_le Finset.univ w v hw
  simpa [w, v, Fin.sum_univ_succ, Finset.sum_singleton, add_assoc] using hj

/-- The upper growth estimate for the three-term convex combination in a cut-off gradient.
No polynomial growth or finiteness of the three `f`-values is assumed: the statement is valid in
`ℝ≥0∞`, including the case where the right-hand side is infinite. -/
theorem HasGGrowth.weighted_three_upper {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {W : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hgrowth : HasGGrowth G α β W) (x₀ : Sp N) (a b c : ℝ≥0)
    (habc : a + b + c = 1) (x y z : Mat m N) :
    W x₀ ((a : ℝ) • x + (b : ℝ) • y + (c : ℝ) • z) ≤
      (β : ℝ≥0∞) *
        (1 + (a : ℝ≥0∞) * G x + (b : ℝ≥0∞) * G y + (c : ℝ≥0∞) * G z) := by
  calc W x₀ ((a : ℝ) • x + (b : ℝ) • y + (c : ℝ) • z)
      ≤ (β : ℝ≥0∞) * (1 + G ((a : ℝ) • x + (b : ℝ) • y + (c : ℝ) • z)) :=
        (hgrowth x₀ _).2
    _ ≤ (β : ℝ≥0∞) *
        (1 + (a : ℝ≥0∞) * G x + (b : ℝ≥0∞) * G y + (c : ℝ≥0∞) * G z) := by
          have hconv := hG.weighted_three_le a b c habc x y z
          have hsum := add_le_add_left hconv (1 : ℝ≥0∞)
          simpa [add_comm, add_left_comm, add_assoc] using
            (mul_le_mul_of_nonneg_left hsum (show 0 ≤ (β : ℝ≥0∞) from zero_le))

/-! ### The boundary of a cube is negligible -/

theorem cube_subset_pi_Icc (ρ : ℝ) (x : Sp N) :
    cube ρ x ⊆ Set.pi univ fun i => Icc (x i - ρ / 2) (x i + ρ / 2) :=
  fun _ hy i hi => Ioo_subset_Icc_self (hy i hi)

theorem volume_frontier_cube (ρ : ℝ) (x : Sp N) : volume (frontier (cube ρ x)) = 0 := by
  have hcl : closure (cube ρ x) ⊆ Set.pi univ fun i => Icc (x i - ρ / 2) (x i + ρ / 2) :=
    closure_minimal (cube_subset_pi_Icc ρ x) (isClosed_set_pi fun _ _ => isClosed_Icc)
  rw [frontier, (isOpen_cube ρ x).interior_eq]
  refine measure_mono_null (sdiff_subset_sdiff_left hcl) ?_
  have hIcc : (Set.pi univ fun i => Icc (x i - ρ / 2) (x i + ρ / 2)) =
      Icc (fun i => x i - ρ / 2) (fun i => x i + ρ / 2) := by
    ext; simp [Pi.le_def]
  rw [measure_sdiff (cube_subset_pi_Icc ρ x) (isOpen_cube ρ x).measurableSet.nullMeasurableSet
    (volume_cube_ne_top ρ x), hIcc, Real.volume_Icc_pi, cube, Real.volume_pi_Ioo, tsub_self]

theorem isBounded_cube (ρ : ℝ) (x : Sp N) : Bornology.IsBounded (cube ρ x) :=
  (Metric.isBounded_Icc (fun i => x i - ρ / 2) (fun i => x i + ρ / 2)).subset
    fun _ hy => ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩

/-! ### `∫ ∇φ = 0` for `φ ∈ Aff₀(U)` -/

theorem lineDeriv_eq_zero_of_eventuallyEq_const {f : Sp N → ℝ} {y : Sp N} {c : ℝ}
    (h : f =ᶠ[𝓝 y] fun _ => c) (v : Sp N) : lineDeriv ℝ f y v = 0 := by
  have : HasFDerivAt f (0 : Sp N →L[ℝ] ℝ) y := (hasFDerivAt_const c y).congr_of_eventuallyEq h
  simpa using (this.hasLineDerivAt v).lineDeriv

/-- A Lipschitz plateau function: `1` on `ball 0 (R+1)`, `0` outside `closedBall 0 (R+2)`. -/
noncomputable def plateau (R : ℝ) (y : Sp N) : ℝ := max 0 (min 1 (R + 2 - ‖y‖))

theorem lipschitzWith_plateau (R : ℝ) : LipschitzWith 1 (plateau (N := N) R) := by
  have h : LipschitzWith 1 (fun y : Sp N => R + 2 - ‖y‖) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul,
        show R + 2 - ‖x‖ - (R + 2 - ‖y‖) = ‖y‖ - ‖x‖ by ring, abs_sub_comm]
      exact abs_norm_sub_norm_le x y
  exact (h.const_min 1).const_max 0

theorem hasCompactSupport_plateau (R : ℝ) : HasCompactSupport (plateau (N := N) R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Sp N) (R + 2)) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  simp only [plateau]
  exact max_eq_left (min_le_right _ _ |>.trans (by linarith))

theorem plateau_eventuallyEq_one {R : ℝ} {y : Sp N} (hy : ‖y‖ ≤ R) :
    plateau (N := N) R =ᶠ[𝓝 y] fun _ => 1 := by
  have hopen : IsOpen {z : Sp N | ‖z‖ < R + 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds (show ‖y‖ < R + 1 by linarith)] with z hz
  simp only [plateau]
  rw [min_eq_left (by linarith [show ‖z‖ < R + 1 from hz])]
  exact max_eq_right zero_le_one

/-- **`∫_U ∇φ = 0`** for `φ ∈ Aff₀(U)`, written on the pieces of `φ`:
`∑ᵢ |Vᵢ| ζᵢ = 0`. -/
theorem sum_volume_smul_eq_zero {U : Set (Sp N)} (hUb : Bornology.IsBounded U)
    (hUf : volume (frontier U) = 0) {φ : Sp N → Tgt m} {K : ℝ≥0} (hK : LipschitzWith K φ)
    (hφ0 : ∀ y ∉ U, φ y = 0) {n : ℕ} {V : Fin n → Set (Sp N)} {ζ : Fin n → Mat m N}
    (hVo : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVc : volume (U \ ⋃ i, V i) = 0) (hφV : ∀ i, ∀ y ∈ V i, HasFDerivAt φ (ζ i) y) :
    ∑ i, (volume (V i)).toReal • ζ i = 0 := by
  classical
  obtain ⟨R, hR⟩ := hUb.closure.exists_norm_le
  refine ContinuousLinearMap.ext fun v => funext fun k => ?_
  simp only [_root_.sum_apply, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, _root_.zero_apply, Pi.zero_apply]
  set f : Sp N → ℝ := fun y => φ y k
  have hf : LipschitzWith K f :=
    LipschitzWith.of_dist_le_mul fun x y => (dist_le_pi_dist (φ x) (φ y) k).trans
      (hK.dist_le_mul x y)
  -- `f` vanishes near every point off `closure U`
  have F0 : ∀ y, y ∉ closure U → f =ᶠ[𝓝 y] fun _ => 0 := by
    intro y hy
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
    exact congrFun (hφ0 z fun h => hz (subset_closure h)) k
  -- integration by parts against the plateau function
  have hIBP := hf.integral_lineDeriv_mul_eq (μ := volume) (lipschitzWith_plateau R)
    (hasCompactSupport_plateau R) v
  have hR' : (fun y => lineDeriv ℝ (plateau R) y (-v) * f y) = fun _ => 0 := by
    funext y
    by_cases hy : y ∈ closure U
    · rw [lineDeriv_eq_zero_of_eventuallyEq_const (plateau_eventuallyEq_one (hR y hy)), zero_mul]
    · rw [(F0 y hy).eq_of_nhds, mul_zero]
  have hL' : (fun y => lineDeriv ℝ f y v * plateau R y) = fun y => lineDeriv ℝ f y v := by
    funext y
    by_cases hy : y ∈ closure U
    · rw [(plateau_eventuallyEq_one (hR y hy)).eq_of_nhds, mul_one]
    · rw [lineDeriv_eq_zero_of_eventuallyEq_const (F0 y hy), zero_mul]
  rw [hR', hL', integral_zero] at hIBP
  -- the line derivative is a.e. the simple function `∑ᵢ 1_{Vᵢ} ζᵢ(v)ₖ`
  set s : Sp N → ℝ := fun y => ∑ i, (V i).indicator (fun _ => ζ i v k) y
  have hs_on : ∀ i, ∀ y ∈ V i, s y = ζ i v k := by
    intro i y hy
    simp only [s]
    rw [Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem
      (fun hj => (hVd hji).le_bot ⟨hj, hy⟩) _) (by simp), indicator_of_mem hy]
  have hae : (fun y => lineDeriv ℝ f y v) =ᵐ[volume] s := by
    refine measure_mono_null (t := (U \ ⋃ i, V i) ∪ frontier U) ?_
      (measure_union_null hVc hUf)
    intro y hy
    change ¬ (lineDeriv ℝ f y v = s y) at hy
    by_cases hyV : ∃ i, y ∈ V i
    · obtain ⟨i, hi⟩ := hyV
      exfalso; apply hy
      have hd : HasFDerivAt f ((ContinuousLinearMap.proj k).comp (ζ i)) y :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).hasFDerivAt.comp y
          (hφV i y hi)
      rw [(hd.hasLineDerivAt v).lineDeriv, hs_on i y hi]
      rfl
    · push Not at hyV
      by_cases hyU : y ∈ U
      · exact Or.inl ⟨hyU, by simpa using hyV⟩
      · by_cases hyc : y ∈ closure U
        · exact Or.inr ⟨hyc, fun h => hyU (interior_subset h)⟩
        · exfalso; apply hy
          rw [lineDeriv_eq_zero_of_eventuallyEq_const (F0 y hyc)]
          simp only [s]
          exact (Finset.sum_eq_zero fun i _ => indicator_of_notMem (hyV i) _).symm
  have hint : ∫ y, s y = ∑ i, (volume (V i)).toReal * ζ i v k := by
    simp only [s]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator_const _ (hVo i).measurableSet, measureReal_def, smul_eq_mul]
    · intro i _
      refine (integrable_indicator_iff (hVo i).measurableSet).2 ?_
      exact integrableOn_const ((measure_mono (hVU i)).trans_lt hUb.measure_lt_top).ne
  rw [← hint, ← integral_congr_ae hae, hIBP]

/-! ### Convex integrands are invariant -/

/-- `|U| f(ξ) ≤ ∫_U f(ξ + ∇φ)` for `f` convex and `φ ∈ Aff₀(U)` (Jensen's inequality). -/
theorem ConvexENN.volume_mul_le_lintegral {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f)
    {U : Set (Sp N)} (hUb : Bornology.IsBounded U) (hUf : volume (frontier U) = 0)
    (hU0 : volume U ≠ 0) {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 U) (ξ : Mat m N) :
    volume U * f ξ ≤ ∫⁻ y in U, f (ξ + fderiv ℝ φ y) := by
  classical
  obtain ⟨⟨K, hK⟩, h0, -, n, V, ζ, hVo, hVU, hVd, -, hVc, hφV⟩ := hφ
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  have hVt : ∀ i, volume (V i) ≠ ⊤ := fun i => ((measure_mono (hVU i)).trans_lt
    hUb.measure_lt_top).ne
  have hUV : U =ᵐ[volume] ⋃ i, V i :=
    ae_eq_set.2 ⟨hVc, by rw [sdiff_eq_empty.2 (iUnion_subset hVU), measure_empty]⟩
  -- (A) the integral on the pieces
  have hA : ∫⁻ y in U, f (ξ + fderiv ℝ φ y) = ∑ i, volume (V i) * f (ξ + ζ i) := by
    rw [setLIntegral_congr hUV, lintegral_iUnion (fun i => (hVo i).measurableSet) hVd,
      tsum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet
      (g := fun _ => f (ξ + ζ i)) fun y hy => by rw [(hφV i y hy).fderiv],
      setLIntegral_const, mul_comm]
  -- (B) `|U| = ∑ |Vᵢ|`
  have hB : volume U = ∑ i, volume (V i) := by
    rw [measure_congr hUV, measure_iUnion (fun i j hij => hVd hij)
      (fun i => (hVo i).measurableSet), tsum_fintype]
  have hzero := sum_volume_smul_eq_zero hUb hUf hK h0 hVo hVU hVd hVc hφV
  -- (C) Jensen with weights `|Vᵢ| / |U|`
  set T : ℝ≥0 := (volume U).toNNReal
  have hT : (T : ℝ≥0∞) = volume U := ENNReal.coe_toNNReal hUt
  have hT0 : T ≠ 0 := by
    intro h; apply hU0; rw [← hT, h, ENNReal.coe_zero]
  set w : Fin n → ℝ≥0 := fun i => (volume (V i)).toNNReal / T
  have hTsum : T = ∑ i, (volume (V i)).toNNReal := by
    simp only [T, hB]; exact ENNReal.toNNReal_sum fun i _ => hVt i
  have hw : ∑ i, w i = 1 := by
    simp only [w]; rw [← Finset.sum_div, ← hTsum, div_self hT0]
  have hpts : ∑ i, (w i : ℝ) • (ξ + ζ i) = ξ := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    rw [show (∑ i, (w i : ℝ)) = 1 by exact_mod_cast hw, one_smul, add_eq_left]
    have : ∑ i, (w i : ℝ) • ζ i = (T : ℝ)⁻¹ • ∑ i, (volume (V i)).toReal • ζ i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]; congr 1
      simp only [w, NNReal.coe_div, ENNReal.coe_toNNReal_eq_toReal]; ring
    rw [this, hzero, smul_zero]
  have hJ := hf.map_sum_le Finset.univ w (fun i => ξ + ζ i) hw
  rw [hpts] at hJ
  rw [hA, ← hT]
  calc (T : ℝ≥0∞) * f ξ ≤ T * ∑ i, (w i : ℝ≥0∞) * f (ξ + ζ i) := by gcongr
    _ = ∑ i, volume (V i) * f (ξ + ζ i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← ENNReal.coe_mul, mul_div_cancel₀ _ hT0, ENNReal.coe_toNNReal (hVt i)]

theorem ConvexENN.volume_mul_le_Yt {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f) {ρ : ℝ} (hρ : 0 < ρ)
    (ξ : Mat m N) : volume (cube ρ (0 : Sp N)) * f ξ ≤ Yt (fun _ => f) (cube ρ (0 : Sp N)) ξ :=
  le_iInf₂ fun _ hφ => hf.volume_mul_le_lintegral (isBounded_cube ρ 0) (volume_frontier_cube ρ 0)
    (volume_cube_pos hρ 0).ne' hφ ξ

theorem volume_cube_one : volume (cube 1 (0 : Sp N)) = 1 := by rw [volume_cube]; simp

/-- `𝒵_aff f = f` for convex `f`. -/
theorem ConvexENN.Zaff_eq {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f) : Zaff f = f := by
  funext ξ
  refine le_antisymm (Zaff_le f ξ) ?_
  have := hf.volume_mul_le_Yt one_pos ξ
  rwa [volume_cube_one, one_mul] at this

/-- `ℋ_aff f = f` for convex `f` not depending on `x`. -/
theorem ConvexENN.Haff_eq {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f) :
    Haff (fun _ : Sp N => f) = f := by
  funext ξ
  refine le_antisymm ?_ (le_iInf fun k => ?_)
  · refine (iInf_le _ 0).trans ?_
    simp only [Nat.cast_zero, zero_add, volume_cube_one, div_one]
    exact Zaff_le f ξ
  · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [ENNReal.le_div_iff_mul_le (Or.inl (volume_cube_pos hk 0).ne')
      (Or.inl (volume_cube_ne_top _ 0)), mul_comm]
    exact hf.volume_mul_le_Yt hk ξ

theorem ConvexENN.const_mul {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) (c : ℝ≥0∞) :
    ConvexENN fun ξ => c * G ξ := by
  intro ξ ζ t ht
  calc c * G ((t : ℝ) • ξ + ((1 - t : ℝ≥0) : ℝ) • ζ)
      ≤ c * (t * G ξ + (1 - t : ℝ≥0) * G ζ) := by gcongr; exact hG ξ ζ t ht
    _ = t * (c * G ξ) + (1 - t : ℝ≥0) * (c * G ζ) := by ring

theorem ConvexENN.const_mul_one_add {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) (c : ℝ≥0∞) :
    ConvexENN fun ξ => c * (1 + G ξ) := by
  intro ξ ζ t ht
  have h1 : (t : ℝ≥0∞) + (1 - t : ℝ≥0) = 1 := by
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le ht, ENNReal.coe_one]
  calc c * (1 + G ((t : ℝ) • ξ + ((1 - t : ℝ≥0) : ℝ) • ζ))
      ≤ c * ((t + (1 - t : ℝ≥0)) + (t * G ξ + (1 - t : ℝ≥0) * G ζ)) := by
        rw [h1]; gcongr; exact hG ξ ζ t ht
    _ = t * (c * (1 + G ξ)) + (1 - t : ℝ≥0) * (c * (1 + G ζ)) := by ring

/-- Lemma `lem:consequences` (iii) for `ℋ_aff`: `G`-growth passes from `L` to `ℋ_aff L`. -/
theorem HasGGrowth.Haff {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (h : HasGGrowth G α β L) :
    HasGGrowth G α β (fun _ => Homogenization.Haff L) := by
  intro _ ξ
  constructor
  · have := Haff_mono (L := fun _ ξ => (α : ℝ≥0∞) * G ξ) (L' := L) (fun x ξ => (h x ξ).1) ξ
    rwa [(hG.const_mul α).Haff_eq] at this
  · have := Haff_mono (L := L) (L' := fun _ ξ => (β : ℝ≥0∞) * (1 + G ξ))
      (fun x ξ => (h x ξ).2) ξ
    rwa [(hG.const_mul_one_add β).Haff_eq] at this

/-- Lemma `lem:consequences` (iii) for `𝒵_aff`. -/
theorem HasGGrowth.Zaff {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) {α β : ℝ≥0}
    {L : Mat m N → ℝ≥0∞} (h : HasGGrowth G α β (fun _ => L)) :
    HasGGrowth G α β (fun _ => Homogenization.Zaff L) := by
  intro _ ξ
  constructor
  · have := Zaff_mono (L := fun ξ => (α : ℝ≥0∞) * G ξ) (L' := L) (fun ξ => (h 0 ξ).1) ξ
    rwa [(hG.const_mul α).Zaff_eq] at this
  · have := Zaff_mono (L := L) (L' := fun ξ => (β : ℝ≥0∞) * (1 + G ξ)) (fun ξ => (h 0 ξ).2) ξ
    rwa [(hG.const_mul_one_add β).Zaff_eq] at this

end Homogenization
