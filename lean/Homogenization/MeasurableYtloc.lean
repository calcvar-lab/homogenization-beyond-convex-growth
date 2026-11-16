import Homogenization.Product

/-!
# Exact measurability (H6) of `𝒴_loc W` for `W = a(x) H(ξ)`

For `a` measurable with `1 ≤ a ≤ A`, `H` upper semicontinuous and `G` convex with
`G ≤ H ≤ γ(1+G)`, the function `(x,ξ) ↦ 𝒴_loc W(x,ξ)` is jointly Borel measurable
(`prodW_measurable_Ytloc`), without modification on a null set of `x`. Consequently the
hypothesis `Measurable (uncurry (Ytloc W))` can be dropped from Theorem `th:product`
(`th_product_H8`, `th_product_iii_unconditional`).

Proof:
* `Yt_cube_le_add`: `𝒴 W(Q_{ρ'}) ≤ 𝒴 W(Q_ρ) + M |Q_{ρ'} \ Q_ρ|` for `ρ ≤ ρ'` when `W(·,ξ) ≤ M`
  (competitors extended by `0`, `Aff0_mono_of_frontier_null`). Hence the normalized cell energy
  is lower semicontinuous from the left in `ρ`, and the `limsup` defining `𝒴_loc` is computed
  along rational radii (`Ytloc_eq_iInf_iSup_rat`); when `H(ξ) = ∞` every cell energy is `∞`.
* For a fixed radius, `(x,ξ) ↦ 𝒴 W(Q_q(x),ξ)` is upper semicontinuous
  (`upperSemicontinuous_Yt_prodW`): after translation it is an infimum, over `φ ∈ Aff₀(Q_q)`, of
  finite sums `∑ᵢ (∫_{Vᵢ} a(z + x) dz) H(ξ + ζᵢ)`, where `x ↦ ∫_{Vᵢ} a(z+x) dz` is continuous
  (`continuous_setLIntegral_comp_add`, dominated convergence, `|∂Vᵢ| = 0`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- `Aff₀(U) ⊆ Aff₀(U')` for open `U ⊆ U'` with `|U' ∩ ∂U| = 0` (extension by `0`). -/
theorem Aff0_mono_of_frontier_null {U U' : Set (Sp N)} (hUo : IsOpen U) (hU'o : IsOpen U')
    (hUU' : U ⊆ U') (hf : volume (U' ∩ frontier U) = 0) {φ : Sp N → Tgt m}
    (hφ : φ ∈ Aff0 U) : φ ∈ Aff0 U' := by
  have hfr : U' \ (U ∪ (U' \ closure U)) ⊆ U' ∩ frontier U := by
    rintro y ⟨hy, hyn⟩
    have h1 : y ∉ U := fun h => hyn (Or.inl h)
    have h2 : y ∈ closure U := by
      by_contra h
      exact hyn (Or.inr ⟨hy, h⟩)
    exact ⟨hy, h2, by rwa [hUo.interior_eq]⟩
  have h := Aff0.add_sum (U := U') (χ := fun _ => (0 : Tgt m)) (K := 0)
    (LipschitzWith.const 0) (fun _ _ => rfl) (V := ![U, U' \ closure U])
    (ζ := fun _ => 0) (fun i => by fin_cases i <;> simp [hUo, hU'o.sdiff isClosed_closure])
    (fun i => by fin_cases i <;> simp [hUU'])
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · change Disjoint U (U' \ closure U)
        exact Disjoint.mono_left subset_closure disjoint_sdiff_right
      · change Disjoint (U' \ closure U) U
        exact (Disjoint.mono_left subset_closure disjoint_sdiff_right).symm
      · exact absurd rfl hij)
    (fun i => by
      fin_cases i
      · simpa using hf
      · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        refine measure_mono_null ?_ hf
        rintro y ⟨hy, hyf⟩
        refine ⟨hy, ?_⟩
        rw [Set.sdiff_eq] at hyf
        rcases frontier_inter_subset _ _ hyf with ⟨h1, -⟩ | ⟨-, h2⟩
        · have h3 : y ∈ U' ∩ frontier U' := ⟨hy, h1⟩
          rw [hU'o.inter_frontier_eq] at h3
          exact h3.elim
        · rw [frontier_compl] at h2
          exact frontier_closure_subset h2)
    (measure_mono_null (by
      intro y hy
      apply hfr
      refine ⟨hy.1, fun h => hy.2 ?_⟩
      rcases h with h | h
      · exact mem_iUnion.2 ⟨0, by simpa using h⟩
      · exact mem_iUnion.2 ⟨1, by simpa using h⟩) hf)
    (fun _ y _ => hasFDerivAt_const (0 : Tgt m) y)
    (ψ := ![φ, 0]) (fun i => by
      fin_cases i
      · simpa using hφ
      · simpa using zero_mem_Aff0 (m := m) (hU'o.sdiff isClosed_closure))
  have h' : (fun _ => (0 : Tgt m)) + φ ∈ Aff0 U' := by simpa [Fin.sum_univ_two] using h
  convert h' using 1
  funext y
  simp

/-- `𝒴 W(Q_{ρ'}(x),ξ) ≤ 𝒴 W(Q_ρ(x),ξ) + M |Q_{ρ'}(x) \ Q_ρ(x)|` for `ρ ≤ ρ'` when `W(·,ξ) ≤ M`
(extension of the competitors by `0`). -/
theorem Yt_cube_le_add {W : Sp N → Mat m N → ℝ≥0∞} {ξ : Mat m N} {M : ℝ≥0∞}
    (hM : ∀ y, W y ξ ≤ M) {ρ ρ' : ℝ} (hρ : ρ ≤ ρ') (x : Sp N) :
    Yt W (cube ρ' x) ξ ≤ Yt W (cube ρ x) ξ + M * volume (cube ρ' x \ cube ρ x) := by
  have hsub := SubaddCube.cube_subset_cube hρ x
  unfold Yt
  rw [ENNReal.iInf_add]
  refine le_iInf fun φ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hφ => ?_
  have hφ' := Aff0_mono_of_frontier_null (isOpen_cube ρ x) (isOpen_cube ρ' x) hsub
    (measure_mono_null inter_subset_right (volume_frontier_cube ρ x)) hφ
  refine (iInf₂_le φ hφ').trans ?_
  rw [← lintegral_inter_add_sdiff _ (cube ρ' x) (isOpen_cube ρ x).measurableSet,
    inter_eq_right.2 hsub]
  gcongr
  have hae : ∀ᵐ y ∂(volume.restrict (cube ρ' x \ cube ρ x)), W y (ξ + fderiv ℝ φ y) ≤ M := by
    rw [ae_restrict_iff' ((isOpen_cube ρ' x).measurableSet.diff
      (isOpen_cube ρ x).measurableSet), ae_iff]
    refine measure_mono_null (fun y hy => ?_) (volume_frontier_cube ρ x)
    simp only [mem_ofPred_eq, Classical.not_imp] at hy
    obtain ⟨⟨-, hyQ⟩, hyM⟩ := hy
    by_contra hyf
    apply hyM
    have hyc : y ∉ closure (cube ρ x) := fun h => hyf ⟨h, by rwa [(isOpen_cube ρ x).interior_eq]⟩
    have hev : φ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hyc] with z hz
      exact hφ.2.1 z fun h => hz (subset_closure h)
    rw [hev.fderiv_eq, fderiv_const_apply, add_zero]
    exact hM y
  calc ∫⁻ y in cube ρ' x \ cube ρ x, W y (ξ + fderiv ℝ φ y)
      ≤ ∫⁻ _ in cube ρ' x \ cube ρ x, M := lintegral_mono_ae hae
    _ = M * volume (cube ρ' x \ cube ρ x) := setLIntegral_const _ _

/-- The normalized cell energy `𝒴 W(Q_ρ(x),ξ)/|Q_ρ(x)|`. -/
noncomputable def cellAvg (W : Sp N → Mat m N → ℝ≥0∞) (ρ : ℝ) (x : Sp N) (ξ : Mat m N) :
    ℝ≥0∞ :=
  Yt W (cube ρ x) ξ / volume (cube ρ x)

/-- If `W(·,ξ) ≤ M < ∞`, the normalized cell energy at `ρ < δ` is bounded by its supremum over the
rational radii in `]0,δ[` (lower semicontinuity from the left, by `Yt_cube_le_add`). -/
theorem cellAvg_le_iSup_rat {W : Sp N → Mat m N → ℝ≥0∞} {ξ : Mat m N} {M : ℝ≥0∞}
    (hMtop : M ≠ ⊤) (hM : ∀ y, W y ξ ≤ M) (x : Sp N) {ρ δ : ℝ} (hρ : 0 < ρ) (hρδ : ρ < δ) :
    cellAvg W ρ x ξ ≤ ⨆ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) < δ), cellAvg W q x ξ := by
  set S := ⨆ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) < δ), cellAvg W q x ξ
  by_contra h
  rw [not_le] at h
  have hS : S ≠ ⊤ := ne_top_of_lt h
  set v : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal t ^ N
  have hv : ∀ t, volume (cube t x) = v t := fun t => volume_cube t x
  have hv0 : ∀ t, 0 < t → v t ≠ 0 := fun t ht => by simp [v, ht]
  have hvt : ∀ t, v t ≠ ⊤ := fun t => by simp [v]
  have hYv : ∀ t, 0 < t → Yt W (cube t x) ξ = cellAvg W t x ξ * v t := fun t ht => by
    simp only [cellAvg, hv]
    rw [ENNReal.div_mul_cancel (hv0 t ht) (hvt t)]
  have key : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ρ →
      Yt W (cube ρ x) ξ ≤ S * v q + M * (v ρ - v q) := by
    intro q hq0 hqρ
    have h1 := Yt_cube_le_add hM hqρ.le x
    have hdiff : volume (cube ρ x \ cube q x) = v ρ - v q := by
      rw [measure_sdiff (SubaddCube.cube_subset_cube hqρ.le x)
        (isOpen_cube _ _).measurableSet.nullMeasurableSet (by rw [hv]; exact hvt _), hv, hv]
    have h2 : Yt W (cube q x) ξ ≤ S * v q := by
      have hle : cellAvg W q x ξ ≤ S := le_iSup₂_of_le q ⟨hq0, hqρ.trans hρδ⟩ le_rfl
      rw [hYv q hq0]
      gcongr
    calc Yt W (cube ρ x) ξ ≤ Yt W (cube q x) ξ + M * volume (cube ρ x \ cube q x) := h1
      _ ≤ S * v q + M * (v ρ - v q) := by rw [hdiff]; gcongr
  have hlt : S * v ρ < Yt W (cube ρ x) ξ := by
    rw [hYv ρ hρ, mul_comm S, mul_comm (cellAvg W ρ x ξ)]
    exact ENNReal.mul_lt_mul_right (hv0 ρ hρ) (hvt ρ) h
  have hvc : Continuous v := (ENNReal.continuous_pow N).comp ENNReal.continuous_ofReal
  have hB : Tendsto (fun t => S * v t + M * (v ρ - v t)) (𝓝 ρ)
      (𝓝 (S * v ρ + M * (v ρ - v ρ))) :=
    (ENNReal.Tendsto.const_mul (hvc.tendsto ρ) (Or.inr hS)).add
      (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.sub tendsto_const_nhds (hvc.tendsto ρ)
        (Or.inl (hvt ρ))) (Or.inr hMtop))
  rw [tsub_self, mul_zero, add_zero] at hB
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1
    ((hB.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hlt))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hl hρ : max l 0 < ρ)
  have hq0 : 0 < (q : ℝ) := (le_max_right _ _).trans_lt hq1
  exact absurd (key q hq0 hq2) (not_le.2 (hsub ⟨(le_max_left _ _).trans_lt hq1, hq2⟩))

/-- The `limsup` defining `𝒴_loc` can be computed along rational radii. -/
theorem Ytloc_eq_iInf_iSup_rat {W : Sp N → Mat m N → ℝ≥0∞} (x : Sp N) (ξ : Mat m N)
    (hξ : (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ y, W y ξ ≤ M) ∨ ∀ ρ : ℝ, 0 < ρ → cellAvg W ρ x ξ = ⊤) :
    Ytloc W x ξ = ⨅ n : ℕ, ⨆ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1)),
      cellAvg W q x ξ := by
  have hb : (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ => True) (fun n => Ioo 0 (1 / ((n : ℝ) + 1))) :=
    (nhdsGT_basis (0 : ℝ)).to_hasBasis
      (fun δ hδ => by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        exact ⟨n, trivial, Ioo_subset_Ioo_right hn.le⟩)
      (fun n _ => ⟨1 / ((n : ℝ) + 1), by positivity, subset_rfl⟩)
  change limsup (fun ρ => cellAvg W ρ x ξ) (𝓝[>] 0) = _
  rw [hb.limsup_eq_iInf_iSup]
  refine iInf_congr fun n => ?_
  rw [iInf_pos trivial]
  refine le_antisymm (iSup₂_le fun ρ hρ => ?_)
    (iSup₂_le fun q hq => le_iSup₂_of_le (q : ℝ) hq le_rfl)
  rcases hξ with ⟨M, hMt, hM⟩ | htop
  · exact cellAvg_le_iSup_rat hMt hM x hρ.1 hρ.2
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    rw [htop ρ hρ.1]
    exact le_iSup₂_of_le q ⟨hq1, hq2⟩ (htop q hq1).ge

/-- Joint measurability of `𝒴_loc W` from that of the normalized cell energies at rational radii. -/
theorem measurable_Ytloc_of_cellAvg {W : Sp N → Mat m N → ℝ≥0∞}
    (hξ : ∀ x ξ, (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ y, W y ξ ≤ M) ∨ ∀ ρ : ℝ, 0 < ρ → cellAvg W ρ x ξ = ⊤)
    (hmeas : ∀ q : ℚ, 0 < (q : ℝ) →
      Measurable fun p : Sp N × Mat m N => cellAvg W q p.1 p.2) :
    Measurable (uncurry (Ytloc W)) := by
  have e : uncurry (Ytloc W) = fun p : Sp N × Mat m N => ⨅ n : ℕ,
      ⨆ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1)), cellAvg W q p.1 p.2 := by
    funext p
    exact Ytloc_eq_iInf_iSup_rat p.1 p.2 (hξ p.1 p.2)
  rw [e]
  refine Measurable.iInf fun n => Measurable.iSup fun q => ?_
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1)
  · simp only [ciSup_pos hq]
    exact hmeas q hq.1
  · simp only [hq, iSup_false]
    exact measurable_const

/-- Translation of the affine Dirichlet problem: `𝒴 W(U,ξ) = 𝒴 W(·+a)((·+a)⁻¹U, ξ)`. -/
theorem Yt_translate (W : Sp N → Mat m N → ℝ≥0∞) (U : Set (Sp N)) (a : Sp N) (ξ : Mat m N) :
    Yt (fun y => W (y + a)) ((· + a) ⁻¹' U) ξ = Yt W U ξ := by
  have key : ∀ (W : Sp N → Mat m N → ℝ≥0∞) (U : Set (Sp N)) (a : Sp N),
      Yt (fun y => W (y + a)) ((· + a) ⁻¹' U) ξ ≤ Yt W U ξ := by
    intro W U a
    refine le_iInf₂ fun φ hφ => (iInf₂_le _ (comp_add_mem_Aff0 hφ a)).trans (le_of_eq ?_)
    have hmp := measurePreserving_add_right (volume : Measure (Sp N)) a
    have hemb : MeasurableEmbedding (fun y : Sp N => y + a) :=
      (MeasurableEquiv.addRight a).measurableEmbedding
    simp_rw [fderiv_comp_add_right]
    exact hmp.setLIntegral_comp_preimage_emb hemb (fun y => W y (ξ + fderiv ℝ φ y)) U
  refine le_antisymm (key W U a) ?_
  have h := key (fun y => W (y + a)) ((· + a) ⁻¹' U) (-a)
  simp only [neg_add_cancel_right] at h
  rwa [← preimage_comp, show ((· + a) ∘ (· + -a) : Sp N → Sp N) = id from
    funext fun y => neg_add_cancel_right y a, preimage_id] at h

theorem preimage_add_cube (q : ℝ) (x : Sp N) : (· + x) ⁻¹' cube q x = cube q 0 := by
  ext y
  simp only [cube, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ioo, Pi.add_apply,
    Pi.zero_apply, zero_sub, zero_add]
  exact forall_congr' fun i => by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- `x ↦ ∫_V a(z + x) dz` is continuous for `a` bounded measurable and `V` bounded open with
`|∂V| = 0` (dominated convergence after the change of variables `y = z + x`). -/
theorem continuous_setLIntegral_comp_add {a : Sp N → ℝ} (ham : Measurable a) {A : ℝ}
    (haA : ∀ y, a y ≤ A) {V : Set (Sp N)} (hVo : IsOpen V) (hVb : Bornology.IsBounded V)
    (hVf : volume (frontier V) = 0) :
    Continuous fun x => ∫⁻ z in V, ENNReal.ofReal (a (z + x)) := by
  have hF : ∀ x, ∫⁻ z in V, ENNReal.ofReal (a (z + x)) =
      ∫⁻ y, ((· + -x) ⁻¹' V).indicator (fun y => ENNReal.ofReal (a y)) y := by
    intro x
    rw [lintegral_indicator ((hVo.preimage (continuous_add_const _)).measurableSet)]
    have hmp := measurePreserving_add_right (volume : Measure (Sp N)) x
    have hemb : MeasurableEmbedding (fun y : Sp N => y + x) :=
      (MeasurableEquiv.addRight x).measurableEmbedding
    have e : (fun y => y + x) ⁻¹' ((fun y => y + -x) ⁻¹' V) = V := by
      ext z
      simp
    have h := hmp.setLIntegral_comp_preimage_emb hemb (fun y => ENNReal.ofReal (a y))
      ((· + -x) ⁻¹' V)
    rw [e] at h
    exact h
  simp_rw [hF]
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨R, hR⟩ := hVb.subset_closedBall 0
  set B : Set (Sp N) := Metric.closedBall 0 (R + ‖x₀‖ + 1)
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator fun _ => ENNReal.ofReal A)
    (Eventually.of_forall fun x => (ham.ennreal_ofReal).indicator
      ((hVo.preimage (continuous_add_const _)).measurableSet)) ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ (· + -x) ⁻¹' V
    · have hyB : y ∈ B := by
        have h1 := hR hy
        simp only [B, Metric.mem_closedBall, dist_zero_right] at h1 ⊢
        rw [Metric.mem_ball, dist_eq_norm] at hx
        have h2 : ‖y‖ ≤ ‖y + -x‖ + ‖x‖ := by
          calc ‖y‖ = ‖(y + -x) + x‖ := by rw [neg_add_cancel_right]
            _ ≤ _ := norm_add_le _ _
        have h3 : ‖x‖ ≤ ‖x₀‖ + 1 := by
          have := norm_le_norm_add_norm_sub' x x₀
          linarith
        linarith
      rw [indicator_of_mem hy, indicator_of_mem hyB]
      exact ENNReal.ofReal_le_ofReal (haA y)
    · rw [indicator_of_notMem hy]
      exact zero_le
  · rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet, setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  · have hnull : volume ((· + -x₀) ⁻¹' frontier V) = 0 := by
      rw [measure_preimage_add_right]; exact hVf
    refine measure_mono_null (fun y hy => ?_) hnull
    simp only at hy
    by_contra hyf
    apply hy
    by_cases hyV : y + -x₀ ∈ V
    · have hev : ∀ᶠ x in 𝓝 x₀, y + -x ∈ V :=
        ((continuous_const.add continuous_neg).tendsto x₀).eventually (hVo.mem_nhds hyV)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with x hx
      rw [indicator_of_mem (show y ∈ (· + -x) ⁻¹' V from hx),
        indicator_of_mem (show y ∈ (· + -x₀) ⁻¹' V from hyV)]
    · have hyc : y + -x₀ ∉ closure V := fun h =>
        hyf ⟨h, by rwa [hVo.interior_eq]⟩
      have hev : ∀ᶠ x in 𝓝 x₀, y + -x ∉ closure V :=
        ((continuous_const.add continuous_neg).tendsto x₀).eventually
          (isClosed_closure.isOpen_compl.mem_nhds hyc)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with x hx
      rw [indicator_of_notMem (show y ∉ (· + -x) ⁻¹' V from fun h => hx (subset_closure h)),
        indicator_of_notMem (show y ∉ (· + -x₀) ⁻¹' V from hyV)]

/-- `(x, ξ) ↦ g(x) f(ξ)` is upper semicontinuous for `f` upper semicontinuous and `g` continuous
with values in `]0,∞[`. -/
theorem upperSemicontinuous_mul_of_continuous {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : β → ℝ≥0∞} (hf : UpperSemicontinuous f) {g : α → ℝ≥0∞}
    (hg : Continuous g) (hg0 : ∀ x, g x ≠ 0) (hgt : ∀ x, g x ≠ ⊤) :
    UpperSemicontinuous fun p : α × β => g p.1 * f p.2 := by
  intro p₀ y hy
  change g p₀.1 * f p₀.2 < y at hy
  have hf0 : f p₀.2 ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (hg0 _)] at hy
    exact not_top_lt hy
  have h1 : Tendsto (fun δ : ℝ≥0 => (δ : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
    simpa using ENNReal.continuous_coe.tendsto (0 : ℝ≥0)
  have ht : Tendsto (fun δ : ℝ≥0 => (g p₀.1 + δ) * (f p₀.2 + δ)) (𝓝 0)
      (𝓝 ((g p₀.1 + 0) * (f p₀.2 + 0))) :=
    ENNReal.Tendsto.mul (tendsto_const_nhds.add h1) (Or.inr (by simpa using hf0))
      (tendsto_const_nhds.add h1) (Or.inr (by simpa using hgt _))
  simp only [add_zero] at ht
  obtain ⟨δ, hδy, hδ0⟩ := ((ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hy)).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ≥0))) |>.exists
  have hδ : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hg' : ∀ᶠ p in 𝓝 p₀, g p.1 < g p₀.1 + δ :=
    (hg.continuousAt.comp continuous_fst.continuousAt).eventually
      (gt_mem_nhds (ENNReal.lt_add_right (hgt _) hδ))
  have hf' : ∀ᶠ p in 𝓝 p₀, f p.2 < f p₀.2 + δ :=
    (continuous_snd.tendsto p₀).eventually (hf p₀.2 _ (ENNReal.lt_add_right hf0 hδ))
  filter_upwards [hg', hf'] with p hp1 hp2
  exact (mul_le_mul' hp1.le hp2.le).trans_lt hδy

/-- For `W = aH`, the cell energy at a fixed radius is jointly upper semicontinuous in `(x, ξ)`. -/
theorem upperSemicontinuous_Yt_prodW {a : Sp N → ℝ} {A : ℝ} {H : Mat m N → ℝ≥0∞}
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (ham : Measurable a) (hHusc : UpperSemicontinuous H)
    (q : ℝ) :
    UpperSemicontinuous fun p : Sp N × Mat m N => Yt (prodW a H) (cube q p.1) p.2 := by
  have e : (fun p : Sp N × Mat m N => Yt (prodW a H) (cube q p.1) p.2) = fun p =>
      ⨅ φ ∈ (Aff0 (cube q (0 : Sp N)) : Set (Sp N → Tgt m)),
        ∫⁻ z in cube q 0, ENNReal.ofReal (a (z + p.1)) * H (p.2 + fderiv ℝ φ z) := by
    funext p
    rw [← Yt_translate (prodW a H) (cube q p.1) p.1 p.2, preimage_add_cube]
    rfl
  rw [e]
  refine upperSemicontinuous_iInf fun φ => upperSemicontinuous_iInf fun hφ => ?_
  obtain ⟨K, n, V, η, -, -, hVo, hVU, hVd, hVf, hVc, hφV⟩ := Aff0.data hφ
  have hsplit : (fun p : Sp N × Mat m N =>
      ∫⁻ z in cube q 0, ENNReal.ofReal (a (z + p.1)) * H (p.2 + fderiv ℝ φ z)) =
      fun p => ∑ i, (∫⁻ z in V i, ENNReal.ofReal (a (z + p.1))) * H (p.2 + η i) := by
    funext p
    rw [lintegral_eq_sum_pieces_fintype hVo hVU hVd hVc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet
      (g := fun z => ENNReal.ofReal (a (z + p.1)) * H (p.2 + η i))
      (fun z hz => by rw [(hφV i z hz).fderiv])]
    exact lintegral_mul_const _ (ham.comp (measurable_id.add_const _)).ennreal_ofReal
  rw [hsplit]
  refine upperSemicontinuous_sum fun i _ => ?_
  have hVb : Bornology.IsBounded (V i) := (isBounded_cube q (0 : Sp N)).subset (hVU i)
  by_cases hV0 : volume (V i) = 0
  · have h0 : ∀ x : Sp N, ∫⁻ z in V i, ENNReal.ofReal (a (z + x)) = 0 := fun x => by
      rw [Measure.restrict_eq_zero.2 hV0, lintegral_zero_measure]
    simp only [h0, zero_mul]
    exact upperSemicontinuous_const
  have hfr : volume (frontier (V i)) = 0 := by
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null (hVf i) (volume_frontier_cube q (0 : Sp N)))
    by_cases hyQ : y ∈ cube q (0 : Sp N)
    · exact Or.inl ⟨hyQ, hy⟩
    · refine Or.inr ⟨closure_mono (hVU i) hy.1, ?_⟩
      rwa [(isOpen_cube q 0).interior_eq]
  have hcont := continuous_setLIntegral_comp_add ham (fun y => (ha y).2) (hVo i) hVb hfr
  refine upperSemicontinuous_mul_of_continuous (hHusc.comp (continuous_add_const (η i)))
    hcont (fun x => ?_) (fun x => ?_)
  · refine (lt_of_lt_of_le (pos_iff_ne_zero.2 hV0) ?_).ne'
    calc volume (V i) = ∫⁻ _ in V i, 1 := by rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ z in V i, ENNReal.ofReal (a (z + x)) :=
          lintegral_mono fun z => ENNReal.one_le_ofReal.2 (ha _).1
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := A))
      (hVb.measure_lt_top (μ := volume)).ne) ?_
    calc ∫⁻ z in V i, ENNReal.ofReal (a (z + x)) ≤ ∫⁻ _ in V i, ENNReal.ofReal A :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (ha _).2
      _ = ENNReal.ofReal A * volume (V i) := setLIntegral_const _ _

/-- **(H6) for `W = aH`.** For `a` measurable with `1 ≤ a ≤ A`, `H` upper semicontinuous, and
`G` convex with `G ≤ H ≤ γ(1+G)`, the function `(x,ξ) ↦ 𝒴_loc W(x,ξ)` is jointly Borel
measurable (no modification on a null set). -/
theorem prodW_measurable_Ytloc {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} {a : Sp N → ℝ} {A : ℝ}
    (hG : ConvexENN G) (hGH : ∀ ξ, G ξ ≤ H ξ) (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (ham : Measurable a) (hHusc : UpperSemicontinuous H) :
    Measurable (uncurry (Ytloc (prodW a H))) := by
  refine measurable_Ytloc_of_cellAvg (fun x ξ => ?_) (fun q hq => ?_)
  · by_cases hH : H ξ = ⊤
    · refine Or.inr fun ρ hρ => ?_
      have hGt : G ξ = ⊤ := by
        by_contra hGt
        exact (ENNReal.mul_ne_top ENNReal.coe_ne_top
          (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hGt⟩)) (top_le_iff.1 (hH ▸ hHG ξ))
      have hv0 : volume (cube ρ x) ≠ 0 := (volume_cube_pos hρ x).ne'
      have hlow := (prodW_setGrowth (γ := γ) hG hGH hHG ha ξ (cube ρ x) (isOpen_cube ρ x)
        (isBounded_cube ρ x)).1
      rw [hGt, ENNReal.coe_one, one_mul, ENNReal.mul_top hv0, top_le_iff] at hlow
      simp only [cellAvg, hlow]
      exact ENNReal.top_div_of_ne_top (volume_cube_ne_top ρ x)
    · refine Or.inl ⟨ENNReal.ofReal A * H ξ, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH,
        fun y => ?_⟩
      simp only [prodW]
      gcongr
      exact (ha y).2
  · have h := (upperSemicontinuous_Yt_prodW (m := m) ha ham hHusc q).measurable
    simp only [cellAvg, volume_cube]
    exact h.div_const _

/-- **Theorem `th:product` (ii), (H8)**, without the measurability hypothesis on `𝒴_loc W`
(now `prodW_measurable_Ytloc`); no cited hypothesis. -/
theorem th_product_H8 [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} {a : Sp N → ℝ} {A : ℝ}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) (hG0 : (0 : Mat m N) ∈ dom G)
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hγ : 0 < γ) (hHusc : UpperSemicontinuous H) (hGH : ∀ ξ, G ξ ≤ H ξ)
    (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (hHrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ)
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (halsc : LowerSemicontinuous a)
    (haper : ∀ (z : Fin N → ℤ) x, a (x + fun i => (z i : ℝ)) = a x)
    (ξ : Mat m N) :
    Zaff (Haff (Ytloc (prodW a H))) ξ ≤
      radial (Hp (ENNReal.ofReal p) (Ytloc (prodW a H))) ξ :=
  (th_product_ii (p := p) hG hGo hG0 hGsing hγ hHusc hGH hHG hHrad ha halsc haper).2.2.2.2.2.2
    (prodW_measurable_Ytloc hG hGH hHG ha halsc.measurable hHusc) ξ

/-- **Theorem `th:product` (iii)** without the measurability hypothesis on `𝒴_loc W` and without
cited hypothesis: `∫_Ω a(x/ε) H(∇u)` Γ-converges to `∫_Ω \widehat{ℋ(a 𝒵_aff H)}(∇u)`. -/
theorem th_product_iii_unconditional [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (N : ℝ) < p) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω)
    {G H : Mat m N → ℝ≥0∞} {γ : ℝ≥0} {a : Sp N → ℝ} {A : ℝ}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) (hG0 : (0 : Mat m N) ∈ dom G)
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hγ : 0 < γ) (hHusc : UpperSemicontinuous H) (hGH : ∀ ξ, G ξ ≤ H ξ)
    (hHG : ∀ ξ, H ξ ≤ γ * (1 + G ξ))
    (hHrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ξ, H (t • ξ) ≤ H ξ)
    (ha : ∀ x, 1 ≤ a x ∧ a x ≤ A) (halsc : LowerSemicontinuous a)
    (haper : ∀ (z : Fin N → ℤ) x, a (x + fun i => (z i : ℝ)) = a x)
    {c₀ : ℝ≥0} (hc₀ : 0 < c₀) (hcoer : ∀ ξ, ENNReal.ofReal (c₀ * ‖ξ‖ ^ p) ≤ G ξ) :
    IsCoercive p c₀ (Ytloc (prodW a H)) ∧
      Whom p (prodW a H) =
        radial (Hp (ENNReal.ofReal p) (fun x ξ => ENNReal.ofReal (a x) * Zaff H ξ)) ∧
      GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun (prodW a H))
        (intHom (Whom p (prodW a H))) :=
  th_product_iii p hp hΩ hG hGo hG0 hGsing hγ hHusc hGH hHG hHrad ha halsc haper hc₀ hcoer
    (prodW_measurable_Ytloc hG hGH hHG ha halsc.measurable hHusc)

end Homogenization
