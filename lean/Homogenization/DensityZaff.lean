import Homogenization.DensityHaff
import Homogenization.SepConvex

/-!
# The upper bound in Proposition `prop:densityZaff`

For `L : 𝕄 → [0,∞]`, `A` bounded open and `ξ ∈ 𝕄`, there are `φ_k ∈ Aff₀(A)`, `φ_k → 0`
uniformly, with `limsup_k ∫_A L(ξ + ∇φ_k) ≤ |A| 𝒵_aff L(ξ)`. This is the only half of
Proposition `prop:densityZaff` ([oah-jpm11, Proposition 3.17]) used in Step 3.

Proof: by the Vitali covering theorem, `A` is covered up to a null set by countably many disjoint
cubes `Qₐ ⊂ A` of side `≤ 2δ`; a near-optimal `φ_η ∈ Aff₀(Y)` is transplanted on each of them by
translation and rescaling. The glued function is Lipschitz (`lipschitzWith_tsum_cells`), has the
finitely many gradient values of `φ_η`, and energy `|A| ∫_Y L(ξ + ∇φ_η)`. Note that the pieces of
the glued function are countable unions of open sets: what is finite is the number of values of the
gradient, as allowed by the definition of `Aff`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### Countable gluing of Lipschitz functions with disjoint supports -/

section Gluing

variable {ι : Type*} {O : ι → Set (Sp N)} {f : ι → Sp N → Tgt m}

theorem tsum_cells_of_mem (hOd : Pairwise fun i j => Disjoint (O i) (O j))
    (hf0 : ∀ i, ∀ y ∉ O i, f i y = 0) {i : ι} {x : Sp N} (hx : x ∈ O i) :
    ∑' k, f k x = f i x :=
  tsum_eq_single i fun k hk => hf0 k x fun h => (hOd hk).le_bot ⟨h, hx⟩

theorem tsum_cells_of_notMem (hf0 : ∀ i, ∀ y ∉ O i, f i y = 0) {x : Sp N}
    (hx : ∀ i, x ∉ O i) : ∑' k, f k x = 0 := by
  rw [show (fun k => f k x) = fun _ => 0 from funext fun k => hf0 k x (hx k), tsum_zero]

theorem tsum_cells_of_mem_closure (hOo : ∀ i, IsOpen (O i))
    (hOd : Pairwise fun i j => Disjoint (O i) (O j)) (hf0 : ∀ i, ∀ y ∉ O i, f i y = 0)
    {i : ι} {x : Sp N} (hx : x ∈ closure (O i)) (hx' : x ∉ O i) : ∑' k, f k x = 0 := by
  refine tsum_cells_of_notMem hf0 fun j hj => ?_
  by_cases hij : i = j
  · exact hx' (hij ▸ hj)
  · exact ((hOd hij).closure_left (hOo j)).le_bot ⟨hx, hj⟩

/-- A segment from a point of an open set `U` to a point outside `U` meets `closure U ∖ U`. -/
theorem exists_mem_segment_closure_notMem {U : Set (Sp N)} (hU : IsOpen U) {x y : Sp N}
    (hx : x ∈ U) (hy : y ∉ U) : ∃ b ∈ segment ℝ x y, b ∈ closure U ∧ b ∉ U := by
  by_contra hcon
  push Not at hcon
  have hpre := (convex_segment x y).isPreconnected
  have hsub : segment ℝ x y ⊆ U ∪ (closure U)ᶜ := fun b hb => by
    by_cases h : b ∈ closure U
    · exact Or.inl (hcon b hb h)
    · exact Or.inr h
  obtain ⟨b, -, hbU, hbV⟩ := hpre U (closure U)ᶜ hU isClosed_closure.isOpen_compl hsub
    ⟨x, left_mem_segment ℝ x y, hx⟩
    ⟨y, right_mem_segment ℝ x y, fun h => hy (hcon y (right_mem_segment ℝ x y) h)⟩
  exact hbV (subset_closure hbU)

theorem dist_le_of_mem_segment {x y b : Sp N} (hb : b ∈ segment ℝ x y) :
    dist x b ≤ dist x y := by
  have := dist_add_dist_of_mem_segment hb
  linarith [dist_nonneg (x := b) (y := y)]

/-- **Countable gluing.** If the `fᵢ` are `K`-Lipschitz and vanish outside pairwise disjoint open
sets `Oᵢ`, then `∑ᵢ fᵢ` is `K`-Lipschitz. -/
theorem lipschitzWith_tsum_cells (hOo : ∀ i, IsOpen (O i))
    (hOd : Pairwise fun i j => Disjoint (O i) (O j)) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hf0 : ∀ i, ∀ y ∉ O i, f i y = 0) :
    LipschitzWith K fun x => ∑' i, f i x := by
  set F : Sp N → Tgt m := fun x => ∑' i, f i x
  -- from a point `x ∈ Oᵢ` to a point `b` of `closure Oᵢ ∖ Oᵢ` on the segment towards `y`
  have aux : ∀ i x y, x ∈ O i → y ∉ O i → ∃ b ∈ segment ℝ x y, b ∈ closure (O i) ∧ b ∉ O i ∧
      F b = 0 ∧ dist (F x) (F b) ≤ K * dist x b := by
    intro i x y hx hy
    obtain ⟨b, hb, hbc, hbO⟩ := exists_mem_segment_closure_notMem (hOo i) hx hy
    have hFb : F b = 0 := tsum_cells_of_mem_closure hOo hOd hf0 hbc hbO
    refine ⟨b, hb, hbc, hbO, hFb, ?_⟩
    have hFx : F x = f i x := tsum_cells_of_mem hOd hf0 hx
    rw [hFx, hFb, ← hf0 i b hbO]
    exact (hf i).dist_le_mul x b
  have claim : ∀ x y, (∃ i, x ∈ O i) → dist (F x) (F y) ≤ K * dist x y := by
    rintro x y ⟨i, hx⟩
    by_cases hy : y ∈ O i
    · rw [show F x = f i x from tsum_cells_of_mem hOd hf0 hx,
        show F y = f i y from tsum_cells_of_mem hOd hf0 hy]
      exact (hf i).dist_le_mul x y
    obtain ⟨b, hb, hbc, hbO, hFb, hxb⟩ := aux i x y hx hy
    have hbx : dist x b + dist b y = dist x y := dist_add_dist_of_mem_segment hb
    by_cases hy' : ∃ j, y ∈ O j
    · obtain ⟨j, hj⟩ := hy'
      have hbj : b ∉ O j := by
        intro h
        by_cases hij : i = j
        · exact hbO (hij ▸ h)
        · exact ((hOd hij).closure_left (hOo j)).le_bot ⟨hbc, h⟩
      obtain ⟨b', hb', -, -, hFb', hyb'⟩ := aux j y b hj hbj
      have hb'y : dist y b' + dist b' b = dist y b := dist_add_dist_of_mem_segment hb'
      calc dist (F x) (F y) ≤ dist (F x) (F b) + dist (F b) (F y) := dist_triangle _ _ _
        _ = dist (F x) (F b) + dist (F y) (F b') := by rw [hFb, hFb', dist_comm (0 : Tgt m) (F y)]
        _ ≤ K * dist x b + K * dist y b' := add_le_add hxb hyb'
        _ ≤ K * dist x y := by
            rw [← mul_add]
            refine mul_le_mul_of_nonneg_left ?_ K.2
            linarith [dist_nonneg (x := b') (y := b), dist_comm b y]
    · push Not at hy'
      have hFy : F y = 0 := tsum_cells_of_notMem hf0 hy'
      calc dist (F x) (F y) = dist (F x) (F b) := by rw [hFy, hFb]
        _ ≤ K * dist x b := hxb
        _ ≤ K * dist x y := mul_le_mul_of_nonneg_left (dist_le_of_mem_segment hb) K.2
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  by_cases hx : ∃ i, x ∈ O i
  · exact claim x y hx
  by_cases hy : ∃ i, y ∈ O i
  · rw [dist_comm, dist_comm x]; exact claim y x hy
  push Not at hx hy
  rw [show F x = 0 from tsum_cells_of_notMem hf0 hx, show F y = 0 from tsum_cells_of_notMem hf0 hy,
    dist_self]
  exact mul_nonneg K.2 dist_nonneg

end Gluing

/-! ### Copies of a cell corrector on the cube `Q_ρ(c)` -/

section Copy

/-- The affine map `x ↦ (x - c)/ρ` sending `Q_ρ(c)` onto `Y`. -/
noncomputable def affMap (ρ : ℝ) (c x : Sp N) : Sp N := ρ⁻¹ • x + -(ρ⁻¹ • c)

/-- The copy `x ↦ ρ φ((x - c)/ρ)`. -/
noncomputable def zcopy (φ : Sp N → Tgt m) (ρ : ℝ) (c : Sp N) (x : Sp N) : Tgt m :=
  (ρ⁻¹)⁻¹ • φ (affMap ρ c x)

variable {ρ : ℝ} (hρ : 0 < ρ) (c : Sp N)
include hρ

omit hρ in
theorem preimage_affMap (S : Set (Sp N)) :
    affMap ρ c ⁻¹' S = (ρ⁻¹ • ·) ⁻¹' ((· + -(ρ⁻¹ • c)) ⁻¹' S) := rfl

theorem preimage_affMap_cube : affMap ρ c ⁻¹' cube 1 0 = cube ρ c := by
  rw [preimage_affMap, ← cube_eq_preimage_add, preimage_smul_cube (inv_pos.2 hρ), one_div,
    inv_inv, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]

theorem volume_preimage_affMap (S : Set (Sp N)) :
    volume (affMap ρ c ⁻¹' S) = ENNReal.ofReal (ρ ^ N) * volume S := by
  rw [preimage_affMap, Measure.addHaar_preimage_smul _ (inv_ne_zero hρ.ne'),
    measure_preimage_add_right, finrank_Sp, inv_pow, inv_inv, abs_of_pos (pow_pos hρ N)]

/-- `affMap` as a homeomorphism. -/
noncomputable def affHomeo : Sp N ≃ₜ Sp N :=
  (Homeomorph.smulOfNeZero ρ⁻¹ (inv_ne_zero hρ.ne')).trans (Homeomorph.addRight (-(ρ⁻¹ • c)))

theorem affHomeo_apply (x : Sp N) : affHomeo hρ c x = affMap ρ c x := rfl

theorem frontier_preimage_affMap (S : Set (Sp N)) :
    frontier (affMap ρ c ⁻¹' S) = affMap ρ c ⁻¹' frontier S :=
  ((affHomeo hρ c).preimage_frontier S).symm

theorem continuous_affMap : Continuous (affMap ρ c) := (affHomeo hρ c).continuous

theorem zcopy_lipschitz {φ : Sp N → Tgt m} {K : ℝ≥0} (hK : LipschitzWith K φ) :
    LipschitzWith K (zcopy φ ρ c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [zcopy, inv_inv, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
  have h := hK.dist_le_mul (affMap ρ c x) (affMap ρ c y)
  have hxy : dist (affMap ρ c x) (affMap ρ c y) = ρ⁻¹ * dist x y := by
    simp only [affMap, dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
  rw [hxy] at h
  calc ρ * dist (φ (affMap ρ c x)) (φ (affMap ρ c y)) ≤ ρ * (K * (ρ⁻¹ * dist x y)) :=
        mul_le_mul_of_nonneg_left h hρ.le
    _ = K * dist x y := by field_simp

theorem zcopy_eq_zero {φ : Sp N → Tgt m} (h0 : ∀ y ∉ cube 1 (0 : Sp N), φ y = 0) {x : Sp N}
    (hx : x ∉ cube ρ c) : zcopy φ ρ c x = 0 := by
  have : affMap ρ c x ∉ cube 1 (0 : Sp N) := fun h => hx (by
    rw [← preimage_affMap_cube hρ c]; exact h)
  simp [zcopy, h0 _ this]

theorem zcopy_hasFDerivAt {φ : Sp N → Tgt m} {ζ : Mat m N} {x : Sp N}
    (h : HasFDerivAt φ ζ (affMap ρ c x)) : HasFDerivAt (zcopy φ ρ c) ζ x := by
  have h1 : HasFDerivAt (affMap ρ c) (ρ⁻¹ • ContinuousLinearMap.id ℝ (Sp N)) x :=
    ((hasFDerivAt_id x).const_smul ρ⁻¹).add_const _
  have h2 := (h.comp x h1).const_smul (ρ⁻¹)⁻¹
  have heq : (ρ⁻¹)⁻¹ • ζ.comp (ρ⁻¹ • ContinuousLinearMap.id ℝ (Sp N)) = ζ := by
    ext v k
    simp [smul_smul, mul_inv_cancel₀ hρ.ne']
  exact h2.congr_fderiv heq

/-- An affine copy of an `Aff₀` function is again `Aff₀` on the copied domain. -/
theorem zcopy_mem_Aff0 {B : Set (Sp N)} {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 B) :
    zcopy φ ρ c ∈ Aff0 (affMap ρ c ⁻¹' B) := by
  obtain ⟨K, n, V, ζ, hK, h0, hVo, hVU, hVd, hVf, hVc, hφV⟩ := Aff0.data hφ
  have hnull : ∀ S : Set (Sp N), volume S = 0 → volume (affMap ρ c ⁻¹' S) = 0 :=
    fun S hS => by rw [volume_preimage_affMap hρ c, hS, mul_zero]
  refine ⟨⟨K, zcopy_lipschitz hρ c hK⟩, ?_,
    ⟨⟨K, (zcopy_lipschitz hρ c hK).lipschitzOnWith⟩, n,
    (fun i => affMap ρ c ⁻¹' V i), ζ, fun i => (hVo i).preimage (continuous_affMap hρ c),
    fun i => preimage_mono (hVU i), fun i j hij => (hVd hij).preimage _, fun i => ?_, ?_,
    fun i x hx => zcopy_hasFDerivAt hρ c (hφV i (affMap ρ c x) hx)⟩⟩
  · intro x hx
    simp only [zcopy]
    rw [h0 (affMap ρ c x) hx, smul_zero]
  · have hfr : frontier (affMap ρ c ⁻¹' V i) = affMap ρ c ⁻¹' frontier (V i) :=
      frontier_preimage_affMap hρ c (V i)
    rw [hfr, ← preimage_inter]
    exact hnull _ (hVf i)
  · rw [← preimage_iUnion, ← preimage_sdiff]
    exact hnull _ hVc

theorem fderiv_zcopy (φ : Sp N → Tgt m) (x : Sp N) :
    fderiv ℝ (zcopy φ ρ c) x = fderiv ℝ φ (affMap ρ c x) := by
  have := fderiv_rescale (fun y => φ (y + -(ρ⁻¹ • c))) (inv_ne_zero hρ.ne') x
  rw [show zcopy φ ρ c = fun x => (ρ⁻¹)⁻¹ • (fun y => φ (y + -(ρ⁻¹ • c))) (ρ⁻¹ • x)
    from rfl, this, fderiv_comp_add_right]
  rfl

theorem setLIntegral_comp_affMap {B : Set (Sp N)} (hB : MeasurableSet B) (F : Sp N → ℝ≥0∞) :
    ∫⁻ x in affMap ρ c ⁻¹' B, F (affMap ρ c x) = ENNReal.ofReal (ρ ^ N) * ∫⁻ y in B, F y := by
  set a : Sp N := -(ρ⁻¹ • c)
  have hpre : MeasurableSet ((· + a) ⁻¹' B : Set (Sp N)) := (measurable_add_const a) hB
  have h1 := setLIntegral_comp_smul (inv_ne_zero hρ.ne') hpre (fun y => F (y + a))
  rw [inv_pow, inv_inv, abs_of_pos (pow_pos hρ N)] at h1
  change ∫⁻ x in (ρ⁻¹ • ·) ⁻¹' ((· + a) ⁻¹' B), (fun y => F (y + a)) (ρ⁻¹ • x) = _
  rw [h1]
  congr 1
  exact (measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding F B

theorem lintegral_zcopy (L : Mat m N → ℝ≥0∞) (φ : Sp N → Tgt m) (ξ : Mat m N) :
    ∫⁻ x in cube ρ c, L (ξ + fderiv ℝ (zcopy φ ρ c) x) =
      ENNReal.ofReal (ρ ^ N) * ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ φ y) := by
  rw [← setLIntegral_comp_affMap hρ c (isOpen_cube 1 0).measurableSet
    (fun y => L (ξ + fderiv ℝ φ y)), preimage_affMap_cube hρ c]
  simp_rw [fderiv_zcopy hρ c φ]

/-- Change of variables for a zero-boundary corrector copied to an arbitrary measurable set. -/
theorem lintegral_zcopy_set {B : Set (Sp N)} (hB : MeasurableSet B)
    (L : Mat m N → ℝ≥0∞) (φ : Sp N → Tgt m) (ξ : Mat m N) :
    ∫⁻ x in affMap ρ c ⁻¹' B, L (ξ + fderiv ℝ (zcopy φ ρ c) x) =
      ENNReal.ofReal (ρ ^ N) * ∫⁻ y in B, L (ξ + fderiv ℝ φ y) := by
  rw [← setLIntegral_comp_affMap hρ c hB (fun y => L (ξ + fderiv ℝ φ y))]
  simp_rw [fderiv_zcopy hρ c φ]

end Copy

/-! ### The Vitali covering by cubes and the glued competitor -/

theorem ball_eq_cube {r : ℝ} (hr : 0 < r) (x : Sp N) : Metric.ball x r = cube (2 * r) x := by
  ext y
  rw [ball_pi x hr]
  simp only [cube, Set.mem_pi, mem_univ, true_implies, Metric.mem_ball, Real.dist_eq, mem_Ioo,
    abs_lt]
  exact forall_congr' fun i => by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Vitali covering of `A` by disjoint cubes of side `≤ 2δ`, up to a null set. -/
theorem exists_vitali_cells {A : Set (Sp N)} (hA : IsOpen A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : Set (Sp N × ℝ), u.Countable ∧ (∀ a ∈ u, 0 < a.2 ∧ a.2 ≤ δ ∧ cube (2 * a.2) a.1 ⊆ A) ∧
      (u.Pairwise fun a b => Disjoint (cube (2 * a.2) a.1) (cube (2 * b.2) b.1)) ∧
      volume (A \ ⋃ a ∈ u, cube (2 * a.2) a.1) = 0 := by
  set t : Set (Sp N × ℝ) := {a | 0 < a.2 ∧ a.2 ≤ δ ∧ Metric.closedBall a.1 a.2 ⊆ A}
  obtain ⟨u, hut, huc, hud, hcov⟩ := Vitali.exists_disjoint_covering_ae volume A t
    ((3 : ℝ≥0) ^ N) (fun a => a.2) (fun a => a.1) (fun a => Metric.closedBall a.1 a.2)
    (fun a _ => subset_rfl)
    (fun a ha => by
      rw [Real.volume_pi_closedBall _ (by linarith [ha.1]),
        Real.volume_pi_closedBall _ ha.1.le, Fintype.card_fin]
      refine le_of_eq ?_
      rw [show (2 * (3 * a.2)) ^ N = (3 : ℝ) ^ N * (2 * a.2) ^ N by
          rw [show 2 * (3 * a.2) = 3 * (2 * a.2) by ring, mul_pow],
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
      simp)
    (fun a ha => ⟨a.1, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self ha.1)⟩)
    (fun a _ => Metric.isClosed_closedBall)
    (fun x hx ε hε => by
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hA x hx
      refine ⟨(x, min (min ε δ) (ρ / 2)), ⟨by positivity, (min_le_left _ _).trans
        (min_le_right _ _), (Metric.closedBall_subset_ball ?_).trans hball⟩,
        (min_le_left _ _).trans (min_le_left _ _), rfl⟩
      exact (min_le_right _ _).trans_lt (by linarith))
  have hsub : ∀ a ∈ u, cube (2 * a.2) a.1 ⊆ Metric.closedBall a.1 a.2 := fun a ha => by
    rw [← ball_eq_cube (hut ha).1]; exact Metric.ball_subset_closedBall
  refine ⟨u, huc, fun a ha => ⟨(hut ha).1, (hut ha).2.1, (hsub a ha).trans (hut ha).2.2⟩,
    fun a ha b hb hab => (hud ha hb hab).mono (hsub a ha) (hsub b hb), ?_⟩
  refine measure_mono_null (t := (A \ ⋃ a ∈ u, Metric.closedBall a.1 a.2) ∪
    ⋃ a ∈ u, frontier (cube (2 * a.2) a.1)) ?_ (measure_union_null hcov
      ((measure_biUnion_null_iff huc).2 fun a _ => volume_frontier_cube _ _))
  rintro y ⟨hyA, hy⟩
  by_cases h : y ∈ ⋃ a ∈ u, Metric.closedBall a.1 a.2
  · obtain ⟨a, ha, hya⟩ := mem_iUnion₂.1 h
    refine Or.inr (mem_iUnion₂.2 ⟨a, ha, ?_⟩)
    rw [(isOpen_cube _ _).frontier_eq, ← ball_eq_cube (hut ha).1,
      closure_ball _ (hut ha).1.ne']
    exact ⟨hya, fun h' => hy (mem_iUnion₂.2 ⟨a, ha, by rwa [← ball_eq_cube (hut ha).1]⟩)⟩
  · exact Or.inl ⟨hyA, h⟩

/-- **The glued competitor.** For `φ ∈ Aff₀(Y)` and `δ > 0` there is `Φ ∈ Aff₀(A)` with
`‖Φ‖_∞ ≤ 2δ ‖φ‖_∞` and `∫_A L(ξ + ∇Φ) = |A| ∫_Y L(ξ + ∇φ)`. -/
theorem exists_vitali_competitor (L : Mat m N → ℝ≥0∞) {A : Set (Sp N)} (hA : IsOpen A)
    {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 (cube 1 (0 : Sp N))) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (ξ : Mat m N) :
    ∃ Φ ∈ (Aff0 A : Set (Sp N → Tgt m)), (∀ x, ‖Φ x‖ ≤ 2 * δ * M) ∧
      ∫⁻ x in A, L (ξ + fderiv ℝ Φ x) = volume A * ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ φ y) := by
  classical
  obtain ⟨K, n, V, ζ, hK, h0, hVo, hVU, hVd, hVf, hVc, hφV⟩ := Aff0.data hφ
  obtain ⟨u, huc, hu, hud, hcov⟩ := exists_vitali_cells hA hδ
  have : Countable u := huc.to_subtype
  set ρ : u → ℝ := fun a => 2 * a.1.2
  set cen : u → Sp N := fun a => a.1.1
  have hρ : ∀ a, 0 < ρ a := fun a => by have := (hu a.1 a.2).1; simp only [ρ]; positivity
  set O : u → Set (Sp N) := fun a => cube (ρ a) (cen a)
  have hOo : ∀ a, IsOpen (O a) := fun a => isOpen_cube _ _
  have hOA : ∀ a, O a ⊆ A := fun a => (hu a.1 a.2).2.2
  have hOd : Pairwise fun a b => Disjoint (O a) (O b) := fun a b hab =>
    hud a.2 b.2 fun e => hab (Subtype.ext e)
  have hcovO : volume (A \ ⋃ a, O a) = 0 := by
    rw [← hcov]; congr 1; rw [biUnion_eq_iUnion]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set f : u → Sp N → Tgt m := fun a => zcopy φ (ρ a) (cen a)
  have hf : ∀ a, LipschitzWith K (f a) := fun a => zcopy_lipschitz (hρ a) _ hK
  have hf0 : ∀ a, ∀ y ∉ O a, f a y = 0 := fun a y hy => zcopy_eq_zero (hρ a) _ h0 hy
  set Φ : Sp N → Tgt m := fun x => ∑' a, f a x
  have hΦLip : LipschitzWith K Φ := lipschitzWith_tsum_cells hOo hOd hf hf0
  have hΦloc : ∀ a, ∀ x ∈ O a, Φ =ᶠ[𝓝 x] f a := fun a x hx => by
    filter_upwards [(hOo a).mem_nhds hx] with z hz using tsum_cells_of_mem hOd hf0 hz
  set P : u → Fin n → Set (Sp N) := fun a l => affMap (ρ a) (cen a) ⁻¹' V l
  have hPO : ∀ a l, P a l ⊆ O a := fun a l => by
    change affMap (ρ a) (cen a) ⁻¹' V l ⊆ cube (ρ a) (cen a)
    rw [← preimage_affMap_cube (hρ a) (cen a)]; exact preimage_mono (hVU l)
  set W : Fin n → Set (Sp N) := fun l => ⋃ a, P a l
  have hOW : ∀ a l, O a ∩ W l ⊆ P a l := by
    rintro a l z ⟨hzO, hzW⟩
    obtain ⟨b, hb⟩ := mem_iUnion.1 hzW
    by_cases hab : a = b
    · exact hab ▸ hb
    · exact absurd (hPO b l hb) (Set.disjoint_left.1 (hOd hab) hzO)
  have hnull : ∀ a (S : Set (Sp N)), volume S = 0 →
      volume (affMap (ρ a) (cen a) ⁻¹' S) = 0 := fun a S hS => by
    rw [volume_preimage_affMap (hρ a), hS, mul_zero]
  refine ⟨Φ, ⟨⟨K, hΦLip⟩, fun y hy => tsum_cells_of_notMem hf0 fun a h => hy (hOA a h),
    ⟨K, hΦLip.lipschitzOnWith⟩, n, W, ζ, fun l => isOpen_iUnion fun a =>
      (hVo l).preimage (continuous_affMap (hρ a) _), fun l => iUnion_subset fun a =>
        (hPO a l).trans (hOA a), ?_, fun l => ?_, ?_, fun l y hy => ?_⟩, fun x => ?_, ?_⟩
  · -- disjointness of the pieces
    intro l l' hll'
    refine Set.disjoint_left.2 fun z hz hz' => ?_
    obtain ⟨a, ha⟩ := mem_iUnion.1 hz
    obtain ⟨b, hb⟩ := mem_iUnion.1 hz'
    by_cases hab : a = b
    · subst hab; exact (hVd hll').le_bot ⟨ha, hb⟩
    · exact (hOd hab).le_bot ⟨hPO a l ha, hPO b l' hb⟩
  · -- negligible boundaries
    refine measure_mono_null (t := (A \ ⋃ a, O a) ∪
      ⋃ a, affMap (ρ a) (cen a) ⁻¹' (cube 1 0 ∩ frontier (V l))) ?_
      (measure_union_null hcovO (measure_iUnion_null fun a => hnull a _ (hVf l)))
    rintro y ⟨hyA, hyf⟩
    by_cases hy : ∃ a, y ∈ O a
    · obtain ⟨a, ha⟩ := hy
      refine Or.inr (mem_iUnion.2 ⟨a, ?_, ?_⟩)
      · have : y ∈ affMap (ρ a) (cen a) ⁻¹' cube 1 0 := by
          rw [preimage_affMap_cube (hρ a)]; exact ha
        exact this
      · change y ∈ affMap (ρ a) (cen a) ⁻¹' frontier (V l)
        rw [← frontier_preimage_affMap (hρ a)]
        refine ⟨closure_mono (hOW a l) ((hOo a).inter_closure ⟨ha, frontier_subset_closure hyf⟩),
          fun hint => hyf.2 (interior_mono (subset_iUnion (fun b => P b l) a) hint)⟩
    · exact Or.inl ⟨hyA, fun h => hy (mem_iUnion.1 h)⟩
  · -- the pieces cover `A` up to a null set
    refine measure_mono_null (t := (A \ ⋃ a, O a) ∪
      ⋃ a, affMap (ρ a) (cen a) ⁻¹' (cube 1 0 \ ⋃ l, V l)) ?_
      (measure_union_null hcovO (measure_iUnion_null fun a => hnull a _ hVc))
    rintro y ⟨hyA, hyW⟩
    by_cases hy : ∃ a, y ∈ O a
    · obtain ⟨a, ha⟩ := hy
      refine Or.inr (mem_iUnion.2 ⟨a, ?_, fun h => hyW ?_⟩)
      · have : y ∈ affMap (ρ a) (cen a) ⁻¹' cube 1 0 := by
          rw [preimage_affMap_cube (hρ a)]; exact ha
        exact this
      · obtain ⟨l, hl⟩ := mem_iUnion.1 h
        exact mem_iUnion.2 ⟨l, mem_iUnion.2 ⟨a, hl⟩⟩
    · exact Or.inl ⟨hyA, fun h => hy (mem_iUnion.1 h)⟩
  · -- the gradient on the pieces
    obtain ⟨a, ha⟩ := mem_iUnion.1 hy
    exact (zcopy_hasFDerivAt (hρ a) (cen a) (hφV l _ ha)).congr_of_eventuallyEq
      (hΦloc a y (hPO a l ha))
  · -- the uniform bound
    by_cases hx : ∃ a, x ∈ O a
    · obtain ⟨a, ha⟩ := hx
      rw [show Φ x = f a x from tsum_cells_of_mem hOd hf0 ha]
      simp only [f, zcopy, inv_inv, norm_smul, Real.norm_eq_abs, abs_of_pos (hρ a)]
      have hρδ : ρ a ≤ 2 * δ := by have := (hu a.1 a.2).2.1; simp only [ρ]; linarith
      calc ρ a * ‖φ (affMap (ρ a) (cen a) x)‖ ≤ ρ a * M :=
            mul_le_mul_of_nonneg_left (hM _) (hρ a).le
        _ ≤ 2 * δ * M := mul_le_mul_of_nonneg_right hρδ hM0
    · push Not at hx
      rw [show Φ x = 0 from tsum_cells_of_notMem hf0 hx, norm_zero]
      positivity
  · -- the energy
    have hAO : A =ᵐ[volume] ⋃ a, O a :=
      ae_eq_set.2 ⟨hcovO, by rw [sdiff_eq_empty.2 (iUnion_subset hOA), measure_empty]⟩
    rw [setLIntegral_congr hAO, lintegral_iUnion (fun a => (hOo a).measurableSet) hOd,
      measure_congr hAO, measure_iUnion hOd fun a => (hOo a).measurableSet,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [setLIntegral_congr_fun (hOo a).measurableSet
      (g := fun x => L (ξ + fderiv ℝ (f a) x)) fun x hx => by rw [(hΦloc a x hx).fderiv_eq],
      lintegral_zcopy (hρ a), volume_cube, ENNReal.ofReal_pow (hρ a).le]

/-- The easy half of domain independence: copying a cell test into a bounded open set. -/
theorem Yt_le_volume_mul_Zaff (L : Mat m N → ℝ≥0∞) {A : Set (Sp N)} (hA : IsOpen A)
    (hAb : Bornology.IsBounded A) (hA0 : volume A ≠ 0) (ξ : Mat m N) :
    Yt (fun _ => L) A ξ ≤ volume A * Zaff L ξ := by
  have hAt : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  simp only [Yt, Zaff]
  rw [ENNReal.mul_iInf_of_ne hA0 hAt]
  refine le_iInf fun φ => ?_
  rw [ENNReal.mul_iInf_of_ne hA0 hAt]
  refine le_iInf fun hφ => ?_
  have hφmem := hφ
  obtain ⟨⟨K, hK⟩, h0, -⟩ := hφ
  obtain ⟨M, hM⟩ := hK.continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro (isBounded_cube 1 0).isCompact_closure fun y hy =>
      h0 y fun h => hy (subset_closure h))
  obtain ⟨Φ, hΦ, -, hE⟩ :=
    exists_vitali_competitor L hA hφmem hM (δ := 1) (by norm_num) ξ
  exact (iInf₂_le Φ hΦ).trans (le_of_eq hE)

/-- An open set with null frontier has the same volume as its closure. -/
theorem volume_closure_eq_of_frontier_null {A : Set (Sp N)} (hA : IsOpen A)
    (hAf : volume (frontier A) = 0) : volume (closure A) = volume A := by
  rw [closure_eq_self_union_frontier]
  have hdis : Disjoint A (frontier A) := by
    rw [disjoint_left]
    intro x hxA hxF
    have hx : x ∈ A ∩ frontier A := ⟨hxA, hxF⟩
    rw [hA.inter_frontier_eq] at hx
    simp at hx
  rw [measure_union hdis isClosed_frontier.measurableSet, hAf]
  simp

/-- Nonempty open sets in `ℝᴺ` have positive Lebesgue volume. -/
theorem volume_pos_of_isOpen_nonempty {A : Set (Sp N)} (hA : IsOpen A)
    (hAn : A.Nonempty) : 0 < volume A := by
  obtain ⟨x, hx⟩ := hAn
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hA x hx
  have hvol : ENNReal.ofReal (r ^ N) ≤ volume A := by
    have hsub : Metric.closedBall x (r / 2) ⊆ A :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hmono := measure_mono (μ := volume) hsub
    rw [Real.volume_pi_closedBall x (by positivity)] at hmono
    simpa [Fintype.card_fin, show 2 * (r / 2) = r by ring] using hmono
  exact (ENNReal.ofReal_pos.mpr (pow_pos hr N)).trans_le hvol

/-- A homothetic copy centered at `a` lies in the corresponding ball when the original
domain lies in a ball centered at `x₀`. -/
theorem affine_preimage_closure_subset_closedBall {D : Set (Sp N)} (x₀ a : Sp N)
    {R r : ℝ} (hr : 0 < r)
    (hD : closure D ⊆ Metric.closedBall x₀ R) :
    affMap r (a - r • x₀) ⁻¹' closure D ⊆ Metric.closedBall a (r * R) := by
  intro x hx
  rw [Metric.mem_closedBall]
  have hmap : a + r • (affMap r (a - r • x₀) x - x₀) = x := by
    ext i
    simp [affMap, Pi.add_apply, Pi.smul_apply]
    field_simp [hr.ne']
    ring
  have hdist : dist x a = r * dist (affMap r (a - r • x₀) x) x₀ := by
    calc
      dist x a = dist (a + r • (affMap r (a - r • x₀) x - x₀)) a :=
        (congrArg (fun z => dist z a) hmap).symm
      _ = r * dist (affMap r (a - r • x₀) x) x₀ := by
        simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rw [hdist]
  have hxR := Metric.mem_closedBall.mp (hD hx)
  exact mul_le_mul_of_nonneg_left hxR hr.le

/-- Vitali packing of a bounded open set with null boundary by contained homothetic copies.
The Vitali theorem returns strictly disjoint closed copies; consequently touching boundaries are
never silently treated as disjoint. -/
theorem exists_vitali_domain_copies {D : Set (Sp N)} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hDf : volume (frontier D) = 0) :
    ∃ u : Set (Sp N × ℝ), u.Countable ∧
      (∀ p ∈ u, 0 < p.2 ∧
        affMap p.2 (p.1 - p.2 • Classical.choose hDne) ⁻¹' closure D ⊆ cube 1 0) ∧
      u.PairwiseDisjoint (fun p => affMap p.2
        (p.1 - p.2 • Classical.choose hDne) ⁻¹' closure D) ∧
      volume (cube 1 0 \ ⋃ p ∈ u, affMap p.2
        (p.1 - p.2 • Classical.choose hDne) ⁻¹' closure D) = 0 := by
  classical
  let x₀ := Classical.choose hDne
  have hx₀ : x₀ ∈ D := Classical.choose_spec hDne
  obtain ⟨M, hM⟩ := hDb.closure.exists_norm_le
  let R : ℝ := M + ‖x₀‖ + 1
  have hM0 : 0 ≤ M := (norm_nonneg x₀).trans (hM x₀ (subset_closure hx₀))
  have hR : 0 < R := by dsimp [R]; nlinarith [hM0, norm_nonneg x₀]
  have hDball : closure D ⊆ Metric.closedBall x₀ R := by
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall]
    calc
      dist x x₀ ≤ ‖x‖ + ‖x₀‖ := dist_le_norm_add_norm x x₀
      _ ≤ M + ‖x₀‖ := add_le_add (hM x (subset_closure hx)) le_rfl
      _ ≤ R := by dsimp [R]; linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD x₀ hx₀
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδε : δ < ε := by dsimp [δ]; linarith
  have hvolD : ENNReal.ofReal ((2 * δ) ^ N) ≤ volume D := by
    have hvol := measure_mono (μ := volume)
      ((Metric.closedBall_subset_ball hδε).trans hball)
    rw [Real.volume_pi_closedBall x₀ hδ.le] at hvol
    simpa [Fintype.card_fin] using hvol
  have hclvol : volume (closure D) = volume D := volume_closure_eq_of_frontier_null hD hDf
  let C : ℝ≥0 := ⟨((3 * R) / δ) ^ N,
    pow_nonneg (div_nonneg (by positivity) (by positivity)) _⟩
  let K : Sp N × ℝ → Set (Sp N) := fun p =>
    affMap p.2 (p.1 - p.2 • x₀) ⁻¹' closure D
  let t : Set (Sp N × ℝ) := {p | 0 < p.2 ∧ K p ⊆ cube 1 0}
  have hKball : ∀ p ∈ t, K p ⊆ Metric.closedBall p.1 (p.2 * R) := by
    intro p hp
    exact affine_preimage_closure_subset_closedBall x₀ p.1 hp.1 hDball
  obtain ⟨u, hu, huc, hud, hcover⟩ := Vitali.exists_disjoint_covering_ae volume
    (cube 1 (0 : Sp N)) t C (fun p => p.2 * R) (fun p => p.1) K
    hKball
    (fun p hp => by
      rw [Real.volume_pi_closedBall _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (mul_nonneg hp.1.le hR.le))]
      rw [show 2 * (3 * (p.2 * R)) = 6 * (p.2 * R) by ring, Fintype.card_fin]
      rw [volume_preimage_affMap (hp.1) (p.1 - p.2 • x₀), hclvol]
      have hC : (C : ℝ≥0∞) = ENNReal.ofReal (((3 * R) / δ) ^ N) := by
        rw [ENNReal.coe_nnreal_eq]
        dsimp [C]
        rfl
      rw [hC]
      have hscale : (6 * (p.2 * R)) ^ N =
          ((3 * R) / δ) ^ N * (p.2 ^ N * (2 * δ) ^ N) := by
        have hbase : 6 * (p.2 * R) = ((3 * R) / δ) * (p.2 * (2 * δ)) := by
          field_simp [ne_of_gt hδ]
          ring
        rw [hbase, mul_pow, mul_pow]
      rw [hscale]
      rw [ENNReal.ofReal_mul (p := ((3 * R) / δ) ^ N) (q := p.2 ^ N * (2 * δ) ^ N)
        (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) hR.le) hδ.le) N)]
      rw [ENNReal.ofReal_mul (p := p.2 ^ N) (q := (2 * δ) ^ N)
        (pow_nonneg hp.1.le N)]
      gcongr)
    (fun p hp => by
      have hopen : IsOpen (affMap p.2 (p.1 - p.2 • x₀) ⁻¹' D) :=
        hD.preimage (continuous_affMap hp.1 (p.1 - p.2 • x₀))
      have hsub : affMap p.2 (p.1 - p.2 • x₀) ⁻¹' D ⊆ interior (K p) := by
        intro y hy
        rw [mem_interior_iff_mem_nhds]
        exact Filter.mem_of_superset (hopen.mem_nhds hy) (fun z hz => subset_closure hz)
      refine ⟨p.1, hsub ?_⟩
      have hmap : affMap p.2 (p.1 - p.2 • x₀) p.1 = x₀ := by
        ext i
        simp [affMap, Pi.sub_apply, Pi.smul_apply]
        field_simp [hp.1.ne']
        ring
      rw [mem_preimage, hmap]
      exact hx₀)
    (fun p hp => isClosed_closure.preimage (continuous_affMap hp.1 (p.1 - p.2 • x₀)))
    (fun x hx η hη => by
      obtain ⟨s, hs, hballY⟩ := Metric.isOpen_iff.mp (isOpen_cube 1 (0 : Sp N)) x hx
      let r : ℝ := min (η / (R + 1)) (s / (R + 1))
      have hr : 0 < r := by dsimp [r]; positivity
      have hrη : r * R ≤ η := by
        dsimp [r]
        have : R ≤ R + 1 := by linarith
        have hη' : η / (R + 1) * R ≤ η := by
          rw [div_mul_eq_mul_div]
          exact (div_le_iff₀ (by linarith)).2 (by nlinarith)
        exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hR.le).trans hη'
      have hrs : r * R < s := by
        apply lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le)
        rw [div_mul_eq_mul_div]
        exact (div_lt_iff₀ (by linarith)).2 (by nlinarith)
      have hcopyBall := affine_preimage_closure_subset_closedBall x₀ x hr hDball
      have hcopy : K (x, r) ⊆ cube 1 0 :=
        hcopyBall.trans ((Metric.closedBall_subset_ball hrs).trans hballY)
      exact ⟨(x, r), ⟨hr, hcopy⟩, hrη, rfl⟩)
  exact ⟨u, huc, hu, hud, hcover⟩

/-- Copy an `Aff₀(D)` test into the unit cube by a Vitali packing of translated homothetic
copies of `D`. The identity is stated with the normalized energy on `D`. -/
theorem exists_domain_copy_competitor (L : Mat m N → ℝ≥0∞) {D : Set (Sp N)}
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hDf : volume (frontier D) = 0) {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 D)
    (ξ : Mat m N) :
    ∃ Φ ∈ (Aff0 (cube 1 (0 : Sp N)) : Set (Sp N → Tgt m)),
      ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ Φ y) =
        (volume D)⁻¹ * ∫⁻ y in D, L (ξ + fderiv ℝ φ y) := by
  classical
  obtain ⟨u, hu_count, hu, hud, hKcover⟩ := exists_vitali_domain_copies hD hDb hDne hDf
  let x₀ := Classical.choose hDne
  have hx₀ : x₀ ∈ D := Classical.choose_spec hDne
  let _ : Countable u := hu_count.to_subtype
  obtain ⟨Kφ, hφLip⟩ := hφ.1
  obtain ⟨⟨Kloc, hKloc⟩, n, V, ζ, hVo, hVU, hVd, hVf, hVc, hφV⟩ := hφ.2.2
  have hφ0 : ∀ y ∉ D, φ y = 0 := hφ.2.1
  have hvolDtop : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hvolDpos : 0 < volume D := volume_pos_of_isOpen_nonempty hD hDne
  let O : u → Set (Sp N) := fun p =>
    affMap p.1.2 (p.1.1 - p.1.2 • x₀) ⁻¹' D
  let ρ : u → ℝ := fun p => p.1.2
  let c : u → Sp N := fun p => p.1.1 - p.1.2 • x₀
  have hρ : ∀ p, 0 < ρ p := fun p => (hu p.1 p.2).1
  have hOopen : ∀ p, IsOpen (O p) := fun p =>
    hD.preimage (continuous_affMap (hρ p) (c p))
  have hOK : ∀ p, O p ⊆ affMap (ρ p) (c p) ⁻¹' closure D := fun p y hy =>
    subset_closure hy
  have hOY : ∀ p, O p ⊆ cube 1 0 := fun p =>
    (hOK p).trans (hu p.1 p.2).2
  have hOd : Pairwise fun p q => Disjoint (O p) (O q) := by
    intro p q hpq
    exact (hud p.2 q.2 (fun h => hpq (Subtype.ext h))).mono (hOK p) (hOK q)
  have hnull : ∀ p (S : Set (Sp N)), volume S = 0 →
      volume (affMap (ρ p) (c p) ⁻¹' S) = 0 := by
    intro p S hS
    rw [volume_preimage_affMap (hρ p) (c p), hS, mul_zero]
  have hOcover : volume (cube 1 0 \ ⋃ p, O p) = 0 := by
    have hKcover' : volume (cube 1 0 \ ⋃ p : u,
        affMap (ρ p) (c p) ⁻¹' closure D) = 0 := by
      rw [← hKcover]
      congr 1
      rw [biUnion_eq_iUnion]
    have hbad : ∀ p, volume ((affMap (ρ p) (c p) ⁻¹' closure D) \ O p) = 0 := by
      intro p
      have heq : (affMap (ρ p) (c p) ⁻¹' closure D) \ O p =
          affMap (ρ p) (c p) ⁻¹' frontier D := by
        rw [show O p = affMap (ρ p) (c p) ⁻¹' D by rfl, ← preimage_sdiff,
          hD.frontier_eq]
      rw [heq]
      exact hnull p _ hDf
    refine measure_mono_null (t := (cube 1 0 \ ⋃ p, affMap (ρ p) (c p) ⁻¹' closure D) ∪
      ⋃ p, ((affMap (ρ p) (c p) ⁻¹' closure D) \ O p)) ?_
      (measure_union_null hKcover' (measure_iUnion_null hbad))
    intro y hy
    by_cases hyK : y ∈ ⋃ p, affMap (ρ p) (c p) ⁻¹' closure D
    · obtain ⟨p, hp⟩ := mem_iUnion.1 hyK
      refine Or.inr (mem_iUnion.2 ⟨p, ?_⟩)
      refine ⟨hp, ?_⟩
      intro hyO
      exact hy.2 (mem_iUnion.2 ⟨p, hyO⟩)
    · exact Or.inl ⟨hy.1, hyK⟩
  let f : u → Sp N → Tgt m := fun p => zcopy φ (ρ p) (c p)
  have hfLip : ∀ p, LipschitzWith Kφ (f p) := fun p => zcopy_lipschitz (hρ p) (c p) hφLip
  have hf0 : ∀ p y, y ∉ O p → f p y = 0 := by
    intro p y hy
    change zcopy φ (ρ p) (c p) y = 0
    simp only [zcopy]
    rw [hφ0 (affMap (ρ p) (c p) y) hy, smul_zero]
  let Φ : Sp N → Tgt m := fun y => ∑' p, f p y
  have hΦLip : LipschitzWith Kφ Φ := lipschitzWith_tsum_cells hOopen hOd hfLip hf0
  have hΦloc : ∀ p y, y ∈ O p → Φ =ᶠ[𝓝 y] f p := by
    intro p y hy
    filter_upwards [(hOopen p).mem_nhds hy] with z hz
    exact tsum_cells_of_mem hOd hf0 hz
  let P : u → Fin n → Set (Sp N) := fun p i => affMap (ρ p) (c p) ⁻¹' V i
  let W : Fin n → Set (Sp N) := fun i => ⋃ p, P p i
  have hPO : ∀ p i, P p i ⊆ O p := fun p i => preimage_mono (hVU i)
  have hOW : ∀ p i, O p ∩ W i ⊆ P p i := by
    intro p i y hy
    obtain ⟨q, hq⟩ := mem_iUnion.1 hy.2
    by_cases hpq : p = q
    · subst q; exact hq
    · exact absurd (hPO q i hq) (Set.disjoint_left.1 (hOd hpq) hy.1)
  have hWopen : ∀ i, IsOpen (W i) := fun i => isOpen_iUnion fun p =>
    (hVo i).preimage (continuous_affMap (hρ p) (c p))
  have hWY : ∀ i, W i ⊆ cube 1 0 := fun i => iUnion_subset fun p =>
    (hPO p i).trans (hOY p)
  have hWdisj : Pairwise fun i j => Disjoint (W i) (W j) := by
    intro i j hij
    refine Set.disjoint_left.2 fun y hy hy' => ?_
    obtain ⟨p, hp⟩ := mem_iUnion.1 hy
    obtain ⟨q, hq⟩ := mem_iUnion.1 hy'
    by_cases hpq : p = q
    · subst q
      exact (hVd hij).le_bot ⟨hp, hq⟩
    · exact (hOd hpq).le_bot ⟨hPO p i hp, hPO q j hq⟩
  have hWfront : ∀ i, volume (cube 1 0 ∩ frontier (W i)) = 0 := by
    intro i
    have hpreNull : ∀ p,
        volume (affMap (ρ p) (c p) ⁻¹' (D ∩ frontier (V i))) = 0 :=
      fun p => hnull p _ (hVf i)
    refine measure_mono_null (t := (cube 1 0 \ ⋃ p, O p) ∪
      ⋃ p, affMap (ρ p) (c p) ⁻¹' (D ∩ frontier (V i))) ?_
      (measure_union_null hOcover (measure_iUnion_null hpreNull))
    rintro y ⟨hyY, hyfront⟩
    by_cases hyO : ∃ p, y ∈ O p
    · obtain ⟨p, hp⟩ := hyO
      have hycl : y ∈ closure (P p i) :=
        closure_mono (hOW p i) ((hOopen p).inter_closure ⟨hp, frontier_subset_closure hyfront⟩)
      have hPopen : IsOpen (P p i) :=
        (hVo i).preimage (continuous_affMap (hρ p) (c p))
      have hynot : y ∉ P p i := by
        intro h
        have hyW : y ∈ W i := mem_iUnion.mpr ⟨p, h⟩
        have hmem : y ∈ W i ∩ frontier (W i) := ⟨hyW, hyfront⟩
        rw [(hWopen i).inter_frontier_eq] at hmem
        exact hmem.elim
      have hypfront : y ∈ frontier (P p i) := by
        rw [hPopen.frontier_eq]
        exact ⟨hycl, hynot⟩
      have hyD : affMap (ρ p) (c p) y ∈ D := hp
      have hyVfront : affMap (ρ p) (c p) y ∈ frontier (V i) := by
        have heq := frontier_preimage_affMap (ρ := ρ p) (c := c p)
          (hρ := hρ p) (V i)
        rw [heq] at hypfront
        exact hypfront
      exact Or.inr (mem_iUnion.2 ⟨p, ⟨hyD, hyVfront⟩⟩)
    · exact Or.inl ⟨hyY, fun hy => hyO (mem_iUnion.1 hy)⟩
  have hWcover : volume (cube 1 0 \ ⋃ i, W i) = 0 := by
    have hpreNull : ∀ p,
        volume (affMap (ρ p) (c p) ⁻¹' (D \ ⋃ i, V i)) = 0 :=
      fun p => hnull p _ hVc
    refine measure_mono_null (t := (cube 1 0 \ ⋃ p, O p) ∪
      ⋃ p, affMap (ρ p) (c p) ⁻¹' (D \ ⋃ i, V i)) ?_
      (measure_union_null hOcover (measure_iUnion_null hpreNull))
    intro y hy
    by_cases hyO : ∃ p, y ∈ O p
    · obtain ⟨p, hp⟩ := hyO
      refine Or.inr (mem_iUnion.2 ⟨p, ⟨hp, ?_⟩⟩)
      intro hV
      obtain ⟨i, hi⟩ := mem_iUnion.1 hV
      exact hy.2 (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨p, hi⟩⟩)
    · exact Or.inl ⟨hy.1, fun hy' => hyO (mem_iUnion.1 hy')⟩
  have hWderiv : ∀ i y, y ∈ W i → HasFDerivAt Φ (ζ i) y := by
    intro i y hy
    obtain ⟨p, hp⟩ := mem_iUnion.1 hy
    have hloc := hΦloc p y ((hPO p i) hp)
    simpa [f] using
      (zcopy_hasFDerivAt (hρ p) (c p) (hφV i _ hp)).congr_of_eventuallyEq hloc
  have hΦA : Φ ∈ Aff0 (cube 1 (0 : Sp N)) := by
    refine ⟨⟨Kφ, hΦLip⟩, ?_, ⟨⟨Kφ, hΦLip.lipschitzOnWith⟩, n, W, ζ, hWopen,
      hWY, hWdisj, hWfront, hWcover, hWderiv⟩⟩
    intro y hy
    apply tsum_cells_of_notMem hf0
    intro p hp
    exact hy (hOY p hp)
  have hOae : cube 1 0 =ᵐ[volume] ⋃ p, O p :=
    ae_eq_set.2 ⟨hOcover, measure_mono_null (t := (∅ : Set (Sp N))) (by
      intro y hy
      obtain ⟨p, hp⟩ := mem_iUnion.1 hy.1
      exact hy.2 (hOY p hp)) (by simp)⟩
  have hscaleSum : (∑' p, ENNReal.ofReal ((ρ p) ^ N)) * volume D = 1 := by
    have hvolUnion : volume (⋃ p, O p) = 1 := by
      calc
        volume (⋃ p, O p) = volume (cube 1 0) := (measure_congr hOae).symm
        _ = 1 := by rw [volume_cube]; norm_num
    have hvolPieces : volume (⋃ p, O p) =
        (∑' p, ENNReal.ofReal ((ρ p) ^ N)) * volume D := by
      rw [measure_iUnion hOd fun p => (hOopen p).measurableSet]
      calc
        (∑' p, volume (O p)) = ∑' p, ENNReal.ofReal ((ρ p) ^ N) * volume D := by
          refine tsum_congr fun p => ?_
          rw [show O p = affMap (ρ p) (c p) ⁻¹' D by rfl,
            volume_preimage_affMap (hρ p) (c p)]
        _ = (∑' p, ENNReal.ofReal ((ρ p) ^ N)) * volume D := by
          rw [← ENNReal.tsum_mul_right]
    exact hvolPieces.symm.trans hvolUnion
  have hvolD0 : volume D ≠ 0 := ne_of_gt hvolDpos
  have hvolDneTop : volume D ≠ ⊤ := hvolDtop
  have hscale : (∑' p, ENNReal.ofReal ((ρ p) ^ N)) = (volume D)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left hscaleSum
  refine ⟨Φ, hΦA, ?_⟩
  have henergy : ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ Φ y) =
      (∑' p, ENNReal.ofReal ((ρ p) ^ N)) * ∫⁻ y in D, L (ξ + fderiv ℝ φ y) := by
    have hI : ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ Φ y) =
        ∑' p, ∫⁻ y in O p, L (ξ + fderiv ℝ (f p) y) := by
      rw [setLIntegral_congr hOae, lintegral_iUnion (fun p => (hOopen p).measurableSet) hOd]
      refine tsum_congr fun p => ?_
      rw [setLIntegral_congr_fun (hOopen p).measurableSet
        (g := fun y => L (ξ + fderiv ℝ (f p) y)) fun y hy => by
          rw [(hΦloc p y hy).fderiv_eq]
        , show O p = affMap (ρ p) (c p) ⁻¹' D by rfl,
        lintegral_zcopy_set (ρ := ρ p) (c := c p) (hρ := hρ p)
          hD.measurableSet L φ ξ]
    rw [hI]
    calc
      (∑' p, ∫⁻ y in O p, L (ξ + fderiv ℝ (f p) y)) =
          ∑' p, ENNReal.ofReal ((ρ p) ^ N) * ∫⁻ y in D, L (ξ + fderiv ℝ φ y) := by
        refine tsum_congr fun p => ?_
        rw [show O p = affMap (ρ p) (c p) ⁻¹' D by rfl,
          lintegral_zcopy_set (ρ := ρ p) (c := c p) (hρ := hρ p)
            hD.measurableSet L φ ξ]
      _ = (∑' p, ENNReal.ofReal ((ρ p) ^ N)) *
          ∫⁻ y in D, L (ξ + fderiv ℝ φ y) := by rw [← ENNReal.tsum_mul_right]
  rw [henergy, hscale]

/-- The reverse, hard half of domain independence for `Aff₀` tests. -/
theorem Zaff_le_normalized_Yt (L : Mat m N → ℝ≥0∞) {D : Set (Sp N)} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hDf : volume (frontier D) = 0) (ξ : Mat m N) :
    Zaff L ξ ≤ (volume D)⁻¹ * Yt (fun _ => L) D ξ := by
  have hvolD0 : volume D ≠ 0 := ne_of_gt (volume_pos_of_isOpen_nonempty hD hDne)
  have hvolDtop : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hinv0 : (volume D)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hvolDtop
  have hinvtop : (volume D)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hvolD0
  simp only [Zaff, Yt]
  rw [ENNReal.mul_iInf_of_ne hinv0 hinvtop]
  refine le_iInf fun ψ => ?_
  rw [ENNReal.mul_iInf_of_ne hinv0 hinvtop]
  refine le_iInf fun hψ => ?_
  obtain ⟨Φ, hΦ, hE⟩ := exists_domain_copy_competitor L hD hDb hDne hDf hψ ξ
  exact (iInf₂_le Φ hΦ).trans (le_of_eq hE)

/-- Independence of the affine cell domain. The cited statement assumes `L` Borel; the two
copying arguments hold for arbitrary `L`, so no measurability hypothesis is needed. -/
theorem aff0_domainIndependence (L : Mat m N → ℝ≥0∞)
    {D : Set (Sp N)} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (hDne : D.Nonempty) (hDf : volume (frontier D) = 0) (ξ : Mat m N) :
    (volume D)⁻¹ * Yt (fun _ => L) D ξ = Zaff L ξ := by
  have hD0 : volume D ≠ 0 := ne_of_gt (volume_pos_of_isOpen_nonempty hD hDne)
  have hDtop : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hforward := Yt_le_volume_mul_Zaff L hD hDb hD0 ξ
  have hback := Zaff_le_normalized_Yt L hD hDb hDne hDf ξ
  apply le_antisymm ?_ hback
  calc
    (volume D)⁻¹ * Yt (fun _ => L) D ξ ≤
        (volume D)⁻¹ * (volume D * Zaff L ξ) :=
      mul_le_mul_of_nonneg_left hforward (bot_le : (0 : ℝ≥0∞) ≤ (volume D)⁻¹)
    _ = Zaff L ξ := ENNReal.inv_mul_cancel_left hD0 hDtop

/-- The rank-one step needed to derive the cited local-Lipschitz property reduces to coordinate
convexity on the interior of the effective domain. The matrix-to-coordinate map is contractive,
so the constant supplied by `locallyLipschitzOn_of_coordConvex` is unchanged. -/
theorem CitedZaffLocLip_of_coordConvex
    (hcoord : ∀ L : Mat m N → ℝ≥0∞,
      CoordConvexOn (matCoordEquiv m N '' interior (dom (Zaff L)))
        (fun A => Zaff L ((matCoordEquiv m N).symm A))) :
    CitedZaffLocLip N m := by
  intro L ξ hξ
  have hV : IsOpen (interior (dom (Zaff L))) := isOpen_interior
  have hfin : ∀ A ∈ interior (dom (Zaff L)), Zaff L A ≠ ⊤ := by
    intro A hA
    exact (lt_top_iff_ne_top.mp (by simpa [dom] using interior_subset hA))
  exact locallyLipschitzOn_of_matCoordConvex hV hfin (hcoord L) ξ hξ

/-- Once the rank-one inequality for each affine envelope is proved on its effective-domain
interior, `CitedZaffLocLip` follows in the operator-norm matrix space. -/
theorem CitedZaffLocLip_of_rankOneConvexOn
    (hRank : ∀ L : Mat m N → ℝ≥0∞,
      RankOneConvexOn (interior (dom (Zaff L))) (Zaff L)) :
    CitedZaffLocLip N m :=
  CitedZaffLocLip_of_coordConvex fun L => (hRank L).coordConvex

/-- The affine cell envelope is idempotent: applying the cell formula twice has no further
effect. This holds for arbitrary integrands, without a measurability assumption. -/
theorem Zaff_Zaff (L : Mat m N → ℝ≥0∞) (ξ : Mat m N) :
    Zaff (Zaff L) ξ = Zaff L ξ := by
  apply le_antisymm (Zaff_le (Zaff L) ξ)
  simp only [Zaff, Yt]
  refine le_iInf fun φ => ?_
  refine le_iInf fun hφ => ?_
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  classical
  obtain ⟨Kφ, n, V, ζ, hKφ, hφ0, hVo, hVU, hVd, hVf, hVc, hφV⟩ := Aff0.data hφ
  let η' : ℝ≥0∞ := (η : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)
  have hη' : η' ≠ 0 := by
    simp only [η', ne_eq, ENNReal.div_eq_zero_iff, ENNReal.coe_eq_zero, not_or]
    exact ⟨hη.ne', by simp⟩
  have hVfront : ∀ i, volume (frontier (V i)) = 0 := by
    intro i
    have hsub : frontier (V i) ⊆
        (cube 1 0 ∩ frontier (V i)) ∪ frontier (cube 1 0) := by
      intro y hy
      by_cases hyY : y ∈ cube 1 0
      · exact Or.inl ⟨hyY, hy⟩
      · right
        rw [(isOpen_cube 1 (0 : Sp N)).frontier_eq]
        exact ⟨closure_mono (hVU i) (frontier_subset_closure hy), hyY⟩
    exact measure_mono_null hsub
      (measure_union_null (hVf i) (volume_frontier_cube 1 0))
  have hχexists : ∀ i, ∃ χ ∈ (Aff0 (V i) : Set (Sp N → Tgt m)),
      ∫⁻ y in V i, L (ξ + ζ i + fderiv ℝ χ y) ≤
        volume (V i) * Zaff L (ξ + ζ i) + η' := by
    intro i
    by_cases hVi : (V i).Nonempty
    · have hViBound : Bornology.IsBounded (V i) := (isBounded_cube 1 0).subset (hVU i)
      have hVi0 : volume (V i) ≠ 0 :=
        ne_of_gt (volume_pos_of_isOpen_nonempty (hVo i) hVi)
      have hVitop : volume (V i) ≠ ⊤ := hViBound.measure_lt_top.ne
      have hdom := aff0_domainIndependence L (hVo i) hViBound hVi (hVfront i) (ξ + ζ i)
      have hYeq : Yt (fun _ => L) (V i) (ξ + ζ i) =
          volume (V i) * Zaff L (ξ + ζ i) := by
        calc
          _ = volume (V i) * ((volume (V i))⁻¹ *
              Yt (fun _ => L) (V i) (ξ + ζ i)) :=
                (ENNReal.mul_inv_cancel_left hVi0 hVitop).symm
          _ = _ := congrArg (fun t : ℝ≥0∞ => volume (V i) * t) hdom
      by_cases hZi : Zaff L (ξ + ζ i) = ⊤
      · refine ⟨0, zero_mem_Aff0 (hVo i), ?_⟩
        simp [η', hZi, hVi0]
      · have hYtop : Yt (fun _ => L) (V i) (ξ + ζ i) ≠ ⊤ := by
          rw [hYeq]
          exact ENNReal.mul_ne_top hVitop hZi
        have hnear : Yt (fun _ => L) (V i) (ξ + ζ i) <
            volume (V i) * Zaff L (ξ + ζ i) + η' := by
          calc
            Yt (fun _ => L) (V i) (ξ + ζ i) <
                Yt (fun _ => L) (V i) (ξ + ζ i) + η' :=
              ENNReal.lt_add_right hYtop hη'
            _ = _ := by rw [hYeq]
        obtain ⟨χ, hχ, hχlt⟩ := by simpa [Yt, iInf_lt_iff] using hnear
        refine ⟨χ, hχ, ?_⟩
        exact hχlt.le
    · have hVempty : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hVi
      refine ⟨0, zero_mem_Aff0 (hVo i), ?_⟩
      simp [hVempty]
  choose χ hχA hχenergy using hχexists
  choose Kχ nχ P θ hKχ hχ0 hPo hPs hPd hPf hPc hχP using
    fun i => Aff0.data (hχA i)
  let Ψ : Sp N → Tgt m := φ + ∑ i, χ i
  have hΨA : Ψ ∈ Aff0 (cube 1 (0 : Sp N)) := by
    dsimp [Ψ]
    exact Aff0.add_sum hKφ hφ0 hVo hVU hVd hVf hVc hφV hχA
  have hΨderiv : ∀ i l y, y ∈ P i l →
      HasFDerivAt Ψ (ζ i + θ i l) y := by
    intro i l y hy
    have hyV : y ∈ V i := hPs i l hy
    have hlocal : Ψ =ᶠ[𝓝 y] fun z => φ z + χ i z := by
      filter_upwards [(hVo i).mem_nhds hyV] with z hz
      dsimp [Ψ]
      simpa using congrArg (fun w : Tgt m => φ z + w)
        (sum_eq_of_mem_piece hVd hχ0 hz)
    exact ((hφV i y hyV).add (hχP i l y hy)).congr_of_eventuallyEq hlocal
  have hpieceEnergy : ∀ i,
      ∫⁻ y in V i, L (ξ + fderiv ℝ Ψ y) =
        ∫⁻ y in V i, L (ξ + ζ i + fderiv ℝ (χ i) y) := by
    intro i
    rw [lintegral_eq_sum_pieces (hPo i) (hPs i) (hPd i) (hPc i)]
    rw [lintegral_eq_sum_pieces (hPo i) (hPs i) (hPd i) (hPc i)]
    refine Finset.sum_congr rfl fun l _ => ?_
    apply setLIntegral_congr_fun (hPo i l).measurableSet
    intro y hy
    change L (ξ + fderiv ℝ Ψ y) = L (ξ + ζ i + fderiv ℝ (χ i) y)
    rw [(hΨderiv i l y hy).fderiv, (hχP i l y hy).fderiv]
    simp [add_assoc]
  have hΨenergy : ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ Ψ y) ≤
      (∑ i, volume (V i) * Zaff L (ξ + ζ i)) + η := by
    rw [lintegral_eq_sum_pieces hVo hVU hVd hVc]
    calc
      (∑ i, ∫⁻ y in V i, L (ξ + fderiv ℝ Ψ y)) ≤
          ∑ i, (volume (V i) * Zaff L (ξ + ζ i) + η') :=
        Finset.sum_le_sum fun i _ => by rw [hpieceEnergy i]; exact hχenergy i
      _ = (∑ i, volume (V i) * Zaff L (ξ + ζ i)) + n * η' := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (∑ i, volume (V i) * Zaff L (ξ + ζ i)) + η := by
        gcongr
        calc
          (n : ℝ≥0∞) * η' ≤ ((n : ℝ≥0∞) + 1) * η' := by gcongr; exact le_self_add
          _ = η := by dsimp [η']; exact ENNReal.mul_div_cancel (by simp) (by simp)
  have hbase : ∫⁻ y in cube 1 0, Zaff L (ξ + fderiv ℝ φ y) =
      ∑ i, volume (V i) * Zaff L (ξ + ζ i) := by
    rw [lintegral_eq_sum_pieces hVo hVU hVd hVc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet
      (g := fun _ => Zaff L (ξ + ζ i)) fun y hy => by rw [(hφV i y hy).fderiv],
      setLIntegral_const, mul_comm]
  calc
    Zaff L ξ ≤ ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ Ψ y) := iInf₂_le Ψ hΨA
    _ ≤ (∑ i, volume (V i) * Zaff L (ξ + ζ i)) + η := hΨenergy
    _ = (∫⁻ y in cube 1 0, Zaff L (ξ + fderiv ℝ φ y)) + η := by rw [← hbase]

/-- Idempotence reduces an affine-cell test for `Zaff L` to the energy of the original cell
envelope, with one summand for each of its finitely many affine gradients. This avoids choosing
additional correctors on the bulk phase regions in the rank-one argument. -/
theorem Zaff_le_piecewise_energy (L : Mat m N → ℝ≥0∞) (ξ : Mat m N)
    {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 (cube 1 (0 : Sp N)))
    {n : ℕ} {V : Fin n → Set (Sp N)} {ζ : Fin n → Mat m N}
    (hVo : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ cube 1 (0 : Sp N))
    (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVc : volume (cube 1 (0 : Sp N) \ ⋃ i, V i) = 0)
    (hφV : ∀ i, ∀ y ∈ V i, HasFDerivAt φ (ζ i) y) :
    Zaff L ξ ≤ ∑ i, volume (V i) * Zaff L (ξ + ζ i) := by
  calc
    Zaff L ξ = Zaff (Zaff L) ξ := (Zaff_Zaff L ξ).symm
    _ ≤ ∫⁻ y in cube 1 0, Zaff L (ξ + fderiv ℝ φ y) := by
      rw [Zaff, Yt]
      exact iInf₂_le φ hφ
    _ = ∑ i, volume (V i) * Zaff L (ξ + ζ i) := by
      rw [lintegral_eq_sum_pieces hVo hVU hVd hVc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [setLIntegral_congr_fun (hVo i).measurableSet
        (g := fun _ => Zaff L (ξ + ζ i)) fun y hy => by rw [(hφV i y hy).fderiv],
        setLIntegral_const, mul_comm]

/-! ### The upper bound in Proposition `prop:densityZaff` -/

theorem densityZaffUpper : DensityZaffUpper N m := by
  classical
  intro L A hA hAb ξ
  set Z := Zaff L ξ
  have hzero : (0 : Sp N → Tgt m) ∈ Aff0 A := zero_mem_Aff0 hA
  have hsmall0 : UnifSmall atTop fun _ : ℕ => (0 : Sp N → Tgt m) :=
    fun δ hδ => Eventually.of_forall fun _ y => by simp [hδ.le]
  by_cases hA0 : volume A = 0
  · refine ⟨fun _ => 0, fun _ => hzero, hsmall0, ?_⟩
    exact (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun k =>
      (setLIntegral_measure_zero _ _ hA0).le)).trans zero_le
  by_cases hZ : Z = ⊤
  · refine ⟨fun _ => 0, fun _ => hzero, hsmall0, ?_⟩
    rw [hZ, ENNReal.mul_top hA0]; exact le_top
  have hAt : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  set ηs : ℕ → ℝ≥0∞ := fun k => ((k : ℝ≥0∞) + 1)⁻¹
  have hηs : ∀ k, 0 < ηs k := fun k => ENNReal.inv_pos.2 (by simp)
  -- near-optimal correctors on `Y`
  have hcorr : ∀ k, ∃ φ ∈ (Aff0 (cube 1 (0 : Sp N)) : Set (Sp N → Tgt m)),
      ∫⁻ y in cube 1 0, L (ξ + fderiv ℝ φ y) < Z + ηs k := by
    intro k
    have := ENNReal.lt_add_right hZ (hηs k).ne'
    simpa [Z, Zaff, Yt, iInf_lt_iff] using this
  choose φs hφs hI using hcorr
  have hMφ : ∀ k, ∃ M, ∀ y, ‖φs k y‖ ≤ M := fun k => by
    obtain ⟨⟨K, hK⟩, h0, -⟩ := hφs k
    exact hK.continuous.bounded_above_of_compact_support
      (HasCompactSupport.intro (isBounded_cube 1 0).isCompact_closure
        fun y hy => h0 y fun h => hy (subset_closure h))
  choose Ms hMs using hMφ
  have hM0 : ∀ k, 0 ≤ Ms k := fun k => (norm_nonneg _).trans (hMs k 0)
  set δs : ℕ → ℝ := fun k => 1 / (((k : ℝ) + 1) * (2 * Ms k + 1))
  have hδs : ∀ k, 0 < δs k := fun k => by have := hM0 k; positivity
  have hδM : ∀ k, 2 * δs k * Ms k ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have h1 := hM0 k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    simp only [δs]
    have hd : (0 : ℝ) < ((k : ℝ) + 1) * (2 * Ms k + 1) := by positivity
    rw [show 2 * (1 / (((k : ℝ) + 1) * (2 * Ms k + 1))) * Ms k =
      (2 * Ms k) / (((k : ℝ) + 1) * (2 * Ms k + 1)) by ring, div_le_div_iff₀ hd hk]
    nlinarith
  choose Φs hΦA hΦb hΦE using fun k =>
    exists_vitali_competitor L hA (hφs k) (hMs k) (hδs k) ξ
  refine ⟨Φs, hΦA, fun δ hδ => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop K] with k hk y
    refine (hΦb k y).trans ((hδM k).trans (le_trans ?_ hK.le))
    gcongr
  · have hη0 : Tendsto ηs atTop (𝓝 0) := by
      have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      exact h.congr fun k => by simp [ηs, Function.comp]
    have hlim : Tendsto (fun k => volume A * (Z + ηs k)) atTop (𝓝 (volume A * (Z + 0))) :=
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hη0) (Or.inr hAt)
    rw [add_zero] at hlim
    refine (limsup_le_limsup (Eventually.of_forall fun k => ?_)).trans hlim.limsup_eq.le
    rw [hΦE k]
    gcongr
    exact (hI k).le

/-- **Theorem `main-Ggrowth`.** Conditional formalization: the main theorem is proved from four
cited results (`CitedAHM14`, `CitedAffineApprox`, `CitedVitaliEnvelope`, `CitedZaffLocLip`).
Three are now proved in Lean and `CitedVitaliEnvelope` is replaced by the proved inequality
`vitaliEnvelopeUpper` (see `main_Ggrowth_final_unconditional`, `AHM14.lean`); `CitedVitaliEnvelope`
is also proved, downstream (`citedVitaliEnvelope_holds`, `VitaliEquality.lean`).
See `REGISTRY.md` for the dependency registry and for other article results that remain
unformalized. -/
theorem main_Ggrowth_final [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (N : ℝ) < p) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} (hW : Hypotheses p G W)
    (hAHM : CitedAHM14 N m p) (hApprox : CitedAffineApprox N m p)
    (hLip : CitedZaffLocLip N m) (hV : CitedVitaliEnvelope N) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W) (intHom (Whom p W)) :=
  main_Ggrowth_of_densities p hp hΩ hW hAHM hApprox hLip densityZaffUpper densityHaff
    (step4 hΩ hW hV.upper)

end Homogenization
