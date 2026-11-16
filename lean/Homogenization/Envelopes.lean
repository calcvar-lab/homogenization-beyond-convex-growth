import Homogenization.Basic

/-!
# Elementary properties of the envelopes

* Remark `lEnvelopes` (i)–(iii): monotonicity, trivial upper bounds, `𝒵_aff ℋ_aff L ≤ ℋ_aff L`.
* Lemma `lem:ruusc-transfer`: the ru-usc property passes to `𝒴_loc`, `ℋ_aff` and `𝒵_aff`.
* Remark `rem:B1c` (i) / Lemma `lem:consequences` (iii), first item: (Z3) implies the `G`-growth of
  `𝒴_loc W`.
* Lemma `lem:consequences` (ii): `p`-coercivity of `W` itself.
* Lemma `lem:measurability`, first assertion: `𝒵_aff (a H) = a 𝒵_aff H`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### The class `Aff₀(U)` -/

theorem zero_mem_Aff0 {U : Set (Sp N)} (hU : IsOpen U) : (0 : Sp N → Tgt m) ∈ Aff0 U := by
  refine ⟨⟨0, LipschitzWith.const 0⟩, fun _ _ => rfl, ⟨0, (LipschitzWith.const 0).lipschitzOnWith⟩,
    1, fun _ => U, fun _ => 0, fun _ => hU, fun _ => subset_rfl, ?_, fun _ => ?_, ?_,
    fun _ y _ => hasFDerivAt_const (0 : Tgt m) y⟩
  · intro i j hij; exact absurd (Subsingleton.elim i j) hij
  · rw [hU.inter_frontier_eq, measure_empty]
  · rw [iUnion_const, sdiff_self, measure_empty]

theorem smul_mem_Aff0 {U : Set (Sp N)} {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 U) (t : ℝ) :
    t • φ ∈ Aff0 U := by
  obtain ⟨⟨K, hK⟩, h0, ⟨K', hK'⟩, n, V, ξ, hVo, hVU, hVd, hVf, hVc, hφV⟩ := hφ
  refine ⟨⟨_, (lipschitzWith_smul t).comp hK⟩, fun y hy => by simp [h0 y hy],
    ⟨_, (lipschitzWith_smul t).comp_lipschitzOnWith hK'⟩, n, V, fun i => t • ξ i, hVo, hVU, hVd,
    hVf, hVc, fun i y hy => (hφV i y hy).const_smul t⟩

/-- The inequality behind the ru-usc transfer: if `W(y,tζ) ≤ a W(y,ζ) + b` everywhere, then
`𝒴 W(U,tξ) ≤ a 𝒴 W(U,ξ) + b|U|`. -/
theorem Yt_smul_le (W : Sp N → Mat m N → ℝ≥0∞) (U : Set (Sp N)) (t : ℝ) {a b : ℝ≥0∞}
    (ha₀ : a ≠ 0) (ha : a ≠ ⊤) (hW : ∀ y ζ, W y (t • ζ) ≤ a * W y ζ + b) (ξ : Mat m N) :
    Yt W U (t • ξ) ≤ a * Yt W U ξ + b * volume U := by
  simp only [Yt]
  rw [ENNReal.mul_iInf_of_ne ha₀ ha, ENNReal.iInf_add]
  refine le_iInf fun φ => ?_
  rw [ENNReal.mul_iInf_of_ne ha₀ ha, ENNReal.iInf_add]
  refine le_iInf fun hφ => ?_
  refine (iInf₂_le (t • φ) (smul_mem_Aff0 hφ t)).trans ?_
  have hder : ∀ y, t • ξ + fderiv ℝ (t • φ) y = t • (ξ + fderiv ℝ φ y) := by
    intro y; rw [fderiv_const_smul_field, Pi.smul_apply, smul_add]
  simp_rw [hder]
  calc ∫⁻ y in U, W y (t • (ξ + fderiv ℝ φ y))
      ≤ ∫⁻ y in U, (a * W y (ξ + fderiv ℝ φ y) + b) := lintegral_mono fun y => hW _ _
    _ = a * (∫⁻ y in U, W y (ξ + fderiv ℝ φ y)) + b * volume U := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ha, setLIntegral_const]

/-- `(1 + η) f + η c` form of the ru-usc condition. -/
theorem RUUSCWith.le_affine {c : ℝ≥0} {f : Sp N → Mat m N → ℝ≥0∞} (hf : RUUSCWith c f)
    {η : ℝ≥0} (hη : 0 < η) :
    ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ x ξ, f x (t • ξ) ≤ (1 + η) * f x ξ + η * c := by
  filter_upwards [hf η hη] with t ht x ξ
  by_cases hfin : f x ξ < ⊤
  · calc f x (t • ξ) ≤ f x ξ + η * (c + f x ξ) := ht x ξ hfin
      _ = (1 + η) * f x ξ + η * c := by ring
  · rw [not_lt, top_le_iff] at hfin
    simp [hfin]

theorem RUUSCWith.of_le_affine {c : ℝ≥0} {f : Sp N → Mat m N → ℝ≥0∞}
    (h : ∀ η : ℝ≥0, 0 < η → ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ x ξ,
      f x (t • ξ) ≤ (1 + η) * f x ξ + η * c) : RUUSCWith c f := by
  intro η hη
  filter_upwards [h η hη] with t ht x ξ _
  calc f x (t • ξ) ≤ (1 + η) * f x ξ + η * c := ht x ξ
    _ = f x ξ + η * (c + f x ξ) := by ring

theorem volume_cube_pos {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) : 0 < volume (cube ρ x) := by
  rw [volume_cube]; exact ENNReal.pow_pos (ENNReal.ofReal_pos.2 hρ) _

theorem volume_cube_ne_top (ρ : ℝ) (x : Sp N) : volume (cube ρ x) ≠ ⊤ := by
  rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- `(a y + b |Q|) / |Q| = a y / |Q| + b` for `0 < |Q| < ∞`. -/
theorem affine_div_volume {a y b V : ℝ≥0∞} (hV₀ : V ≠ 0) (hV : V ≠ ⊤) :
    (a * y + b * V) / V = a * (y / V) + b := by
  rw [ENNReal.add_div, mul_div_assoc, ENNReal.mul_div_cancel_right hV₀ hV]

/-- Lemma `lem:ruusc-transfer` for `𝒴_loc`: if `W` is ru-usc with constant `c`, so is `𝒴_loc W`. -/
theorem RUUSCWith.Ytloc {c : ℝ≥0} {W : Sp N → Mat m N → ℝ≥0∞} (hW : RUUSCWith c W) :
    RUUSCWith c (Ytloc W) := by
  refine RUUSCWith.of_le_affine fun η hη => ?_
  filter_upwards [hW.le_affine hη] with t ht x ξ
  have h1 : (1 + (η : ℝ≥0∞)) ≠ 0 := by simp
  have h2 : (1 + (η : ℝ≥0∞)) ≠ ⊤ := by simp
  unfold Homogenization.Ytloc
  calc limsup (fun ρ : ℝ => Yt W (cube ρ x) (t • ξ) / volume (cube ρ x)) (𝓝[>] 0)
      ≤ limsup (fun ρ : ℝ => (1 + (η : ℝ≥0∞)) * (Yt W (cube ρ x) ξ / volume (cube ρ x)) +
          (η : ℝ≥0∞) * c) (𝓝[>] 0) := by
        refine limsup_le_limsup ?_
        filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        rw [← affine_div_volume (volume_cube_pos hρ x).ne' (volume_cube_ne_top ρ x)]
        exact ENNReal.div_le_div_right (Yt_smul_le W _ t h1 h2 (fun y ζ => ht y ζ) ξ) _
    _ = (1 + (η : ℝ≥0∞)) * limsup (fun ρ : ℝ => Yt W (cube ρ x) ξ / volume (cube ρ x)) (𝓝[>] 0)
          + (η : ℝ≥0∞) * c := by
        rw [limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault),
          ENNReal.limsup_const_mul_of_ne_top h2]

/-- Lemma `lem:ruusc-transfer` for `ℋ_aff`. -/
theorem RUUSCWith.Haff {c : ℝ≥0} {W : Sp N → Mat m N → ℝ≥0∞} (hW : RUUSCWith c W) :
    RUUSCWith c (fun _ => Haff W) := by
  refine RUUSCWith.of_le_affine fun η hη => ?_
  filter_upwards [hW.le_affine hη] with t ht _ ξ
  have h1 : (1 + (η : ℝ≥0∞)) ≠ 0 := by simp
  have h2 : (1 + (η : ℝ≥0∞)) ≠ ⊤ := by simp
  simp only [Homogenization.Haff]
  rw [ENNReal.mul_iInf_of_ne h1 h2, ENNReal.iInf_add]
  refine iInf_mono fun k => ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [← affine_div_volume (volume_cube_pos hk 0).ne' (volume_cube_ne_top _ 0)]
  exact ENNReal.div_le_div_right (Yt_smul_le W _ t h1 h2 (fun y ζ => ht y ζ) ξ) _

/-- Lemma `lem:ruusc-transfer` for `𝒵_aff`. -/
theorem RUUSCWith.Zaff {c : ℝ≥0} {L : Mat m N → ℝ≥0∞} (hL : RUUSCWith c (fun _ => L)) :
    RUUSCWith c (fun _ => Zaff L) := by
  refine RUUSCWith.of_le_affine fun η hη => ?_
  filter_upwards [hL.le_affine hη] with t ht _ ξ
  have h1 : (1 + (η : ℝ≥0∞)) ≠ 0 := by simp
  have h2 : (1 + (η : ℝ≥0∞)) ≠ ⊤ := by simp
  have hY : volume (cube 1 (0 : Sp N)) = 1 := by rw [volume_cube]; simp
  have := Yt_smul_le (fun _ => L) (cube 1 0) t h1 h2 (fun _ ζ => ht 0 ζ) ξ
  rwa [hY, mul_one] at this

theorem RUUSC.Ytloc {W : Sp N → Mat m N → ℝ≥0∞} (hW : RUUSC W) : RUUSC (Ytloc W) :=
  let ⟨c, hc, h⟩ := hW; ⟨c, hc, h.Ytloc⟩

/-- `Λ = 𝒵_aff ℋ_aff L` inherits the ru-usc property of `L` (used in Step 2 with `L = 𝒴_loc W`). -/
theorem RUUSC.Zaff_Haff {L : Sp N → Mat m N → ℝ≥0∞} (hL : RUUSC L) :
    RUUSC (fun _ => Zaff (Haff L)) :=
  let ⟨c, hc, h⟩ := hL; ⟨c, hc, h.Haff.Zaff⟩

/-! ### Lemma `lem:consequences` (i): periodicity of `𝒴_loc W` -/

theorem comp_add_mem_Aff0 {U : Set (Sp N)} {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 U) (a : Sp N) :
    (fun y => φ (y + a)) ∈ Aff0 ((· + a) ⁻¹' U) := by
  obtain ⟨⟨K, hK⟩, h0, ⟨K', hK'⟩, n, V, ξ, hVo, hVU, hVd, hVf, hVc, hφV⟩ := hφ
  have hiso : Isometry (fun y : Sp N => y + a) := isometry_add_right a
  refine ⟨⟨K * 1, hK.comp hiso.lipschitz⟩, fun y hy => h0 _ hy,
    ⟨K' * 1, hK'.comp hiso.lipschitz.lipschitzOnWith (fun _ hy => hy)⟩, n,
    fun i => (· + a) ⁻¹' V i, ξ, fun i => (hVo i).preimage (continuous_add_const a),
    fun i => preimage_mono (hVU i), fun i j hij => (hVd hij).preimage _, fun i => ?_, ?_,
    fun i y hy => (hasFDerivAt_comp_add_right a).2 (hφV i _ hy)⟩
  · have hfr : (· + a) ⁻¹' frontier (V i) = frontier ((· + a) ⁻¹' V i) :=
      (Homeomorph.addRight a).preimage_frontier (V i)
    change volume ((· + a) ⁻¹' U ∩ frontier ((· + a) ⁻¹' V i)) = 0
    rw [← hfr, ← preimage_inter, measure_preimage_add_right]; exact hVf i
  · rw [← preimage_iUnion, ← preimage_sdiff, measure_preimage_add_right]; exact hVc

/-- Translation invariance of the affine Dirichlet problem for an integrand invariant under the
translation by `a`. -/
theorem Yt_preimage_add {W : Sp N → Mat m N → ℝ≥0∞} {a : Sp N} (hW : ∀ y, W (y + a) = W y)
    (U : Set (Sp N)) (ξ : Mat m N) : Yt W ((· + a) ⁻¹' U) ξ ≤ Yt W U ξ := by
  refine le_iInf₂ fun φ hφ => (iInf₂_le _ (comp_add_mem_Aff0 hφ a)).trans (le_of_eq ?_)
  have hmp := measurePreserving_add_right (volume : Measure (Sp N)) a
  have hemb : MeasurableEmbedding (fun y : Sp N => y + a) :=
    (MeasurableEquiv.addRight a).measurableEmbedding
  simp_rw [fderiv_comp_add_right]
  rw [← hmp.setLIntegral_comp_preimage_emb hemb (fun y => W y (ξ + fderiv ℝ φ y)) U]
  simp_rw [hW]

theorem Yt_preimage_add_eq {W : Sp N → Mat m N → ℝ≥0∞} {a : Sp N} (hW : ∀ y, W (y + a) = W y)
    (U : Set (Sp N)) (ξ : Mat m N) : Yt W ((· + a) ⁻¹' U) ξ = Yt W U ξ := by
  refine le_antisymm (Yt_preimage_add hW U ξ) ?_
  have hW' : ∀ y, W (y + -a) = W y := fun y => by rw [← hW (y + -a), neg_add_cancel_right]
  have := Yt_preimage_add hW' ((· + a) ⁻¹' U) ξ
  rwa [← preimage_comp, show ((· + a) ∘ (· + -a) : Sp N → Sp N) = id from
    funext fun y => neg_add_cancel_right y a, preimage_id] at this

/-- Lemma `lem:consequences` (i): (Z2) implies that `𝒴_loc W` is `1`-periodic. -/
theorem IsPeriodic.Ytloc {W : Sp N → Mat m N → ℝ≥0∞} (hW : IsPeriodic W) :
    IsPeriodic (Ytloc W) := by
  intro z x ξ
  set a : Sp N := fun i => (z i : ℝ)
  have hW' : ∀ y, W (y + -a) = W y := by
    intro y
    have h := hW (-z) y
    have e : (fun i => (((-z) i : ℤ) : ℝ)) = -a := by ext i; simp [a]
    rw [e] at h
    exact funext h
  have hcube : ∀ ρ, cube ρ (x + a) = (· + -a) ⁻¹' cube ρ x := by
    intro ρ; rw [cube_add]; rfl
  simp only [Homogenization.Ytloc, hcube, Yt_preimage_add_eq hW', measure_preimage_add_right]

/-! ### Remark `lEnvelopes` -/

theorem Yt_mono {L L' : Sp N → Mat m N → ℝ≥0∞} (h : L ≤ L') (U : Set (Sp N)) (ξ : Mat m N) :
    Yt L U ξ ≤ Yt L' U ξ :=
  iInf₂_mono fun _ _ => lintegral_mono fun y => h y _

theorem Ytloc_mono {L L' : Sp N → Mat m N → ℝ≥0∞} (h : L ≤ L') : Ytloc L ≤ Ytloc L' :=
  fun _ _ => limsup_le_limsup (Eventually.of_forall fun _ =>
    ENNReal.div_le_div_right (Yt_mono h _ _) _)

theorem Haff_mono {L L' : Sp N → Mat m N → ℝ≥0∞} (h : L ≤ L') : Haff L ≤ Haff L' :=
  fun _ => iInf_mono fun _ => ENNReal.div_le_div_right (Yt_mono h _ _) _

theorem Zaff_mono {L L' : Mat m N → ℝ≥0∞} (h : L ≤ L') : Zaff L ≤ Zaff L' :=
  fun _ => Yt_mono (fun _ => h) _ _

theorem Ytp_mono {p : ℝ≥0∞} {L L' : Sp N → Mat m N → ℝ≥0∞} (h : L ≤ L') (U : Set (Sp N))
    (ξ : Mat m N) : Ytp p L U ξ ≤ Ytp p L' U ξ :=
  iInf₂_mono fun _ _ => lintegral_mono fun y => h y _

theorem Hp_mono {p : ℝ≥0∞} {L L' : Sp N → Mat m N → ℝ≥0∞} (h : L ≤ L') : Hp p L ≤ Hp p L' :=
  fun _ => iInf_mono fun _ => ENNReal.div_le_div_right (Ytp_mono h _ _) _

theorem radial_mono {f f' : Mat m N → ℝ≥0∞} (h : f ≤ f') : radial f ≤ radial f' :=
  fun _ => liminf_le_liminf (Eventually.of_forall fun _ => h _)

/-- Remark `lEnvelopes` (ii): `𝒴 L(U,ξ) ≤ ∫_U L(y,ξ) dy`. -/
theorem Yt_le_lintegral (L : Sp N → Mat m N → ℝ≥0∞) {U : Set (Sp N)} (hU : IsOpen U)
    (ξ : Mat m N) : Yt L U ξ ≤ ∫⁻ y in U, L y ξ := by
  refine (iInf₂_le (0 : Sp N → Tgt m) (zero_mem_Aff0 hU)).trans (le_of_eq ?_)
  simp

/-- Remark `lEnvelopes` (ii): `𝒵_aff L₀ ≤ L₀`. -/
theorem Zaff_le (L₀ : Mat m N → ℝ≥0∞) : Zaff L₀ ≤ L₀ := by
  intro ξ
  refine (Yt_le_lintegral _ (isOpen_cube 1 0) ξ).trans (le_of_eq ?_)
  rw [setLIntegral_const, volume_cube]; simp

/-- Remark `lEnvelopes` (iii): `𝒵_aff ℋ_aff L ≤ ℋ_aff L`. -/
theorem Zaff_Haff_le (L : Sp N → Mat m N → ℝ≥0∞) : Zaff (Haff L) ≤ Haff L := Zaff_le _

/-! ### `G`-growth of `𝒴_loc W` and coercivity of `W` -/

/-- Remark `rem:B1c` (i): the set-function bound (Z3) implies the pointwise `G`-growth (Z1') of
`𝒴_loc h`. -/
theorem HasGGrowth.Ytloc {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {W : Sp N → Mat m N → ℝ≥0∞}
    (h : ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      (α : ℝ≥0∞) * volume U * G ξ ≤ Yt W U ξ ∧ Yt W U ξ ≤ β * volume U * (1 + G ξ)) :
    HasGGrowth G α β (Ytloc W) := by
  intro x ξ
  have key : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (α : ℝ≥0∞) * G ξ ≤ Yt W (cube ρ x) ξ / volume (cube ρ x) ∧
      Yt W (cube ρ x) ξ / volume (cube ρ x) ≤ β * (1 + G ξ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    have hV₀ := (volume_cube_pos hρ x).ne'
    have hV := volume_cube_ne_top ρ x
    have hb : Bornology.IsBounded (cube ρ x) := by
      refine (Metric.isBounded_Icc (fun i => x i - ρ / 2) (fun i => x i + ρ / 2)).subset ?_
      intro y hy
      exact ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩
    obtain ⟨h1, h2⟩ := h ξ _ (isOpen_cube ρ x) hb
    constructor
    · rw [ENNReal.le_div_iff_mul_le (Or.inl hV₀) (Or.inl hV)]
      calc (α : ℝ≥0∞) * G ξ * volume (cube ρ x) = α * volume (cube ρ x) * G ξ := by ring
        _ ≤ _ := h1
    · rw [ENNReal.div_le_iff hV₀ hV]
      calc Yt W (cube ρ x) ξ ≤ β * volume (cube ρ x) * (1 + G ξ) := h2
        _ = β * (1 + G ξ) * volume (cube ρ x) := by ring
  constructor
  · exact le_limsup_of_le (by isBoundedDefault) fun b hb =>
      (hb.and key).exists.elim fun _ h => h.2.1.trans h.1
  · exact limsup_le_of_le (by isBoundedDefault) (key.mono fun _ h => h.2)

/-- Lemma `lem:consequences` (ii): under (Z4) and (Z7), `c₀|ξ|ᵖ ≤ 𝒴_loc W(x,ξ) ≤ W(x,ξ)` off a null
set. -/
theorem coercive_W {p : ℝ} {c₀ : ℝ≥0} {W : Sp N → Mat m N → ℝ≥0∞}
    (h4 : IsCoercive p c₀ (Ytloc W)) (h7 : ∀ᵐ x, ∀ ξ, Ytloc W x ξ ≤ W x ξ) :
    ∀ᵐ x, ∀ ξ, ENNReal.ofReal (c₀ * ‖ξ‖ ^ p) ≤ Ytloc W x ξ ∧ Ytloc W x ξ ≤ W x ξ :=
  h7.mono fun x hx ξ => ⟨h4 x ξ, hx ξ⟩

/-! ### Product integrands `a(x) H(ξ)` (identity used in `th:product`(i)) -/

/-- `𝒵_aff (a H) = a 𝒵_aff H` for a constant `a ∈ ]0,∞[`. -/
theorem Zaff_const_mul (H : Mat m N → ℝ≥0∞) {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha : a ≠ ⊤) :
    Zaff (fun ξ => a * H ξ) = fun ξ => a * Zaff H ξ := by
  funext ξ
  simp only [Zaff, Yt]
  rw [ENNReal.mul_iInf_of_ne ha₀ ha]
  refine iInf_congr fun φ => ?_
  rw [ENNReal.mul_iInf_of_ne ha₀ ha]
  exact iInf_congr fun _ => lintegral_const_mul' _ _ ha

/-- Identity of `th:product`(i): if `W(x,ξ) = a(x) H(ξ)` and
`𝒴_loc W(x,·) = 𝒵_aff W(x,·)` for a.e. `x`, then
`𝒴_loc W(x,ξ) = a(x) 𝒵_aff H(ξ)` for a.e. `x` and every `ξ`. -/
theorem Ytloc_eq_mul_Zaff (a : Sp N → ℝ≥0∞) (ha₀ : ∀ x, a x ≠ 0) (ha : ∀ x, a x ≠ ⊤)
    (H : Mat m N → ℝ≥0∞)
    (h : ∀ᵐ x, Ytloc (fun y ξ => a y * H ξ) x = Zaff (fun ξ => a x * H ξ)) :
    ∀ᵐ x, ∀ ξ, Ytloc (fun y ξ => a y * H ξ) x ξ = a x * Zaff H ξ :=
  h.mono fun x hx ξ => by rw [hx, Zaff_const_mul H (ha₀ x) (ha x)]

/-- Former form of `lem:measurability`: under the hypotheses of `Ytloc_eq_mul_Zaff`,
if `a` and `𝒵_aff H` are Borel measurable, then `𝒴_loc W` coincides, for a.e. `x` and
every `ξ`, with the jointly measurable function `(x, ξ) ↦ a(x) 𝒵_aff H(ξ)`. This is (H6) up to
modification on a Lebesgue-null set of `x`; the article now proves exact (H6) for finite sums of
products (`measurable_Ytloc_sumW`). It does not prove the literal field
`Hypotheses.measurable_Ytloc` (`Measurable (uncurry (Ytloc W))`) without that modification.
Borel measurability of `H` is not needed for this conclusion. -/
theorem Ytloc_ae_eq_measurable_of_mul (a : Sp N → ℝ≥0∞) (ha_meas : Measurable a)
    (ha₀ : ∀ x, a x ≠ 0) (ha : ∀ x, a x ≠ ⊤) (H : Mat m N → ℝ≥0∞)
    (hZ : Measurable (Zaff H))
    (h : ∀ᵐ x, Ytloc (fun y ξ => a y * H ξ) x = Zaff (fun ξ => a x * H ξ)) :
    ∃ W' : Sp N → Mat m N → ℝ≥0∞, Measurable (uncurry W') ∧
      ∀ᵐ x, ∀ ξ, Ytloc (fun y ξ => a y * H ξ) x ξ = W' x ξ := by
  refine ⟨fun x ξ => a x * Zaff H ξ, ?_, ?_⟩
  · exact (ha_meas.comp measurable_fst).mul (hZ.comp measurable_snd)
  · exact h.mono fun x hx ξ => by
      rw [hx, Zaff_const_mul H (ha₀ x) (ha x)]

end Homogenization
