import Homogenization.Recovery
import Homogenization.Jensen
import Homogenization.Examples.ProperDomain

/-! # Lemma `lem:consequences` (iii): growth and coercivity of the envelopes

* `ConvexENN.volume_mul_le_lintegral_W1p0_of_lsc`: Jensen's inequality for Sobolev correctors at
  every `ξ ∈ 𝕄`, for `G` convex, lower semicontinuous with `0 ∈ int(dom G)` (H1).
* `HasGGrowth.le_Hp_of_lsc`, `HasGGrowth.Hp`: under (H1), `ℋ_p L` has `(α,β)`-`G`-growth on all
  of `𝕄` (not only on `int(dom G)`, compare `HasGGrowth.le_Hp`).
* `IsCoercive.Hp`, `IsCoercive.Haff`, `IsCoercive.Zaff_Haff`: the `p`-coercivity of `L` passes to
  `ℋ_p L`, `ℋ_aff L` and `𝒵_aff ℋ_aff L`, with the same constant.
* `lem_consequences_iii`: Lemma `lem:consequences` (iii) assembled from (H1), (H3) and (H4).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- Convexity is preserved by the dilation `ζ ↦ G(sζ)`. -/
theorem ConvexENN.comp_smul {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) (s : ℝ) :
    ConvexENN (fun ζ => G (s • ζ)) := by
  intro ξ ζ t ht
  have h := hG (s • ξ) (s • ζ) t ht
  have heq : s • ((t : ℝ) • ξ + ((1 - t : ℝ≥0) : ℝ) • ζ) =
      (t : ℝ) • (s • ξ) + ((1 - t : ℝ≥0) : ℝ) • (s • ζ) := by
    rw [smul_add, smul_comm s (t : ℝ) ξ, smul_comm s ((1 - t : ℝ≥0) : ℝ) ζ]
  simpa only [heq] using h

section Jensen

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-- **Jensen's inequality** for Sobolev correctors at every point: for `G` convex, lower
semicontinuous with `0 ∈ int(dom G)`, `|U| G(ξ) ≤ ∫_U G(ξ + ∇φ)` for every `ξ ∈ 𝕄`. -/
theorem ConvexENN.volume_mul_le_lintegral_W1p0_of_lsc {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGlsc : LowerSemicontinuous G) (h0 : (0 : Mat m N) ∈ interior (dom G))
    {U : Set (Sp N)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUf : volume (frontier U) = 0) (hU0 : volume U ≠ 0)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 (ENNReal.ofReal p) U) (ξ : Mat m N) :
    volume U * G ξ ≤ ∫⁻ y in U, G (ξ + u.2 y) := by
  by_cases hcl : ξ ∈ closure (dom G)
  swap
  · rw [hG.lintegral_W1p0_eq_top_of_not_mem_closure_dom hUo hUb hUf hU0 hu hcl]
    exact le_top
  set A := ∫⁻ y in U, G (ξ + u.2 y) with hA_def
  by_cases hA : A = ⊤
  · rw [hA]; exact le_top
  have hUt : volume U ≠ ⊤ := hUb.measure_lt_top.ne
  set C := G 0 * volume U
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top (interior_subset h0 : (0 : Mat m N) ∈ dom G).ne hUt
  -- the inequality at `tξ`, `0 ≤ t < 1`
  have key : ∀ t : ℝ≥0, t < 1 →
      volume U * G ((t : ℝ) • ξ) ≤ (t : ℝ≥0∞) * A + ((1 - t : ℝ≥0) : ℝ≥0∞) * C := by
    intro t ht
    have hint : (t : ℝ) • ξ ∈ interior (dom G) := by
      have h := hG.convex_dom.combo_interior_closure_mem_interior h0 hcl
        (a := ((1 - t : ℝ≥0) : ℝ)) (b := (t : ℝ)) (by simpa using ht) t.2
        (by rw [NNReal.coe_sub ht.le]; simp)
      simpa using h
    have hG' := hG.comp_smul (t : ℝ)
    have hsub : (fun ζ => (t : ℝ) • ζ) ⁻¹' interior (dom G) ⊆
        dom (fun ζ => G ((t : ℝ) • ζ)) :=
      fun ζ (hζ : (t : ℝ) • ζ ∈ interior (dom G)) => (interior_subset hζ : (t : ℝ) • ζ ∈ dom G)
    have hξ' : ξ ∈ interior (dom fun ζ => G ((t : ℝ) • ζ)) :=
      interior_maximal hsub (isOpen_interior.preimage (continuous_const_smul _)) hint
    have hJ := hG'.volume_mul_le_lintegral_W1p0 hUo hUb hUf hu hξ'
    have hpt : ∀ y, G ((t : ℝ) • (ξ + u.2 y)) ≤ t * G (ξ + u.2 y) + (1 - t : ℝ≥0) * G 0 := by
      intro y
      have h := hG (ξ + u.2 y) 0 t ht.le
      simpa only [smul_zero, add_zero] using h
    calc volume U * G ((t : ℝ) • ξ)
        ≤ ∫⁻ y in U, G ((t : ℝ) • (ξ + u.2 y)) := hJ
      _ ≤ ∫⁻ y in U, ((t : ℝ≥0∞) * G (ξ + u.2 y) + ((1 - t : ℝ≥0) : ℝ≥0∞) * G 0) :=
          lintegral_mono hpt
      _ = (t : ℝ≥0∞) * A + ((1 - t : ℝ≥0) : ℝ≥0∞) * C := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
            setLIntegral_const, hA_def, mul_assoc]
  -- passage to the limit `t → 1⁻`
  have hsmul : Tendsto (fun t : ℝ≥0 => (t : ℝ) • ξ) (𝓝[<] 1) (𝓝 ξ) := by
    have h : Tendsto (fun t : ℝ≥0 => (t : ℝ) • ξ) (𝓝 1) (𝓝 (((1 : ℝ≥0) : ℝ) • ξ)) :=
      ((NNReal.continuous_coe.smul continuous_const).tendsto 1)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) * A + ((1 - t : ℝ≥0) : ℝ≥0∞) * C) (𝓝[<] 1)
      (𝓝 A) := by
    have h1 : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞)) (𝓝[<] 1) (𝓝 1) :=
      (ENNReal.continuous_coe.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans (by simp)
    have h2 : Tendsto (fun t : ℝ≥0 => ((1 - t : ℝ≥0) : ℝ≥0∞)) (𝓝[<] 1) (𝓝 0) := by
      have : Tendsto (fun t : ℝ≥0 => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      have h := (ENNReal.continuous_coe.tendsto _).comp
        (this.mono_left (nhdsWithin_le_nhds (s := Iio 1)))
      rw [tsub_self, ENNReal.coe_zero] at h
      exact h
    have := (ENNReal.Tendsto.mul_const h1 (Or.inr hA)).add
      (ENNReal.Tendsto.mul_const h2 (Or.inr hC))
    simpa using this
  have hy : ∀ y < G ξ, y ≤ A / volume U := by
    intro y hy
    rw [ENNReal.le_div_iff_mul_le (Or.inl hU0) (Or.inl hUt), mul_comm]
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] 1, volume U * y ≤
        (t : ℝ≥0∞) * A + ((1 - t : ℝ≥0) : ℝ≥0∞) * C := by
      filter_upwards [hsmul.eventually (hGlsc ξ y hy), self_mem_nhdsWithin] with t ht ht1
      exact (by gcongr : volume U * y ≤ volume U * G ((t : ℝ) • ξ)).trans (key t ht1)
    have : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, one_pos⟩
    exact ge_of_tendsto hF hev
  have hle : G ξ ≤ A / volume U := le_of_forall_lt_imp_le_of_dense hy
  rwa [ENNReal.le_div_iff_mul_le (Or.inl hU0) (Or.inl hUt), mul_comm] at hle

/-- **Lemma `lem:consequences` (iii), lower bound for `ℋ`**: under (H1), `α G ≤ ℋ_p L` on all
of `𝕄`. -/
theorem HasGGrowth.le_Hp_of_lsc {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGlsc : LowerSemicontinuous G) (h0 : (0 : Mat m N) ∈ interior (dom G)) {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (h : HasGGrowth G α β L) (ξ : Mat m N) :
    (α : ℝ≥0∞) * G ξ ≤ Hp (ENNReal.ofReal p) L ξ := by
  refine le_iInf fun k => ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [ENNReal.le_div_iff_mul_le (Or.inl (volume_cube_pos hk 0).ne')
    (Or.inl (volume_cube_ne_top _ 0))]
  refine le_iInf₂ fun u hu => ?_
  have hJ := hG.volume_mul_le_lintegral_W1p0_of_lsc hGlsc h0 (isOpen_cube _ _)
    (isBounded_cube _ _) (volume_frontier_cube _ _) (volume_cube_pos hk 0).ne' hu ξ
  calc (α : ℝ≥0∞) * G ξ * volume (cube ((k : ℝ) + 1) (0 : Sp N))
      = α * (volume (cube ((k : ℝ) + 1) (0 : Sp N)) * G ξ) := by ring
    _ ≤ α * ∫⁻ y in cube ((k : ℝ) + 1) 0, G (ξ + u.2 y) := by gcongr
    _ = ∫⁻ y in cube ((k : ℝ) + 1) 0, α * G (ξ + u.2 y) :=
        (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
    _ ≤ ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ξ + u.2 y) := lintegral_mono fun y => (h y _).1

/-- **Lemma `lem:consequences` (iii) for `ℋ`**: under (H1), if `L` has `(α,β)`-`G`-growth, so
does `ℋ_p L`. -/
theorem HasGGrowth.Hp {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGlsc : LowerSemicontinuous G) (h0 : (0 : Mat m N) ∈ interior (dom G)) {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (h : HasGGrowth G α β L) :
    HasGGrowth G α β (fun _ => Homogenization.Hp (ENNReal.ofReal p) L) :=
  fun _ ξ => ⟨h.le_Hp_of_lsc hG hGlsc h0 ξ, h.Hp_le _ ξ⟩

/-- The coercivity density `ξ ↦ c₀ |ξ|ᵖ` is convex for `p ≥ 1`. -/
theorem convexENN_coercive (c₀ : ℝ≥0) :
    ConvexENN (fun ξ : Mat m N => ENNReal.ofReal (c₀ * ‖ξ‖ ^ p)) := by
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.mp hP.out
  refine convexENN_of_nonneg_convexOn (fun χ => by positivity) ?_
  have := (norm_rpow_convexOn (m := m) (N := N) p hp).smul c₀.2
  simpa [Pi.smul_def, smul_eq_mul] using this

/-- **Lemma `lem:consequences` (iii), coercivity of `ℋ`**: `c₀|ξ|ᵖ ≤ ℋ_p L(ξ)`. -/
theorem IsCoercive.Hp {c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞} (hL : IsCoercive p c₀ L) :
    IsCoercive p c₀ (fun _ => Homogenization.Hp (ENNReal.ofReal p) L) := by
  intro _ ξ
  set f : Mat m N → ℝ≥0∞ := fun ξ => ENNReal.ofReal (c₀ * ‖ξ‖ ^ p)
  have hgr : HasGGrowth f 1 1 (fun _ => f) := fun _ ζ => by
    constructor
    · simp
    · simp only [ENNReal.coe_one, one_mul]; exact le_add_self
  have hint : ξ ∈ interior (dom f) := by
    have : dom f = univ := eq_univ_of_forall fun ζ => ENNReal.ofReal_lt_top
    simp [this]
  have h1 := hgr.le_Hp (p := p) (convexENN_coercive c₀) hint
  rw [ENNReal.coe_one, one_mul] at h1
  exact h1.trans (Hp_mono (fun x ζ => hL x ζ) ξ)

end Jensen

/-- **Lemma `lem:consequences` (iii), coercivity of `ℋ_aff`**. -/
theorem IsCoercive.Haff {p : ℝ} (hp : 1 ≤ p) {c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hL : IsCoercive p c₀ L) : IsCoercive p c₀ (fun _ => Homogenization.Haff L) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  intro _ ξ
  have h := Haff_mono (L := fun _ ξ => ENNReal.ofReal (c₀ * ‖ξ‖ ^ p)) (L' := L)
    (fun x ζ => hL x ζ) ξ
  rwa [(convexENN_coercive (p := p) c₀).Haff_eq] at h

/-- **Lemma `lem:consequences` (iii), coercivity of `𝒵_aff ℋ_aff`**. -/
theorem IsCoercive.Zaff_Haff {p : ℝ} (hp : 1 ≤ p) {c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hL : IsCoercive p c₀ L) :
    IsCoercive p c₀ (fun _ => Homogenization.Zaff (Homogenization.Haff L)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  intro _ ξ
  have h := Zaff_mono (L := fun ξ => ENNReal.ofReal (c₀ * ‖ξ‖ ^ p))
    (L' := Homogenization.Haff L) (fun ζ => (hL.Haff hp) 0 ζ) ξ
  rwa [(convexENN_coercive (p := p) c₀).Zaff_eq] at h

/-- Under `(α,β)`-`G`-growth with `α > 0`, `dom L(x,·) = dom G` for every `x`. -/
theorem HasGGrowth.dom_eq {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (h : HasGGrowth G α β L) (hα : 0 < α) (x : Sp N) : dom (L x) = dom G := by
  ext ξ
  refine ⟨fun hξ => h.G_finite_of_L_finite hα hξ, fun hξ => ?_⟩
  exact (h x ξ).2.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hξ⟩))

/-- **Lemma `lem:consequences` (iii)**. Under (H1) and (H3), each of `𝒴_loc W`, `ℋ(𝒴_loc W)`,
`ℋ_aff(𝒴_loc W)` and `𝒵_aff ℋ_aff(𝒴_loc W)` has `(α,β)`-`G`-growth, hence effective domain
`dom G`; under (H4) with constant `c₀`, all four are `p`-coercive with constant `c₀`. The
measurability (H6), needed in the paper for the integrals to be Lebesgue integrals, is not used
(Lean integrals are lower integrals). -/
theorem lem_consequences_iii {p : ℝ} (hp : 1 ≤ p) {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGlsc : LowerSemicontinuous G) (h0 : (0 : Mat m N) ∈ interior (dom G)) {α β : ℝ≥0}
    (hα : 0 < α) {W : Sp N → Mat m N → ℝ≥0∞}
    (hset : ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      (α : ℝ≥0∞) * volume U * G ξ ≤ Yt W U ξ ∧ Yt W U ξ ≤ β * volume U * (1 + G ξ)) :
    (HasGGrowth G α β (Ytloc W) ∧
      HasGGrowth G α β (fun _ => Homogenization.Hp (ENNReal.ofReal p) (Ytloc W)) ∧
      HasGGrowth G α β (fun _ => Homogenization.Haff (Ytloc W)) ∧
      HasGGrowth G α β (fun _ => Homogenization.Zaff (Homogenization.Haff (Ytloc W)))) ∧
    (∀ x, dom (Ytloc W x) = dom G) ∧ dom (Homogenization.Hp (ENNReal.ofReal p) (Ytloc W)) = dom G ∧
      dom (Homogenization.Haff (Ytloc W)) = dom G ∧
      dom (Homogenization.Zaff (Homogenization.Haff (Ytloc W))) = dom G ∧
    ∀ c₀ : ℝ≥0, IsCoercive p c₀ (Ytloc W) →
      IsCoercive p c₀ (fun _ => Homogenization.Hp (ENNReal.ofReal p) (Ytloc W)) ∧
      IsCoercive p c₀ (fun _ => Homogenization.Haff (Ytloc W)) ∧
      IsCoercive p c₀ (fun _ => Homogenization.Zaff (Homogenization.Haff (Ytloc W))) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  have hY : HasGGrowth G α β (Ytloc W) := HasGGrowth.Ytloc hset
  have hH : HasGGrowth G α β (fun _ => Homogenization.Hp (ENNReal.ofReal p) (Ytloc W)) :=
    hY.Hp hG hGlsc h0
  have hA : HasGGrowth G α β (fun _ => Homogenization.Haff (Ytloc W)) := hY.Haff hG
  have hZ : HasGGrowth G α β (fun _ => Homogenization.Zaff (Homogenization.Haff (Ytloc W))) :=
    hA.Zaff hG
  refine ⟨⟨hY, hH, hA, hZ⟩, hY.dom_eq hα, hH.dom_eq hα 0, hA.dom_eq hα 0, hZ.dom_eq hα 0,
    fun c₀ hc => ⟨hc.Hp, hc.Haff hp, hc.Zaff_Haff hp⟩⟩

end Homogenization
