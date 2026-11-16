import Homogenization.Product

/-! # Section 3: Remark `rem:B1c` (ii) and Proposition `prop:Z3suff` in the form of the paper

* `Ytloc_le_limsup_avg` and `Ytloc_le_sum_of_pos`: Remark `rem:B1c` (ii). For
  `h(x,ξ) = ∑ᵢ aᵢ(x) Hᵢ(ξ)` with `aᵢ > 0` everywhere and locally integrable, and `Hᵢ` arbitrary,
  `𝒴_loc h ≤ h` outside one null set of `x` (hypothesis (H7)).
* `prop_Z3suff_paper`: Proposition `prop:Z3suff` with the hypotheses of the paper: no periodicity,
  singularity of `G` on `∂(dom G)` only. The hypothesis `0 ∈ int(dom G)` of (H1) is not needed.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- **Remark `rem:B1c` (ii), first assertion**:
`𝒴_loc h(x,ξ) ≤ limsup_{ρ→0} ⨍_{Q_ρ(x)} h(y,ξ) dy`. -/
theorem Ytloc_le_limsup_avg (h : Sp N → Mat m N → ℝ≥0∞) (x : Sp N) (ξ : Mat m N) :
    Ytloc h x ξ ≤ limsup (fun ρ : ℝ => (∫⁻ y in cube ρ x, h y ξ) / volume (cube ρ x)) (𝓝[>] 0) :=
  limsup_le_limsup (Eventually.of_forall fun ρ =>
    ENNReal.div_le_div_right (Yt_le_lintegral h (isOpen_cube ρ x) ξ) _)

/-- **Remark `rem:B1c` (ii)**: for `h(x,ξ) = ∑ᵢ aᵢ(x) Hᵢ(ξ)` with `aᵢ : ℝᴺ → ]0,∞[` locally
integrable and `Hᵢ : 𝕄 → [0,∞]` arbitrary, there is one null set outside of which
`𝒴_loc h(x,ξ) ≤ h(x,ξ)` for every `ξ`, i.e. `h` satisfies (H7). -/
theorem Ytloc_le_sum_of_pos [NeZero N] {ν : ℕ} {a : Fin ν → Sp N → ℝ}
    {H : Fin ν → Mat m N → ℝ≥0∞} (hpos : ∀ i x, 0 < a i x)
    (hloc : ∀ i, LocallyIntegrable (a i) volume) :
    ∀ᵐ x, ∀ ξ, Ytloc (fun x ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) x ξ ≤
      ∑ i, ENNReal.ofReal (a i x) * H i ξ := by
  have hleb := fun i => ae_tendsto_setLIntegral_affMap_div (hloc i)
  filter_upwards [ae_all_iff.2 hleb] with x hx ξ
  set h : Sp N → Mat m N → ℝ≥0∞ := fun x ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ
  change Ytloc h x ξ ≤ h x ξ
  by_cases htop : ∃ i, H i ξ = ⊤
  · obtain ⟨i, hi⟩ := htop
    have : h x ξ = ⊤ := by
      apply top_unique
      calc ⊤ = ENNReal.ofReal (a i x) * H i ξ := by
            rw [hi, ENNReal.mul_top (by simpa using hpos i x)]
        _ ≤ h x ξ := Finset.single_le_sum (f := fun j => ENNReal.ofReal (a j x) * H j ξ)
            (fun _ _ => zero_le) (Finset.mem_univ i)
    rw [this]; exact le_top
  push Not at htop
  have hcube : ∀ i, Tendsto (fun r : ℝ => (∫⁻ y in cube r x, ENNReal.ofReal (a i y)) /
      volume (cube r x)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (a i x))) := by
    intro i
    refine (hx i (cube 1 0) (isOpen_cube 1 0) (isBounded_cube 1 0)
      ⟨0, self_mem_cube one_pos 0⟩).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [preimage_affMap_cube hr x]
  have hsum : Tendsto (fun r : ℝ => (∫⁻ y in cube r x, h y ξ) / volume (cube r x)) (𝓝[>] 0)
      (𝓝 (h x ξ)) := by
    have hT : Tendsto (fun r : ℝ => ∑ i, H i ξ *
        ((∫⁻ y in cube r x, ENNReal.ofReal (a i y)) / volume (cube r x))) (𝓝[>] 0)
        (𝓝 (∑ i, H i ξ * ENNReal.ofReal (a i x))) :=
      tendsto_finsetSum _ fun i _ => ENNReal.Tendsto.const_mul (hcube i) (Or.inr (htop i))
    refine (hT.congr fun r => ?_).trans (by simp only [h, mul_comm]; exact le_rfl)
    have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin ν)), AEMeasurable
        (fun y => ENNReal.ofReal (a i y) * H i ξ) (volume.restrict (cube r x)) :=
      fun i _ => ((hloc i).aestronglyMeasurable.aemeasurable.ennreal_ofReal.mul_const _).restrict
    simp only [h]
    rw [lintegral_finsetSum' _ hmeas, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_mul_const'' _ (hloc i).aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict,
      div_eq_mul_inv]
    ring
  exact (Ytloc_le_limsup_avg h x ξ).trans hsum.limsup_eq.le

/-- **Proposition `prop:Z3suff`**, in the form of the paper: `G` convex and lower semicontinuous
with `dom G` open and `G(tξ) → ∞` as `t → 1⁻` for every `ξ ∈ ∂(dom G)`; `W` satisfies the
set-function bound (H3) and (H6), and `𝒴_loc W(x,·)` is upper semicontinuous for a.e. `x`. Then
`𝒵_aff ℋ_aff(𝒴_loc W) ≤ \widehat{ℋ(𝒴_loc W)}` (H8). Neither the periodicity of `W` nor
`0 ∈ int(dom G)` is assumed. Step 3 follows the paper: `𝒵_aff K ≤ K` and the continuity of
`𝒵_aff K` on the interior of its domain (`citedZaffLocLip`). -/
theorem prop_Z3suff_paper [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {W : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    (hGo : IsOpen (dom G))
    (hGsing : ∀ ξ ∈ frontier (dom G), Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hα : 0 < α)
    (hset : ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      (α : ℝ≥0∞) * volume U * G ξ ≤ Yt W U ξ ∧ Yt W U ξ ≤ β * volume U * (1 + G ξ))
    (hYm : Measurable (uncurry (Ytloc W)))
    (husc : ∀ᵐ x, UpperSemicontinuous (Ytloc W x)) (ξ : Mat m N) :
    Zaff (Haff (Ytloc W)) ξ ≤ radial (Hp (ENNReal.ofReal p) (Ytloc W)) ξ := by
  have hLgr : HasGGrowth G α β (Ytloc W) := HasGGrowth.Ytloc hset
  have hEq : Hp (ENNReal.ofReal p) (Ytloc W) = Haff (Ytloc W) :=
    funext fun ζ => (Haff_eq_Hp_of_usc_of_isOpen (p := p) hG hGlsc hGo hα hYm hLgr husc ζ).symm
  by_cases hξ : ξ ∈ dom G
  · set K := Haff (Ytloc W)
    have hdom : dom G ⊆ dom (Zaff K) := by
      intro ζ hζ
      have hK : K ζ ≤ β * (1 + G ζ) := by
        rw [← hEq]; exact hLgr.Hp_le _ ζ
      have hfin : (β : ℝ≥0∞) * (1 + G ζ) < ⊤ :=
        ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hζ⟩)
      exact ((Zaff_le K ζ).trans hK).trans_lt hfin
    have hint : ξ ∈ interior (dom (Zaff K)) := interior_maximal hdom hGo hξ
    obtain ⟨C, s, hs, hC⟩ := citedZaffLocLip (N := N) (m := m) K ξ hint
    have hc0 : ContinuousAt (fun ζ => ENNReal.ofReal (Zaff K ζ).toReal) ξ :=
      ENNReal.continuous_ofReal.continuousAt.comp
        ((hC.continuousOn ξ (mem_of_mem_nhds hs)).continuousAt hs)
    have hc : ContinuousAt (Zaff K) ξ := by
      refine hc0.congr ?_
      filter_upwards [isOpen_interior.mem_nhds hint] with ζ hζ
      exact ENNReal.ofReal_toReal (interior_subset hζ).ne
    have htend : Tendsto (fun t : ℝ => t • ξ) (𝓝[<] 1) (𝓝 ξ) := by
      have h : Tendsto (fun t : ℝ => t • ξ) (𝓝 1) (𝓝 ((1 : ℝ) • ξ)) :=
        (continuous_id.smul continuous_const).continuousAt
      rw [one_smul] at h
      exact h.mono_left nhdsWithin_le_nhds
    rw [radial, hEq, ← ((hc.tendsto.comp htend).liminf_eq)]
    exact liminf_le_liminf (Eventually.of_forall fun t => Zaff_le K (t • ξ))
  · have htop : Tendsto (fun t : ℝ => Hp (ENNReal.ofReal p) (Ytloc W) (t • ξ)) (𝓝[<] 1)
        (𝓝 ⊤) := by
      have hα0 : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
      have h := ENNReal.Tendsto.const_mul (a := (α : ℝ≥0∞))
        (tendsto_top_of_not_mem_dom hGo hGsing hξ) (Or.inl ENNReal.top_ne_zero)
      rw [ENNReal.mul_top hα0] at h
      exact tendsto_nhds_top_mono h (Eventually.of_forall fun t =>
        hLgr.mul_le_Hp_of_isOpen hG hGo hα (t • ξ))
    rw [radial, htop.liminf_eq]
    exact le_top

end Homogenization
