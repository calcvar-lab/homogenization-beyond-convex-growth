import Homogenization.USCIneq
import Homogenization.Subadditive

/-! # Lemma `lemma_osc_general`

Identification of the localized envelope: under a one-sided oscillation condition, a uniform
Lebesgue-point condition and upper semicontinuity, `𝒴_loc h(x,·) = 𝒵_aff h(x,·)` and it is upper
semicontinuous, for a.e. `x` (`lemma_osc_general`). Lemma `lem:sumosc` is not proved here.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- The center of a cube of positive side length belongs to the cube. -/
theorem self_mem_cube {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) : x ∈ cube ρ x := by
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo]
  intro i; constructor <;> linarith

/-- Step 1 of `lemma_osc_general`: under the one-sided oscillation condition (i) at `x`,
`𝒵_aff h(x,·) ≤ 𝒴_loc h(x,·)`. Condition (i) is stated pointwise:
`h(x,ξ) ≤ (1 + ε) h(z,ξ)` for `z ∈ Q_ρ(x)`, which is equivalent to the paper's
`(1 + ε) inf_{Q_ρ(x)} h(·,ξ) ≥ h(x,ξ)`. -/
theorem Zaff_le_Ytloc_of_osc [NeZero N] {h : Sp N → Mat m N → ℝ≥0∞} {x : Sp N}
    (hosc : ∀ ε : ℝ≥0, 0 < ε → ∃ ρ > 0, ∀ z ∈ cube ρ x, ∀ ξ, h x ξ ≤ (1 + ε) * h z ξ)
    (ξ : Mat m N) : Zaff (h x) ξ ≤ Ytloc h x ξ := by
  have key : ∀ ε : ℝ≥0, 0 < ε → Zaff (h x) ξ ≤ (1 + ε) * Ytloc h x ξ := by
    intro ε hε
    obtain ⟨ρ₀, hρ₀, hρ₀h⟩ := hosc ε hε
    have hε0 : (1 + (ε : ℝ≥0∞)) ≠ 0 := by positivity
    have hεtop : (1 + (ε : ℝ≥0∞)) ≠ ⊤ := by simp
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Zaff (h x) ξ / (1 + ε) ≤
        Yt h (cube ρ x) ξ / volume (cube ρ x) := by
      filter_upwards [Ioo_mem_nhdsGT hρ₀] with ρ hρ
      have hsub : cube ρ x ⊆ cube ρ₀ x := SubaddCube.cube_subset_cube hρ.2.le x
      have hD0 := (volume_cube_pos hρ.1 x).ne'
      have hDtop := volume_cube_ne_top ρ x
      have hZ := aff0_domainIndependence (h x) (isOpen_cube ρ x)
        (isBounded_cube ρ x) ⟨x, self_mem_cube hρ.1 x⟩ (volume_frontier_cube ρ x) ξ
      have hY : Yt (fun _ => h x) (cube ρ x) ξ ≤ (1 + ε) * Yt h (cube ρ x) ξ := by
        simp only [Yt]
        rw [ENNReal.mul_iInf_of_ne hε0 hεtop]
        refine le_iInf fun φ => ?_
        rw [ENNReal.mul_iInf_of_ne hε0 hεtop]
        refine le_iInf fun hφ => (iInf₂_le φ hφ).trans ?_
        rw [← lintegral_const_mul' _ _ hεtop]
        exact setLIntegral_mono' (isOpen_cube ρ x).measurableSet
          fun z hz => hρ₀h z (hsub hz) _
      apply ENNReal.div_le_of_le_mul
      rw [← hZ]
      calc (volume (cube ρ x))⁻¹ * Yt (fun _ => h x) (cube ρ x) ξ
          ≤ (volume (cube ρ x))⁻¹ * ((1 + ε) * Yt h (cube ρ x) ξ) := by gcongr
        _ = Yt h (cube ρ x) ξ / volume (cube ρ x) * (1 + ε) := by
          rw [div_eq_mul_inv]; ring
    have hlim : Zaff (h x) ξ / (1 + ε) ≤ Ytloc h x ξ :=
      le_limsup_of_frequently_le hev.frequently (by isBoundedDefault)
    rwa [ENNReal.div_le_iff hε0 hεtop, mul_comm] at hlim
  by_cases hY : Ytloc h x ξ = ⊤
  · rw [hY]; exact le_top
  have htend : Tendsto (fun ε : ℝ≥0 => (1 + (ε : ℝ≥0∞)) * Ytloc h x ξ) (𝓝[>] 0)
      (𝓝 (Ytloc h x ξ)) := by
    have h1 : Tendsto (fun ε : ℝ≥0 => (1 + (ε : ℝ≥0∞))) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun ε : ℝ≥0 => (1 + (ε : ℝ≥0∞))) (𝓝 0) (𝓝 (1 + ((0 : ℝ≥0) : ℝ≥0∞))) :=
        tendsto_const_nhds.add (ENNReal.continuous_coe.tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hY)
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-- Step 2 of `lemma_osc_general`: if `x` is a Lebesgue point of `h(·,ξ)` in the sense of
condition (ii) for every `ξ` with `h(x,ξ) < ∞` and every nonempty bounded open `O`, then
`𝒴_loc h(x,·) ≤ 𝒵_aff h(x,·)`. Here `affMap r x ⁻¹' O = x + rO`. -/
theorem Ytloc_le_Zaff_of_lebesgue [NeZero N] {h : Sp N → Mat m N → ℝ≥0∞} {x : Sp N}
    (hleb : ∀ ξ, h x ξ < ⊤ → ∀ O : Set (Sp N), IsOpen O → Bornology.IsBounded O →
      O.Nonempty → Tendsto (fun r : ℝ => (∫⁻ y in affMap r x ⁻¹' O, h y ξ) /
        volume (affMap r x ⁻¹' O)) (𝓝[>] 0) (𝓝 (h x ξ)))
    (ξ : Mat m N) : Ytloc h x ξ ≤ Zaff (h x) ξ := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ hZ => ?_
  have hlt : Zaff (h x) ξ < Zaff (h x) ξ + δ :=
    ENNReal.lt_add_right hZ.ne (by exact_mod_cast hδ.ne')
  obtain ⟨φ, hφ, hφlt⟩ : ∃ φ ∈ (Aff0 (cube 1 (0 : Sp N)) : Set (Sp N → Tgt m)),
      ∫⁻ y in cube 1 0, h x (ξ + fderiv ℝ φ y) < Zaff (h x) ξ + δ := by
    have := hlt
    simp only [Zaff, Yt, iInf_lt_iff] at this
    obtain ⟨φ, hφ, hlt'⟩ := this
    exact ⟨φ, hφ, hlt'⟩
  obtain ⟨K, n, V, ζ, -, -, hVo, hVU, hVd, -, hVc, hφV⟩ := Aff0.data hφ
  have hVb : ∀ i, Bornology.IsBounded (V i) := fun i => (isBounded_cube 1 0).subset (hVU i)
  have hsplit1 : ∫⁻ y in cube 1 0, h x (ξ + fderiv ℝ φ y) =
      ∑ i, volume (V i) * h x (ξ + ζ i) := by
    rw [lintegral_eq_sum_pieces_fintype hVo hVU hVd hVc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet (g := fun _ => h x (ξ + ζ i))
      (fun y hy => by rw [(hφV i y hy).fderiv]), setLIntegral_const, mul_comm]
  have hfin : ∀ i, (V i).Nonempty → h x (ξ + ζ i) < ⊤ := by
    intro i hne
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have hpos : volume (V i) ≠ 0 := (volume_pos_of_isOpen_nonempty (hVo i) hne).ne'
    have hsum : ∑ j, volume (V j) * h x (ξ + ζ j) = ⊤ := by
      apply top_unique
      calc ⊤ = volume (V i) * h x (ξ + ζ i) := by rw [htop, ENNReal.mul_top hpos]
        _ ≤ _ := Finset.single_le_sum (f := fun j => volume (V j) * h x (ξ + ζ j))
            (fun _ _ => zero_le) (Finset.mem_univ i)
    rw [hsplit1, hsum] at hφlt
    exact not_top_lt hφlt
  let g : ℝ → ℝ≥0∞ := fun r => ∑ i, volume (V i) *
    ((∫⁻ y in affMap r x ⁻¹' V i, h y (ξ + ζ i)) / volume (affMap r x ⁻¹' V i))
  have hq : ∀ r : ℝ, 0 < r → Yt h (cube r x) ξ / volume (cube r x) ≤ g r := by
    intro r hr
    have hmem : zcopy φ r x ∈ Aff0 (cube r x) := by
      have := zcopy_mem_Aff0 hr x hφ
      rwa [preimage_affMap_cube hr x] at this
    have hWo : ∀ i, IsOpen (affMap r x ⁻¹' V i) :=
      fun i => (hVo i).preimage (continuous_affMap hr x)
    have hW : ∀ i, affMap r x ⁻¹' V i ⊆ cube r x := fun i => by
      rw [← preimage_affMap_cube hr x]
      exact preimage_mono (hVU i)
    have hint : ∫⁻ y in cube r x, h y (ξ + fderiv ℝ (zcopy φ r x) y) =
        ∑ i, ∫⁻ y in affMap r x ⁻¹' V i, h y (ξ + ζ i) := by
      rw [lintegral_eq_sum_pieces_fintype (V := fun i => affMap r x ⁻¹' V i) hWo hW
        (fun i j hij => (hVd hij).preimage _) ?_]
      · refine Finset.sum_congr rfl fun i _ =>
          setLIntegral_congr_fun (hWo i).measurableSet fun y hy => ?_
        rw [fderiv_zcopy hr x φ y, (hφV i _ hy).fderiv]
      · rw [← preimage_affMap_cube hr x, ← preimage_iUnion, ← preimage_sdiff,
          volume_preimage_affMap hr x, hVc, mul_zero]
    have hvolQ : volume (cube r x) = ENNReal.ofReal (r ^ N) := by
      rw [← preimage_affMap_cube hr x, volume_preimage_affMap hr x, volume_cube_one, mul_one]
    have hr0 : ENNReal.ofReal (r ^ N) ≠ 0 := by
      simpa using pow_pos hr N
    calc Yt h (cube r x) ξ / volume (cube r x)
        ≤ (∫⁻ y in cube r x, h y (ξ + fderiv ℝ (zcopy φ r x) y)) / volume (cube r x) := by
          gcongr
          exact iInf₂_le _ hmem
      _ = g r := by
        simp only [g]
        rw [hint, div_eq_mul_inv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [volume_preimage_affMap hr x, hvolQ]
        by_cases hVi : V i = ∅
        · simp [hVi]
        · have hv0 : volume (V i) ≠ 0 :=
            (volume_pos_of_isOpen_nonempty (hVo i) (nonempty_iff_ne_empty.2 hVi)).ne'
          have hvtop : volume (V i) ≠ ⊤ := (hVb i).measure_lt_top.ne
          rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hr0) (Or.inl ENNReal.ofReal_ne_top),
            mul_comm (volume (V i)), mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hv0 hvtop,
            mul_one]
  have hglim : Tendsto g (𝓝[>] 0) (𝓝 (∑ i, volume (V i) * h x (ξ + ζ i))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    by_cases hVi : (V i).Nonempty
    · exact ENNReal.Tendsto.const_mul
        (hleb _ (hfin i hVi) (V i) (hVo i) (hVb i) hVi) (Or.inr (hVb i).measure_lt_top.ne)
    · rw [not_nonempty_iff_eq_empty] at hVi
      simp [hVi]
  calc Ytloc h x ξ ≤ limsup g (𝓝[>] 0) :=
        limsup_le_limsup (eventually_nhdsWithin_of_forall hq)
    _ = ∑ i, volume (V i) * h x (ξ + ζ i) := hglim.limsup_eq
    _ = ∫⁻ y in cube 1 0, h x (ξ + fderiv ℝ φ y) := hsplit1.symm
    _ ≤ Zaff (h x) ξ + δ := hφlt.le

/-- Step 3 of `lemma_osc_general`: `𝒵_aff L` is upper semicontinuous when `L` is (an
infimum of finite nonnegative combinations of translates of `L`). -/
theorem Zaff_upperSemicontinuous {L : Mat m N → ℝ≥0∞} (hL : UpperSemicontinuous L) :
    UpperSemicontinuous (Zaff L) := by
  change UpperSemicontinuous fun ζ => ⨅ φ ∈ (Aff0 (cube 1 (0 : Sp N)) : Set (Sp N → Tgt m)),
    ∫⁻ y in cube 1 0, L (ζ + fderiv ℝ φ y)
  refine upperSemicontinuous_iInf fun φ => upperSemicontinuous_iInf fun hφ => ?_
  obtain ⟨K, n, V, η, -, -, hVo, hVU, hVd, -, hVc, hφV⟩ := Aff0.data hφ
  have hsplit : (fun ζ => ∫⁻ y in cube 1 0, L (ζ + fderiv ℝ φ y)) =
      fun ζ => ∑ i, volume (V i) * L (ζ + η i) := by
    funext ζ
    rw [lintegral_eq_sum_pieces_fintype hVo hVU hVd hVc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet (g := fun _ => L (ζ + η i))
      (fun y hy => by rw [(hφV i y hy).fderiv]), setLIntegral_const, mul_comm]
  rw [hsplit]
  refine upperSemicontinuous_sum fun i _ => ?_
  have hvtop : volume (V i) ≠ ⊤ :=
    ((isBounded_cube 1 (0 : Sp N)).subset (hVU i)).measure_lt_top.ne
  exact (ENNReal.continuous_const_mul hvtop).comp_upperSemicontinuous
    (hL.comp (continuous_add_const (η i))) fun a b hab => by simp only; gcongr

/-- **Lemma `lemma_osc_general`**, at a fixed point `x` satisfying (i)–(iii):
`𝒴_loc h(x,·) = 𝒵_aff h(x,·)`, and it is upper semicontinuous. -/
theorem Ytloc_eq_Zaff_of_osc [NeZero N] {h : Sp N → Mat m N → ℝ≥0∞} {x : Sp N}
    (hosc : ∀ ε : ℝ≥0, 0 < ε → ∃ ρ > 0, ∀ z ∈ cube ρ x, ∀ ξ, h x ξ ≤ (1 + ε) * h z ξ)
    (hleb : ∀ ξ, h x ξ < ⊤ → ∀ O : Set (Sp N), IsOpen O → Bornology.IsBounded O →
      O.Nonempty → Tendsto (fun r : ℝ => (∫⁻ y in affMap r x ⁻¹' O, h y ξ) /
        volume (affMap r x ⁻¹' O)) (𝓝[>] 0) (𝓝 (h x ξ)))
    (husc : UpperSemicontinuous (h x)) :
    Ytloc h x = Zaff (h x) ∧ UpperSemicontinuous (Ytloc h x) := by
  have heq : Ytloc h x = Zaff (h x) := funext fun ξ =>
    le_antisymm (Ytloc_le_Zaff_of_lebesgue hleb ξ) (Zaff_le_Ytloc_of_osc hosc ξ)
  exact ⟨heq, heq ▸ Zaff_upperSemicontinuous husc⟩

/-- **Lemma `lemma_osc_general`**: under (i) the one-sided oscillation condition, (ii) the
Lebesgue-point condition on all sets `x + rO` and (iii) upper semicontinuity of `h(x,·)`, each
for a.e. `x`, one has `𝒴_loc h(x,·) = 𝒵_aff h(x,·)`, upper semicontinuous, for a.e. `x`.
No measurability of `h` is needed. Condition (i) is in the pointwise form of
`Zaff_le_Ytloc_of_osc`; (ii) is written with `affMap r x ⁻¹' O = x + rO`. -/
theorem lemma_osc_general [NeZero N] {h : Sp N → Mat m N → ℝ≥0∞}
    (hosc : ∀ᵐ x, ∀ ε : ℝ≥0, 0 < ε → ∃ ρ > 0, ∀ z ∈ cube ρ x, ∀ ξ,
      h x ξ ≤ (1 + ε) * h z ξ)
    (hleb : ∀ᵐ x, ∀ ξ, h x ξ < ⊤ → ∀ O : Set (Sp N), IsOpen O → Bornology.IsBounded O →
      O.Nonempty → Tendsto (fun r : ℝ => (∫⁻ y in affMap r x ⁻¹' O, h y ξ) /
        volume (affMap r x ⁻¹' O)) (𝓝[>] 0) (𝓝 (h x ξ)))
    (husc : ∀ᵐ x, UpperSemicontinuous (h x)) :
    ∀ᵐ x, Ytloc h x = Zaff (h x) ∧ UpperSemicontinuous (Ytloc h x) := by
  filter_upwards [hosc, hleb, husc] with x h1 h2 h3
  exact Ytloc_eq_Zaff_of_osc h1 h2 h3

end Homogenization
