import Homogenization.OscGeneral
import Homogenization.Vitali

/-! # Lemma `lem:sumosc`

The uniform Lebesgue-point property of Remark `rem:oscgen` along the sets `x + rO`
(`ae_tendsto_setLIntegral_affMap_div`), and Lemma `lem:sumosc` (`lem_sumosc`), which checks the
three hypotheses of `lemma_osc_general` for `h(x,ξ) = ∑ᵢ aᵢ(x) Hᵢ(ξ)`.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ}

/-- Remark `rem:oscgen`: a locally integrable `f` has, at a.e. `x`, averages over
`x + rO` converging to `f(x)` for every nonempty bounded open `O` (one null set for all `O`).
Here `x + rO = affMap r x ⁻¹' O`; the integrand is `ofReal ∘ f`. -/
theorem ae_tendsto_setLIntegral_affMap_div [NeZero N] {f : Sp N → ℝ}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ O : Set (Sp N), IsOpen O → Bornology.IsBounded O → O.Nonempty →
      Tendsto (fun r : ℝ => (∫⁻ y in affMap r x ⁻¹' O, ENNReal.ofReal (f y)) /
        volume (affMap r x ⁻¹' O)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (f x))) := by
  filter_upwards [(vfam N).ae_tendsto_lintegral_enorm_sub_div hf] with x hx
  intro O hOo hOb hOne
  obtain ⟨c₀, hc₀⟩ := hOb.subset_closedBall 0
  set c : ℝ := max c₀ 1 with hc_def
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hOc : O ⊆ closedBall 0 c := hc₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hO0 : volume O ≠ 0 := (volume_pos_of_isOpen_nonempty hOo hOne).ne'
  have hOtop : volume O ≠ ⊤ := hOb.measure_lt_top.ne
  set v := ENNReal.ofReal (f x)
  let W : ℝ → Set (Sp N) := fun r => affMap r x ⁻¹' O
  let B : ℝ → Set (Sp N) := fun r => closedBall x (r * c)
  let e : ℝ → ℝ≥0∞ := fun r => (∫⁻ y in W r, ‖f y - f x‖ₑ) / volume (W r)
  let q : ℝ → ℝ≥0∞ := fun r => (∫⁻ y in B r, ‖f y - f x‖ₑ) / volume (B r)
  set κ : ℝ≥0∞ := ENNReal.ofReal (c ^ N) * volume (ball (0 : Sp N) 1) / volume O
  have hκ : κ ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne) hO0
  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    have hδ : Tendsto (fun r : ℝ => r * c) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => r * c) (𝓝 0) (𝓝 (0 * c)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        exact mul_pos hr hc
    have hmem : ∀ᶠ r in 𝓝[>] (0 : ℝ), x ∈ closedBall ((fun _ : ℝ => x) r) (1 * (r * c)) := by
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mem_closedBall_self (by positivity)
    exact hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
      (fun _ : ℝ => x) (fun r => r * c) hδ hmem)
  have hWB : ∀ r, 0 < r → W r ⊆ B r := by
    intro r hr y hy
    have hy' : affMap r x y ∈ closedBall (0 : Sp N) c := hOc hy
    rw [mem_closedBall, dist_zero_right] at hy'
    have : affMap r x y = r⁻¹ • (y - x) := by simp [affMap, sub_eq_add_neg]
    rw [this, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hy'
    rw [mem_closedBall, dist_eq_norm]
    calc ‖y - x‖ = r * (r⁻¹ * ‖y - x‖) := by field_simp
      _ ≤ r * c := by gcongr
  have hvolW : ∀ r, 0 < r → volume (W r) = ENNReal.ofReal (r ^ N) * volume O :=
    fun r hr => volume_preimage_affMap hr x O
  have hvolB : ∀ r, 0 < r → volume (B r) =
      ENNReal.ofReal (r ^ N) * (ENNReal.ofReal (c ^ N) * volume (ball (0 : Sp N) 1)) := by
    intro r hr
    rw [Measure.addHaar_closedBall volume x (by positivity), finrank_Sp, mul_pow,
      ENNReal.ofReal_mul (by positivity), mul_assoc]
  have he_le : ∀ r, 0 < r → e r ≤ κ * q r := by
    intro r hr
    have hr0 : ENNReal.ofReal (r ^ N) ≠ 0 := by simpa using pow_pos hr N
    have hB0 : volume (B r) ≠ 0 := by
      rw [hvolB r hr]
      exact mul_ne_zero hr0 (mul_ne_zero (by simpa using pow_pos hc N)
        (measure_ball_pos volume _ one_pos).ne')
    have hBtop : volume (B r) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hratio : volume (B r) / volume (W r) = κ := by
      rw [hvolB r hr, hvolW r hr, ENNReal.mul_div_mul_left _ _ hr0 ENNReal.ofReal_ne_top]
    calc e r ≤ (∫⁻ y in B r, ‖f y - f x‖ₑ) / volume (W r) :=
          ENNReal.div_le_div_right (lintegral_mono_set (hWB r hr)) _
      _ = q r * (volume (B r) / volume (W r)) := by
          simp only [q, div_eq_mul_inv]
          rw [mul_assoc, ← mul_assoc (volume (B r))⁻¹, ENNReal.inv_mul_cancel hB0 hBtop, one_mul]
      _ = κ * q r := by rw [hratio, mul_comm]
  have he : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r => κ * q r) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hq (Or.inr hκ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall fun _ => zero_le) (eventually_nhdsWithin_of_forall he_le)
  have hmeas : AEMeasurable (fun y => ‖f y - f x‖ₑ) volume :=
    (hf.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm
  have hW0 : ∀ r, 0 < r → volume (W r) ≠ 0 := fun r hr => by
    rw [hvolW r hr]
    exact mul_ne_zero (by simpa using pow_pos hr N) hO0
  have hWtop : ∀ r, 0 < r → volume (W r) ≠ ⊤ := fun r hr => by
    rw [hvolW r hr]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOtop
  have hpt1 : ∀ y, ENNReal.ofReal (f y) ≤ v + ‖f y - f x‖ₑ := by
    intro y
    rw [Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal (f y) ≤ ENNReal.ofReal (f x + |f y - f x|) :=
          ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (f y - f x)])
      _ ≤ v + ENNReal.ofReal |f y - f x| := ENNReal.ofReal_add_le
  have hpt2 : ∀ y, v ≤ ENNReal.ofReal (f y) + ‖f y - f x‖ₑ := by
    intro y
    rw [Real.enorm_eq_ofReal_abs]
    calc v ≤ ENNReal.ofReal (f y + |f y - f x|) :=
          ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (f y - f x)])
      _ ≤ ENNReal.ofReal (f y) + ENNReal.ofReal |f y - f x| := ENNReal.ofReal_add_le
  have hupper : ∀ r, 0 < r →
      (∫⁻ y in W r, ENNReal.ofReal (f y)) / volume (W r) ≤ v + e r := by
    intro r hr
    calc (∫⁻ y in W r, ENNReal.ofReal (f y)) / volume (W r)
        ≤ (∫⁻ y in W r, (v + ‖f y - f x‖ₑ)) / volume (W r) :=
          ENNReal.div_le_div_right (lintegral_mono hpt1) _
      _ = (v * volume (W r) + ∫⁻ y in W r, ‖f y - f x‖ₑ) / volume (W r) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
      _ = v + e r := by
          rw [ENNReal.add_div, ENNReal.mul_div_cancel_right (hW0 r hr) (hWtop r hr)]
  have hlower : ∀ r, 0 < r →
      v - e r ≤ (∫⁻ y in W r, ENNReal.ofReal (f y)) / volume (W r) := by
    intro r hr
    rw [tsub_le_iff_right]
    calc v = v * volume (W r) / volume (W r) :=
          (ENNReal.mul_div_cancel_right (hW0 r hr) (hWtop r hr)).symm
      _ ≤ (∫⁻ y in W r, (ENNReal.ofReal (f y) + ‖f y - f x‖ₑ)) / volume (W r) := by
          refine ENNReal.div_le_div_right ?_ _
          rw [← setLIntegral_const]
          exact lintegral_mono hpt2
      _ = (∫⁻ y in W r, ENNReal.ofReal (f y)) / volume (W r) + e r := by
          rw [lintegral_add_right' _ hmeas.restrict, ENNReal.add_div]
  have hlo : Tendsto (fun r => v - e r) (𝓝[>] 0) (𝓝 v) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds he (Or.inl ENNReal.ofReal_ne_top)
  have hup : Tendsto (fun r => v + e r) (𝓝[>] 0) (𝓝 v) := by
    simpa using tendsto_const_nhds.add he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    (eventually_nhdsWithin_of_forall hlower) (eventually_nhdsWithin_of_forall hupper)

variable {m : ℕ}

/-- **Lemma `lem:sumosc`**: for `h(x,ξ) = ∑ᵢ aᵢ(x) Hᵢ(ξ)` with `aᵢ` lower semicontinuous with
values in `[η, Λ]` (`η > 0`) and `Hᵢ` upper semicontinuous, for a.e. `x` (one null set for all
`ξ`): `𝒴_loc h(x,·) = 𝒵_aff h(x,·) ≤ h(x,·)`, and `𝒴_loc h(x,·)` is upper semicontinuous. The
Borel measurability of `aᵢ` and `Hᵢ` is not assumed (`aᵢ` is measurable, being l.s.c.). -/
theorem lem_sumosc [NeZero N] {ν : ℕ} {a : Fin ν → Sp N → ℝ} {H : Fin ν → Mat m N → ℝ≥0∞}
    {η Λ : ℝ} (hη : 0 < η) (ha : ∀ i x, η ≤ a i x ∧ a i x ≤ Λ)
    (halsc : ∀ i, LowerSemicontinuous (a i)) (hH : ∀ i, UpperSemicontinuous (H i)) :
    ∀ᵐ x, Ytloc (fun x ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) x =
        Zaff (fun ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) ∧
      Zaff (fun ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) ≤
        (fun ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) ∧
      UpperSemicontinuous (Ytloc (fun x ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ) x) := by
  set h : Sp N → Mat m N → ℝ≥0∞ := fun x ξ => ∑ i, ENNReal.ofReal (a i x) * H i ξ with hh
  have hapos : ∀ i x, 0 < a i x := fun i x => lt_of_lt_of_le hη (ha i x).1
  have hmeas : ∀ i, Measurable (a i) := fun i => (halsc i).measurable
  have hloc : ∀ i, LocallyIntegrable (a i) volume := by
    intro i
    rw [locallyIntegrable_iff]
    intro k hk
    refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne
      (hmeas i).aestronglyMeasurable (M := max Λ (-Λ)) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(ha i x).1, (ha i x).2, le_max_left Λ (-Λ), le_max_right Λ (-Λ),
      hapos i x]
  -- (i) one-sided oscillation
  have h1 : ∀ x, ∀ ε : ℝ≥0, 0 < ε → ∃ ρ > 0, ∀ z ∈ cube ρ x, ∀ ξ,
      h x ξ ≤ (1 + ε) * h z ξ := by
    intro x ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hev : ∀ᶠ z in 𝓝 x, ∀ i, a i x ≤ (1 + ε) * a i z := by
      rw [eventually_all]
      intro i
      have hlt : a i x / (1 + ε) < a i x := div_lt_self (hapos i x) (by linarith)
      filter_upwards [halsc i x _ hlt] with z hz
      have := (div_lt_iff₀ (by linarith : (0 : ℝ) < 1 + ε)).1 hz
      linarith
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hev
    refine ⟨2 * r, by positivity, fun z hz ξ => ?_⟩
    rw [← ball_eq_cube hr] at hz
    have hz' := hball hz
    simp only [hh]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_assoc]
    gcongr ?_ * _
    calc ENNReal.ofReal (a i x) ≤ ENNReal.ofReal ((1 + ε) * a i z) :=
          ENNReal.ofReal_le_ofReal (hz' i)
      _ = (1 + ε) * ENNReal.ofReal (a i z) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one hε'.le,
            ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
  -- (ii) Lebesgue points
  have h2 : ∀ᵐ x, ∀ ξ, h x ξ < ⊤ → ∀ O : Set (Sp N), IsOpen O → Bornology.IsBounded O →
      O.Nonempty → Tendsto (fun r : ℝ => (∫⁻ y in affMap r x ⁻¹' O, h y ξ) /
        volume (affMap r x ⁻¹' O)) (𝓝[>] 0) (𝓝 (h x ξ)) := by
    have hall := ae_all_iff.2 fun i => ae_tendsto_setLIntegral_affMap_div (hloc i)
    filter_upwards [hall] with x hx ξ hξ O hOo hOb hOne
    have hHfin : ∀ i, H i ξ ≠ ⊤ := by
      intro i hi
      have : ENNReal.ofReal (a i x) * H i ξ ≤ h x ξ :=
        Finset.single_le_sum (f := fun j => ENNReal.ofReal (a j x) * H j ξ)
          (fun _ _ => zero_le) (Finset.mem_univ i)
      rw [hi, ENNReal.mul_top (by simpa using hapos i x)] at this
      exact (not_top_lt (this.trans_lt hξ))
    have heq : (fun r : ℝ => (∫⁻ y in affMap r x ⁻¹' O, h y ξ) / volume (affMap r x ⁻¹' O)) =
        fun r => ∑ i, (∫⁻ y in affMap r x ⁻¹' O, ENNReal.ofReal (a i y)) /
          volume (affMap r x ⁻¹' O) * H i ξ := by
      funext r
      simp only [hh]
      rw [lintegral_finsetSum _ fun i _ => ((hmeas i).ennreal_ofReal).mul_const _,
        div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lintegral_mul_const' _ _ (hHfin i), div_eq_mul_inv]
      ring
    rw [heq]
    exact tendsto_finsetSum _ fun i _ =>
      ENNReal.Tendsto.mul_const (hx i O hOo hOb hOne) (Or.inr (hHfin i))
  -- (iii) upper semicontinuity
  have h3 : ∀ x, UpperSemicontinuous (h x) := by
    intro x
    refine upperSemicontinuous_sum fun i _ => ?_
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_upperSemicontinuous
      (hH i) fun u w huw => by simp only; gcongr
  filter_upwards [lemma_osc_general (Eventually.of_forall h1) h2
    (Eventually.of_forall h3)] with x hx
  exact ⟨hx.1, Zaff_le _, hx.2⟩

end Homogenization
