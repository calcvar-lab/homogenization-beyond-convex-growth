import Homogenization.HypothesesRemarks
import Homogenization.RadialRep
import Homogenization.Subadditive
import Homogenization.AffSobolev

/-!
# Section 2: Remark `lEnvelopes` (i)–(iii) and Remark `rem:radialrep-convex`

* `lEnvelopes_i`, `lEnvelopes_ii`, `lEnvelopes_iii`: the elementary properties of the envelopes
  recorded in Remark `lEnvelopes` (monotonicity, comparison with the unperturbed energy, comparison
  of the affine and Sobolev classes), for `θ ∈ {Aff, p}`, without measurability assumptions.
* `radialrep_convex`: for a convex `f : 𝕄 → [0,∞]` with `0 ∈ int(dom f)` and every `ξ`,
  `f(tξ) → f̄(ξ)` as `t → 1⁻`, where `f̄(ξ) = liminf_{ζ → ξ} f(ζ)` is the lower semicontinuous
  envelope; hence `f̄ = f̂` ([Roc70, Theorem 7.5], cited in the article, here proved).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- **Remark `lEnvelopes` (i).** The envelopes are monotone. -/
theorem lEnvelopes_i (p : ℝ≥0∞) {L L' : Sp N → Mat m N → ℝ≥0∞} (h : L ≤ L')
    {L₀ L₀' : Mat m N → ℝ≥0∞} (h₀ : L₀ ≤ L₀') :
    (∀ U ξ, Yt L U ξ ≤ Yt L' U ξ) ∧ (∀ U ξ, Ytp p L U ξ ≤ Ytp p L' U ξ) ∧
      Ytloc L ≤ Ytloc L' ∧ Haff L ≤ Haff L' ∧ Hp p L ≤ Hp p L' ∧ Zaff L₀ ≤ Zaff L₀' :=
  ⟨fun U ξ => Yt_mono h U ξ, fun U ξ => Ytp_mono h U ξ, Ytloc_mono h, Haff_mono h, Hp_mono h,
    Zaff_mono h₀⟩

/-- **Remark `lEnvelopes` (ii).** Comparison with the unperturbed energy (the corrector `0`). -/
theorem lEnvelopes_ii (p : ℝ≥0∞) (L : Sp N → Mat m N → ℝ≥0∞) (L₀ : Mat m N → ℝ≥0∞) :
    (∀ U : Set (Sp N), IsOpen U → ∀ ξ, Yt L U ξ ≤ ∫⁻ y in U, L y ξ) ∧
      (∀ (U : Set (Sp N)) ξ, Ytp p L U ξ ≤ ∫⁻ y in U, L y ξ) ∧
      (∀ x ξ, Ytloc L x ξ ≤
        limsup (fun ρ : ℝ => (∫⁻ y in cube ρ x, L y ξ) / volume (cube ρ x)) (𝓝[>] 0)) ∧
      (∀ ξ, Haff L ξ ≤ ⨅ k : ℕ, (∫⁻ y in cube ((k : ℝ) + 1) 0, L y ξ) /
        volume (cube ((k : ℝ) + 1) (0 : Sp N))) ∧
      (∀ ξ, Hp p L ξ ≤ ⨅ k : ℕ, (∫⁻ y in cube ((k : ℝ) + 1) 0, L y ξ) /
        volume (cube ((k : ℝ) + 1) (0 : Sp N))) ∧
      Zaff L₀ ≤ L₀ := by
  refine ⟨fun U hU ξ => Yt_le_lintegral L hU ξ, fun U ξ => Ytp_le_lintegral p L U ξ,
    fun x ξ => Ytloc_le_limsup_avg L x ξ, fun ξ => ?_, fun ξ => ?_, Zaff_le L₀⟩
  · exact iInf_mono fun k =>
      ENNReal.div_le_div_right (Yt_le_lintegral L (isOpen_cube _ _) ξ) _
  · exact iInf_mono fun k => ENNReal.div_le_div_right (Ytp_le_lintegral p L _ ξ) _

/-- **Remark `lEnvelopes` (iii).** `ℋ L ≤ ℋ_aff L` and `𝒵_aff ℋ_aff L ≤ ℋ_aff L`. -/
theorem lEnvelopes_iii (p : ℝ≥0∞) [Fact (1 ≤ p)] (L : Sp N → Mat m N → ℝ≥0∞) :
    Hp p L ≤ Haff L ∧ Zaff (Haff L) ≤ Haff L :=
  ⟨Hp_le_Haff p L, Zaff_Haff_le L⟩

/-- **Remark `rem:radialrep-convex`** ([Roc70, Theorem 7.5]). Let `f : 𝕄 → [0,∞]` be convex with
`0 ∈ int(dom f)`. Then, for every `ξ`, `f(tξ) → f̄(ξ)` as `t → 1⁻`, where
`f̄(ξ) = liminf_{ζ → ξ} f(ζ)` is the lower semicontinuous envelope of `f`; in particular
`f̂ = f̄`. -/
theorem radialrep_convex {f : Mat m N → ℝ≥0∞} (hf : ConvexENN f)
    (h0 : (0 : Mat m N) ∈ interior (dom f)) (ξ : Mat m N) :
    Tendsto (fun t : ℝ => f (t • ξ)) (𝓝[<] 1) (𝓝 (liminf f (𝓝 ξ))) ∧
      radial f ξ = liminf f (𝓝 ξ) := by
  set ℓ := liminf f (𝓝 ξ)
  -- `f` is bounded by `M` near `0`
  have hf0 : f 0 ≠ ⊤ := (interior_subset h0 : (0 : Mat m N) ∈ dom f).ne
  set M : ℝ≥0∞ := f 0 + 1
  have hMt : M ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hf0, ENNReal.one_ne_top⟩
  have hnear : ∀ᶠ w in 𝓝 (0 : Mat m N), f w < M :=
    (hf.continuousOn_interior_dom.continuousAt (isOpen_interior.mem_nhds h0)).eventually
      (gt_mem_nhds (ENNReal.lt_add_right hf0 one_ne_zero))
  -- lower bound: `ℓ ≤ liminf_{t → 1⁻} f(tξ)`
  have hmap : Tendsto (fun t : ℝ => t • ξ) (𝓝[<] 1) (𝓝 ξ) := by
    have : Tendsto (fun t : ℝ => t • ξ) (𝓝 1) (𝓝 ((1 : ℝ) • ξ)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlow : ℓ ≤ liminf (fun t : ℝ => f (t • ξ)) (𝓝[<] 1) := by
    refine le_of_forall_lt fun b hb => ?_
    obtain ⟨c, hbc, hcℓ⟩ := exists_between hb
    have hev : ∀ᶠ ζ in 𝓝 ξ, c < f ζ := eventually_lt_of_lt_liminf hcℓ
    exact lt_of_lt_of_le hbc (le_liminf_of_le (by isBoundedDefault)
      ((hmap.eventually hev).mono fun t ht => ht.le))
  -- upper bound: `f(tξ) ≤ t ℓ + (1 - t) M` for `t ∈ ]0,1[`
  have hpt : ℓ ≠ ⊤ → ∀ t : ℝ, 0 < t → t < 1 →
      f (t • ξ) ≤ ENNReal.ofReal t * ℓ + ENNReal.ofReal (1 - t) * M := by
    intro hℓ t ht0 ht1
    have h1t : 0 < 1 - t := by linarith
    set w : Mat m N → Mat m N := fun ζ => (t / (1 - t)) • (ξ - ζ)
    have hw : Tendsto w (𝓝 ξ) (𝓝 0) := by
      have : Tendsto w (𝓝 ξ) (𝓝 ((t / (1 - t)) • (ξ - ξ))) :=
        ((continuous_const.sub continuous_id).const_smul (t / (1 - t))).tendsto ξ
      simpa using this
    have hconv : ∀ ζ, f (t • ξ) ≤ ENNReal.ofReal t * f ζ + ENNReal.ofReal (1 - t) * f (w ζ) := by
      intro ζ
      have h := hf ζ (w ζ) t.toNNReal (by rw [Real.toNNReal_le_one]; exact ht1.le)
      have e : ((t.toNNReal : ℝ) • ζ + ((1 - t.toNNReal : ℝ≥0) : ℝ) • w ζ) = t • ξ := by
        rw [NNReal.coe_sub (by rw [Real.toNNReal_le_one]; exact ht1.le), NNReal.coe_one,
          Real.coe_toNNReal _ ht0.le]
        simp only [w, smul_smul]
        rw [mul_div_cancel₀ _ h1t.ne', smul_sub]
        abel
      rw [e] at h
      have e1 : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := rfl
      have e2 : ((1 - t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 - t) := by
        rw [ENNReal.ofReal_sub _ ht0.le, ENNReal.ofReal_one, ENNReal.coe_sub, ENNReal.coe_one]
        rfl
      rwa [e1, e2] at h
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hb : ℓ < ℓ + ε := ENNReal.lt_add_right hℓ (by exact_mod_cast hε.ne')
    have hfreq : ∃ᶠ ζ in 𝓝 ξ, f ζ < ℓ + ε := frequently_lt_of_liminf_lt (by isBoundedDefault) hb
    obtain ⟨ζ, hζ, hwζ⟩ := (hfreq.and_eventually (hw.eventually hnear)).exists
    have htle : ENNReal.ofReal t ≤ 1 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ht1.le
    calc f (t • ξ) ≤ ENNReal.ofReal t * f ζ + ENNReal.ofReal (1 - t) * f (w ζ) := hconv ζ
      _ ≤ ENNReal.ofReal t * (ℓ + ε) + ENNReal.ofReal (1 - t) * M := by gcongr
      _ = ENNReal.ofReal t * ℓ + ENNReal.ofReal (1 - t) * M + ENNReal.ofReal t * ε := by ring
      _ ≤ ENNReal.ofReal t * ℓ + ENNReal.ofReal (1 - t) * M + ε := by
          gcongr
          calc ENNReal.ofReal t * (ε : ℝ≥0∞) ≤ 1 * ε := by gcongr
            _ = ε := one_mul _
  have hup : limsup (fun t : ℝ => f (t • ξ)) (𝓝[<] 1) ≤ ℓ := by
    by_cases hℓ : ℓ = ⊤
    · rw [hℓ]; exact le_top
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal t * ℓ + ENNReal.ofReal (1 - t) * M)
        (𝓝[<] 1) (𝓝 ℓ) := by
      have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal t) (𝓝[<] 1) (𝓝 1) := by
        have := (ENNReal.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
        simpa using this
      have h2 : Tendsto (fun t : ℝ => ENNReal.ofReal (1 - t)) (𝓝[<] 1) (𝓝 0) := by
        have hc : Continuous fun t : ℝ => ENNReal.ofReal (1 - t) :=
          ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)
        have := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
        simpa using this
      have := (ENNReal.Tendsto.mul_const h1 (Or.inr hℓ)).add
        (ENNReal.Tendsto.mul_const h2 (Or.inr hMt))
      simpa using this
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), f (t • ξ) ≤
        ENNReal.ofReal t * ℓ + ENNReal.ofReal (1 - t) * M := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with t
        (ht1 : t < 1) (ht0 : 0 < t)
      exact hpt hℓ t ht0 ht1
    calc limsup (fun t : ℝ => f (t • ξ)) (𝓝[<] 1)
        ≤ limsup (fun t : ℝ => ENNReal.ofReal t * ℓ + ENNReal.ofReal (1 - t) * M) (𝓝[<] 1) :=
          limsup_le_limsup hev
      _ = ℓ := hlim.limsup_eq
  have hT : Tendsto (fun t : ℝ => f (t • ξ)) (𝓝[<] 1) (𝓝 ℓ) :=
    tendsto_of_le_liminf_of_limsup_le hlow hup
  exact ⟨hT, hT.liminf_eq⟩

end Homogenization
