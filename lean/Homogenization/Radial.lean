import Homogenization.Cutoff

/-!
# Radial envelopes of ru-usc functions

Formalization, for `[0,∞]`-valued integrands and `u₀ = 0`, of the results of
on radial envelopes from [oahjpm14] used in [oah-jpm-zorgati14]:

* `RUUSCWith.tendsto_radial` (radial representation formula of [oahjpm14], first part): if `f` is
  ru-usc, then `f̂(ξ) = liminf_{t→1⁻} f(tξ)` is a genuine limit, `f(tξ) → f̂(ξ)` as `t → 1⁻`,
  for every `ξ`.
  No star-shapedness is needed for this statement: for `t` close to `1` one chooses `s ∈ ]t,1[`
  with `f(sξ)` almost minimal and writes `tξ = (t/s)(sξ)`;
* `RUUSCWith.radial` (radial representation formula of [oahjpm14], second part): `f̂` is ru-usc
  with the same constant;
* `RUUSCWith.Hp` (Proposition `Coro-Prop-ru-usc2` of [oah-jpm-zorgati14]): the Sobolev multi-cell
  envelope `ℋ_p W` inherits the ru-usc property of `W` (via `W1p0.smul`, `Ytp_smul_le`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### The Sobolev cell problem under scaling of the matrix -/

theorem W1p0.smul {p : ℝ≥0∞} {U : Set (Sp N)} {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 p U) (t : ℝ) : (t • u.1, t • u.2) ∈ W1p0 p U := by
  obtain ⟨h0, h1, h2, hw⟩ := hu
  refine ⟨fun y hy => by simp [h0 y hy], h1.const_smul t, h2.const_smul t, ?_⟩
  intro ψ hψ hcs hsub v
  have h := hw ψ hψ hcs hsub v
  calc ∫ y, fderiv ℝ ψ y v • (t • u.1) y = t • ∫ y, fderiv ℝ ψ y v • u.1 y := by
        rw [← integral_smul]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [Pi.smul_apply]
        rw [smul_comm]
    _ = t • -∫ y, ψ y • u.2 y v := by rw [h]
    _ = -∫ y, ψ y • (t • u.2) y v := by
        rw [smul_neg, ← integral_smul]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [Pi.smul_apply, smul_apply]
        rw [smul_comm]

/-- `𝒴_p W(U, tξ) ≤ a 𝒴_p W(U, ξ) + b|U|` when `W(y, tζ) ≤ a W(y, ζ) + b`. -/
theorem Ytp_smul_le {p : ℝ≥0∞} (W : Sp N → Mat m N → ℝ≥0∞) (U : Set (Sp N)) (t : ℝ)
    {a b : ℝ≥0∞} (ha₀ : a ≠ 0) (ha : a ≠ ⊤) (hW : ∀ y ζ, W y (t • ζ) ≤ a * W y ζ + b)
    (ξ : Mat m N) : Ytp p W U (t • ξ) ≤ a * Ytp p W U ξ + b * volume U := by
  simp only [Ytp]
  rw [ENNReal.mul_iInf_of_ne ha₀ ha, ENNReal.iInf_add]
  refine le_iInf fun φg => ?_
  rw [ENNReal.mul_iInf_of_ne ha₀ ha, ENNReal.iInf_add]
  refine le_iInf fun hφg => ?_
  refine (iInf₂_le (t • φg.1, t • φg.2) (W1p0.smul hφg t)).trans ?_
  have hder : ∀ y, t • ξ + (t • φg.2) y = t • (ξ + φg.2 y) := fun y => by
    rw [Pi.smul_apply, smul_add]
  simp_rw [hder]
  calc ∫⁻ y in U, W y (t • (ξ + φg.2 y))
      ≤ ∫⁻ y in U, (a * W y (ξ + φg.2 y) + b) := lintegral_mono fun y => hW _ _
    _ = a * (∫⁻ y in U, W y (ξ + φg.2 y)) + b * volume U := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ha, setLIntegral_const]

/-- **Proposition `Coro-Prop-ru-usc2`**: `ℋ_p W` inherits the ru-usc property of `W`. -/
theorem RUUSCWith.Hp {p : ℝ≥0∞} {c : ℝ≥0} {W : Sp N → Mat m N → ℝ≥0∞} (hW : RUUSCWith c W) :
    RUUSCWith c (fun _ => Hp p W) := by
  refine RUUSCWith.of_le_affine fun η hη => ?_
  filter_upwards [hW.le_affine hη] with t ht _ ξ
  have h1 : (1 + (η : ℝ≥0∞)) ≠ 0 := by simp
  have h2 : (1 + (η : ℝ≥0∞)) ≠ ⊤ := by simp
  simp only [Homogenization.Hp]
  rw [ENNReal.mul_iInf_of_ne h1 h2, ENNReal.iInf_add]
  refine iInf_mono fun k => ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [← affine_div_volume (volume_cube_pos hk 0).ne' (volume_cube_ne_top _ 0)]
  exact ENNReal.div_le_div_right (Ytp_smul_le W _ t h1 h2 (fun y ζ => ht y ζ) ξ) _

theorem RUUSC.Hp {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞} (hW : RUUSC W) :
    RUUSC (fun _ => Hp p W) :=
  let ⟨c, hc, h⟩ := hW; ⟨c, hc, h.Hp⟩

/-! ### The radial envelope of an ru-usc function -/

/-- For `b' < ⊤`, `(1 + η) b' + η c < b` for some `η > 0` as soon as `b' < b`. -/
theorem exists_eta_affine_lt {b' b : ℝ≥0∞} (hb' : b' < b) (hb'top : b' ≠ ⊤) (c : ℝ≥0) :
    ∃ η : ℝ≥0, 0 < η ∧ (1 + (η : ℝ≥0∞)) * b' + η * c < b := by
  have h1 : Tendsto (fun η : ℝ≥0 => (η : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_coe.tendsto (0 : ℝ≥0))
  have h2 : Tendsto (fun η : ℝ≥0 => (1 + (η : ℝ≥0∞)) * b' + η * c) (𝓝 0) (𝓝 b') := by
    have h3 : Tendsto (fun η : ℝ≥0 => (1 + (η : ℝ≥0∞)) * b') (𝓝 0) (𝓝 ((1 + 0) * b')) :=
      ENNReal.Tendsto.mul_const ((tendsto_const_nhds (x := (1 : ℝ≥0∞))).add h1) (Or.inr hb'top)
    have h4 : Tendsto (fun η : ℝ≥0 => (η : ℝ≥0∞) * c) (𝓝 0) (𝓝 (0 * (c : ℝ≥0∞))) :=
      ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.coe_ne_top)
    simpa using h3.add h4
  obtain ⟨η, hη, hη0⟩ := ((h2.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hb')).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ≥0))) |>.exists
  exact ⟨η, hη0, hη⟩

/-- **Radial representation formula of [oahjpm14], first part.** For `f` ru-usc, `f(tξ) → f̂(ξ)`
as `t → 1⁻`. -/
theorem RUUSCWith.tendsto_radial {c : ℝ≥0} {f : Mat m N → ℝ≥0∞} (hf : RUUSCWith c (fun _ => f))
    (ξ : Mat m N) : Tendsto (fun t : ℝ => f (t • ξ)) (𝓝[<] 1) (𝓝 (radial f ξ)) := by
  refine tendsto_order.2 ⟨fun a ha => eventually_lt_of_lt_liminf ha, fun b hb => ?_⟩
  obtain ⟨b', hLb', hb'b⟩ := exists_between hb
  obtain ⟨η, hη0, hηb⟩ := exists_eta_affine_lt hb'b (hb'b.trans_le le_top).ne c
  have hev := hf.le_affine hη0
  obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hfreq : ∃ᶠ s in 𝓝[<] (1 : ℝ), f (s • ξ) < b' :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hLb'
  filter_upwards [Ioo_mem_nhdsLT (show max t₀ 0 < 1 from max_lt ht₀ one_pos)] with t ht
  have ht0 : 0 < t := (le_max_right _ _).trans_lt ht.1
  obtain ⟨s, hs, hst⟩ := (hfreq.and_eventually (Ioo_mem_nhdsLT ht.2)).exists
  have hs0 : 0 < s := ht0.trans hst.1
  have hτ : t / s ∈ Ioo t₀ 1 := by
    refine ⟨?_, (div_lt_one hs0).2 hst.1⟩
    calc t₀ ≤ max t₀ 0 := le_max_left _ _
      _ < t := ht.1
      _ < t / s := by rw [lt_div_iff₀ hs0]; nlinarith [hst.2]
  have h := hsub hτ 0 (s • ξ)
  rw [smul_smul, div_mul_cancel₀ t hs0.ne'] at h
  calc f (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * f (s • ξ) + η * c := h
    _ ≤ (1 + (η : ℝ≥0∞)) * b' + η * c := by gcongr
    _ < b := hηb

/-- **Radial representation formula of [oahjpm14], second part.** The radial envelope of an ru-usc
function is ru-usc, with the same constant. -/
theorem RUUSCWith.radial {c : ℝ≥0} {f : Mat m N → ℝ≥0∞} (hf : RUUSCWith c (fun _ => f)) :
    RUUSCWith c (fun _ => Homogenization.radial f) := by
  intro η hη
  filter_upwards [hf η hη] with τ hτ _ ξ hξ
  have hA := hf.tendsto_radial (τ • ξ)
  have hB := hf.tendsto_radial ξ
  have hC : Tendsto (fun s : ℝ => f (s • ξ) + η * (c + f (s • ξ))) (𝓝[<] 1)
      (𝓝 (Homogenization.radial f ξ + η * (c + Homogenization.radial f ξ))) :=
    hB.add (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hB) (Or.inr ENNReal.coe_ne_top))
  refine le_of_tendsto_of_tendsto hA hC ?_
  filter_upwards [hB.eventually (gt_mem_nhds hξ)] with s hs
  rw [smul_comm]
  exact hτ 0 (s • ξ) hs

theorem RUUSC.radial {f : Mat m N → ℝ≥0∞} (hf : RUUSC (fun _ => f)) :
    RUUSC (fun _ => radial f) :=
  let ⟨c, hc, h⟩ := hf; ⟨c, hc, h.radial⟩

end Homogenization
