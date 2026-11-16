import Homogenization.DensityZaff

/-!
# Two remarks of Section 2

* `ConvexENN.ruuscWith` (Remark `rem:radialrep-convex`): a convex `G : 𝕄 → [0,∞]` with
  `G(0) < ∞` is uniformly ru-usc relative to `0`, with any constant `c > 0`, since
  `G(tξ) - G(ξ) ≤ (1-t) G(0)`.
* `Ytloc_const`, `Haff_const` (Remark `lEnvelopes` (iv), `env:indep`): for an integrand that does
  not depend on `x`, `𝒴_loc L(x,ξ) = 𝒵_aff L₀(ξ)` and `ℋ_aff L = 𝒵_aff L₀`, by the domain
  independence `aff0_domainIndependence` applied to the cubes `Q_ρ(x)` and `kY`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- **Remark `rem:radialrep-convex`.** A convex `G` with `G(0) < ∞` is uniformly ru-usc relative
to `0`, with every constant `c > 0`. -/
theorem ConvexENN.ruuscWith {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hG0 : G 0 ≠ ⊤) {c : ℝ≥0}
    (hc : 0 < c) : RUUSCWith c (fun _ : Sp N => G) := by
  intro η hη
  have hpos : (0 : ℝ≥0∞) < (η : ℝ≥0∞) * c :=
    pos_iff_ne_zero.2 (mul_ne_zero (by exact_mod_cast hη.ne') (by exact_mod_cast hc.ne'))
  have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (1 - t)) (𝓝[<] 1) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.tendsto_ofReal h
  have h2 : Tendsto (fun t : ℝ => ENNReal.ofReal (1 - t) * G 0) (𝓝[<] 1) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hG0)
  filter_upwards [h2.eventually (gt_mem_nhds hpos),
    Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht hti x ξ _
  set τ : ℝ≥0 := ⟨t, hti.1.le⟩
  have hτ : τ ≤ 1 := hti.2.le
  have hconv := hG ξ 0 τ hτ
  rw [smul_zero, add_zero] at hconv
  have hτc : ((1 - τ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 - t) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub hτ]
    rfl
  calc G (t • ξ) ≤ τ * G ξ + (1 - τ : ℝ≥0) * G 0 := hconv
    _ ≤ G ξ + η * (c + G ξ) := by
        refine add_le_add (mul_le_of_le_one_left zero_le (by exact_mod_cast hτ)) ?_
        rw [hτc]
        exact ht.le.trans (by gcongr; exact le_self_add)

theorem mem_cube_self {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) : x ∈ cube ρ x := by
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo]
  intro i
  constructor <;> linarith

/-- For an integrand independent of `x` and every cube `Q_ρ(x)`,
`𝒴 L(Q_ρ(x),ξ)/|Q_ρ(x)| = 𝒵_aff L₀(ξ)`. -/
theorem Yt_cube_div_volume_const (L₀ : Mat m N → ℝ≥0∞) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N)
    (ξ : Mat m N) :
    Yt (fun _ => L₀) (cube ρ x) ξ / volume (cube ρ x) = Zaff L₀ ξ := by
  rw [ENNReal.div_eq_inv_mul]
  exact aff0_domainIndependence L₀ (isOpen_cube ρ x) (isBounded_cube ρ x)
    ⟨x, mem_cube_self hρ x⟩ (volume_frontier_cube ρ x) ξ

/-- **Remark `lEnvelopes` (iv), first identity.** `𝒴_loc L(x,ξ) = 𝒵_aff L₀(ξ)` when `L` does not
depend on `x`. -/
theorem Ytloc_const (L₀ : Mat m N → ℝ≥0∞) (x : Sp N) (ξ : Mat m N) :
    Ytloc (fun _ => L₀) x ξ = Zaff L₀ ξ := by
  unfold Ytloc
  have h : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      Yt (fun _ => L₀) (cube ρ x) ξ / volume (cube ρ x) = Zaff L₀ ξ :=
    eventually_nhdsWithin_of_forall fun ρ hρ => Yt_cube_div_volume_const L₀ hρ x ξ
  rw [limsup_congr h]
  exact limsup_const _

/-- **Remark `lEnvelopes` (iv), second identity.** `ℋ_aff L = 𝒵_aff L₀` when `L` does not depend
on `x`. -/
theorem Haff_const (L₀ : Mat m N → ℝ≥0∞) (ξ : Mat m N) :
    Haff (fun _ => L₀) ξ = Zaff L₀ ξ := by
  unfold Haff
  have h : ∀ k : ℕ, Yt (fun _ => L₀) (cube ((k : ℝ) + 1) 0) ξ /
      volume (cube ((k : ℝ) + 1) (0 : Sp N)) = Zaff L₀ ξ := fun k =>
    Yt_cube_div_volume_const L₀ (by positivity) 0 ξ
  simp_rw [h]
  exact iInf_const

end Homogenization
