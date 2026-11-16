import Homogenization.RankOne

/-! # Lemma `lem:HaffZaff`

This file proves parts (i) and (ii) concerning the affine envelope `ℋ_aff` and its relation to
`𝒵_aff`. Part (iii), identifying `ℋ` with `ℋ_aff` under upper semicontinuity, remains open.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- For `Φ ∈ Aff₀(Y)` and `k ∈ ℕ`, the rescaled energy on `Y` dominates `ℋ_aff L(ξ)`.
This is the rescaling step used in the proof of part (i), completed by `Zaff_Haff_eq` below. -/
theorem Haff_le_lintegral_cell_rescale (L : Sp N → Mat m N → ℝ≥0∞) (ξ : Mat m N)
    (k : ℕ) {Φ : Sp N → Tgt m} (hΦ : Φ ∈ Aff0 (cube 1 (0 : Sp N))) :
    Haff L ξ ≤ ∫⁻ x in cube 1 (0 : Sp N),
      L (((k : ℝ) + 1) • x) (ξ + fderiv ℝ Φ x) := by
  let ε : ℝ := ((k : ℝ) + 1)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hrescale := iInf_rescale L hε (isOpen_cube 1 0).measurableSet ξ
  have hpre : (ε • ·) ⁻¹' cube 1 (0 : Sp N) = cube ((k : ℝ) + 1) 0 := by
    rw [preimage_smul_cube hε 1 0]
    congr 1
    · dsimp [ε]
      field_simp
    · simp
  have hscale := iInf₂_le (f := fun (φ : Sp N → Tgt m)
      (_ : φ ∈ (Aff0 (cube 1 (0 : Sp N)) : Set (Sp N → Tgt m))) =>
        ∫⁻ y in cube 1 (0 : Sp N), L (ε⁻¹ • y) (ξ + fderiv ℝ φ y)) Φ hΦ
  rw [hrescale] at hscale
  rw [hpre] at hscale
  have hvol : ENNReal.ofReal (ε ^ N) * Yt L (cube ((k : ℝ) + 1) 0) ξ =
      Yt L (cube ((k : ℝ) + 1) 0) ξ / volume (cube ((k : ℝ) + 1) (0 : Sp N)) := by
    rw [ENNReal.div_eq_inv_mul, volume_cube]
    have hp : ε ^ N = (((k : ℝ) + 1) ^ N)⁻¹ := by
      dsimp [ε]
      rw [inv_pow]
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [hp, ENNReal.ofReal_inv_of_pos (pow_pos hk N),
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ (k : ℝ) + 1) N]
  calc
    Haff L ξ ≤ Yt L (cube ((k : ℝ) + 1) 0) ξ /
        volume (cube ((k : ℝ) + 1) (0 : Sp N)) := iInf_le _ k
    _ = ENNReal.ofReal (ε ^ N) * Yt L (cube ((k : ℝ) + 1) 0) ξ := hvol.symm
    _ ≤ ∫⁻ y in cube 1 (0 : Sp N), L (ε⁻¹ • y) (ξ + fderiv ℝ Φ y) := hscale
    _ = ∫⁻ x in cube 1 (0 : Sp N), L (((k : ℝ) + 1) • x) (ξ + fderiv ℝ Φ x) := by
      congr 4
      dsimp [ε]
      rw [inv_inv]

/-- Gluing step of Lemma `lem:HaffZaff` (i): for `φ ∈ Aff₀(Y)` with pieces `Vᵢ` and gradients
`ζᵢ`, adding to `φ` the correctors of `densityHaff` on each piece gives `Φ_ε ∈ Aff₀(Y)`
whose `ε`-energies have limsup at most `∫_Y ℋ_aff L(ξ + ∇φ)`. The lemma itself is not
proved here; `Zaff_Haff_eq` below completes part (i) using this gluing step. -/
theorem exists_Aff0_glue_Haff {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hα : 0 < α)
    (hLm : Measurable (uncurry L)) (hLper : IsPeriodic L) (hLgr : HasGGrowth G α β L)
    (ξ : Mat m N) {φ : Sp N → Tgt m}
    (hφ : φ ∈ Aff0 (cube 1 (0 : Sp N))) :
    ∃ Φ : ℝ → Sp N → Tgt m, (∀ ε, Φ ε ∈ Aff0 (cube 1 (0 : Sp N))) ∧
      limsup (fun ε => ∫⁻ x in cube 1 (0 : Sp N),
        L (ε⁻¹ • x) (ξ + fderiv ℝ (Φ ε) x)) (𝓝[>] 0) ≤
          ∫⁻ x in cube 1 (0 : Sp N), Haff L (ξ + fderiv ℝ φ x) := by
  classical
  obtain ⟨K, n, V, ζ, hK, h0, hVo, hVU, hVd, hVf, hVc, hφV⟩ := Aff0.data hφ
  have hVb : ∀ i, Bornology.IsBounded (V i) := fun i =>
    (isBounded_cube 1 0).subset (hVU i)
  have hlocal : ∀ i, ∃ ψ : ℝ → Sp N → Tgt m,
      (∀ ε, ψ ε ∈ Aff0 (V i)) ∧
      limsup (fun ε => ∫⁻ x in V i,
        L (ε⁻¹ • x) (ξ + ζ i + fderiv ℝ (ψ ε) x)) (𝓝[>] 0) ≤
          volume (V i) * Haff L (ξ + ζ i) := by
    intro i
    obtain ⟨ψ, hψ, _, hlim⟩ :=
      densityHaff G α β L hG hα hLm hLper hLgr (V i) (hVo i) (hVb i) (ξ + ζ i)
    exact ⟨ψ, hψ, hlim⟩
  choose ψ hψ hψlim using hlocal
  let Φ : ℝ → Sp N → Tgt m := fun ε => φ + ∑ i, ψ i ε
  have hΦ : ∀ ε, Φ ε ∈ Aff0 (cube 1 (0 : Sp N)) := by
    intro ε
    exact Aff0.add_sum hK h0 hVo hVU hVd hVf hVc hφV (fun i => hψ i ε)
  have hψdata : ∀ ε, ∀ i, ∃ K', LipschitzWith K' (ψ i ε) ∧
      ∀ x ∉ V i, ψ i ε x = 0 := by
    intro ε i
    obtain ⟨K', _, _, _, hK', h0', _, _, _, _, _, _⟩ := Aff0.data (hψ i ε)
    exact ⟨K', hK', h0'⟩
  choose Kψ hKψ hzeroψ using hψdata
  have henergy : ∀ ε,
      (∫⁻ x in cube 1 (0 : Sp N), L (ε⁻¹ • x) (ξ + fderiv ℝ (Φ ε) x)) =
        ∑ i, ∫⁻ x in V i,
          L (ε⁻¹ • x) (ξ + ζ i + fderiv ℝ (ψ i ε) x) := by
    intro ε
    rw [lintegral_eq_sum_pieces_fintype hVo hVU hVd hVc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun_ae (hVo i).measurableSet ?_]
    filter_upwards [(hKψ ε i).ae_differentiableAt] with x hdiff hx
    have hlocalEq : ∀ᶠ y in 𝓝 x, Φ ε y = φ y + ψ i ε y := by
      filter_upwards [(hVo i).mem_nhds hx] with y hy
      simp only [Φ, Pi.add_apply]
      rw [sum_eq_of_mem_piece hVd (fun j z hz => hzeroψ ε j z hz) hy]
    have hderiv : HasFDerivAt (Φ ε) (ζ i + fderiv ℝ (ψ i ε) x) x := by
      have hφderiv := hφV i x hx
      have hψderiv := hdiff.hasFDerivAt
      have hadd := hφderiv.add hψderiv
      exact hadd.congr_of_eventuallyEq hlocalEq
    rw [hderiv.fderiv, add_assoc]
  have hlimsum :
      limsup (fun ε => ∫⁻ x in cube 1 (0 : Sp N),
        L (ε⁻¹ • x) (ξ + fderiv ℝ (Φ ε) x)) (𝓝[>] 0) ≤
        ∑ i, volume (V i) * Haff L (ξ + ζ i) := by
    simp_rw [henergy]
    exact (limsup_finset_sum_le Finset.univ _).trans
      (Finset.sum_le_sum fun i _ => hψlim i)
  have htarget :
      (∑ i, volume (V i) * Haff L (ξ + ζ i)) =
        ∫⁻ x in cube 1 (0 : Sp N), Haff L (ξ + fderiv ℝ φ x) := by
    rw [lintegral_eq_sum_pieces_fintype hVo hVU hVd hVc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun (hVo i).measurableSet
      (g := fun _ => Haff L (ξ + ζ i))]
    · rw [setLIntegral_const, mul_comm]
    · intro x hx
      change Haff L (ξ + fderiv ℝ φ x) = Haff L (ξ + ζ i)
      exact congrArg (fun A => Haff L (ξ + A)) (hφV i x hx).fderiv
  exact ⟨Φ, hΦ, hlimsum.trans_eq htarget⟩

/-- **Lemma `lem:HaffZaff` (i)**: `𝒵_aff(ℋ_aff L) = ℋ_aff L` for measurable,
`1`-periodic `L` with `G`-growth (`G` convex, `α > 0`). -/
theorem Zaff_Haff_eq {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hα : 0 < α) (hLm : Measurable (uncurry L)) (hLper : IsPeriodic L)
    (hLgr : HasGGrowth G α β L) : Zaff (Haff L) = Haff L := by
  funext ξ
  refine le_antisymm (Zaff_Haff_le L ξ) ?_
  dsimp [Zaff, Yt]
  refine le_iInf₂ fun φ hφ => ?_
  let b := ∫⁻ y in cube 1 (0 : Sp N), Haff L (ξ + fderiv ℝ φ y)
  obtain ⟨Φ, hΦ, hlim⟩ := exists_Aff0_glue_Haff hG hα hLm hLper hLgr ξ hφ
  let f : ℝ → ℝ≥0∞ := fun ε => ∫⁻ x in cube 1 (0 : Sp N),
    L (ε⁻¹ • x) (ξ + fderiv ℝ (Φ ε) x)
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ hb => ?_
  have hlim' : limsup f (𝓝[>] 0) < b + δ := by
    exact hlim.trans_lt (ENNReal.lt_add_right hb.ne (by positivity))
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < b + δ := eventually_lt_of_limsup_lt hlim'
  have htend : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have htoTop : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact tendsto_inv_atTop_zero.comp htoTop
    · filter_upwards [Filter.Eventually.of_forall fun k : ℕ =>
        show 0 < ((k : ℝ) + 1)⁻¹ from inv_pos.mpr (by positivity)] with k hk
      exact hk
  obtain ⟨k, hk⟩ := (htend.eventually hev).exists
  have hres := Haff_le_lintegral_cell_rescale L ξ k (hΦ (((k : ℝ) + 1)⁻¹))
  have hfk : f (((k : ℝ) + 1)⁻¹) < b + δ := hk
  have : Haff L ξ ≤ b + δ := hres.trans (le_of_lt (by simpa [f, inv_inv] using hfk))
  simpa [b] using this

/-- Under `G`-growth with `α > 0`, `ℋ_aff L` and `G` have the same effective domain. -/
theorem dom_Haff_eq {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hα : 0 < α) (hLgr : HasGGrowth G α β L) : dom (Haff L) = dom G := by
  ext ξ
  change Haff L ξ < ⊤ ↔ G ξ < ⊤
  constructor
  · intro hfinite
    obtain ⟨hlower, _⟩ := hLgr.Haff hG 0 ξ
    have hprod : (α : ℝ≥0∞) * G ξ < ⊤ := hlower.trans_lt hfinite
    have hαne : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hα)
    rcases ENNReal.mul_lt_top_iff.mp hprod with ⟨_, hg⟩ | hzero | hgzero
    · exact hg
    · exact False.elim (hαne hzero)
    · exact lt_top_iff_ne_top.mpr (by rw [hgzero]; exact ENNReal.zero_ne_top)
  · intro hfinite
    obtain ⟨_, hupper⟩ := hLgr.Haff hG 0 ξ
    apply hupper.trans_lt
    rcases eq_or_ne β 0 with hβ | hβ
    · simp [hβ]
    · apply ENNReal.mul_lt_top_iff.mpr
      left
      exact ⟨ENNReal.coe_lt_top, ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hfinite⟩⟩

/-- **Lemma `lem:HaffZaff` (ii)**: `ℋ_aff L` is locally Lipschitz on `int(dom G)`. It uses
(i) and `citedZaffLocLip`. Part (iii), `ℋ L = ℋ_aff L` under upper semicontinuity, is not
proved here. -/
theorem Haff_locallyLipschitzOn {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hα : 0 < α) (hLm : Measurable (uncurry L)) (hLper : IsPeriodic L)
    (hLgr : HasGGrowth G α β L) :
    ∀ ξ ∈ interior (dom G), ∃ K : ℝ≥0, ∃ s ∈ 𝓝 ξ,
      LipschitzOnWith K (fun ζ => (Haff L ζ).toReal) s := by
  have h := citedZaffLocLip (N := N) (m := m) (Haff L)
  rw [Zaff_Haff_eq hG hα hLm hLper hLgr, dom_Haff_eq hG hα hLgr] at h
  exact h

end Homogenization
