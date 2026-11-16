import Homogenization.HaffZaff
import Homogenization.Domains
import Homogenization.ApproxConvexZero

/-! # Proposition `lemmaUSC_ineq`

The first assertion of `lemmaUSC_ineq` (on `int(dom G)`) and `lem:HaffZaff` (iii) are proved,
using Lemma `lemme_approx_convex_zero` for cubes (`approxConvexZero_cube`, proved in
`ApproxConvexZero.lean`); no cited hypothesis is used. The second assertion (equality on all of
`𝕄` when `dom G` is open) is `Haff_eq_Hp_of_usc_of_isOpen`. Proposition `prop:Z3suff` (hypothesis
(Z8)) is `prop_Z3suff`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

/-- Pointwise step of the reverse Fatou lemma: `g₀ - f₀ ≤ liminf (gₙ - fₙ)` when
`g₀ ≤ liminf gₙ` and `limsup fₙ ≤ f₀`. -/
theorem sub_le_liminf_sub {g f : ℕ → ℝ≥0∞} {g₀ f₀ : ℝ≥0∞}
    (hg : g₀ ≤ liminf g atTop) (hf : limsup f atTop ≤ f₀) :
    g₀ - f₀ ≤ liminf (fun n => g n - f n) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  have hr' : f₀ < g₀ - r := by
    have h1 : r + f₀ < g₀ := lt_tsub_iff_right.mp hr
    exact lt_tsub_iff_left.mpr h1
  obtain ⟨d, hfd, hdg⟩ := exists_between hr'
  have hdr : d + r < g₀ := lt_tsub_iff_right.mp hdg
  obtain ⟨c, hdc, hcg⟩ := exists_between hdr
  have hgev : ∀ᶠ n in atTop, c < g n := eventually_lt_of_lt_liminf (hcg.trans_le hg)
  have hfev : ∀ᶠ n in atTop, f n < d := eventually_lt_of_limsup_lt (hf.trans_lt hfd)
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hgev, hfev] with n hgn hfn
  calc r ≤ c - d := (lt_tsub_iff_left.mpr hdc).le
    _ ≤ g n - f n := tsub_le_tsub hgn.le hfn.le

/-- Arithmetic step of the reverse Fatou lemma for `ℝ≥0∞`-valued sequences. -/
theorem limsup_le_of_le_liminf_sub {a b : ℕ → ℝ≥0∞} {A F : ℝ≥0∞} (hA : A ≠ ⊤)
    (ha : Tendsto a atTop (𝓝 A)) (hba : ∀ᶠ n in atTop, b n ≤ a n) (hFA : F ≤ A)
    (h : A - F ≤ liminf (fun n => a n - b n) atTop) :
    limsup b atTop ≤ F := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  have hAδ : A + δ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hA, ENNReal.coe_ne_top⟩
  have hev : ∀ᶠ n in atTop, a n ≤ A + δ :=
    ha.eventually (ge_mem_nhds (ENNReal.lt_add_right hA hδ'.ne'))
  have h2 : liminf (fun n => a n - b n) atTop ≤ liminf (fun n => (A + δ) - b n) atTop :=
    liminf_le_liminf (hev.mono fun n hn => tsub_le_tsub_right hn _)
  rw [ENNReal.liminf_const_sub _ _ hAδ] at h2
  have h3 : A - F ≤ (A + δ) - limsup b atTop := h.trans h2
  have hbA : limsup b atTop ≤ A := (limsup_le_limsup hba).trans ha.limsup_eq.le
  have hb : limsup b atTop ≤ A + δ := hbA.trans le_self_add
  have hFtop : F ≠ ⊤ := ne_top_of_le_ne_top hA hFA
  have hbtop : limsup b atTop ≠ ⊤ := ne_top_of_le_ne_top hA hbA
  have := (ENNReal.toReal_le_toReal (ENNReal.sub_ne_top hA) (ENNReal.sub_ne_top hAδ)).2 h3
  rw [ENNReal.toReal_sub_of_le hFA hA, ENNReal.toReal_sub_of_le hb hAδ,
    ENNReal.toReal_add hA ENNReal.coe_ne_top] at this
  rw [← ENNReal.toReal_le_toReal hbtop (ENNReal.add_ne_top.mpr ⟨hFtop, ENNReal.coe_ne_top⟩),
    ENNReal.toReal_add hFtop ENNReal.coe_ne_top]
  linarith

/-- Reverse Fatou lemma with varying dominating functions: if `fₙ ≤ gₙ`,
`∫ gₙ → ∫ g₀ < ∞`, `g₀ ≤ liminf gₙ` and `limsup fₙ ≤ f₀ ≤ g₀` a.e.,
then `limsup ∫ fₙ ≤ ∫ f₀`.
It is a tool for `lemmaUSC_ineq`, which is not proved here. -/
theorem limsup_lintegral_le_of_dominating {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : ℕ → α → ℝ≥0∞} {f₀ g₀ : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (hg : ∀ n, AEMeasurable (g n) μ)
    (hf₀ : AEMeasurable f₀ μ)
    (hfg : ∀ n, f n ≤ᵐ[μ] g n) (hf₀g₀ : f₀ ≤ᵐ[μ] g₀)
    (hg₀ : ∫⁻ x, g₀ x ∂μ ≠ ⊤)
    (hgint : Tendsto (fun n => ∫⁻ x, g n x ∂μ) atTop (𝓝 (∫⁻ x, g₀ x ∂μ)))
    (hg_liminf : ∀ᵐ x ∂μ, g₀ x ≤ liminf (fun n => g n x) atTop)
    (hf_limsup : ∀ᵐ x ∂μ, limsup (fun n => f n x) atTop ≤ f₀ x) :
    limsup (fun n => ∫⁻ x, f n x ∂μ) atTop ≤ ∫⁻ x, f₀ x ∂μ := by
  have hF : ∫⁻ x, f₀ x ∂μ ≤ ∫⁻ x, g₀ x ∂μ := lintegral_mono_ae hf₀g₀
  have hpt : ∀ᵐ x ∂μ, g₀ x - f₀ x ≤ liminf (fun n => g n x - f n x) atTop := by
    filter_upwards [hg_liminf, hf_limsup] with x h1 h2
    exact sub_le_liminf_sub h1 h2
  have hfatou : ∫⁻ x, (g₀ x - f₀ x) ∂μ ≤
      liminf (fun n => ∫⁻ x, (g n x - f n x) ∂μ) atTop :=
    (lintegral_mono_ae hpt).trans (lintegral_liminf_le' fun n => (hg n).sub (hf n))
  have hgfin : ∀ᶠ n in atTop, ∫⁻ x, g n x ∂μ ≠ ⊤ :=
    hgint.eventually (isOpen_ne.mem_nhds hg₀)
  have hcongr : ∀ᶠ n in atTop, ∫⁻ x, (g n x - f n x) ∂μ =
      ∫⁻ x, g n x ∂μ - ∫⁻ x, f n x ∂μ := by
    filter_upwards [hgfin] with n hn
    exact lintegral_sub' (hf n) (ne_top_of_le_ne_top hn (lintegral_mono_ae (hfg n))) (hfg n)
  rw [lintegral_sub' hf₀ (ne_top_of_le_ne_top hg₀ hF) hf₀g₀, liminf_congr hcongr] at hfatou
  exact limsup_le_of_le_liminf_sub hg₀ hgint
    (Eventually.of_forall fun n => lintegral_mono_ae (hfg n)) hF hfatou

variable {N m : ℕ}

/-- Sequential form of lower semicontinuity: `h x₀ ≤ liminf h(xₙ)` when `xₙ → x₀`. -/
theorem LowerSemicontinuous.le_liminf_seq {E : Type*} [TopologicalSpace E]
    {h : E → ℝ≥0∞} (hh : LowerSemicontinuous h) {x : ℕ → E} {x₀ : E}
    (hx : Tendsto x atTop (𝓝 x₀)) : h x₀ ≤ liminf (fun n => h (x n)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
  exact le_liminf_of_le (by isBoundedDefault) ((hx.eventually (hh x₀ y hy)).mono fun _ h => h.le)

/-- Sequential form of upper semicontinuity. -/
theorem UpperSemicontinuous.limsup_le_seq {E : Type*} [TopologicalSpace E]
    {h : E → ℝ≥0∞} (hh : UpperSemicontinuous h) {x : ℕ → E} {x₀ : E}
    (hx : Tendsto x atTop (𝓝 x₀)) : limsup (fun n => h (x n)) atTop ≤ h x₀ := by
  refine le_of_forall_gt_imp_ge_of_dense fun y hy => ?_
  exact limsup_le_of_le (by isBoundedDefault) ((hx.eventually (hh x₀ y hy)).mono fun _ h => h.le)

/-- Convexity is preserved by the translation `ζ ↦ G(ξ₀ + ζ)`. -/
theorem ConvexENN.comp_add_left {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) (ξ₀ : Mat m N) :
    ConvexENN (fun ζ => G (ξ₀ + ζ)) := by
  intro ξ ζ t ht
  have h := hG (ξ₀ + ξ) (ξ₀ + ζ) t ht
  have heq : (t : ℝ) • (ξ₀ + ξ) + ((1 - t : ℝ≥0) : ℝ) • (ξ₀ + ζ) =
      ξ₀ + ((t : ℝ) • ξ + ((1 - t : ℝ≥0) : ℝ) • ζ) := by
    have hsum : (t : ℝ) + ((1 - t : ℝ≥0) : ℝ) = 1 := by
      rw [NNReal.coe_sub ht]; simp
    calc (t : ℝ) • (ξ₀ + ξ) + ((1 - t : ℝ≥0) : ℝ) • (ξ₀ + ζ)
        = ((t : ℝ) + ((1 - t : ℝ≥0) : ℝ)) • ξ₀ +
            ((t : ℝ) • ξ + ((1 - t : ℝ≥0) : ℝ) • ζ) := by
          rw [smul_add, smul_add, add_smul]; abel
      _ = _ := by rw [hsum, one_smul]
  rw [heq] at h
  exact h

/-- If `ξ₀ ∈ int(dom G)`, then `0` is interior to the domain of `ζ ↦ G(ξ₀ + ζ)`. -/
theorem zero_mem_interior_dom_comp_add {G : Mat m N → ℝ≥0∞} {ξ₀ : Mat m N}
    (hξ₀ : ξ₀ ∈ interior (dom G)) :
    (0 : Mat m N) ∈ interior (dom (fun ζ => G (ξ₀ + ζ))) := by
  have hpre : dom (fun ζ => G (ξ₀ + ζ)) = (Homeomorph.addLeft ξ₀) ⁻¹' dom G := rfl
  rw [hpre, ← (Homeomorph.addLeft ξ₀).preimage_interior]
  simpa using hξ₀

/-- Core estimate of Proposition `lemmaUSC_ineq`: for `ξ₀ ∈ int(dom G)` and every Sobolev
corrector `φ₀` on the cell `(k+1)Y`, `ℋ_aff L(ξ₀) |(k+1)Y| ≤ ∫ L(y, ξ₀ + ∇φ₀)`.
It uses `approxConvexZero_cube` with `Ψ = G(ξ₀ + ·)` (a.e. convergence of the gradients and
convergence of the energies) and the reverse Fatou lemma `limsup_lintegral_le_of_dominating`. -/
theorem Haff_mul_volume_le_lintegral_of_usc [NeZero N] {p : ℝ}
    [hP : Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞}
    {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    (hα : 0 < α) (hLm : Measurable (uncurry L)) (hLgr : HasGGrowth G α β L)
    (husc : ∀ᵐ x, UpperSemicontinuous (L x)) {ξ₀ : Mat m N}
    (hξ₀ : ξ₀ ∈ interior (dom G))
    (k : ℕ) {φ₀ : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hφ₀ : φ₀ ∈ W1p0 (ENNReal.ofReal p) (cube ((k : ℝ) + 1) (0 : Sp N))) :
    Haff L ξ₀ * volume (cube ((k : ℝ) + 1) (0 : Sp N)) ≤
      ∫⁻ y in cube ((k : ℝ) + 1) (0 : Sp N), L y (ξ₀ + φ₀.2 y) := by
  set Q : Set (Sp N) := cube ((k : ℝ) + 1) (0 : Sp N) with hQ
  set μ : Measure (Sp N) := volume.restrict Q with hμ
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  by_cases hE : ∫⁻ y in Q, L y (ξ₀ + φ₀.2 y) = ⊤
  · rw [hE]; exact le_top
  -- finite `G`-energy
  have hαne : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
  have hGfin : ∫⁻ y in Q, G (ξ₀ + φ₀.2 y) < ⊤ := by
    have h1 : (α : ℝ≥0∞) * ∫⁻ y in Q, G (ξ₀ + φ₀.2 y) ≤
        ∫⁻ y in Q, L y (ξ₀ + φ₀.2 y) := by
      rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact lintegral_mono fun y => (hLgr y _).1
    have h2 := h1.trans_lt (lt_top_iff_ne_top.2 hE)
    exact (ENNReal.mul_lt_top_iff.mp h2).elim (fun h => h.2)
      (fun h => h.elim (fun h0 => absurd h0 hαne)
        (fun h0 => by rw [h0]; exact ENNReal.zero_lt_top))
  -- Lemma `lemme_approx_convex_zero` on the cube `Q`
  set Ψ : Mat m N → ℝ≥0∞ := fun ζ => G (ξ₀ + ζ) with hΨ
  have hΨlsc : LowerSemicontinuous Ψ :=
    hGlsc.comp (continuous_const.add continuous_id)
  have hp1 : 1 ≤ p := ENNReal.one_le_ofReal.1 hP.out
  obtain ⟨φ, hφAff, hae, henergy⟩ := approxConvexZero_cube hp1 hk hφ₀
    (hG.comp_add_left ξ₀) hΨlsc (zero_mem_interior_dom_comp_add hξ₀) hGfin
  have hmeas₀ : AEStronglyMeasurable φ₀.2 μ := (hφ₀.2.2.1.restrict Q).1
  set ns : ℕ → ℕ := id
  have hns : StrictMono ns := strictMono_id
  -- reverse Fatou
  have hβc : Continuous fun t : ℝ≥0∞ => (β : ℝ≥0∞) * (1 + t) :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
      (continuous_const_add (1 : ℝ≥0∞))
  have hβm : Monotone fun t : ℝ≥0∞ => (β : ℝ≥0∞) * (1 + t) := fun a b hab =>
    mul_le_mul_right (add_le_add_right hab 1) _
  have hGm : Measurable G := hGlsc.measurable
  have hfm : ∀ i, AEMeasurable (fun y => L y (ξ₀ + fderiv ℝ (φ (ns i)) y)) μ := fun i =>
    (hLm.comp (measurable_id.prodMk
      (measurable_const.add (measurable_fderiv ℝ (φ (ns i)))))).aemeasurable
  have hgm : ∀ i, AEMeasurable
      (fun y => (β : ℝ≥0∞) * (1 + G (ξ₀ + fderiv ℝ (φ (ns i)) y))) μ := fun i =>
    (measurable_const.mul (measurable_const.add
      (hGm.comp (measurable_const.add (measurable_fderiv ℝ (φ (ns i))))))).aemeasurable
  have hf₀m : AEMeasurable (fun y => L y (ξ₀ + φ₀.2 y)) μ :=
    hLm.comp_aemeasurable (aemeasurable_id.prodMk (aemeasurable_const.add hmeas₀.aemeasurable))
  have hQvol : μ univ ≠ ⊤ := by
    rw [hμ, Measure.restrict_apply_univ]; exact (isBounded_cube _ _).measure_lt_top.ne
  have hgsplit : ∀ D : Sp N → Mat m N, Measurable (fun y => G (ξ₀ + D y)) →
      ∫⁻ y, (β : ℝ≥0∞) * (1 + G (ξ₀ + D y)) ∂μ =
        (β : ℝ≥0∞) * (μ univ + ∫⁻ y, G (ξ₀ + D y) ∂μ) := by
    intro D hD
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_add_left measurable_const,
      lintegral_const, one_mul]
  have hG₀m : AEMeasurable (fun y => G (ξ₀ + φ₀.2 y)) μ :=
    hGm.comp_aemeasurable (aemeasurable_const.add hmeas₀.aemeasurable)
  have hint₀ : ∫⁻ y, (β : ℝ≥0∞) * (1 + G (ξ₀ + φ₀.2 y)) ∂μ =
      (β : ℝ≥0∞) * (μ univ + ∫⁻ y, G (ξ₀ + φ₀.2 y) ∂μ) := by
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_add_left' aemeasurable_const,
      lintegral_const, one_mul]
  have hg₀fin : ∫⁻ y, (β : ℝ≥0∞) * (1 + G (ξ₀ + φ₀.2 y)) ∂μ ≠ ⊤ := by
    rw [hint₀]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hQvol, hGfin.ne⟩)
  have hgint : Tendsto (fun i => ∫⁻ y, (β : ℝ≥0∞) *
      (1 + G (ξ₀ + fderiv ℝ (φ (ns i)) y)) ∂μ) atTop
      (𝓝 (∫⁻ y, (β : ℝ≥0∞) * (1 + G (ξ₀ + φ₀.2 y)) ∂μ)) := by
    have h1 := henergy.comp hns.tendsto_atTop
    rw [hint₀]
    have heq :
        (fun i => ∫⁻ y, (β : ℝ≥0∞) * (1 + G (ξ₀ + fderiv ℝ (φ (ns i)) y)) ∂μ) =
        fun i => (β : ℝ≥0∞) * (μ univ + ∫⁻ y, G (ξ₀ + fderiv ℝ (φ (ns i)) y) ∂μ) := by
      funext i
      exact hgsplit _ (hGm.comp (measurable_const.add (measurable_fderiv ℝ (φ (ns i)))))
    rw [heq]
    exact ENNReal.Tendsto.const_mul (tendsto_const_nhds.add h1) (Or.inr ENNReal.coe_ne_top)
  have hgliminf : ∀ᵐ y ∂μ, (β : ℝ≥0∞) * (1 + G (ξ₀ + φ₀.2 y)) ≤
      liminf (fun i => (β : ℝ≥0∞) * (1 + G (ξ₀ + fderiv ℝ (φ (ns i)) y))) atTop := by
    filter_upwards [hae] with y hy
    exact LowerSemicontinuous.le_liminf_seq (hβc.comp_lowerSemicontinuous hGlsc hβm)
      (tendsto_const_nhds.add hy)
  have hflimsup : ∀ᵐ y ∂μ, limsup (fun i => L y (ξ₀ + fderiv ℝ (φ (ns i)) y)) atTop ≤
      L y (ξ₀ + φ₀.2 y) := by
    filter_upwards [hae, ae_restrict_of_ae husc] with y hy hyusc
    exact UpperSemicontinuous.limsup_le_seq hyusc (tendsto_const_nhds.add hy)
  have hrev := limsup_lintegral_le_of_dominating hfm hgm hf₀m
    (fun i => Eventually.of_forall fun y => (hLgr y _).2)
    (Eventually.of_forall fun y => (hLgr y _).2) hg₀fin hgint hgliminf hflimsup
  -- each affine competitor bounds `ℋ_aff`
  have hvol0 : volume Q ≠ 0 := (volume_cube_pos hk 0).ne'
  have hvoltop : volume Q ≠ ⊤ := (isBounded_cube _ _).measure_lt_top.ne
  have hlow : ∀ i, Haff L ξ₀ * volume Q ≤
      ∫⁻ y, L y (ξ₀ + fderiv ℝ (φ (ns i)) y) ∂μ := by
    intro i
    have h1 : Haff L ξ₀ ≤ Yt L Q ξ₀ / volume Q := iInf_le _ k
    have h2 : Yt L Q ξ₀ ≤ ∫⁻ y in Q, L y (ξ₀ + fderiv ℝ (φ (ns i)) y) :=
      iInf₂_le _ (hφAff (ns i))
    calc Haff L ξ₀ * volume Q ≤ Yt L Q ξ₀ / volume Q * volume Q := by gcongr
      _ = Yt L Q ξ₀ := ENNReal.div_mul_cancel hvol0 hvoltop
      _ ≤ _ := h2
  exact (le_limsup_of_frequently_le (Frequently.of_forall hlow) (by isBoundedDefault)).trans hrev

/-- **Proposition `lemmaUSC_ineq`** (first assertion): if `G` is convex and lower
semicontinuous, `L` is measurable with `G`-growth (`α > 0`) and `L(x,·)` is upper
semicontinuous for a.e. `x`, then
`ℋ_aff L = ℋ L` on `int(dom G)`. The second assertion
of the proposition (equality on all of `𝕄` when `dom G` is open) is
`Haff_eq_Hp_of_usc_of_isOpen`. -/
theorem Haff_eq_Hp_of_usc [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞}
    {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    (hα : 0 < α) (hLm : Measurable (uncurry L)) (hLgr : HasGGrowth G α β L)
    (husc : ∀ᵐ x, UpperSemicontinuous (L x)) {ξ₀ : Mat m N}
    (hξ₀ : ξ₀ ∈ interior (dom G)) :
    Haff L ξ₀ = Hp (ENNReal.ofReal p) L ξ₀ := by
  refine le_antisymm (le_iInf fun k => ?_) (Hp_le_Haff _ L ξ₀)
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [ENNReal.le_div_iff_mul_le (Or.inl (volume_cube_pos hk 0).ne')
    (Or.inl (isBounded_cube _ _).measure_lt_top.ne)]
  exact le_iInf₂ fun φ₀ hφ₀ =>
    Haff_mul_volume_le_lintegral_of_usc (p := p) hG hGlsc hα hLm hLgr
    husc hξ₀ k hφ₀

/-- **Lemma `lem:HaffZaff` (iii)**: under upper semicontinuity, `ℋ L` is locally Lipschitz on
`int(dom G)` (via `Haff_eq_Hp_of_usc` and `Haff_locallyLipschitzOn`). -/
theorem Hp_locallyLipschitzOn_of_usc [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞}
    {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    (hα : 0 < α) (hLm : Measurable (uncurry L)) (hLper : IsPeriodic L)
    (hLgr : HasGGrowth G α β L) (husc : ∀ᵐ x, UpperSemicontinuous (L x)) :
    ∀ ξ ∈ interior (dom G), ∃ K : ℝ≥0, ∃ s ∈ 𝓝 ξ,
      LipschitzOnWith K (fun ζ => (Hp (ENNReal.ofReal p) L ζ).toReal) s := by
  intro ξ hξ
  obtain ⟨K, s, hs, hK⟩ := Haff_locallyLipschitzOn hG hα hLm hLper hLgr ξ hξ
  refine ⟨K, s ∩ interior (dom G), inter_mem hs (isOpen_interior.mem_nhds hξ), ?_⟩
  intro x hx y hy
  have hx' := Haff_eq_Hp_of_usc (p := p) hG hGlsc hα hLm hLgr husc hx.2
  have hy' := Haff_eq_Hp_of_usc (p := p) hG hGlsc hα hLm hLgr husc hy.2
  simp only [← hx', ← hy']
  exact hK hx.1 hy.1

section OpenDom

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-- When `dom G` is open, a `W^{1,p}_0` perturbation of a matrix `ζ ∉ dom G` has infinite
`G`-energy (Jensen-type argument by separating `ζ` from the open convex set `dom G`). -/
theorem ConvexENN.lintegral_W1p0_eq_top_of_not_mem_dom_of_isOpen
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGo : IsOpen (dom G)) {U : Set (Sp N)}
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUf : volume (frontier U) = 0)
    (hU0 : volume U ≠ 0) {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 (ENNReal.ofReal p) U) {ζ : Mat m N}
    (hζ : ζ ∉ dom G) : ∫⁻ y in U, G (ζ + u.2 y) = ⊤ := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hG.convex_dom hGo hζ
  let μ := volume.restrict U
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hUb.measure_lt_top.ne
  have hint : Integrable u.2 μ := (hu.2.2.1.restrict U).integrable hP.out
  let T : Set (Sp N) := {y | 0 ≤ f (u.2 y)}
  have hTval : ∀ y ∈ T, G (ζ + u.2 y) = ⊤ := by
    intro y hy
    have hy' : (0 : ℝ) ≤ f (u.2 y) := hy
    by_contra hne
    have := hf _ (lt_top_iff_ne_top.2 hne)
    rw [map_add] at this
    linarith
  have hT : NullMeasurableSet T μ :=
    nullMeasurableSet_le aemeasurable_const
      (f.continuous.measurable.comp_aemeasurable hint.aemeasurable)
  by_contra hne
  have hzero : μ T = 0 := by
    by_contra hμ
    apply hne
    apply top_unique
    calc (⊤ : ℝ≥0∞) = ∫⁻ y, T.indicator (fun _ => (⊤ : ℝ≥0∞)) y ∂μ := by
          rw [lintegral_indicator_const₀ hT]
          simp [hμ]
      _ ≤ ∫⁻ y, G (ζ + u.2 y) ∂μ := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ T
          · simp [hy, hTval y hy]
          · simp [hy]
  have hneg : ∀ᵐ y ∂μ, f (u.2 y) < 0 := by
    rw [ae_iff]
    have hset : {y | ¬ f (u.2 y) < 0} = T := by
      ext y
      simp [T]
    rw [hset, hzero]
  have hcompl : μ univ ≤ μ (support fun y => -f (u.2 y)) := by
    calc μ univ ≤ μ T + μ Tᶜ := by
          rw [← union_compl_self T]
          exact measure_union_le _ _
      _ = μ Tᶜ := by rw [hzero, zero_add]
      _ ≤ μ (support fun y => -f (u.2 y)) := by
          refine measure_mono fun y hy => ?_
          have hy' : ¬ (0 ≤ f (u.2 y)) := hy
          simp only [mem_support, ne_eq, neg_eq_zero]
          intro h0
          exact hy' h0.ge
  have hμpos : 0 < μ univ := by
    rw [Measure.restrict_apply_univ]
    exact pos_iff_ne_zero.2 hU0
  have hpos : 0 < ∫ y, -f (u.2 y) ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae
      (hneg.mono fun y hy => by simp only [Pi.zero_apply, Pi.neg_apply]; linarith)
      (f.integrable_comp hint).neg).2 (hμpos.trans_le hcompl)
  have hI : ∫ y, -f (u.2 y) ∂μ = 0 := by
    rw [integral_neg, ContinuousLinearMap.integral_comp_comm f hint,
      W1p0.integral_grad_eq_zero hUo hUb hUf hu, map_zero, neg_zero]
  linarith

/-- When `dom G` is open, `Hp` is infinite outside `dom G` if the lower growth coefficient is
positive. -/
theorem HasGGrowth.Hp_eq_top_of_not_mem_dom_of_isOpen
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) (h : HasGGrowth G α β L) (hα : 0 < α)
    {ζ : Mat m N} (hζ : ζ ∉ dom G) : Hp (ENNReal.ofReal p) L ζ = ⊤ := by
  apply top_unique
  rw [Hp]
  refine le_iInf fun k => ?_
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hY : Ytp (ENNReal.ofReal p) L (cube ((k : ℝ) + 1) 0) ζ = ⊤ := by
    apply top_unique
    rw [Ytp]
    refine le_iInf₂ fun u hu => ?_
    have hA := hG.lintegral_W1p0_eq_top_of_not_mem_dom_of_isOpen hGo
      (isOpen_cube _ _) (isBounded_cube _ _) (volume_frontier_cube _ _)
      (volume_cube_pos hk 0).ne' hu hζ
    calc
      ⊤ = (α : ℝ≥0∞) * ∫⁻ y in cube ((k : ℝ) + 1) 0, G (ζ + u.2 y) := by
        rw [hA]
        exact (ENNReal.mul_top (by exact_mod_cast hα.ne')).symm
      _ = ∫⁻ y in cube ((k : ℝ) + 1) 0, α * G (ζ + u.2 y) :=
        (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
      _ ≤ ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ζ + u.2 y) :=
        lintegral_mono fun y => (h y _).1
  rw [hY, ENNReal.top_div_of_ne_top (volume_cube_ne_top _ _)]

end OpenDom

/-- **Proposition `lemmaUSC_ineq`** (second assertion): if moreover `dom G` is open, then
`ℋ_aff L = ℋ L` on all of `𝕄`. -/
theorem Haff_eq_Hp_of_usc_of_isOpen [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞}
    {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    (hGo : IsOpen (dom G)) (hα : 0 < α) (hLm : Measurable (uncurry L))
    (hLgr : HasGGrowth G α β L) (husc : ∀ᵐ x, UpperSemicontinuous (L x)) (ξ : Mat m N) :
    Haff L ξ = Hp (ENNReal.ofReal p) L ξ := by
  by_cases hξ : ξ ∈ dom G
  · exact Haff_eq_Hp_of_usc (p := p) hG hGlsc hα hLm hLgr husc (by rwa [hGo.interior_eq])
  · have hH := hLgr.Hp_eq_top_of_not_mem_dom_of_isOpen (p := p) hG hGo hα hξ
    rw [hH]
    exact top_unique (hH ▸ Hp_le_Haff _ L ξ)

/-- Under `G`-growth (`α > 0`, `G` convex), measurability and periodicity, `ℋ_aff L` is
continuous at every point of `int(dom G)` (from `Haff_locallyLipschitzOn`). -/
theorem Haff_continuousAt {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hα : 0 < α) (hLm : Measurable (uncurry L)) (hLper : IsPeriodic L)
    (hLgr : HasGGrowth G α β L) {ξ : Mat m N} (hξ : ξ ∈ interior (dom G)) :
    ContinuousAt (Haff L) ξ := by
  obtain ⟨K, s, hs, hK⟩ := Haff_locallyLipschitzOn hG hα hLm hLper hLgr ξ hξ
  have hc : ContinuousAt (fun ζ => ENNReal.ofReal (Haff L ζ).toReal) ξ :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((hK.continuousOn ξ (mem_of_mem_nhds hs)).continuousAt hs)
  refine hc.congr ?_
  filter_upwards [isOpen_interior.mem_nhds hξ] with ζ hζ
  have hfin : Haff L ζ ≠ ⊤ := by
    have : ζ ∈ dom (Haff L) := by
      rw [dom_Haff_eq hG hα hLgr]
      exact interior_subset hζ
    exact this.ne
  exact ENNReal.ofReal_toReal hfin

/-- Under `G`-growth with `α > 0` and `dom G` open, `α G ≤ ℋ L` on all of `𝕄`. -/
theorem HasGGrowth.mul_le_Hp_of_isOpen {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGo : IsOpen (dom G)) (h : HasGGrowth G α β L) (hα : 0 < α)
    (ζ : Mat m N) : (α : ℝ≥0∞) * G ζ ≤ Hp (ENNReal.ofReal p) L ζ := by
  by_cases hζ : ζ ∈ dom G
  · exact h.le_Hp hG (by rwa [hGo.interior_eq])
  · rw [h.Hp_eq_top_of_not_mem_dom_of_isOpen hG hGo hα hζ]
    exact le_top

/-- **Proposition `prop:Z3suff`**, for a general integrand `L` (to be applied to
`L = 𝒴_loc h`): if `G` is convex and lower semicontinuous with `dom G` open and
`G(tξ) → ∞` as `t → 1⁻` for every `ξ ∉ dom G`, and `L` is measurable, `1`-periodic, has
`G`-growth (`α > 0`) and `L(x,·)` is upper semicontinuous for a.e. `x`, then
`𝒵_aff(ℋ_aff L) ≤ \widehat{ℋ L}`.
For `dom G` open, the singularity hypothesis is required at every `ξ ∉ dom G`; at
`ξ ∉ closure (dom G)` it holds automatically, but this equivalence with the paper's condition
(stated on `∂(dom G)`) is not proved here. -/
theorem Zaff_Haff_le_radial_Hp_of_usc [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    (hGo : IsOpen (dom G))
    (hGsing : ∀ ξ ∉ dom G, Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hα : 0 < α) (hLm : Measurable (uncurry L)) (hLper : IsPeriodic L)
    (hLgr : HasGGrowth G α β L) (husc : ∀ᵐ x, UpperSemicontinuous (L x)) (ξ : Mat m N) :
    Zaff (Haff L) ξ ≤ radial (Hp (ENNReal.ofReal p) L) ξ := by
  rw [Zaff_Haff_eq hG hα hLm hLper hLgr]
  by_cases hξ : ξ ∈ dom G
  · have hEq : Hp (ENNReal.ofReal p) L = Haff L :=
      funext fun ζ => (Haff_eq_Hp_of_usc_of_isOpen (p := p) hG hGlsc hGo hα hLm hLgr husc ζ).symm
    have htend : Tendsto (fun t : ℝ => t • ξ) (𝓝[<] 1) (𝓝 ξ) := by
      have h : Tendsto (fun t : ℝ => t • ξ) (𝓝 1) (𝓝 ((1 : ℝ) • ξ)) :=
        (continuous_id.smul continuous_const).continuousAt
      rw [one_smul] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hc := Haff_continuousAt hG hα hLm hLper hLgr (by rwa [hGo.interior_eq])
    rw [radial, hEq]
    exact ((hc.tendsto.comp htend).liminf_eq).ge
  · have htop : Tendsto (fun t : ℝ => Hp (ENNReal.ofReal p) L (t • ξ)) (𝓝[<] 1) (𝓝 ⊤) := by
      have hα0 : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
      have h := ENNReal.Tendsto.const_mul (a := (α : ℝ≥0∞)) (hGsing ξ hξ)
        (Or.inl ENNReal.top_ne_zero)
      rw [ENNReal.mul_top hα0] at h
      exact tendsto_nhds_top_mono h (Eventually.of_forall fun t =>
        hLgr.mul_le_Hp_of_isOpen hG hGo hα (t • ξ))
    rw [radial, htop.liminf_eq]
    exact le_top

/-- **Proposition `prop:Z3suff`** (hypothesis (Z8) of `Hypotheses`): for `W` measurable,
`1`-periodic, with the set-function bound (Z3), `𝒴_loc W` measurable (Z6) and
`𝒴_loc W(x,·)` upper semicontinuous for a.e. `x`, and `G` as in
`Zaff_Haff_le_radial_Hp_of_usc`, `𝒵_aff ℋ_aff(𝒴_loc W) ≤ \widehat{ℋ(𝒴_loc W)}`. The
measurability of `𝒴_loc W` is assumed (Z6), not derived. -/
theorem prop_Z3suff [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {W : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G) (hGlsc : LowerSemicontinuous G)
    (hGo : IsOpen (dom G))
    (hGsing : ∀ ξ ∉ dom G, Tendsto (fun t : ℝ => G (t • ξ)) (𝓝[<] 1) (𝓝 ⊤))
    (hα : 0 < α) (hWper : IsPeriodic W)
    (hset : ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      (α : ℝ≥0∞) * volume U * G ξ ≤ Yt W U ξ ∧ Yt W U ξ ≤ β * volume U * (1 + G ξ))
    (hYm : Measurable (uncurry (Ytloc W)))
    (husc : ∀ᵐ x, UpperSemicontinuous (Ytloc W x)) (ξ : Mat m N) :
    Zaff (Haff (Ytloc W)) ξ ≤ radial (Hp (ENNReal.ofReal p) (Ytloc W)) ξ :=
  Zaff_Haff_le_radial_Hp_of_usc (p := p) hG hGlsc hGo hGsing hα hYm hWper.Ytloc
    (HasGGrowth.Ytloc hset) husc ξ

end Homogenization
