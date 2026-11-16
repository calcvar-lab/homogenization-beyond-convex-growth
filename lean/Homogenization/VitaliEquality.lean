import Homogenization.Vitali

/-!
# The equality in Theorem `Vitali-envelope-cite`

Under the hypotheses of `VitaliEnvelopeUpper`, the inequality `∫_A lowDeriv ≤ S^*(A)` holds for
every open `A ⊆ Ω` (`lintegral_lowDeriv_le_vitaliEnv`). With `vitaliEnv_le_lintegral` this gives
the equality `S^*(A) = ∫_A lowDeriv` of the cited Theorem A.16 of [oah-cloz-jpm17], so that
`CitedVitaliEnvelope` holds (`citedVitaliEnvelope_holds`).

The proof continues the numbering of the steps of `Homogenization.Vitali` (Steps 1–3), for the
Lebesgue measure, axis-parallel cubes (the balls of the sup norm) and a nonnegative set function:

* **Step 4** (`le_tsum_add_setLIntegral`): if the `Qᵢ` are pairwise disjoint open sets with
  closures in an open `Q ⊆ Ω` and null frontiers, then `S(Q) ≤ ∑ S(Qᵢ) + ∫_{Q ∖ ⋃ Qᵢ} g`.
* **Good balls** (`ae_good_ball`): for a.e. `x ∈ Ω` and every `τ > 0`,
  `∫_{Q_ρ(x)} lowDeriv ≤ S(Q_ρ(x)) + τ |Q_ρ(x)|` for small `ρ`.
* **Step 5** (`lintegral_lowDeriv_le_vitaliEnv_add`): a Vitali covering of `O` by disjoint good
  balls `B_l` gives `∫_O lowDeriv ≤ ∑ S(B_l) + τ |O|`; for a family of `𝒱^η(O)`, the cubes whose
  closure lies in `B_l` cover `B_l` except for the layer of width `η` along `∂B_l`, whose
  `∫ g` tends to `0` with `η`.

`vitaliEnvelope_full` collects all the conclusions of Theorem `Vitali-envelope-cite` for
`dS = lowDeriv S Ω`: measurability, finiteness a.e., `∫_Ω dS < ∞`, the limit along centred cubes
and the equality. The hypothesis of the paper, a finite Radon measure `ν ≪ 𝓛ᴺ`, is written as a
measurable density `g` with `∫_Ω g < ∞`, as in `CitedVitaliEnvelope`; the passage from `ν` to `g`
(Radon–Nikodym) is not formalized here. The main theorem (`main_Ggrowth_final_two`) uses only the
inequality form `VitaliEnvelopeUpper`.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ} [NeZero N] {Ω : Set (Sp N)} {S : Set (Sp N) → ℝ≥0∞} {g : Sp N → ℝ≥0∞}

omit [NeZero N] in
/-- **Step 4 of Theorem `Vitali-envelope-cite`** (inner estimate): for pairwise disjoint open sets
`Qᵢ` with closures in an open `Q ⊆ Ω` and null frontiers,
`S(Q) ≤ ∑ᵢ S(Qᵢ) + ∫_{Q ∖ ⋃ Qᵢ} g`. The `Qᵢ` need not cover `Q`. This is a step only: it
says nothing about the Vitali envelope. -/
theorem le_tsum_add_setLIntegral (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V)
    {Q : Set (Sp N)} (hQo : IsOpen Q) (hQΩ : Q ⊆ Ω) {Qi : ℕ → Set (Sp N)}
    (hQio : ∀ i, IsOpen (Qi i)) (hQic : ∀ i, closure (Qi i) ⊆ Q)
    (hQid : Pairwise fun i j => Disjoint (Qi i) (Qi j))
    (hQif : ∀ i, volume (frontier (Qi i)) = 0) :
    S Q ≤ ∑' i, S (Qi i) + ∫⁻ x in Q \ ⋃ i, Qi i, g x := by
  set a : ℕ → ℝ≥0∞ := fun i => ∫⁻ x in Qi i, g x with ha
  have hQiQ : ∀ i, Qi i ⊆ Q := fun i => subset_closure.trans (hQic i)
  have hsum : ∑' i, a i ≠ ⊤ := by
    rw [ha, ← lintegral_iUnion (fun i => (hQio i).measurableSet) hQid]
    exact ne_top_of_le_ne_top hgfin.ne (lintegral_mono_set ((iUnion_subset hQiQ).trans hQΩ))
  have hlim : Tendsto (fun n => ∑' i, S (Qi i) + (∫⁻ x in Q \ ⋃ i, Qi i, g x) + ∑' k, a (k + n))
      atTop (𝓝 (∑' i, S (Qi i) + (∫⁻ x in Q \ ⋃ i, Qi i, g x) + 0)) :=
    tendsto_const_nhds.add (ENNReal.tendsto_sum_nat_add a hsum)
  rw [add_zero] at hlim
  refine ge_of_tendsto' hlim fun n => ?_
  set W := ⋃ i ∈ Finset.range n, Qi i with hW_def
  have hWo : IsOpen W := isOpen_biUnion fun i _ => hQio i
  have hWQ : W ⊆ Q := iUnion₂_subset fun i _ => hQiQ i
  set V := Q \ closure W with hV_def
  have hVo : IsOpen V := hQo.sdiff isClosed_closure
  have hVQ : V ⊆ Q := sdiff_subset
  have hSW : ∀ n, S (⋃ i ∈ Finset.range n, Qi i) ≤ ∑ i ∈ Finset.range n, S (Qi i) := by
    intro n
    induction n with
    | zero => simp [S_empty hdom]
    | succ n ih =>
      have hU : (⋃ i ∈ Finset.range (n + 1), Qi i) = (⋃ i ∈ Finset.range n, Qi i) ∪ Qi n := by
        rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
      rw [Finset.sum_range_succ]
      have hAo : IsOpen (⋃ i ∈ Finset.range (n + 1), Qi i) := isOpen_biUnion fun i _ => hQio i
      have hAΩ : (⋃ i ∈ Finset.range (n + 1), Qi i) ⊆ Ω :=
        (iUnion₂_subset fun i _ => hQiQ i).trans hQΩ
      have hdisj : Disjoint (⋃ i ∈ Finset.range n, Qi i) (Qi n) := by
        rw [Set.disjoint_iUnion₂_left]
        intro i hi
        exact hQid (Finset.mem_range.1 hi).ne
      calc S (⋃ i ∈ Finset.range (n + 1), Qi i)
          ≤ S (⋃ i ∈ Finset.range n, Qi i) + S (Qi n) :=
            hsub _ _ _ hAo (isOpen_biUnion fun i _ => hQio i) (hQio n) hAΩ hdisj
              hU.symm.subset (by rw [hU, sdiff_self, measure_empty])
        _ ≤ _ := add_le_add ih le_rfl
  have hfr : volume (Q \ (W ∪ V)) = 0 := by
    refine measure_mono_null (t := ⋃ i ∈ Finset.range n, frontier (Qi i)) ?_
      (le_antisymm ((measure_biUnion_finset_le _ _).trans (by simp [hQif])) zero_le)
    rintro x ⟨hxQ, hxWV⟩
    have hxcl : x ∈ closure W := by
      by_contra h
      exact hxWV (Or.inr ⟨hxQ, h⟩)
    have hxW : x ∉ W := fun h => hxWV (Or.inl h)
    rw [hW_def, Finset.closure_biUnion] at hxcl
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hxcl
    refine mem_iUnion₂.2 ⟨i, hi, ?_⟩
    rw [(hQio i).frontier_eq]
    exact ⟨hxi, fun h => hxW (mem_iUnion₂.2 ⟨i, hi, h⟩)⟩
  have hSQ : S Q ≤ S W + S V :=
    hsub Q W V hQo hWo hVo hQΩ
      (Set.disjoint_left.2 fun x hxW hxV => hxV.2 (subset_closure hxW)) (union_subset hWQ hVQ) hfr
  have hVsub : V ⊆ (Q \ ⋃ i, Qi i) ∪ ⋃ k, Qi (k + n) := by
    rintro x ⟨hxQ, hxW⟩
    by_cases h : x ∈ ⋃ i, Qi i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      refine Or.inr (mem_iUnion.2 ⟨i - n, ?_⟩)
      have hin : n ≤ i := by
        by_contra hlt
        exact hxW (subset_closure (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (not_le.1 hlt), hi⟩))
      rwa [Nat.sub_add_cancel hin]
    · exact Or.inl ⟨hxQ, h⟩
  have hSV : S V ≤ (∫⁻ x in Q \ ⋃ i, Qi i, g x) + ∑' k, a (k + n) :=
    calc S V ≤ ∫⁻ x in V, g x := hdom V hVo (hVQ.trans hQΩ)
      _ ≤ ∫⁻ x in (Q \ ⋃ i, Qi i) ∪ ⋃ k, Qi (k + n), g x := lintegral_mono_set hVsub
      _ ≤ (∫⁻ x in Q \ ⋃ i, Qi i, g x) + ∫⁻ x in ⋃ k, Qi (k + n), g x := lintegral_union_le _ _ _
      _ ≤ _ := add_le_add le_rfl (lintegral_iUnion_le _ _)
  calc S Q ≤ S W + S V := hSQ
    _ ≤ ∑ i ∈ Finset.range n, S (Qi i) + ((∫⁻ x in Q \ ⋃ i, Qi i, g x) + ∑' k, a (k + n)) :=
        add_le_add (hSW n) hSV
    _ ≤ ∑' i, S (Qi i) + ((∫⁻ x in Q \ ⋃ i, Qi i, g x) + ∑' k, a (k + n)) :=
        add_le_add (ENNReal.sum_le_tsum _) le_rfl
    _ = _ := by rw [add_assoc]

/-- **Good balls**: for a.e. `x ∈ Ω` and every `τ > 0`, the centred cubes
`Q_ρ(x) = ball x (ρ/2)` satisfy `∫_{Q_ρ(x)} lowDeriv ≤ S(Q_ρ(x)) + τ |Q_ρ(x)|` for small `ρ`
(depending on `x` and `τ`). This is a local estimate only. -/
theorem ae_good_ball (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ τ : ℝ, 0 < τ → ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      ∫⁻ y in ball x (ρ / 2), lowDeriv S Ω y ≤
        S (ball x (ρ / 2)) + ENNReal.ofReal τ * volume (ball x (ρ / 2)) := by
  have hΩm := hΩo.measurableSet
  set D := lowDeriv S Ω with hD_def
  have hDint : ∫⁻ x, Ω.indicator D x ≠ ⊤ := by
    rw [lintegral_indicator hΩm]
    exact (lintegral_lowDeriv_lt_top hΩo hg hgfin hdom).ne
  have hfin : ∀ᵐ x ∂(volume.restrict Ω), D x < ⊤ :=
    ae_lt_top measurable_lowDeriv (lintegral_lowDeriv_lt_top hΩo hg hgfin hdom).ne
  have hleb : ∀ᵐ x ∂(volume.restrict Ω),
      Tendsto (avgOn (Ω.indicator D)) ((vfam N).filterAt x) (𝓝 (Ω.indicator D x)) :=
    ae_restrict_of_ae ((vfam N).ae_tendsto_lintegral_div
      (measurable_lowDeriv.indicator hΩm).aemeasurable hDint)
  filter_upwards [ae_tendsto_ratio hΩo hΩb hg hgfin hdom hsub, hfin, hleb,
    ae_restrict_mem hΩm] with x hrat hxfin hx hxΩ τ hτ
  have hc := tendsto_avgOn_ball_center (f := Ω.indicator D) hx
  rw [Set.indicator_of_mem hxΩ] at hc
  have hτ2 : ENNReal.ofReal (τ / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      avgOn (Ω.indicator D) (ball x (ρ / 2)) < D x + ENNReal.ofReal (τ / 2) :=
    (tendsto_order.1 hc).2 _ (ENNReal.lt_add_right hxfin.ne hτ2)
  have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      D x ≤ S (cube ρ x) / volume (cube ρ x) + ENNReal.ofReal (τ / 2) := by
    by_cases hD0 : D x = 0
    · exact Eventually.of_forall fun ρ => by rw [hD0]; exact zero_le
    · have hlt : D x - ENNReal.ofReal (τ / 2) < D x := ENNReal.sub_lt_self hxfin.ne hD0 hτ2
      filter_upwards [(tendsto_order.1 hrat).1 _ hlt] with ρ hρ
      exact tsub_le_iff_right.1 hρ.le
  obtain ⟨ρΩ, hρΩ, hballΩ⟩ := Metric.isOpen_iff.1 hΩo x hxΩ
  filter_upwards [h1, h2, Ioo_mem_nhdsGT hρΩ] with ρ h1 h2 hρ
  have hρ0 : 0 < ρ / 2 := half_pos hρ.1
  have hbΩ : ball x (ρ / 2) ⊆ Ω := (ball_subset_ball (by linarith [hρ.2])).trans hballΩ
  rw [cube_eq_ball hρ.1] at h2
  rw [avgOn, setLIntegral_indicator_of_subset isOpen_ball.measurableSet hbΩ] at h1
  have hv0 := volume_ball_ne_zero x hρ0
  have hvt := volume_ball_ne_top x (ρ / 2)
  have h3 : (∫⁻ y in ball x (ρ / 2), D y) / volume (ball x (ρ / 2)) ≤
      S (ball x (ρ / 2)) / volume (ball x (ρ / 2)) + ENNReal.ofReal τ := by
    calc _ ≤ D x + ENNReal.ofReal (τ / 2) := h1.le
      _ ≤ (S (ball x (ρ / 2)) / volume (ball x (ρ / 2)) + ENNReal.ofReal (τ / 2)) +
          ENNReal.ofReal (τ / 2) := add_le_add h2 le_rfl
      _ = _ := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  rw [ENNReal.div_le_iff hv0 hvt, add_mul, ENNReal.div_mul_cancel hv0 hvt] at h3
  exact h3

/-- **Step 5 of Theorem `Vitali-envelope-cite`**, with an error `τ`:
`∫_O lowDeriv ≤ S^*(O) + τ |O|` for every `τ > 0`. The case `τ = 0` is
`lintegral_lowDeriv_le_vitaliEnv`. -/
theorem lintegral_lowDeriv_le_vitaliEnv_add (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V)
    {O : Set (Sp N)} (hOo : IsOpen O) (hOΩ : O ⊆ Ω) {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ x in O, lowDeriv S Ω x ≤ vitaliEnv S O + ENNReal.ofReal τ * volume O := by
  classical
  have hΩm := hΩo.measurableSet
  set D := lowDeriv S Ω with hD_def
  -- the good points of `O`
  set G : Set (Sp N) := {x | x ∈ O ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
    ∫⁻ y in ball x (ρ / 2), D y ≤
      S (ball x (ρ / 2)) + ENNReal.ofReal τ * volume (ball x (ρ / 2))} with hG_def
  have hOG : volume (O \ G) = 0 := by
    have h := ae_good_ball hΩo hΩb hg hgfin hdom hsub
    rw [ae_restrict_iff' hΩm] at h
    have h' : ∀ᵐ x, x ∈ O → x ∈ G := by
      filter_upwards [h] with x hx hxO
      exact ⟨hxO, hx (hOΩ hxO) τ hτ⟩
    exact measure_mono_null (fun x (hx : x ∈ O \ G) (h'' : x ∈ O → x ∈ G) => hx.2 (h'' hx.1))
      (ae_iff.1 h')
  -- the good balls
  set t : Set (Sp N × ℝ) := {a | 0 < a.2 ∧ closedBall a.1 a.2 ⊆ O ∧
    ∫⁻ y in ball a.1 a.2, D y ≤
      S (ball a.1 a.2) + ENNReal.ofReal τ * volume (ball a.1 a.2)} with ht_def
  have hfine : ∀ x ∈ G, ∀ ε > (0 : ℝ), ∃ a ∈ t, a.2 ≤ ε ∧ a.1 = x := by
    rintro x ⟨hxO, hxg⟩ ε hε
    obtain ⟨ρO, hρO, hballO⟩ := Metric.isOpen_iff.1 hOo x hxO
    obtain ⟨ρ, hρg, hρ⟩ :=
      (hxg.and (Ioo_mem_nhdsGT (show (0 : ℝ) < min ε ρO by positivity))).exists
    have hρ0 : 0 < ρ := hρ.1
    have e1 := min_le_left ε ρO
    have e2 := min_le_right ε ρO
    refine ⟨(x, ρ / 2), ⟨half_pos hρ0, ?_, hρg⟩, ?_, rfl⟩
    · exact (closedBall_subset_ball (by linarith [hρ.2])).trans hballO
    · change ρ / 2 ≤ ε
      linarith [hρ.2]
  obtain ⟨u, hut, huc, hud, hcov⟩ := Vitali.exists_disjoint_covering_ae volume G t
    ((3 : ℝ≥0) ^ N) (fun a => a.2) (fun a => a.1) (fun a => closedBall a.1 a.2)
    (fun a _ => subset_rfl)
    (fun a ha => by
      have hr : 0 < a.2 := ha.1
      rw [Real.volume_pi_closedBall _ (by positivity), Real.volume_pi_closedBall _ hr.le,
        Fintype.card_fin, show 2 * (3 * a.2) = 3 * (2 * a.2) by ring,
        mul_pow, ENNReal.ofReal_mul (by positivity)]
      refine le_of_eq ?_
      congr 1
      rw [ENNReal.ofReal_pow (by norm_num)]
      simp)
    (fun a ha => ⟨a.1, ball_subset_interior_closedBall (mem_ball_self ha.1)⟩)
    (fun a _ => isClosed_closedBall) hfine
  have : Countable u := huc.to_subtype
  set B : u → Set (Sp N) := fun l => ball (l : Sp N × ℝ).1 (l : Sp N × ℝ).2 with hB_def
  have hBo : ∀ l, IsOpen (B l) := fun l => isOpen_ball
  have hBO' : ∀ l, B l ⊆ O := fun l => ball_subset_closedBall.trans (hut l.2).2.1
  have hBd : Pairwise (Disjoint on B) := fun l l' hne =>
    (hud l.2 l'.2 (fun h => hne (Subtype.ext h))).mono ball_subset_closedBall
      ball_subset_closedBall
  have hBuniq : ∀ {l l' : u} {y : Sp N}, y ∈ B l → y ∈ B l' → l = l' := by
    intro l l' y h h'
    by_contra hne
    exact Set.disjoint_left.1 (hBd hne) h h'
  -- the balls cover `O` up to a null set
  have hOnull : volume (O \ ⋃ l, B l) = 0 := by
    refine measure_mono_null (t := (O \ G) ∪ (G \ ⋃ a ∈ u, closedBall a.1 a.2) ∪
      ⋃ a ∈ u, sphere a.1 a.2) ?_ (measure_union_null (measure_union_null hOG hcov)
        ((measure_biUnion_null_iff huc).2 fun a _ => Measure.addHaar_sphere volume _ _))
    rintro x ⟨hxO, hxc⟩
    by_cases hxG : x ∈ G
    · by_cases hxB : x ∈ ⋃ a ∈ u, closedBall a.1 a.2
      · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 hxB
        refine Or.inr (mem_iUnion₂.2 ⟨a, ha, ?_⟩)
        have hxnb : x ∉ ball a.1 a.2 := fun h => hxc (mem_iUnion.2 ⟨⟨a, ha⟩, h⟩)
        rw [← ball_union_sphere] at hxa
        exact hxa.resolve_left hxnb
      · exact Or.inl (Or.inr ⟨hxG, hxB⟩)
    · exact Or.inl (Or.inl ⟨hxO, hxG⟩)
  -- `∫_O lowDeriv ≤ ∑ S(B_l) + τ |O|`
  have hDO : ∫⁻ x in O, D x ≤ ∑' l, S (B l) + ENNReal.ofReal τ * volume O := by
    calc ∫⁻ x in O, D x ≤ ∫⁻ x in (⋃ l, B l) ∪ (O \ ⋃ l, B l), D x :=
          lintegral_mono_set fun x hx => by
            by_cases h : x ∈ ⋃ l, B l
            · exact Or.inl h
            · exact Or.inr ⟨hx, h⟩
      _ ≤ (∫⁻ x in ⋃ l, B l, D x) + ∫⁻ x in O \ ⋃ l, B l, D x := lintegral_union_le _ _ _
      _ = ∑' l, ∫⁻ x in B l, D x := by
          rw [setLIntegral_measure_zero _ _ hOnull, add_zero,
            lintegral_iUnion (fun l => (hBo l).measurableSet) hBd]
      _ ≤ ∑' l, (S (B l) + ENNReal.ofReal τ * volume (B l)) :=
          ENNReal.tsum_le_tsum fun l => (hut l.2).2.2
      _ = ∑' l, S (B l) + ENNReal.ofReal τ * volume (⋃ l, B l) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left,
            measure_iUnion hBd fun l => (hBo l).measurableSet]
      _ ≤ _ := by gcongr; exact iUnion_subset hBO'
  -- the layers of width `η` along the boundaries of the balls
  set E : ℝ → Set (Sp N) := fun η => ⋃ l, B l ∩ thickening η (B l)ᶜ with hE_def
  have hEo : ∀ η, IsOpen (E η) := fun η => isOpen_iUnion fun l => (hBo l).inter isOpen_thickening
  -- Step 5: for every family of `𝒱^η(O)`, `∑ S(B_l) ≤ ∑ S(Qᵢ) + ∫_{E η} g`
  have hstep : ∀ η, 0 < η → ∑' l, S (B l) ≤ vitaliDelta S η O + ∫⁻ x in E η, g x := by
    intro η hη
    unfold vitaliDelta
    rw [ENNReal.iInf_add]
    refine le_iInf fun c => ?_
    rw [ENNReal.iInf_add]
    refine le_iInf fun hcf => ?_
    obtain ⟨hc1, -, hc3, hc4⟩ := hcf
    set Q : ℕ → Set (Sp N) := fun i => cube (c i).1 (c i).2 with hQ_def
    set Q' : u → ℕ → Set (Sp N) := fun l i => if closure (Q i) ⊆ B l then Q i else ∅
      with hQ'_def
    have hQ'o : ∀ l i, IsOpen (Q' l i) := fun l i => by
      simp only [hQ'_def]
      split_ifs
      exacts [isOpen_cube _ _, isOpen_empty]
    have hQ'c : ∀ l i, closure (Q' l i) ⊆ B l := fun l i => by
      simp only [hQ'_def]
      split_ifs with h
      exacts [h, by simp]
    have hQ'd : ∀ l, Pairwise fun i j => Disjoint (Q' l i) (Q' l j) := fun l i j hij => by
      simp only [hQ'_def]
      split_ifs
      exacts [hc3 hij, Set.disjoint_empty _, Set.empty_disjoint _, Set.disjoint_empty _]
    have hQ'f : ∀ l i, volume (frontier (Q' l i)) = 0 := fun l i => by
      simp only [hQ'_def]
      split_ifs
      exacts [volume_frontier_cube _ _, by simp]
    have hS' : ∀ l i, S (Q' l i) = if closure (Q i) ⊆ B l then S (Q i) else 0 := fun l i => by
      simp only [hQ'_def]
      split_ifs
      exacts [rfl, S_empty hdom]
    have hrem : ∀ l, B l \ ⋃ i, Q' l i ⊆ (O \ ⋃ i, Q i) ∪ (B l ∩ thickening η (B l)ᶜ) := by
      rintro l y ⟨hyB, hyQ'⟩
      by_cases hy : y ∈ ⋃ i, Q i
      · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
        refine Or.inr ⟨hyB, ?_⟩
        have hnot : ¬ closure (Q i) ⊆ B l := fun h =>
          hyQ' (mem_iUnion.2 ⟨i, by simp only [hQ'_def, if_pos h]; exact hi⟩)
        obtain ⟨z, hzc, hzB⟩ := not_subset.1 hnot
        have hρ : 0 < (c i).1 := by
          by_contra h
          have hi' : y ∈ cube (c i).1 (c i).2 := hi
          rw [cube_eq_empty_of_nonpos (not_lt.1 h)] at hi'
          exact hi'
        rw [mem_thickening_iff]
        exact ⟨z, hzB, (dist_le_of_mem_closure_cube hρ (subset_closure hi) hzc).trans_lt
          (hc1 i).2⟩
      · exact Or.inl ⟨hBO' l hyB, hy⟩
    have hBl : ∀ l, S (B l) ≤ ∑' i, S (Q' l i) + ∫⁻ x in B l ∩ thickening η (B l)ᶜ, g x := by
      intro l
      refine (le_tsum_add_setLIntegral hgfin hdom hsub (hBo l) ((hBO' l).trans hOΩ) (hQ'o l)
        (hQ'c l) (hQ'd l) (hQ'f l)).trans (add_le_add le_rfl ?_)
      calc ∫⁻ x in B l \ ⋃ i, Q' l i, g x
          ≤ ∫⁻ x in (O \ ⋃ i, Q i) ∪ (B l ∩ thickening η (B l)ᶜ), g x :=
            lintegral_mono_set (hrem l)
        _ ≤ (∫⁻ x in O \ ⋃ i, Q i, g x) + ∫⁻ x in B l ∩ thickening η (B l)ᶜ, g x :=
            lintegral_union_le _ _ _
        _ = _ := by rw [setLIntegral_measure_zero _ _ hc4, zero_add]
    have hsumS : ∑' l, ∑' i, S (Q' l i) ≤ ∑' i, S (Q i) := by
      rw [ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum fun i => ?_
      simp only [hS']
      rcases (Q i).eq_empty_or_nonempty with h0 | ⟨y, hy⟩
      · simp [h0, S_empty hdom]
      by_cases h : ∃ l, closure (Q i) ⊆ B l
      · obtain ⟨l0, hl0⟩ := h
        rw [tsum_eq_single l0 fun l hl => if_neg fun hl' =>
          hl (hBuniq (hl' (subset_closure hy)) (hl0 (subset_closure hy))), if_pos hl0]
      · push Not at h
        simp [h]
    have hsumE : ∑' l, ∫⁻ x in B l ∩ thickening η (B l)ᶜ, g x = ∫⁻ x in E η, g x := by
      rw [hE_def, lintegral_iUnion (fun l => ((hBo l).inter isOpen_thickening).measurableSet)
        (fun l l' hne => (hBd hne).mono inter_subset_left inter_subset_left)]
    calc ∑' l, S (B l)
        ≤ ∑' l, (∑' i, S (Q' l i) + ∫⁻ x in B l ∩ thickening η (B l)ᶜ, g x) :=
          ENNReal.tsum_le_tsum hBl
      _ = ∑' l, ∑' i, S (Q' l i) + ∫⁻ x in E η, g x := by rw [ENNReal.tsum_add, hsumE]
      _ ≤ ∑' i, S (Q i) + ∫⁻ x in E η, g x := add_le_add hsumS le_rfl
  -- the layers vanish as `η → 0`
  have hlimE : Tendsto (fun k : ℕ => ∫⁻ x in E (1 / ((k : ℝ) + 1)), g x) atTop (𝓝 0) := by
    set ν := volume.withDensity g with hν
    have heq : ∀ k : ℕ, ∫⁻ x in E (1 / ((k : ℝ) + 1)), g x = ν (E (1 / ((k : ℝ) + 1))) :=
      fun k => (withDensity_apply _ (hEo _).measurableSet).symm
    simp_rw [heq]
    have hanti : Antitone fun k : ℕ => E (1 / ((k : ℝ) + 1)) := by
      intro k k' hkk'
      refine iUnion_mono fun l => inter_subset_inter_right _ (thickening_mono ?_ _)
      gcongr
    have hfin : ∃ k : ℕ, ν (E (1 / ((k : ℝ) + 1))) ≠ ⊤ := ⟨0, by
      rw [← heq 0]
      exact ne_top_of_le_ne_top hgfin.ne (lintegral_mono_set
        ((iUnion_subset fun l => inter_subset_left.trans (hBO' l)).trans hOΩ))⟩
    have hinter : (⋂ k : ℕ, E (1 / ((k : ℝ) + 1))) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      rw [mem_iInter] at hx
      obtain ⟨l, hxl, -⟩ := mem_iUnion.1 (hx 0)
      obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 (hBo l) x hxl
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨l', hxl', hxt⟩ := mem_iUnion.1 (hx k)
      obtain rfl := hBuniq hxl' hxl
      obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hxt
      exact hz (hεB (mem_ball'.2 (hdz.trans hk)))
    have h := tendsto_measure_iInter_atTop (μ := ν) (fun k => (hEo _).nullMeasurableSet)
      hanti hfin
    rwa [hinter, measure_empty] at h
  have hle : ∀ k : ℕ, ∫⁻ x in O, D x ≤
      vitaliEnv S O + (∫⁻ x in E (1 / ((k : ℝ) + 1)), g x) + ENNReal.ofReal τ * volume O := by
    intro k
    have hη : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    calc ∫⁻ x in O, D x ≤ ∑' l, S (B l) + ENNReal.ofReal τ * volume O := hDO
      _ ≤ (vitaliDelta S _ O + ∫⁻ x in E (1 / ((k : ℝ) + 1)), g x) +
          ENNReal.ofReal τ * volume O := add_le_add (hstep _ hη) le_rfl
      _ ≤ _ := by
          gcongr
          exact le_iSup₂ (f := fun δ (_ : 0 < δ) => vitaliDelta S δ O) _ hη
  have hlim : Tendsto (fun k : ℕ => vitaliEnv S O + (∫⁻ x in E (1 / ((k : ℝ) + 1)), g x) +
      ENNReal.ofReal τ * volume O) atTop
      (𝓝 (vitaliEnv S O + 0 + ENNReal.ofReal τ * volume O)) :=
    (tendsto_const_nhds.add hlimE).add tendsto_const_nhds
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hle

/-- **Step 5 of Theorem `Vitali-envelope-cite`**: `∫_O lowDeriv ≤ S^*(O)` for every open `O ⊆ Ω`.
The reverse inequality is `vitaliEnv_le_lintegral`. -/
theorem lintegral_lowDeriv_le_vitaliEnv (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V)
    {O : Set (Sp N)} (hOo : IsOpen O) (hOΩ : O ⊆ Ω) :
    ∫⁻ x in O, lowDeriv S Ω x ≤ vitaliEnv S O := by
  have hOfin : volume O ≠ ⊤ := (hΩb.subset hOΩ).measure_lt_top.ne
  have h : Tendsto (fun τ : ℝ => vitaliEnv S O + ENNReal.ofReal τ * volume O)
      (𝓝[>] 0) (𝓝 (vitaliEnv S O + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h0 : Tendsto (fun τ : ℝ => ENNReal.ofReal τ) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hOfin)
  rw [add_zero] at h
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with τ (hτ : 0 < τ)
  exact lintegral_lowDeriv_le_vitaliEnv_add hΩo hΩb hg hgfin hdom hsub hOo hOΩ hτ

/-- **Theorem `Vitali-envelope-cite`**, the equality: `S^*(O) = ∫_O lowDeriv` for every
open `O ⊆ Ω`. -/
theorem vitaliEnv_eq_lintegral (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V)
    {O : Set (Sp N)} (hOo : IsOpen O) (hOΩ : O ⊆ Ω) :
    vitaliEnv S O = ∫⁻ x in O, lowDeriv S Ω x :=
  le_antisymm (vitaliEnv_le_lintegral hΩo hΩb hg hgfin hdom hOo hOΩ)
    (lintegral_lowDeriv_le_vitaliEnv hΩo hΩb hg hgfin hdom hsub hOo hOΩ)

/-- **Theorem `Vitali-envelope-cite`** ([oah-cloz-jpm17, Theorem A.16]), all conclusions, for
`dS = lowDeriv S Ω`: `dS` is measurable, finite a.e. on `Ω`, with `∫_Ω dS < ∞`; it is the limit of
`S(Q_ρ(x))/|Q_ρ(x)|` as `ρ → 0` for a.e. `x ∈ Ω`; and `S^*(A) = ∫_A dS` for every open `A ⊆ Ω`. -/
theorem vitaliEnvelope_full (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V) :
    Measurable (lowDeriv S Ω) ∧ (∀ᵐ x ∂(volume.restrict Ω), lowDeriv S Ω x < ⊤) ∧
      (∫⁻ x in Ω, lowDeriv S Ω x < ⊤) ∧
      (∀ᵐ x ∂(volume.restrict Ω),
        Tendsto (fun ρ => S (cube ρ x) / volume (cube ρ x)) (𝓝[>] 0) (𝓝 (lowDeriv S Ω x))) ∧
      ∀ A, IsOpen A → A ⊆ Ω → vitaliEnv S A = ∫⁻ x in A, lowDeriv S Ω x :=
  ⟨measurable_lowDeriv,
    ae_lt_top measurable_lowDeriv (lintegral_lowDeriv_lt_top hΩo hg hgfin hdom).ne,
    lintegral_lowDeriv_lt_top hΩo hg hgfin hdom, ae_tendsto_ratio hΩo hΩb hg hgfin hdom hsub,
    fun _ hA hAΩ => vitaliEnv_eq_lintegral hΩo hΩb hg hgfin hdom hsub hA hAΩ⟩

/-- **Theorem `Vitali-envelope-cite`** ([oah-cloz-jpm17, Theorem A.16]), with the equality:
the cited hypothesis `CitedVitaliEnvelope` holds, with `dS = lowDeriv S Ω`. The proposition
`CitedVitaliEnvelope` does not state the measurability, the finiteness a.e. and the integrability
of `dS`; for this witness they are part of `vitaliEnvelope_full`. -/
theorem citedVitaliEnvelope_holds : CitedVitaliEnvelope N := by
  intro Ω hΩo hΩb S g hg hgfin hdom hsub
  exact ⟨lowDeriv S Ω, (vitaliEnvelope_full hΩo hΩb hg hgfin hdom hsub).2.2.2⟩

end Homogenization
