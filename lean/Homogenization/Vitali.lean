import Homogenization.RankOne

/-!
# The upper bound for the Vitali envelope (`Vitali-envelope-cite`, inequality form)

Let `Ω` be bounded open, `S` a nonnegative set function on open subsets of `Ω` with `S(A) ≤ ∫_A g`
for some `g ∈ L¹(Ω)` and subadditive on a.e. partitions into two open sets. Then the lower
derivative `lowDeriv S Ω` of `S` (taken over all cubes containing `x`, not necessarily centred)
is measurable, it is the limit of `S(Q_ρ(x)) / |Q_ρ(x)|` along centred cubes for a.e. `x ∈ Ω`, and
`S^*(A) ≤ ∫_A lowDeriv S Ω` for every open `A ⊆ Ω` (`vitaliEnvelopeUpper`).

The proof establishes the inequality half of [oah-cloz-jpm17, Theorem A.16] (Theorem
`Vitali-envelope-cite` of the paper) in the case of the Lebesgue measure and of axis-parallel
cubes. Since Lebesgue measure is doubling, all cubes containing `x` form a Vitali family
(`IsUnifLocDoublingMeasure.vitaliFamily`), so no centrality condition of Morse type is needed.
In `Sp N` the cubes are the balls of the sup norm: `cube (2r) w = ball w r`.

* `lowDerivR S Ω r` is the infimum of `S(Q)/|Q|` over the cubes `Q ∋ x` of radius `≤ r` with
  `Q̄ ⊆ Ω`; its sublevel sets are open, so it is Borel, and `lowDeriv = sup_r lowDerivR`.
* `lowDeriv ≤ g` a.e. on `Ω` (`lowDeriv_le`), so `lowDeriv ∈ L¹(Ω)`.
* **Key estimate** (`vitaliDelta_le_lintegral_lowDeriv`): choosing at a.e. `x`
  small cubes `Q ∋ x` with `S(Q) ≤ ∫_Q lowDeriv + η|Q|` and applying the Vitali covering theorem
  gives `S^δ(O) ≤ ∫_O lowDeriv`.
* **Step 1** (`le_vitaliDelta_add`): `S(Q) ≤ S^δ(Q) + ε`, by subadditivity and the absolute
  continuity of `∫ g`; hence `S(Q) ≤ ∫_Q lowDeriv` for every cube `Q ⊆ Ω`.
* **Steps 2–3**: along centred cubes,
  `lowDerivR(ρ/2)(x) ≤ S(Q_ρ(x))/|Q_ρ(x)| ≤ ⨍_{Q_ρ(x)} lowDeriv`,
  and both bounds tend to `lowDeriv x` for a.e. `x`.

The cited Theorem A.16 of [oah-cloz-jpm17] also asserts the reverse inequality, proved in
`Homogenization.VitaliEquality` (`citedVitaliEnvelope_holds`). Step 4 of the main proof only uses
the inequality (`VitaliEnvelopeUpper`), so the main theorem does not depend on
`CitedVitaliEnvelope` (`main_Ggrowth_final_two`).
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ}

/-! ### Cubes as sup-norm balls -/

theorem cube_eq_ball {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) : cube ρ x = ball x (ρ / 2) := by
  rw [ball_eq_cube (by positivity), mul_div_cancel₀ _ two_ne_zero]

theorem ball_ae_eq_closedBall [NeZero N] (w : Sp N) (r : ℝ) :
    (ball w r : Set (Sp N)) =ᵐ[volume] closedBall w r := by
  refine ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 ball_subset_closedBall, measure_empty], ?_⟩
  refine measure_mono_null (fun y hy => ?_) (Measure.addHaar_sphere volume w r)
  rw [← ball_union_sphere] at hy
  rcases hy.1 with h | h
  · exact absurd h hy.2
  · exact h

theorem cube_zero_eq_empty [NeZero N] (x : Sp N) : cube 0 x = ∅ := by
  rw [cube]
  refine Set.univ_pi_eq_empty (i := 0) ?_
  simp

/-- The average of `f` over a set. -/
noncomputable def avgOn (f : Sp N → ℝ≥0∞) (a : Set (Sp N)) : ℝ≥0∞ :=
  (∫⁻ y in a, f y) / volume a

theorem avgOn_closedBall [NeZero N] (f : Sp N → ℝ≥0∞) (w : Sp N) (r : ℝ) :
    avgOn f (closedBall w r) = avgOn f (ball w r) := by
  rw [avgOn, avgOn, setLIntegral_congr (ball_ae_eq_closedBall w r).symm,
    measure_congr (ball_ae_eq_closedBall w r).symm]

/-- The doubling Vitali family of all closed balls containing the point (`K = 1`). -/
noncomputable abbrev vfam (N : ℕ) : VitaliFamily (volume : Measure (Sp N)) :=
  IsUnifLocDoublingMeasure.vitaliFamily volume 1

theorem tendsto_half_nhdsGT : Tendsto (fun ρ : ℝ => ρ / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((continuous_id.div_const (2 : ℝ)).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    exact half_pos hρ

/-- Lebesgue differentiation along centred cubes. -/
theorem tendsto_avgOn_ball_center [NeZero N] {f : Sp N → ℝ≥0∞} {x : Sp N}
    (hx : Tendsto (avgOn f) ((vfam N).filterAt x) (𝓝 (f x))) :
    Tendsto (fun ρ => avgOn f (ball x (ρ / 2))) (𝓝[>] 0) (𝓝 (f x)) := by
  have hmem : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), x ∈ closedBall ((fun _ : ℝ => x) ρ) (1 * (ρ / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    exact mem_closedBall_self (by positivity)
  have h := hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
    (fun _ : ℝ => x) (fun ρ => ρ / 2) tendsto_half_nhdsGT hmem)
  refine h.congr' (Eventually.of_forall fun ρ => ?_)
  exact avgOn_closedBall f x _


/-! ### The lower derivative -/

section LowDeriv

variable (S : Set (Sp N) → ℝ≥0∞) (Ω : Set (Sp N))

/-- Balls `ball w r ∋ x` of radius `0 < r ≤ r₀` with `closedBall w r ⊆ Ω`. -/
def admBall (r₀ : ℝ) (x : Sp N) : Set (Sp N × ℝ) :=
  {p | 0 < p.2 ∧ p.2 ≤ r₀ ∧ x ∈ ball p.1 p.2 ∧ closedBall p.1 p.2 ⊆ Ω}

/-- `S(Q)/|Q|` for the cube `Q = ball w r`. -/
noncomputable def ballRatio (p : Sp N × ℝ) : ℝ≥0∞ :=
  S (ball p.1 p.2) / volume (ball p.1 p.2)

/-- `inf {S(Q)/|Q| : Q ∋ x, radius ≤ r₀, Q̄ ⊆ Ω}`. -/
noncomputable def lowDerivR (r₀ : ℝ) (x : Sp N) : ℝ≥0∞ :=
  ⨅ p ∈ admBall Ω r₀ x, ballRatio S p

/-- The lower derivative of `S` along all cubes containing `x`. -/
noncomputable def lowDeriv (x : Sp N) : ℝ≥0∞ :=
  ⨆ k : ℕ, lowDerivR S Ω (1 / ((k : ℝ) + 1)) x

variable {S Ω}

/-- Remark `mesurabilite`: the sublevel sets of `lowDerivR` are open. -/
theorem measurable_lowDerivR (r₀ : ℝ) : Measurable (lowDerivR S Ω r₀) := by
  refine measurable_of_Iio fun a => ?_
  have : lowDerivR S Ω r₀ ⁻¹' Iio a = ⋃ p ∈ {p : Sp N × ℝ | 0 < p.2 ∧ p.2 ≤ r₀ ∧
      closedBall p.1 p.2 ⊆ Ω ∧ ballRatio S p < a}, ball p.1 p.2 := by
    ext x
    simp only [mem_preimage, mem_Iio, lowDerivR, iInf_lt_iff, exists_prop, mem_iUnion, admBall,
      mem_ofPred_eq]
    constructor
    · rintro ⟨p, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨p, ⟨h1, h2, h4, h5⟩, h3⟩
    · rintro ⟨p, ⟨h1, h2, h4, h5⟩, h3⟩
      exact ⟨p, ⟨h1, h2, h3, h4⟩, h5⟩
  rw [this]
  exact (isOpen_biUnion fun p _ => isOpen_ball).measurableSet

theorem measurable_lowDeriv : Measurable (lowDeriv S Ω) :=
  Measurable.iSup fun _ => measurable_lowDerivR _

theorem lowDerivR_anti {r₀ r₁ : ℝ} (h : r₀ ≤ r₁) (x : Sp N) :
    lowDerivR S Ω r₁ x ≤ lowDerivR S Ω r₀ x :=
  biInf_mono fun _ hp => ⟨hp.1, hp.2.1.trans h, hp.2.2⟩

theorem lowDerivR_le_lowDeriv {r₀ : ℝ} (hr : 0 < r₀) (x : Sp N) :
    lowDerivR S Ω r₀ x ≤ lowDeriv S Ω x := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
  exact (lowDerivR_anti hk.le x).trans
    (le_iSup (fun k : ℕ => lowDerivR S Ω (1 / ((k : ℝ) + 1)) x) k)

theorem tendsto_lowDerivR (x : Sp N) :
    Tendsto (fun r => lowDerivR S Ω r x) (𝓝[>] 0) (𝓝 (lowDeriv S Ω x)) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk⟩ := lt_iSup_iff.1 hb
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with r hr
    exact hk.trans_le (lowDerivR_anti hr.2.le x)
  · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact (lowDerivR_le_lowDeriv hr x).trans_lt hb

theorem lowDerivR_le_ballRatio {r₀ : ℝ} {x w : Sp N} {r : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀)
    (hx : x ∈ ball w r) (hΩ : closedBall w r ⊆ Ω) :
    lowDerivR S Ω r₀ x ≤ ballRatio S (w, r) :=
  iInf₂_le (w, r) ⟨hr, hr₀, hx, hΩ⟩

end LowDeriv

/-! ### The hypotheses -/

section Hyp

variable [NeZero N] {Ω : Set (Sp N)} {S : Set (Sp N) → ℝ≥0∞} {g : Sp N → ℝ≥0∞}

omit [NeZero N] in
theorem volume_ball_ne_zero (w : Sp N) {r : ℝ} (hr : 0 < r) : volume (ball w r) ≠ 0 :=
  (measure_ball_pos volume w hr).ne'

omit [NeZero N] in
theorem volume_ball_ne_top (w : Sp N) (r : ℝ) : volume (ball w r) ≠ ⊤ :=
  measure_ball_lt_top.ne

omit [NeZero N] in
theorem S_empty (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) : S ∅ = 0 :=
  le_antisymm ((hdom ∅ isOpen_empty (empty_subset _)).trans (by simp)) zero_le

omit [NeZero N] in
theorem setLIntegral_indicator_of_subset {A : Set (Sp N)} (hA : MeasurableSet A) (hAΩ : A ⊆ Ω)
    (f : Sp N → ℝ≥0∞) : ∫⁻ x in A, Ω.indicator f x = ∫⁻ x in A, f x :=
  setLIntegral_congr_fun hA fun _ hx => Set.indicator_of_mem (hAΩ hx) f

/-- `lowDeriv ≤ g` almost everywhere on `Ω`. -/
theorem ae_lowDeriv_le (hΩo : IsOpen Ω) (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) :
    ∀ᵐ x, x ∈ Ω → lowDeriv S Ω x ≤ g x := by
  have hint : ∫⁻ x, Ω.indicator g x ≠ ⊤ := by
    rw [lintegral_indicator hΩo.measurableSet]; exact hgfin.ne
  filter_upwards [(vfam N).ae_tendsto_lintegral_div
    (hg.indicator hΩo.measurableSet).aemeasurable hint] with x hx hxΩ
  have hc := tendsto_avgOn_ball_center (f := Ω.indicator g) hx
  rw [Set.indicator_of_mem hxΩ] at hc
  obtain ⟨ρΩ, hρΩ, hballΩ⟩ := Metric.isOpen_iff.1 hΩo x hxΩ
  refine iSup_le fun k => ge_of_tendsto hc ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (2 / ((k : ℝ) + 1)) ρΩ by positivity)]
    with ρ hρ
  have hρ0 : 0 < ρ / 2 := half_pos hρ.1
  have h1 := min_le_left (2 / ((k : ℝ) + 1)) ρΩ
  have h2 := min_le_right (2 / ((k : ℝ) + 1)) ρΩ
  have hsub : closedBall x (ρ / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith [hρ.2])).trans hballΩ
  have hle : ρ / 2 ≤ 1 / ((k : ℝ) + 1) := by
    have : ρ < 2 / ((k : ℝ) + 1) := hρ.2.trans_le h1
    rw [div_le_iff₀ two_pos]
    calc ρ ≤ 2 / ((k : ℝ) + 1) := this.le
      _ = 1 / ((k : ℝ) + 1) * 2 := by ring
  have hbΩ : ball x (ρ / 2) ⊆ Ω := ball_subset_closedBall.trans hsub
  calc lowDerivR S Ω (1 / ((k : ℝ) + 1)) x ≤ ballRatio S (x, ρ / 2) :=
        lowDerivR_le_ballRatio hρ0 hle (mem_ball_self hρ0) hsub
    _ ≤ avgOn (Ω.indicator g) (ball x (ρ / 2)) := by
        rw [ballRatio, avgOn, setLIntegral_indicator_of_subset isOpen_ball.measurableSet hbΩ]
        exact ENNReal.div_le_div_right (hdom _ isOpen_ball hbΩ) _

theorem lintegral_lowDeriv_lt_top (hΩo : IsOpen Ω) (hg : Measurable g)
    (hgfin : ∫⁻ x in Ω, g x < ⊤) (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) :
    ∫⁻ x in Ω, lowDeriv S Ω x < ⊤ :=
  (lintegral_mono_ae ((ae_restrict_iff' hΩo.measurableSet).2
    (ae_lowDeriv_le hΩo hg hgfin hdom))).trans_lt hgfin

omit [NeZero N] in
/-- **Step 1 of Theorem `Vitali-envelope-cite`**: `S(Q) ≤ S^δ(Q) + ε`. -/
theorem le_vitaliDelta_add (hΩo : IsOpen Ω) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V)
    {Q : Set (Sp N)} (hQo : IsOpen Q) (hQΩ : Q ⊆ Ω) (hQfin : volume Q ≠ ⊤) (δ : ℝ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : S Q ≤ vitaliDelta S δ Q + ε := by
  have hint : ∫⁻ x, Ω.indicator g x ≠ ⊤ := by
    rw [lintegral_indicator hΩo.measurableSet]; exact hgfin.ne
  obtain ⟨η0, hη0, habs⟩ := exists_pos_setLIntegral_lt_of_measure_lt hint hε
  unfold vitaliDelta
  rw [ENNReal.iInf_add]
  refine le_iInf fun c => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hc => ?_
  obtain ⟨-, hc2, hc3, hc4⟩ := hc
  set Qi : ℕ → Set (Sp N) := fun i => cube (c i).1 (c i).2 with hQi
  have hQio : ∀ i, IsOpen (Qi i) := fun i => isOpen_cube _ _
  have hQiQ : ∀ i, Qi i ⊆ Q := fun i => subset_closure.trans (hc2 i)
  have hsumv : ∑' i, volume (Qi i) ≠ ⊤ := by
    rw [← measure_iUnion hc3 (fun i => (hQio i).measurableSet)]
    exact ne_top_of_le_ne_top hQfin (measure_mono (iUnion_subset hQiQ))
  obtain ⟨n0, hn0⟩ : ∃ n0, ∑' k, volume (Qi (k + n0)) < η0 :=
    ((tendsto_order.1 (ENNReal.tendsto_sum_nat_add _ hsumv)).2 η0 hη0).exists
  set W := ⋃ i ∈ Finset.range n0, Qi i with hW_def
  have hWo : IsOpen W := isOpen_biUnion fun i _ => hQio i
  have hWQ : W ⊆ Q := iUnion₂_subset fun i _ => hQiQ i
  set V := Q \ closure W with hV_def
  have hVo : IsOpen V := hQo.sdiff isClosed_closure
  have hVQ : V ⊆ Q := sdiff_subset
  have hVvol : volume V < η0 := by
    refine lt_of_le_of_lt (measure_mono (t := (Q \ ⋃ i, Qi i) ∪ ⋃ k, Qi (k + n0)) ?_) ?_
    · rintro x ⟨hxQ, hxW⟩
      by_cases h : x ∈ ⋃ i, Qi i
      · obtain ⟨i, hi⟩ := mem_iUnion.1 h
        refine Or.inr (mem_iUnion.2 ⟨i - n0, ?_⟩)
        have hin : n0 ≤ i := by
          by_contra hlt
          push Not at hlt
          exact hxW (subset_closure (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hlt, hi⟩))
        rwa [Nat.sub_add_cancel hin]
      · exact Or.inl ⟨hxQ, h⟩
    · calc volume ((Q \ ⋃ i, Qi i) ∪ ⋃ k, Qi (k + n0))
          ≤ volume (Q \ ⋃ i, Qi i) + volume (⋃ k, Qi (k + n0)) := measure_union_le _ _
        _ ≤ 0 + ∑' k, volume (Qi (k + n0)) := add_le_add (le_of_eq hc4) (measure_iUnion_le _)
        _ < η0 := by rw [zero_add]; exact hn0
  have hSV : S V ≤ ε := by
    refine (hdom V hVo (hVQ.trans hQΩ)).trans ?_
    rw [← setLIntegral_indicator_of_subset hVo.measurableSet (hVQ.trans hQΩ)]
    exact (habs V hVvol).le
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
        exact hc3 (Finset.mem_range.1 hi).ne
      calc S (⋃ i ∈ Finset.range (n + 1), Qi i)
          ≤ S (⋃ i ∈ Finset.range n, Qi i) + S (Qi n) :=
            hsub _ _ _ hAo (isOpen_biUnion fun i _ => hQio i) (hQio n) hAΩ hdisj
              hU.symm.subset (by rw [hU, sdiff_self, measure_empty])
        _ ≤ _ := add_le_add ih le_rfl
  have hfr : volume (Q \ (W ∪ V)) = 0 := by
    refine measure_mono_null (t := ⋃ i ∈ Finset.range n0, frontier (Qi i)) ?_
      (le_antisymm ((measure_biUnion_finset_le _ _).trans
        (by simp [hQi, volume_frontier_cube])) zero_le)
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
  calc S Q ≤ S W + S V := hSQ
    _ ≤ ∑ i ∈ Finset.range n0, S (Qi i) + ε := add_le_add (hSW n0) hSV
    _ ≤ ∑' i, S (Qi i) + ε := add_le_add (ENNReal.sum_le_tsum _) le_rfl

/-- **Key estimate**, with an error `η`: covering `O` by small cubes
`Q ∋ x` on which `S(Q) ≤ ∫_Q lowDeriv + η|Q|`. -/
theorem vitaliDelta_le_add (hΩo : IsOpen Ω) (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) {O : Set (Sp N)} (hOo : IsOpen O)
    (hOΩ : O ⊆ Ω) {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    vitaliDelta S δ O ≤ (∫⁻ x in O, lowDeriv S Ω x) + ENNReal.ofReal η * volume O := by
  classical
  have hΩm := hΩo.measurableSet
  set D := lowDeriv S Ω with hD_def
  set D' := Ω.indicator D with hD'_def
  have hDle := ae_lowDeriv_le hΩo hg hgfin hdom
  have hDint : ∫⁻ x, D' x ≠ ⊤ := by
    rw [hD'_def, lintegral_indicator hΩm]
    exact (lintegral_lowDeriv_lt_top hΩo hg hgfin hdom).ne
  have hgae : ∀ᵐ x, x ∈ Ω → g x < ⊤ :=
    (ae_restrict_iff' hΩm).1 (ae_lt_top hg hgfin.ne)
  have hleb := (vfam N).ae_tendsto_lintegral_div
    (measurable_lowDeriv.indicator hΩm).aemeasurable hDint
  set G : Set (Sp N) := {x | x ∈ O ∧ D x < ⊤ ∧
    Tendsto (avgOn D') ((vfam N).filterAt x) (𝓝 (D' x))} with hG_def
  have hOG : volume (O \ G) = 0 := by
    have h : ∀ᵐ x, x ∈ O → x ∈ G := by
      filter_upwards [hDle, hgae, hleb] with x h1 h2 h3 hxO
      exact ⟨hxO, (h1 (hOΩ hxO)).trans_lt (h2 (hOΩ hxO)), h3⟩
    exact measure_mono_null (fun x (hx : x ∈ O \ G) (h' : x ∈ O → x ∈ G) => hx.2 (h' hx.1))
      (ae_iff.1 h)
  set t : Set (Sp N × Sp N × ℝ) := {a | a.1 ∈ ball a.2.1 a.2.2 ∧ 0 < a.2.2 ∧ 2 * a.2.2 < δ ∧
    closedBall a.2.1 a.2.2 ⊆ O ∧
    S (ball a.2.1 a.2.2) ≤ (∫⁻ y in ball a.2.1 a.2.2, D y) +
      ENNReal.ofReal η * volume (ball a.2.1 a.2.2)} with ht_def
  have hfine : ∀ x ∈ G, ∀ ε > (0 : ℝ), ∃ a ∈ t, 2 * a.2.2 ≤ ε ∧ a.1 = x := by
    rintro x ⟨hxO, hxfin, hxleb⟩ ε hε
    have hxΩ := hOΩ hxO
    have hD'x : D' x = D x := Set.indicator_of_mem hxΩ D
    rw [hD'x] at hxleb
    have hη2 : ENNReal.ofReal (η / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hev : ∀ᶠ a in (vfam N).filterAt x, D x ≤ avgOn D' a + ENNReal.ofReal (η / 2) := by
      by_cases hD0 : D x = 0
      · exact Eventually.of_forall fun a => by rw [hD0]; exact zero_le
      · have hlt : D x - ENNReal.ofReal (η / 2) < D x := ENNReal.sub_lt_self hxfin.ne hD0 hη2
        filter_upwards [(tendsto_order.1 hxleb).1 _ hlt] with a ha
        exact tsub_le_iff_right.1 ha.le
    obtain ⟨ε1, hε1, hε1'⟩ := (vfam N).eventually_filterAt_iff.1 hev
    obtain ⟨ρO, hρO, hballO⟩ := Metric.isOpen_iff.1 hOo x hxO
    set r' := min (min (ε / 2) (δ / 4)) (min (ε1 / 2) (ρO / 4)) with hr'
    have hr'0 : 0 < r' := by positivity
    have hlow : lowDerivR S Ω r' x < D x + ENNReal.ofReal (η / 2) :=
      (lowDerivR_le_lowDeriv hr'0 x).trans_lt (ENNReal.lt_add_right hxfin.ne hη2)
    simp only [lowDerivR, iInf_lt_iff, exists_prop] at hlow
    obtain ⟨⟨w, r⟩, ⟨hr0, hrr', hxw, hwΩ⟩, hratio⟩ := hlow
    have e1 := min_le_left (min (ε / 2) (δ / 4)) (min (ε1 / 2) (ρO / 4))
    have e2 := min_le_right (min (ε / 2) (δ / 4)) (min (ε1 / 2) (ρO / 4))
    have e3 := min_le_left (ε / 2) (δ / 4)
    have e4 := min_le_right (ε / 2) (δ / 4)
    have e5 := min_le_left (ε1 / 2) (ρO / 4)
    have e6 := min_le_right (ε1 / 2) (ρO / 4)
    have hxw' : dist x w < r := mem_ball.1 hxw
    have hcbO : closedBall w r ⊆ O := fun y hy => hballO (by
      rw [mem_ball]
      have := mem_closedBall.1 hy
      linarith [dist_triangle y w x, dist_comm x w])
    have hmemv : closedBall w r ∈ (vfam N).setsAt x :=
      IsUnifLocDoublingMeasure.closedBall_mem_vitaliFamily_of_dist_le_mul volume
        (by rw [one_mul]; exact hxw'.le) hr0
    have hsubx : closedBall w r ⊆ closedBall x ε1 := fun y hy => by
      rw [mem_closedBall] at hy ⊢
      linarith [dist_triangle y w x, dist_comm x w]
    have hav := hε1' _ hmemv hsubx
    have hbΩ : ball w r ⊆ Ω := ball_subset_closedBall.trans (hcbO.trans hOΩ)
    have hav' : avgOn D' (closedBall w r) = (∫⁻ y in ball w r, D y) / volume (ball w r) := by
      rw [avgOn_closedBall, avgOn, hD'_def,
        setLIntegral_indicator_of_subset isOpen_ball.measurableSet hbΩ]
    rw [hav'] at hav
    refine ⟨(x, w, r), ⟨hxw, hr0, by linarith, hcbO, ?_⟩, by linarith, rfl⟩
    have hv0 := volume_ball_ne_zero w hr0
    have hvt := volume_ball_ne_top w r
    have h1 : ballRatio S (w, r) <
        (∫⁻ y in ball w r, D y) / volume (ball w r) + ENNReal.ofReal η := by
      calc ballRatio S (w, r) < D x + ENNReal.ofReal (η / 2) := hratio
        _ ≤ ((∫⁻ y in ball w r, D y) / volume (ball w r) + ENNReal.ofReal (η / 2)) +
            ENNReal.ofReal (η / 2) := add_le_add_left hav _
        _ = (∫⁻ y in ball w r, D y) / volume (ball w r) + ENNReal.ofReal η := by
            rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
    rw [ballRatio, ENNReal.div_lt_iff (Or.inl hv0) (Or.inl hvt), add_mul,
      ENNReal.div_mul_cancel hv0 hvt] at h1
    exact h1.le
  obtain ⟨u, hut, huc, hud, hcov⟩ := Vitali.exists_disjoint_covering_ae volume G t
    ((6 : ℝ≥0) ^ N) (fun a => 2 * a.2.2) (fun a => a.1) (fun a => closedBall a.2.1 a.2.2)
    (fun a ha y hy => by
      rw [mem_closedBall] at hy ⊢
      have := mem_ball.1 ha.1
      linarith [dist_triangle y a.2.1 a.1, dist_comm a.1 a.2.1])
    (fun a ha => by
      have hr := ha.2.1
      rw [Real.volume_pi_closedBall _ (by positivity), Real.volume_pi_closedBall _ hr.le,
        Fintype.card_fin, show 2 * (3 * (2 * a.2.2)) = 6 * (2 * a.2.2) by ring,
        mul_pow, ENNReal.ofReal_mul (by positivity)]
      refine le_of_eq ?_
      congr 1
      rw [ENNReal.ofReal_pow (by norm_num)]
      simp)
    (fun a ha => ⟨a.2.1, ball_subset_interior_closedBall (mem_ball_self ha.2.1)⟩)
    (fun a _ => isClosed_closedBall) hfine
  -- an injective enumeration of `u`
  obtain ⟨f, hfinj⟩ := Set.countable_iff_exists_injective.1 huc
  let e : ℕ → Option u := fun n =>
    if h : ∃ a : u, f a = n then some (Classical.choose h) else none
  have he1 : ∀ a : u, e (f a) = some a := by
    intro a
    have h : ∃ b : u, f b = f a := ⟨a, rfl⟩
    simp only [e, dif_pos h, Option.some.injEq]
    exact hfinj (Classical.choose_spec h)
  have he2 : ∀ n (a : u), e n = some a → f a = n := by
    intro n a h
    simp only [e] at h
    split_ifs at h with h'
    · rw [Option.some.injEq] at h
      rw [← h]
      exact Classical.choose_spec h'
  let c : ℕ → ℝ × Sp N := fun n =>
    (e n).elim (0, 0) fun a => (2 * (a : Sp N × Sp N × ℝ).2.2, (a : Sp N × Sp N × ℝ).2.1)
  have hcnone : ∀ n, e n = none → cube (c n).1 (c n).2 = ∅ := by
    intro n h
    simp only [c, h, Option.elim_none]
    exact cube_zero_eq_empty _
  have hcsome : ∀ n (a : u), e n = some a →
      cube (c n).1 (c n).2 = ball (a : Sp N × Sp N × ℝ).2.1 (a : Sp N × Sp N × ℝ).2.2 := by
    intro n a h
    simp only [c, h, Option.elim_some]
    exact (ball_eq_cube (hut a.2).2.1 _).symm
  have hcO : ∀ n, cube (c n).1 (c n).2 ⊆ O := by
    intro n
    rcases hen : e n with _ | a
    · rw [hcnone n hen]; exact empty_subset _
    · rw [hcsome n a hen]; exact ball_subset_closedBall.trans (hut a.2).2.2.2.1
  have hcdisj : Pairwise fun i j => Disjoint (cube (c i).1 (c i).2) (cube (c j).1 (c j).2) := by
    intro i j hij
    rcases hei : e i with _ | a
    · rw [hcnone i hei]; exact Set.empty_disjoint _
    rcases hej : e j with _ | b
    · rw [hcnone j hej]; exact Set.disjoint_empty _
    rw [hcsome i a hei, hcsome j b hej]
    have hab : a ≠ b := by
      rintro rfl
      exact hij ((he2 i a hei).symm.trans (he2 j a hej))
    exact (hud a.2 b.2 (fun h => hab (Subtype.ext h))).mono ball_subset_closedBall
      ball_subset_closedBall
  have hcfam : c ∈ VitaliFam δ O := by
    refine ⟨fun n => ?_, fun n => ?_, hcdisj, ?_⟩
    · rcases hen : e n with _ | a
      · simp only [c, hen, Option.elim_none]; exact ⟨le_rfl, hδ⟩
      · simp only [c, hen, Option.elim_some]
        exact ⟨by linarith [(hut a.2).2.1], (hut a.2).2.2.1⟩
    · rcases hen : e n with _ | a
      · rw [hcnone n hen, closure_empty]; exact empty_subset _
      · rw [hcsome n a hen, closure_ball _ (hut a.2).2.1.ne']; exact (hut a.2).2.2.2.1
    · refine measure_mono_null (t := (O \ G) ∪ (G \ ⋃ a ∈ u, closedBall a.2.1 a.2.2) ∪
        ⋃ a ∈ u, sphere a.2.1 a.2.2) ?_ (measure_union_null (measure_union_null hOG hcov)
          ((measure_biUnion_null_iff huc).2 fun a _ => Measure.addHaar_sphere volume _ _))
      rintro x ⟨hxO, hxc⟩
      by_cases hxG : x ∈ G
      · by_cases hxB : x ∈ ⋃ a ∈ u, closedBall a.2.1 a.2.2
        · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 hxB
          refine Or.inr (mem_iUnion₂.2 ⟨a, ha, ?_⟩)
          have hxnb : x ∉ ball a.2.1 a.2.2 := fun h => hxc (mem_iUnion.2 ⟨f ⟨a, ha⟩, by
            rw [hcsome _ ⟨a, ha⟩ (he1 ⟨a, ha⟩)]; exact h⟩)
          rw [← ball_union_sphere] at hxa
          exact hxa.resolve_left hxnb
        · exact Or.inl (Or.inr ⟨hxG, hxB⟩)
      · exact Or.inl (Or.inl ⟨hxO, hxG⟩)
  -- the energy of the family
  have hmeas : ∀ n, MeasurableSet (cube (c n).1 (c n).2) := fun n => (isOpen_cube _ _).measurableSet
  calc vitaliDelta S δ O ≤ ∑' n, S (cube (c n).1 (c n).2) := iInf₂_le c hcfam
    _ ≤ ∑' n, ((∫⁻ y in cube (c n).1 (c n).2, D y) +
          ENNReal.ofReal η * volume (cube (c n).1 (c n).2)) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rcases hen : e n with _ | a
        · rw [hcnone n hen, S_empty hdom]; exact zero_le
        · rw [hcsome n a hen]; exact (hut a.2).2.2.2.2
    _ = (∫⁻ y in ⋃ n, cube (c n).1 (c n).2, D y) +
          ENNReal.ofReal η * volume (⋃ n, cube (c n).1 (c n).2) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, lintegral_iUnion hmeas hcdisj,
          measure_iUnion hcdisj hmeas]
    _ ≤ (∫⁻ x in O, D x) + ENNReal.ofReal η * volume O := by
        gcongr
        · exact iUnion_subset hcO
        · exact iUnion_subset hcO

/-- **Key estimate**: `S^δ(O) ≤ ∫_O lowDeriv`. -/
theorem vitaliDelta_le_lintegral (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) {O : Set (Sp N)} (hOo : IsOpen O)
    (hOΩ : O ⊆ Ω) {δ : ℝ} (hδ : 0 < δ) :
    vitaliDelta S δ O ≤ ∫⁻ x in O, lowDeriv S Ω x := by
  have hOfin : volume O ≠ ⊤ := (hΩb.subset hOΩ).measure_lt_top.ne
  have h : Tendsto (fun η : ℝ => (∫⁻ x in O, lowDeriv S Ω x) + ENNReal.ofReal η * volume O)
      (𝓝[>] 0) (𝓝 ((∫⁻ x in O, lowDeriv S Ω x) + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h0 : Tendsto (fun η : ℝ => ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hOfin)
  rw [add_zero] at h
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
  exact vitaliDelta_le_add hΩo hg hgfin hdom hOo hOΩ hδ hη

theorem vitaliEnv_le_lintegral (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) {O : Set (Sp N)} (hOo : IsOpen O)
    (hOΩ : O ⊆ Ω) : vitaliEnv S O ≤ ∫⁻ x in O, lowDeriv S Ω x :=
  iSup₂_le fun _ hδ => vitaliDelta_le_lintegral hΩo hΩb hg hgfin hdom hOo hOΩ hδ

/-- **Step 2 of Theorem `Vitali-envelope-cite`**: `S(Q) ≤ ∫_Q lowDeriv` for every cube `Q ⊆ Ω`. -/
theorem le_lintegral_lowDeriv (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V)
    {w : Sp N} {r : ℝ} (hΩw : ball w r ⊆ Ω) :
    S (ball w r) ≤ ∫⁻ x in ball w r, lowDeriv S Ω x := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  exact (le_vitaliDelta_add hΩo hgfin hdom hsub isOpen_ball hΩw (volume_ball_ne_top w r) 1
    (by exact_mod_cast hε.ne')).trans (add_le_add_left
      (vitaliDelta_le_lintegral hΩo hΩb hg hgfin hdom isOpen_ball hΩw one_pos) _)

/-- **Step 3 of Theorem `Vitali-envelope-cite`**: the derivative along centred cubes. -/
theorem ae_tendsto_ratio (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hg : Measurable g) (hgfin : ∫⁻ x in Ω, g x < ⊤)
    (hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x)
    (hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
      volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V) :
    ∀ᵐ x ∂(volume.restrict Ω),
      Tendsto (fun ρ => S (cube ρ x) / volume (cube ρ x)) (𝓝[>] 0) (𝓝 (lowDeriv S Ω x)) := by
  have hΩm := hΩo.measurableSet
  have hDint : ∫⁻ x, Ω.indicator (lowDeriv S Ω) x ≠ ⊤ := by
    rw [lintegral_indicator hΩm]
    exact (lintegral_lowDeriv_lt_top hΩo hg hgfin hdom).ne
  rw [ae_restrict_iff' hΩm]
  filter_upwards [(vfam N).ae_tendsto_lintegral_div
    (measurable_lowDeriv.indicator hΩm).aemeasurable hDint] with x hx hxΩ
  have hc := tendsto_avgOn_ball_center (f := Ω.indicator (lowDeriv S Ω)) hx
  rw [Set.indicator_of_mem hxΩ] at hc
  have hlow := (tendsto_lowDerivR (S := S) (Ω := Ω) x).comp tendsto_half_nhdsGT
  obtain ⟨ρΩ, hρΩ, hballΩ⟩ := Metric.isOpen_iff.1 hΩo x hxΩ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hc ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hρΩ] with ρ hρ
    have hρ0 : 0 < ρ / 2 := half_pos hρ.1
    have hsub' : closedBall x (ρ / 2) ⊆ Ω :=
      (closedBall_subset_ball (by linarith [hρ.2])).trans hballΩ
    rw [Function.comp_apply, cube_eq_ball hρ.1]
    exact lowDerivR_le_ballRatio hρ0 le_rfl (mem_ball_self hρ0) hsub'
  · filter_upwards [Ioo_mem_nhdsGT hρΩ] with ρ hρ
    have hbΩ : ball x (ρ / 2) ⊆ Ω :=
      (ball_subset_ball (by linarith [hρ.2])).trans hballΩ
    rw [cube_eq_ball hρ.1, avgOn, setLIntegral_indicator_of_subset isOpen_ball.measurableSet hbΩ]
    exact ENNReal.div_le_div_right (le_lintegral_lowDeriv hΩo hΩb hg hgfin hdom hsub hbΩ) _

end Hyp

/-- **Theorem `Vitali-envelope-cite`**, inequality form ([oah-cloz-jpm17, Theorem A.16], for the
Lebesgue measure). -/
theorem vitaliEnvelopeUpper [NeZero N] : VitaliEnvelopeUpper N := by
  intro Ω hΩo hΩb S g hg hgfin hdom hsub
  exact ⟨lowDeriv S Ω, ae_tendsto_ratio hΩo hΩb hg hgfin hdom hsub,
    fun A hA hAΩ => vitaliEnv_le_lintegral hΩo hΩb hg hgfin hdom hA hAΩ⟩

/-- **Theorem `main-Ggrowth`** with two cited results: `CitedZaffLocLip` and
`CitedVitaliEnvelope` are no longer hypotheses. -/
theorem main_Ggrowth_final_two {m : ℕ} [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (N : ℝ) < p) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} (hW : Hypotheses p G W)
    (hAHM : CitedAHM14 N m p) (hApprox : CitedAffineApprox N m p) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W) (intHom (Whom p W)) :=
  main_Ggrowth_of_densities p hp hΩ hW hAHM hApprox citedZaffLocLip densityZaffUpper densityHaff
    (step4 hΩ hW vitaliEnvelopeUpper)

end Homogenization
