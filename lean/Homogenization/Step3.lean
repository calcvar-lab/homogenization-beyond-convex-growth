import Homogenization.Main
import Homogenization.AffSobolev

/-!
# Step 3 of the proof of Theorem `main-Ggrowth`: the recovery sequence for piecewise affine data

This file proves `Step3Statement` (equation `eq:4.13-4.14` of the paper) from the two density
results it relies on:

* `DensityZaffUpper` — the upper bound in Proposition `prop:densityZaff` ([oah-jpm11, Prop. 3.17]),
  proved in `Homogenization.DensityZaff`;
* `DensityHaff` — Proposition `prop:densityHaff` (§7 of the paper), proved in
  `Homogenization.DensityHaff`.

The proof follows the paper: on each piece `Uᵢ` of `φ`, a corrector `φ_{i,k} ∈ Aff₀(Uᵢ)` realizes
`𝒵_aff ℋ_aff(𝒴_loc W)(ξᵢ)`; on each piece `V_{i,k,j}` of `φ_{i,k}`, an oscillating corrector
`ψ_{i,j,k,ε} ∈ Aff₀(V_{i,k,j})` realizes `ℋ_aff(𝒴_loc W)(ξᵢ + ζ_{i,k,j})`; the functions are glued
(`IsPWAffine.add_sum_Aff0`, `Aff0.add_sum`), the energies are summed over the finitely many pieces,
and a diagonal argument in `(k, ε)` (`exists_diagonal_family`) concludes.

Finally `main_Ggrowth_of_densities` is the main theorem with `Step3Statement` replaced by these two
density propositions.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### Piecewise affine functions: index sets, sums, gluing -/

/-- Pieces may be indexed by any finite type. -/
theorem isPWAffine_of_fintype {U : Set (Sp N)} {φ : Sp N → Tgt m} {K : ℝ≥0}
    (hK : LipschitzOnWith K φ U) {ι : Type*} [Finite ι] (V : ι → Set (Sp N))
    (ξ : ι → Mat m N) (hVo : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVf : ∀ i, volume (U ∩ frontier (V i)) = 0) (hVc : volume (U \ ⋃ i, V i) = 0)
    (hφV : ∀ i, ∀ y ∈ V i, HasFDerivAt φ (ξ i) y) : IsPWAffine U φ := by
  have := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨⟨K, hK⟩, Fintype.card ι, V ∘ e.symm, ξ ∘ e.symm, fun i => hVo _, fun i => hVU _,
    fun i j hij => hVd (e.symm.injective.ne hij), fun i => hVf _, ?_, fun i => hφV _⟩
  rw [show (⋃ i, (V ∘ e.symm) i) = ⋃ i, V i from e.symm.surjective.iUnion_comp V]
  exact hVc

theorem inter_frontier_subset {Ω U W : Set (Sp N)} (hU : IsOpen U) (hWU : W ⊆ U) :
    Ω ∩ frontier W ⊆ (U ∩ frontier W) ∪ (Ω ∩ frontier U) := by
  rintro y ⟨hyΩ, hyW⟩
  by_cases hyU : y ∈ U
  · exact Or.inl ⟨hyU, hyW⟩
  · refine Or.inr ⟨hyΩ, ?_⟩
    rw [hU.frontier_eq]
    exact ⟨closure_mono hWU (frontier_subset_closure hyW), hyU⟩

theorem lipschitzWith_sum {ι : Type*} (s : Finset ι) {f : ι → Sp N → Tgt m} {K : ι → ℝ≥0}
    (h : ∀ i, LipschitzWith (K i) (f i)) : LipschitzWith (∑ i ∈ s, K i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

/-- On a piece `Uᵢ`, the functions `χⱼ ∈ Aff₀(Uⱼ)`, `j ≠ i`, vanish. -/
theorem sum_eq_of_mem_piece {n : ℕ} {U : Fin n → Set (Sp N)}
    (hUd : Pairwise fun i j => Disjoint (U i) (U j)) {χ : Fin n → Sp N → Tgt m}
    (hχ0 : ∀ i, ∀ y ∉ U i, χ i y = 0) {i : Fin n} {y : Sp N} (hy : y ∈ U i) :
    (∑ j, χ j) y = χ i y := by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_single i (fun j _ hji => hχ0 j y fun h => (hUd hji).le_bot ⟨h, hy⟩)
    (by simp)

/-- `Aff₀` membership in prenex form (convenient for `choose`). -/
theorem Aff0.data {U : Set (Sp N)} {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 U) :
    ∃ (K : ℝ≥0) (n : ℕ) (V : Fin n → Set (Sp N)) (ξ : Fin n → Mat m N),
      LipschitzWith K φ ∧ (∀ y ∉ U, φ y = 0) ∧ (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U) ∧
      (Pairwise fun i j => Disjoint (V i) (V j)) ∧ (∀ i, volume (U ∩ frontier (V i)) = 0) ∧
      volume (U \ ⋃ i, V i) = 0 ∧ ∀ i, ∀ y ∈ V i, HasFDerivAt φ (ξ i) y := by
  obtain ⟨⟨K, hK⟩, h0, -, n, V, ξ, h1, h2, h3, h4, h5, h6⟩ := hφ
  exact ⟨K, n, V, ξ, hK, h0, h1, h2, h3, h4, h5, h6⟩

/-- **Gluing.** If `φ` is piecewise affine on `Ω` with pieces `Uᵢ`, and `χᵢ ∈ Aff₀(Uᵢ)`, then
`φ + ∑ᵢ χᵢ` is piecewise affine on `Ω` (its pieces are those of the `χᵢ`). -/
theorem IsPWAffine.add_sum_Aff0 {Ω : Set (Sp N)} {φ : Sp N → Tgt m} {Kφ : ℝ≥0}
    (hKφ : LipschitzOnWith Kφ φ Ω) {n : ℕ} {U : Fin n → Set (Sp N)} {ξ : Fin n → Mat m N}
    (hUo : ∀ i, IsOpen (U i)) (hUΩ : ∀ i, U i ⊆ Ω)
    (hUd : Pairwise fun i j => Disjoint (U i) (U j))
    (hUf : ∀ i, volume (Ω ∩ frontier (U i)) = 0) (hUc : volume (Ω \ ⋃ i, U i) = 0)
    (hφU : ∀ i, ∀ y ∈ U i, HasFDerivAt φ (ξ i) y)
    {χ : Fin n → Sp N → Tgt m} (hχ : ∀ i, χ i ∈ Aff0 (U i)) :
    IsPWAffine Ω (φ + ∑ i, χ i) := by
  choose Kχ nχ W η hKχ hχ0 hWo hWU hWd hWf hWc hχW using fun i => Aff0.data (hχ i)
  have hLip : LipschitzOnWith (Kφ + ∑ i, Kχ i) (φ + ∑ i, χ i) Ω :=
    hKφ.add (lipschitzWith_sum Finset.univ hKχ).lipschitzOnWith
  refine isPWAffine_of_fintype hLip (fun σ : (Σ i, Fin (nχ i)) => W σ.1 σ.2)
    (fun σ => ξ σ.1 + η σ.1 σ.2) (fun σ => hWo _ _) (fun σ => (hWU _ _).trans (hUΩ _))
    ?_ (fun σ => ?_) ?_ ?_
  · rintro ⟨i, l⟩ ⟨i', l'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hll : l ≠ l' := fun h => hne (h ▸ rfl)
      exact hWd i hll
    · exact (hUd hii).mono (hWU i l) (hWU i' l')
  · exact measure_mono_null (inter_frontier_subset (hUo σ.1) (hWU σ.1 σ.2))
      (measure_union_null (hWf σ.1 σ.2) (hUf σ.1))
  · refine measure_mono_null (t := (Ω \ ⋃ i, U i) ∪ ⋃ i, (U i \ ⋃ l, W i l)) ?_
      (measure_union_null hUc (measure_iUnion_null fun i => hWc i))
    rintro y ⟨hyΩ, hyW⟩
    by_cases hyU : ∃ i, y ∈ U i
    · obtain ⟨i, hi⟩ := hyU
      refine Or.inr (mem_iUnion.2 ⟨i, hi, fun h => hyW ?_⟩)
      obtain ⟨l, hl⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨⟨i, l⟩, hl⟩
    · exact Or.inl ⟨hyΩ, fun h => hyU (mem_iUnion.1 h)⟩
  · rintro ⟨i, l⟩ y hy
    have hyU : y ∈ U i := hWU i l hy
    have heq : (φ + ∑ j, χ j) =ᶠ[𝓝 y] fun z => φ z + χ i z := by
      filter_upwards [(hUo i).mem_nhds hyU] with z hz
      rw [Pi.add_apply, sum_eq_of_mem_piece hUd hχ0 hz]
    exact ((hφU i y hyU).add (hχW i l y hy)).congr_of_eventuallyEq heq

/-- **Refinement.** If `χ ∈ Aff₀(U)` has pieces `Vⱼ` and `ψⱼ ∈ Aff₀(Vⱼ)`, then
`χ + ∑ⱼ ψⱼ ∈ Aff₀(U)`. -/
theorem Aff0.add_sum {U : Set (Sp N)} {χ : Sp N → Tgt m} {K : ℝ≥0} (hK : LipschitzWith K χ)
    (hχ0 : ∀ y ∉ U, χ y = 0) {n : ℕ} {V : Fin n → Set (Sp N)} {ζ : Fin n → Mat m N}
    (hVo : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVf : ∀ i, volume (U ∩ frontier (V i)) = 0) (hVc : volume (U \ ⋃ i, V i) = 0)
    (hχV : ∀ i, ∀ y ∈ V i, HasFDerivAt χ (ζ i) y)
    {ψ : Fin n → Sp N → Tgt m} (hψ : ∀ i, ψ i ∈ Aff0 (V i)) :
    χ + ∑ i, ψ i ∈ Aff0 U := by
  choose Kψ _ _ _ hKψ hψ0 _ using fun i => Aff0.data (hψ i)
  refine ⟨⟨_, hK.add (lipschitzWith_sum Finset.univ hKψ)⟩, fun y hy => ?_,
    IsPWAffine.add_sum_Aff0 hK.lipschitzOnWith hVo hVU hVd hVf hVc hχV hψ⟩
  rw [Pi.add_apply, Finset.sum_apply, hχ0 y hy, zero_add]
  exact Finset.sum_eq_zero fun i _ => hψ0 i y fun h => hy (hVU i h)

/-! ### Adding a Lipschitz function to an element of `W^{1,p}(Ω)` -/

section AddLip

/-- `MemLp` is stable under addition (normed-group version; `MemLp.add` triggers an expensive
instance search on `Mat m N`). -/
theorem memLp_add' {α E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    [NormedAddCommGroup E] {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f + g) p μ := by
  simpa [sub_neg_eq_add] using hf.sub hg.neg

variable {P : ℝ≥0∞} {Ω : Set (Sp N)}

theorem memLp_of_lipschitzWith (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Sp N → E} {K : ℝ≥0}
    (hg : LipschitzWith K g) : MemLp g P (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  obtain ⟨R, hR⟩ := hΩb.exists_norm_le
  refine MemLp.of_bound hg.continuous.aestronglyMeasurable (‖g 0‖ + K * R) ?_
  rw [ae_restrict_iff' hΩo.measurableSet]
  refine Eventually.of_forall fun y hy => ?_
  have h1 := hg.dist_le_mul y 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at h1
  have h2 := norm_sub_norm_le (g y) (g 0)
  have h3 : (K : ℝ) * ‖y‖ ≤ K * R := mul_le_mul_of_nonneg_left (hR y hy) K.2
  linarith

theorem memLp_fderiv_of_lipschitzWith (hΩb : Bornology.IsBounded Ω) {g : Sp N → Tgt m}
    {K : ℝ≥0} (hg : LipschitzWith K g) : MemLp (fderiv ℝ g) P (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  exact MemLp.of_bound (measurable_fderiv ℝ g).aestronglyMeasurable K
    (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hg)

/-- `h • f` is integrable if `f ∈ Lᵖ(Ω)`, `p ≥ 1`, and `h` is continuous, bounded and vanishes
off `Ω`. -/
theorem integrable_smul_of_memLp [Fact (1 ≤ P)] (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Sp N → E}
    (hf : MemLp f P (volume.restrict Ω)) {h : Sp N → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ y, ‖h y‖ ≤ C) (hsupp : ∀ y ∉ Ω, h y = 0) :
    Integrable (fun y => h y • f y) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  have h1 : Integrable f (volume.restrict Ω) := hf.integrable Fact.out
  have h2 : IntegrableOn (fun y => h y • f y) Ω :=
    h1.bdd_smul C hh.aestronglyMeasurable (Eventually.of_forall hC)
  rw [← integrable_indicator_iff hΩo.measurableSet] at h2
  have heq : Ω.indicator (fun y => h y • f y) = fun y => h y • f y := by
    funext y
    by_cases hy : y ∈ Ω
    · simp [hy]
    · simp [hy, hsupp y hy]
  rwa [heq] at h2

/-- Weak gradients add up (for `Lᵖ` functions and gradients on a bounded open set). -/
theorem HasWeakGrad.add [Fact (1 ≤ P)] (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {f g : Sp N → Tgt m} {Df Dg : Sp N → Mat m N}
    (hf : MemLp f P (volume.restrict Ω)) (hDf : MemLp Df P (volume.restrict Ω))
    (hg : MemLp g P (volume.restrict Ω)) (hDg : MemLp Dg P (volume.restrict Ω))
    (hwf : HasWeakGrad Ω f Df) (hwg : HasWeakGrad Ω g Dg) : HasWeakGrad Ω (f + g) (Df + Dg) := by
  intro ψ hψ hcs hsub v
  have hzero : ∀ y ∉ Ω, y ∉ tsupport ψ := fun y hy h => hy (hsub h)
  have hc1 : Continuous fun y => fderiv ℝ ψ y v :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C1, hC1⟩ := hc1.bounded_above_of_compact_support
    ((hcs.fderiv (𝕜 := ℝ)).mono fun y hy h => hy (by change fderiv ℝ ψ y v = 0; rw [h]; rfl))
  obtain ⟨C2, hC2⟩ := hψ.continuous.bounded_above_of_compact_support hcs
  have hs1 : ∀ y ∉ Ω, fderiv ℝ ψ y v = 0 := fun y hy => by
    have : fderiv ℝ ψ y = 0 := by
      by_contra h; exact hzero y hy (support_fderiv_subset ℝ h)
    rw [this]; rfl
  have hs2 : ∀ y ∉ Ω, ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport (hzero y hy)
  have happ : ∀ {D : Sp N → Mat m N}, MemLp D P (volume.restrict Ω) →
      MemLp (fun y => D y v) P (volume.restrict Ω) := fun hD =>
    hD.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ (Tgt m) v)
  have i1 := integrable_smul_of_memLp hΩo hΩb hf hc1 hC1 hs1
  have i2 := integrable_smul_of_memLp hΩo hΩb hg hc1 hC1 hs1
  have i3 := integrable_smul_of_memLp hΩo hΩb (happ hDf) hψ.continuous hC2 hs2
  have i4 := integrable_smul_of_memLp hΩo hΩb (happ hDg) hψ.continuous hC2 hs2
  simp only [Pi.add_apply, smul_add, _root_.add_apply]
  rw [integral_add i1 i2, integral_add i3 i4, hwf ψ hψ hcs hsub v, hwg ψ hψ hcs hsub v, neg_add]

/-- `u + g ∈ W^{1,p}(Ω)` for `u ∈ W^{1,p}(Ω)` and `g` Lipschitz. -/
noncomputable def W1p.addLip [Fact (1 ≤ P)] (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : W1p N m P Ω) (g : Sp N → Tgt m) {K : ℝ≥0} (hg : LipschitzWith K g) : W1p N m P Ω where
  toFun := u.toFun + g
  grad := u.grad + fderiv ℝ g
  memLp := memLp_add' u.memLp (memLp_of_lipschitzWith (P := P) hΩo hΩb hg)
  memLp_grad := memLp_add' u.memLp_grad (memLp_fderiv_of_lipschitzWith (P := P) hΩb hg)
  weak := HasWeakGrad.add hΩo hΩb u.memLp u.memLp_grad
    (memLp_of_lipschitzWith (P := P) hΩo hΩb hg) (memLp_fderiv_of_lipschitzWith (P := P) hΩb hg)
    u.weak (LipschitzWith.hasWeakGrad hg Ω)

theorem W1p.edist_addLip_le [Fact (1 ≤ P)] (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : W1p N m P Ω) {g : Sp N → Tgt m} {K : ℝ≥0} (hg : LipschitzWith K g) {δ : ℝ}
    (hδ : ∀ y, ‖g y‖ ≤ δ) :
    edist (u.addLip hΩo hΩb g hg) u ≤ volume Ω ^ P.toReal⁻¹ * ENNReal.ofReal δ := by
  rw [W1p.edist_def]
  have := eLpNorm_le_of_ae_bound (μ := volume.restrict Ω) (p := P) (Eventually.of_forall hδ)
  rw [Measure.restrict_apply_univ] at this
  convert this using 2
  simp [W1p.addLip]

end AddLip

/-! ### Integrals over the pieces, finite sums of limsups, uniform smallness -/

theorem lintegral_eq_sum_pieces {U : Set (Sp N)} {n : ℕ} {V : Fin n → Set (Sp N)}
    (hVo : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U) (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVc : volume (U \ ⋃ i, V i) = 0) (F : Sp N → ℝ≥0∞) :
    ∫⁻ y in U, F y = ∑ i, ∫⁻ y in V i, F y := by
  have hUV : U =ᵐ[volume] ⋃ i, V i :=
    ae_eq_set.2 ⟨hVc, by rw [sdiff_eq_empty.2 (iUnion_subset hVU), measure_empty]⟩
  rw [setLIntegral_congr hUV, lintegral_iUnion (fun i => (hVo i).measurableSet) hVd,
    tsum_fintype]

theorem limsup_add_le_ennreal {α : Type*} {l : Filter α} (u v : α → ℝ≥0∞) :
    limsup (fun a => u a + v a) l ≤ limsup u l + limsup v l := by
  by_cases hu : limsup u l = ⊤
  · rw [hu, top_add]; exact le_top
  by_cases hv : limsup v l = ⊤
  · rw [hv, add_top]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hη2 : (0 : ℝ≥0∞) < (η : ℝ≥0∞) / 2 := ENNReal.half_pos (by exact_mod_cast hη.ne')
  have h1 := eventually_lt_of_limsup_lt (ENNReal.lt_add_right hu hη2.ne') (f := l)
  have h2 := eventually_lt_of_limsup_lt (ENNReal.lt_add_right hv hη2.ne') (f := l)
  calc limsup (fun a => u a + v a) l
      ≤ (limsup u l + (η : ℝ≥0∞) / 2) + (limsup v l + (η : ℝ≥0∞) / 2) :=
        limsup_le_of_le (by isBoundedDefault) ((h1.and h2).mono fun _ h => add_le_add h.1.le h.2.le)
    _ = limsup u l + limsup v l + η := by
        rw [add_add_add_comm, ENNReal.add_halves]

theorem limsup_finset_sum_le {ι α : Type*} {l : Filter α} (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : limsup (fun a => ∑ i ∈ s, f i a) l ≤ ∑ i ∈ s, limsup (f i) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun _ => le_rfl)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (limsup_add_le_ennreal (f a) (fun x => ∑ i ∈ s, f i x)).trans (add_le_add le_rfl ih)

/-- Uniform convergence to `0`. -/
def UnifSmall {α : Type*} (l : Filter α) (f : α → Sp N → Tgt m) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ t in l, ∀ y, ‖f t y‖ ≤ δ

theorem UnifSmall.add {α : Type*} {l : Filter α} {f g : α → Sp N → Tgt m} (hf : UnifSmall l f)
    (hg : UnifSmall l g) : UnifSmall l (fun t => f t + g t) := by
  intro δ hδ
  filter_upwards [hf (δ / 2) (by positivity), hg (δ / 2) (by positivity)] with t h1 h2 y
  calc ‖(f t + g t) y‖ ≤ ‖f t y‖ + ‖g t y‖ := norm_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (h1 y) (h2 y)
    _ = δ := add_halves δ

theorem UnifSmall.sum {α ι : Type*} {l : Filter α} (s : Finset ι) {f : ι → α → Sp N → Tgt m}
    (hf : ∀ i, UnifSmall l (f i)) : UnifSmall l (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun δ hδ => Eventually.of_forall fun _ y => by simp [hδ.le]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

/-! ### Diagonalization in `(k, ε)` -/

/-- From families `x k` that are, for `k` large and `ε` small, close to `u` and of energy at most
`ℓ + η`, extract a single family `v ε → u` with `limsup F_ε(v ε) ≤ ℓ`. -/
theorem exists_diagonal_family {X : Type*} [PseudoEMetricSpace X] (x : ℕ → ℝ → X) (u : X)
    (F : ℝ → X → ℝ≥0∞) (ℓ : ℝ≥0∞) (S : Set X) (hS : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), x k ε ∈ S)
    (hx : ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ k in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), edist (x k ε) u < η)
    (hF : ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ k in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε (x k ε) ≤ ℓ + η) :
    ∃ v : ℝ → X, Tendsto v (𝓝[>] 0) (𝓝 u) ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), v ε ∈ S) ∧
      limsup (fun ε => F ε (v ε)) (𝓝[>] 0) ≤ ℓ := by
  let r : ℕ → ℝ≥0∞ := fun k => ((k : ℝ≥0∞) + 1)⁻¹
  have hr_pos : ∀ k, 0 < r k := fun k => ENNReal.inv_pos.2 (by simp)
  have hr_tend : Tendsto r atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    simpa [r] using h2
  have hk : ∀ j, ∃ k, (∀ᶠ ε in 𝓝[>] (0 : ℝ), edist (x k ε) u < r j) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε (x k ε) ≤ ℓ + r j :=
    fun j => ((hx _ (hr_pos j)).and (hF _ (hr_pos j))).exists
  choose mk hmk using hk
  let Q : ℕ → ℝ → Prop := fun j ε =>
    x (mk j) ε ∈ S ∧ edist (x (mk j) ε) u < r j ∧ F ε (x (mk j) ε) ≤ ℓ + r j
  have hQ : ∀ j, ∀ᶠ ε in 𝓝[>] (0 : ℝ), Q j ε := fun j =>
    (hS (mk j)).and ((hmk j).1.and (hmk j).2)
  obtain ⟨κ, hκ, hQκ⟩ := exists_diagonal_nhdsGT Q hQ
  have hrκ : Tendsto (fun ε => r (κ ε)) (𝓝[>] 0) (𝓝 0) := hr_tend.comp hκ
  refine ⟨fun ε => x (mk (κ ε)) ε, ?_, hQκ.mono fun _ h => h.1, ?_⟩
  · exact tendsto_of_edist_le (v := fun _ => u) tendsto_const_nhds hrκ
      (hQκ.mono fun _ h => h.2.1.le)
  · calc limsup (fun ε => F ε (x (mk (κ ε)) ε)) (𝓝[>] 0)
        ≤ limsup (fun ε => ℓ + r (κ ε)) (𝓝[>] 0) := limsup_le_limsup (hQκ.mono fun _ h => h.2.2)
      _ = ℓ := by
        have : Tendsto (fun ε => ℓ + r (κ ε)) (𝓝[>] 0) (𝓝 (ℓ + 0)) :=
          tendsto_const_nhds.add hrκ
        rw [add_zero] at this
        exact this.limsup_eq

/-! ### The density propositions -/

section Statements

variable (N m)

/-- **Proposition `prop:densityZaff`** ([oah-jpm11, Proposition 3.17], cited). -/
def CitedDensityZaff : Prop :=
  ∀ (L : Mat m N → ℝ≥0∞) (A : Set (Sp N)), IsOpen A → Bornology.IsBounded A →
    ∀ ξ : Mat m N, ∃ φ : ℕ → Sp N → Tgt m, (∀ k, φ k ∈ Aff0 A) ∧ UnifSmall atTop φ ∧
      Tendsto (fun k => ∫⁻ y in A, L (ξ + fderiv ℝ (φ k) y)) atTop (𝓝 (volume A * Zaff L ξ))

/-- The upper bound in Proposition `prop:densityZaff`, which is all that Step 3 uses. -/
def DensityZaffUpper : Prop :=
  ∀ (L : Mat m N → ℝ≥0∞) (A : Set (Sp N)), IsOpen A → Bornology.IsBounded A →
    ∀ ξ : Mat m N, ∃ φ : ℕ → Sp N → Tgt m, (∀ k, φ k ∈ Aff0 A) ∧ UnifSmall atTop φ ∧
      limsup (fun k => ∫⁻ y in A, L (ξ + fderiv ℝ (φ k) y)) atTop ≤ volume A * Zaff L ξ

variable {N m} in
theorem CitedDensityZaff.toUpper (h : CitedDensityZaff N m) : DensityZaffUpper N m :=
  fun L A hA hAb ξ => let ⟨φ, h1, h2, h3⟩ := h L A hA hAb ξ; ⟨φ, h1, h2, h3.limsup_eq.le⟩

/-- **Proposition `prop:densityHaff`** (§7 of the paper; proved in `Homogenization.DensityHaff`). -/
def DensityHaff : Prop :=
  ∀ (G : Mat m N → ℝ≥0∞) (α β : ℝ≥0) (L : Sp N → Mat m N → ℝ≥0∞), ConvexENN G → 0 < α →
    Measurable (uncurry L) → IsPeriodic L → HasGGrowth G α β L →
    ∀ (A : Set (Sp N)), IsOpen A → Bornology.IsBounded A → ∀ ξ : Mat m N,
      ∃ ψ : ℝ → Sp N → Tgt m, (∀ ε, ψ ε ∈ Aff0 A) ∧ UnifSmall (𝓝[>] 0) ψ ∧
        limsup (fun ε => ∫⁻ x in A, L (ε⁻¹ • x) (ξ + fderiv ℝ (ψ ε) x)) (𝓝[>] 0) ≤
          volume A * Haff L ξ

end Statements

/-! ### Step 3 -/

/-- **Step 3 of the proof of Theorem `main-Ggrowth`** (`eq:4.13-4.14`): for piecewise affine `φ`
with `∫_Ω Λ(∇φ) < ∞`, there is a family `φ_ε ∈ Aff(Ω)`, `φ_ε → φ` in `Lᵖ`, with
`limsup_{ε→0} ∫_Ω 𝒴_loc W(x/ε, ∇φ_ε) ≤ ∫_Ω Λ(∇φ)`. -/
theorem step3 [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    (hW : Hypotheses p G W) (hZ : DensityZaffUpper N m) (hH : DensityHaff N m) :
    Step3Statement (p := p) W Ω := by
  classical
  intro φ hφA hfin
  obtain ⟨⟨⟨Kφ, hKφ⟩, n, U, ξ, hUo, hUΩ, hUd, hUf, hUc, hφU⟩, hgrad⟩ := hφA
  have hΩm : MeasurableSet Ω := hΩ.isOpen.measurableSet
  have hUb : ∀ i, Bornology.IsBounded (U i) := fun i => hΩ.bounded.subset (hUΩ i)
  -- correctors on the pieces of `φ` (Proposition `prop:densityZaff`)
  choose χ hχA hχsmall hχlim using
    fun i => hZ (Haff (Ytloc W)) (U i) (hUo i) (hUb i) (ξ i)
  choose Kχ nχ V ζ hKχ hχ0 hVo hVU hVd hVf hVc hχV using fun i k => Aff0.data (hχA i k)
  -- oscillating correctors on the pieces of `χ i k` (Proposition `prop:densityHaff`)
  obtain ⟨α, β, hα, -, h3set⟩ := hW.setGrowth
  have hgrowth : HasGGrowth G α β (Ytloc W) := HasGGrowth.Ytloc h3set
  choose ψ hψA hψsmall hψlim using fun (i : Fin n) (k : ℕ) (j : Fin (nχ i k)) =>
    hH G α β (Ytloc W) hW.convex hα hW.measurable_Ytloc hW.periodic.Ytloc hgrowth (V i k j)
      (hVo i k j) ((hUb i).subset (hVU i k j)) (ξ i + ζ i k j)
  have hψ0 : ∀ i k j ε, ∀ y ∉ V i k j, ψ i k j ε y = 0 := fun i k j ε => (hψA i k j ε).2.1
  -- the glued correctors
  let Φ : ℕ → ℝ → Sp N → Tgt m := fun k ε => ∑ i, (χ i k + ∑ j, ψ i k j ε)
  have hLipΦ : ∀ k ε, ∃ K, LipschitzWith K (Φ k ε) := by
    intro k ε
    choose Kψ hKψ using fun i j => (hψA i k j ε).1
    exact ⟨_, lipschitzWith_sum Finset.univ fun i =>
      (hKχ i k).add (lipschitzWith_sum Finset.univ (hKψ i))⟩
  choose KΦ hKΦ using hLipΦ
  let v : ℕ → ℝ → W1p N m (ENNReal.ofReal p) Ω := fun k ε =>
    φ.addLip hΩ.isOpen hΩ.bounded (Φ k ε) (hKΦ k ε)
  -- a.e. on `Ω`, points lie in a piece of `φ`
  have hae_U : ∀ᵐ y ∂(volume.restrict Ω), y ∈ ⋃ i, U i := by
    rw [ae_restrict_iff' hΩm]
    refine ae_iff.2 (measure_mono_null (fun y (hy : ¬(y ∈ Ω → y ∈ ⋃ i, U i)) => ?_) hUc)
    exact ⟨by_contra fun h => hy fun h' => absurd h' h, fun h => hy fun _ => h⟩
  -- `∇φ = ξᵢ` a.e. on `Uᵢ`
  have hgrad_U : ∀ i, ∀ᵐ y, y ∈ U i → φ.grad y = ξ i := by
    intro i
    have := (ae_restrict_iff' hΩm).1 hgrad
    filter_upwards [this] with y hy hyU
    rw [hy (hUΩ i hyU), (hφU i y hyU).fderiv]
  -- locally on `V i k j`, `Φ k ε = χ i k + ψ i k j ε`
  have hΦloc : ∀ k ε i j y, y ∈ V i k j →
      Φ k ε =ᶠ[𝓝 y] fun z => χ i k z + ψ i k j ε z := by
    intro k ε i j y hy
    filter_upwards [(hVo i k j).mem_nhds hy] with z hz
    have hzU : z ∈ U i := hVU i k j hz
    simp only [Φ, Finset.sum_apply, Pi.add_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · intro j' _ hj'
        exact hψ0 i k j' ε z fun h => (hVd i k hj').le_bot ⟨h, hz⟩
      · simp
    · intro i' _ hi'
      have hzU' : z ∉ U i' := fun h => (hUd hi').le_bot ⟨h, hzU⟩
      rw [hχ0 i' k z hzU', zero_add]
      exact Finset.sum_eq_zero fun j' _ => hψ0 i' k j' ε z fun h => hzU' (hVU i' k j' h)
    · simp
  -- (i) the families stay piecewise affine
  have hS : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), v k ε ∈ AffSet (ENNReal.ofReal p) Ω := by
    intro k
    refine Eventually.of_forall fun ε => ⟨?_, ?_⟩
    · exact IsPWAffine.add_sum_Aff0 hKφ hUo hUΩ hUd hUf hUc hφU
        (χ := fun i => χ i k + ∑ j, ψ i k j ε) fun i =>
          Aff0.add_sum (hKχ i k) (hχ0 i k) (hVo i k) (hVU i k) (hVd i k) (hVf i k) (hVc i k)
            (hχV i k) fun j => hψA i k j ε
    · have h2 : ∀ᵐ y ∂(volume.restrict Ω), DifferentiableAt ℝ (Φ k ε) y :=
        ae_restrict_of_ae (hKΦ k ε).ae_differentiableAt
      filter_upwards [hgrad, hae_U, h2] with y hy1 hy2 hy3
      obtain ⟨i, hi⟩ := mem_iUnion.1 hy2
      change φ.grad y + fderiv ℝ (Φ k ε) y = fderiv ℝ (φ.toFun + Φ k ε) y
      rw [hy1, fderiv_add (hφU i y hi).differentiableAt hy3]
  -- (ii) closeness to `φ`
  set c : ℝ≥0∞ := volume Ω ^ (ENNReal.ofReal p).toReal⁻¹
  have hc : c ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      hΩ.bounded.measure_lt_top.ne
  have hχsum : UnifSmall atTop fun k => ∑ i, χ i k := UnifSmall.sum Finset.univ hχsmall
  have hψsum : ∀ k, UnifSmall (𝓝[>] 0) fun ε => ∑ i, ∑ j, ψ i k j ε := fun k =>
    UnifSmall.sum Finset.univ fun i => UnifSmall.sum Finset.univ fun j => hψsmall i k j
  have hx : ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ k in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), edist (v k ε) φ < η := by
    intro η hη
    have ht : Tendsto (fun δ : ℝ => c * ENNReal.ofReal (2 * δ)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ => ENNReal.ofReal (2 * δ)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp) |>.mono_left
            nhdsWithin_le_nhds)
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hc)
    obtain ⟨δ, hδη, hδ⟩ := ((ht.eventually_lt_const hη).and self_mem_nhdsWithin).exists
    filter_upwards [hχsum δ hδ] with k hk
    filter_upwards [hψsum k δ hδ] with ε hε
    have hsplit : Φ k ε = (∑ i, χ i k) + ∑ i, ∑ j, ψ i k j ε := Finset.sum_add_distrib
    have hbound : ∀ y, ‖Φ k ε y‖ ≤ 2 * δ := by
      intro y
      rw [hsplit, Pi.add_apply]
      linarith [norm_add_le ((∑ i, χ i k) y) ((∑ i, ∑ j, ψ i k j ε) y), hk y, hε y]
    exact (W1p.edist_addLip_le hΩ.isOpen hΩ.bounded φ (hKΦ k ε) hbound).trans_lt hδη
  -- (iii) energy estimates
  set ℓ := intHom (Λ W) φ
  let a : ℕ → ℝ≥0∞ := fun k => ∑ i, ∫⁻ y in U i, Haff (Ytloc W) (ξ i + fderiv ℝ (χ i k) y)
  have hℓ : ℓ = ∑ i, volume (U i) * Λ W (ξ i) := by
    simp only [ℓ, intHom]
    rw [lintegral_eq_sum_pieces hUo hUΩ hUd hUc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setLIntegral_congr_fun_ae (hUo i).measurableSet
      ((hgrad_U i).mono fun y hy hyU => by rw [hy hyU]), setLIntegral_const, mul_comm]
  have ha : limsup a atTop ≤ ℓ := by
    rw [hℓ]
    exact (limsup_finset_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hχlim i)
  have hJ : ∀ k, limsup (fun ε => intFun (Ytloc W) ε (v k ε)) (𝓝[>] 0) ≤ a k := by
    intro k
    have hsplitJ : ∀ ε, intFun (Ytloc W) ε (v k ε) = ∑ i, ∑ j,
        ∫⁻ x in V i k j, Ytloc W (ε⁻¹ • x) ((ξ i + ζ i k j) + fderiv ℝ (ψ i k j ε) x) := by
      intro ε
      simp only [intFun]
      rw [lintegral_eq_sum_pieces hUo hUΩ hUd hUc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lintegral_eq_sum_pieces (hVo i k) (hVU i k) (hVd i k) (hVc i k)]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine setLIntegral_congr_fun_ae (hVo i k j).measurableSet ?_
      filter_upwards [hgrad_U i, ((hψA i k j ε).1.choose_spec).ae_differentiableAt]
        with y hy1 hy2 hyV
      have hd : fderiv ℝ (Φ k ε) y = ζ i k j + fderiv ℝ (ψ i k j ε) y := by
        rw [(hΦloc k ε i j y hyV).fderiv_eq]
        exact fderiv_add (hχV i k j y hyV).differentiableAt hy2 |>.trans
          (by rw [(hχV i k j y hyV).fderiv])
      change Ytloc W (ε⁻¹ • y) (φ.grad y + fderiv ℝ (Φ k ε) y) = _
      rw [hy1 (hVU i k j hyV), hd, add_assoc]
    simp_rw [hsplitJ]
    refine (limsup_finset_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (limsup_finset_sum_le _ _).trans ?_
    rw [lintegral_eq_sum_pieces (hVo i k) (hVU i k) (hVd i k) (hVc i k)]
    refine Finset.sum_le_sum fun j _ => (hψlim i k j).trans (le_of_eq ?_)
    rw [setLIntegral_congr_fun (hVo i k j).measurableSet
      (g := fun _ => Haff (Ytloc W) (ξ i + ζ i k j))
      fun y hy => by rw [(hχV i k j y hy).fderiv], setLIntegral_const, mul_comm]
  have hF : ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ k in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intFun (Ytloc W) ε (v k ε) ≤ ℓ + η := by
    intro η hη
    filter_upwards [eventually_lt_of_limsup_lt (ha.trans_lt (ENNReal.lt_add_right hfin.ne hη.ne'))]
      with k hk
    exact (eventually_lt_of_limsup_lt ((hJ k).trans_lt hk)).mono fun _ h => h.le
  exact exists_diagonal_family v φ (intFun (Ytloc W)) ℓ _ hS hx hF

/-- **Theorem `main-Ggrowth`, with Step 3 formalized.** Same as `main_Ggrowth`, the hypothesis
`Step3Statement` being replaced by the two density propositions it relies on. -/
theorem main_Ggrowth_of_densities [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (N : ℝ) < p) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} (hW : Hypotheses p G W)
    (hAHM : CitedAHM14 N m p) (hApprox : CitedAffineApprox N m p)
    (hLip : CitedZaffLocLip N m) (hZ : DensityZaffUpper N m) (hH : DensityHaff N m)
    (h4 : Step4Statement (p := p) W Ω) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W) (intHom (Whom p W)) :=
  main_Ggrowth p hp hΩ hW hAHM hApprox hLip (step3 hΩ hW hZ hH) h4

end Homogenization
