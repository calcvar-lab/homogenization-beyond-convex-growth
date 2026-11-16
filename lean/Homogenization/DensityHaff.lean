import Homogenization.Step4

/-!
# Proposition `prop:densityHaff` (§7 of the paper)

For `L` periodic with `G`-growth and `A` bounded open, there are `ψ_ε ∈ Aff₀(A)`, `ψ_ε → 0`
uniformly, with `limsup_{ε→0} ∫_A L(x/ε, ξ + ∇ψ_ε) ≤ |A| ℋ_aff L(ξ)`.

The proof follows §7: a near-optimal corrector `φ_η ∈ Aff₀(kY)` is transplanted, rescaled by `ε`,
on the cells `εk(z + Y)` of the grid whose closure lies in `A` (Steps 1–3); the energy on these
cells is computed by rescaling and periodicity, the remainder `R_ε` has vanishing measure (it lies
in the `εk`-neighbourhood of `ℝᴺ ∖ A`) (Step 4); a diagonal argument in `η` concludes (Step 5).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### Gluing over a finite family of pieces -/

theorem sum_mem_Aff0_fintype {ι : Type*} [Fintype ι] {A : Set (Sp N)} {V : ι → Set (Sp N)}
    (hVo : ∀ i, IsOpen (V i)) (hVA : ∀ i, V i ⊆ A)
    (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVf : ∀ i, volume (A ∩ frontier (V i)) = 0) (hVc : volume (A \ ⋃ i, V i) = 0)
    {f : ι → Sp N → Tgt m} (hf : ∀ i, f i ∈ Aff0 (V i)) : ∑ i, f i ∈ Aff0 A := by
  let e := Fintype.equivFin ι
  have h := zero_add_sum_mem_Aff0 (V := V ∘ e.symm) (fun i => hVo _) (fun i => hVA _)
    (fun i j hij => hVd (e.symm.injective.ne hij)) (fun i => hVf _)
    (by rw [show (⋃ i, (V ∘ e.symm) i) = ⋃ i, V i from e.symm.surjective.iUnion_comp V]
        exact hVc) (φ := f ∘ e.symm) fun i => hf _
  rwa [show (∑ i, (f ∘ e.symm) i) = ∑ i, f i from e.symm.sum_comp f] at h

theorem lintegral_eq_sum_pieces_fintype {ι : Type*} [Fintype ι] {U : Set (Sp N)}
    {V : ι → Set (Sp N)} (hVo : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hVd : Pairwise fun i j => Disjoint (V i) (V j)) (hVc : volume (U \ ⋃ i, V i) = 0)
    (F : Sp N → ℝ≥0∞) : ∫⁻ y in U, F y = ∑ i, ∫⁻ y in V i, F y := by
  have hUV : U =ᵐ[volume] ⋃ i, V i :=
    ae_eq_set.2 ⟨hVc, by rw [sdiff_eq_empty.2 (iUnion_subset hVU), measure_empty]⟩
  rw [setLIntegral_congr hUV, lintegral_iUnion (fun i => (hVo i).measurableSet) hVd,
    tsum_fintype]

/-! ### The grid `εk(z + Y)` -/

/-- The integer point `z` seen in `ℝᴺ`. -/
def zcast (z : Fin N → ℤ) : Sp N := fun i => (z i : ℝ)

/-- The grid cell `s(z + Y)`. -/
def gridCell (s : ℝ) (z : Fin N → ℤ) : Set (Sp N) := cube s (s • zcast z)

theorem gridCell_disjoint {s : ℝ} (hs : 0 < s) {z z' : Fin N → ℤ} (h : z ≠ z') :
    Disjoint (gridCell s z) (gridCell s z') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  refine Set.disjoint_left.2 fun y hy hy' => hi ?_
  have h1 := hy i (mem_univ i)
  have h2 := hy' i (mem_univ i)
  simp only [Pi.smul_apply, zcast, smul_eq_mul, mem_Ioo] at h1 h2
  have h3 : |((z i : ℝ) - z' i)| < 1 := by
    rw [abs_lt]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have h4 : |z i - z' i| < 1 := by exact_mod_cast h3
  exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h4)

theorem closure_cube {s : ℝ} (hs : 0 < s) (c : Sp N) :
    closure (cube s c) = Set.pi univ fun i => Icc (c i - s / 2) (c i + s / 2) := by
  rw [cube, closure_pi_set]
  congr 1; funext i
  exact closure_Ioo (by linarith)

theorem mem_closure_gridCell_round {s : ℝ} (hs : 0 < s) (x : Sp N) :
    x ∈ closure (gridCell s (fun i => round (x i / s))) := by
  rw [gridCell, closure_cube hs]
  intro i _
  simp only [Pi.smul_apply, zcast, smul_eq_mul, mem_Icc]
  have h := abs_sub_round (x i / s)
  rw [abs_le] at h
  have e : x i = s * (x i / s) := by field_simp
  constructor <;> nlinarith [h.1, h.2]

theorem dist_le_of_mem_closure_cube {s : ℝ} (hs : 0 < s) {c x w : Sp N}
    (hx : x ∈ closure (cube s c)) (hw : w ∈ closure (cube s c)) : dist x w ≤ s := by
  rw [closure_cube hs] at hx hw
  refine (dist_pi_le_iff hs.le).2 fun i => ?_
  have h1 := hx i (mem_univ i)
  have h2 := hw i (mem_univ i)
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem finite_gridCells {s : ℝ} (hs : 0 < s) {A : Set (Sp N)} (hA : Bornology.IsBounded A) :
    {z : Fin N → ℤ | closure (gridCell s z) ⊆ A}.Finite := by
  obtain ⟨R, hR⟩ := hA.exists_norm_le
  set M : ℤ := ⌈R / s⌉
  refine (Set.finite_Icc (-fun _ => M) fun _ => M).subset fun z hz => ?_
  have hc : s • zcast z ∈ A := hz (subset_closure (by
    intro i _
    simp only [Pi.smul_apply, mem_Ioo]
    constructor <;> linarith))
  have hn := hR _ hc
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
  · have hi := (norm_le_pi_norm (s • zcast z) i).trans hn
    simp only [Pi.smul_apply, zcast, smul_eq_mul, Real.norm_eq_abs, abs_mul,
      abs_of_pos hs] at hi
    have h1 : |(z i : ℝ)| ≤ R / s := by rw [le_div_iff₀ hs]; linarith
    have h2 : (|z i| : ℝ) ≤ M := h1.trans (Int.le_ceil _)
    have h3 : |z i| ≤ M := by exact_mod_cast h2
    simp only [Pi.neg_apply]
    rw [abs_le] at h3
    omega

/-! ### The competitor on the grid (Steps 2–4 of §7) -/

/-- The rescaled translated copy `x ↦ ε φ(x/ε - κz)` of the cell corrector. -/
noncomputable def cellCopy (φ : Sp N → Tgt m) (ε κ : ℝ) (z : Fin N → ℤ) (x : Sp N) : Tgt m :=
  (ε⁻¹)⁻¹ • φ (ε⁻¹ • x + -(κ • zcast z))

theorem cube_eq_preimage_add (κ : ℝ) (a : Sp N) :
    cube κ a = (· + -a) ⁻¹' cube κ (0 : Sp N) := by
  have h := cube_add κ 0 a
  rw [zero_add] at h
  rw [h]; rfl

theorem preimage_inv_smul_cube {ε : ℝ} (hε : 0 < ε) (κ : ℝ) (z : Fin N → ℤ) :
    (ε⁻¹ • ·) ⁻¹' cube κ (κ • zcast z) = gridCell (ε * κ) z := by
  rw [preimage_smul_cube (inv_pos.2 hε), gridCell, inv_inv, div_inv_eq_mul, smul_smul,
    mul_comm κ ε]

theorem cellCopy_mem {φ : Sp N → Tgt m} {κ : ℝ} (hφ : φ ∈ Aff0 (cube κ 0)) {ε : ℝ}
    (hε : 0 < ε) (z : Fin N → ℤ) : cellCopy φ ε κ z ∈ Aff0 (gridCell (ε * κ) z) := by
  have h1 := comp_add_mem_Aff0 hφ (-(κ • zcast z))
  rw [← cube_eq_preimage_add] at h1
  have h2 := Aff0.rescale h1 (inv_ne_zero hε.ne')
  rwa [preimage_inv_smul_cube hε] at h2

theorem fderiv_cellCopy (φ : Sp N → Tgt m) {ε : ℝ} (hε : 0 < ε) (κ : ℝ) (z : Fin N → ℤ)
    (x : Sp N) : fderiv ℝ (cellCopy φ ε κ z) x = fderiv ℝ φ (ε⁻¹ • x + -(κ • zcast z)) := by
  have := fderiv_rescale (fun y => φ (y + -(κ • zcast z))) (inv_ne_zero hε.ne') x
  rw [show cellCopy φ ε κ z = fun x => (ε⁻¹)⁻¹ • (fun y => φ (y + -(κ • zcast z))) (ε⁻¹ • x)
    from rfl, this, fderiv_comp_add_right]

/-- The energy of a cell copy: `∫_{cell} L(x/ε, ξ + ∇c_z) = εᴺ ∫_{κY} L(y, ξ + ∇φ)`. -/
theorem lintegral_cellCopy {L : Sp N → Mat m N → ℝ≥0∞} (hL : IsPeriodic L) (φ : Sp N → Tgt m)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (z : Fin N → ℤ) (ξ : Mat m N) :
    ∫⁻ x in gridCell (ε * ((k : ℝ) + 1)) z,
        L (ε⁻¹ • x) (ξ + fderiv ℝ (cellCopy φ ε ((k : ℝ) + 1) z) x) =
      ENNReal.ofReal (ε ^ N) * ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ξ + fderiv ℝ φ y) := by
  set κ : ℝ := (k : ℝ) + 1
  set a : Sp N := -(κ • zcast z)
  simp_rw [fderiv_cellCopy φ hε κ z]
  rw [← preimage_inv_smul_cube hε κ z]
  have h := setLIntegral_comp_smul (inv_ne_zero hε.ne') (isOpen_cube κ (κ • zcast z)).measurableSet
    (fun y => L y (ξ + fderiv ℝ φ (y + a)))
  rw [h, inv_pow, inv_inv, abs_of_pos (pow_pos hε N)]
  congr 1
  -- translation and periodicity
  have hper : ∀ y, L (y + -a) = L y := by
    intro y
    have e : -a = fun i => ((((k + 1 : ℕ) : ℤ) * z i : ℤ) : ℝ) := by
      ext i; simp [a, κ, zcast]
    rw [e]; exact funext (hL (fun j => ((k + 1 : ℕ) : ℤ) * z j) y)
  have hmp := measurePreserving_add_right (volume : Measure (Sp N)) a
  have hemb : MeasurableEmbedding (fun y : Sp N => y + a) :=
    (MeasurableEquiv.addRight a).measurableEmbedding
  rw [cube_eq_preimage_add κ (κ • zcast z)]
  have h2 := hmp.setLIntegral_comp_preimage_emb hemb
    (fun y' => L (y' + -a) (ξ + fderiv ℝ φ y')) (cube κ 0)
  simp only [add_neg_cancel_right] at h2
  rw [show (· + -(κ • zcast z)) = (· + a) from rfl, h2]
  simp_rw [hper]

/-- **Steps 2–4 of §7**: the competitor `ψ_{η,ε}`. -/
theorem exists_cell_competitor {G : Mat m N → ℝ≥0∞} {β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hL : IsPeriodic L) {ξ : Mat m N} (hLξ : ∀ x, L x ξ ≤ β * (1 + G ξ))
    {A : Set (Sp N)} (hAo : IsOpen A) (hAb : Bornology.IsBounded A) {k : ℕ}
    {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 (cube ((k : ℝ) + 1) 0)) {Mφ : ℝ} (hM : ∀ y, ‖φ y‖ ≤ Mφ)
    {c : ℝ≥0∞} (hI : ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ξ + fderiv ℝ φ y) ≤
      c * ENNReal.ofReal ((k : ℝ) + 1) ^ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Sp N → Tgt m, ψ ∈ Aff0 A ∧ (∀ x, ‖ψ x‖ ≤ ε * Mφ) ∧
      ∫⁻ x in A, L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x) ≤
        volume A * c + β * (1 + G ξ) * volume (A ∩ Metric.cthickening (ε * ((k : ℝ) + 1)) Aᶜ) := by
  classical
  set κ : ℝ := (k : ℝ) + 1
  have hκ : 0 < κ := by positivity
  set s := ε * κ
  have hs : 0 < s := mul_pos hε hκ
  set Λ := (finite_gridCells hs hAb).toFinset
  have hΛ : ∀ z, z ∈ Λ ↔ closure (gridCell s z) ⊆ A := fun z => by simp [Λ]
  let ι := {z // z ∈ Λ}
  set C : ι → Set (Sp N) := fun z => gridCell s z.1
  have hCo : ∀ z, IsOpen (C z) := fun z => isOpen_cube _ _
  have hCA : ∀ z : ι, C z ⊆ A := fun z => subset_closure.trans ((hΛ z.1).1 z.2)
  have hCd : Pairwise fun z z' : ι => Disjoint (C z) (C z') := fun z z' h =>
    gridCell_disjoint hs fun e => h (Subtype.ext e)
  set S := ⋃ z, C z
  have hSo : IsOpen S := isOpen_iUnion hCo
  set T := ⋃ z, frontier (C z)
  have hT : volume T = 0 := measure_iUnion_null fun z => volume_frontier_cube _ _
  have hclS : closure S \ S ⊆ T := by
    rintro y ⟨hy1, hy2⟩
    rw [show S = ⋃ z ∈ (univ : Set ι), C z by simp [S], (finite_univ).closure_biUnion] at hy1
    obtain ⟨z, -, hz⟩ := mem_iUnion₂.1 hy1
    refine mem_iUnion.2 ⟨z, ?_⟩
    rw [(hCo z).frontier_eq]
    exact ⟨hz, fun h => hy2 (mem_iUnion.2 ⟨z, h⟩)⟩
  set R := A \ closure S
  have hRo : IsOpen R := hAo.sdiff isClosed_closure
  -- the pieces: `R` and the cells
  let V : Option ι → Set (Sp N) := fun o => o.elim R C
  have hVo : ∀ o, IsOpen (V o) := fun o => by cases o <;> simp [V, hRo, hCo]
  have hVA : ∀ o, V o ⊆ A := fun o => by cases o <;> simp [V, R, hCA]
  have hVd : Pairwise fun o o' => Disjoint (V o) (V o') := by
    rintro (_ | z) (_ | z') h
    · exact absurd rfl h
    · exact Set.disjoint_left.2 fun y hy hy' =>
        hy.2 (subset_closure (mem_iUnion.2 ⟨z', hy'⟩))
    · exact Set.disjoint_left.2 fun y hy hy' =>
        hy'.2 (subset_closure (mem_iUnion.2 ⟨z, hy⟩))
    · exact hCd fun e => h (by rw [e])
  have hVf : ∀ o, volume (A ∩ frontier (V o)) = 0 := by
    rintro (_ | z)
    · refine measure_mono_null (fun y hy => ?_) hT
      obtain ⟨hyA, hyf⟩ := hy
      have h := frontier_inter_subset A (closure S)ᶜ hyf
      rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · have h3 : y ∈ A ∩ frontier A := ⟨hyA, h1⟩
        rw [hAo.inter_frontier_eq] at h3
        exact absurd h3 (notMem_empty y)
      · rw [frontier_compl] at h2
        refine hclS ⟨frontier_subset_closure (frontier_closure_subset h2), fun hyS => ?_⟩
        have := frontier_closure_subset h2
        rw [hSo.frontier_eq] at this
        exact this.2 hyS
    · exact measure_mono_null inter_subset_right (volume_frontier_cube _ _)
  have hVc : volume (A \ ⋃ o, V o) = 0 := by
    refine measure_mono_null (fun y hy => hclS ⟨by_contra fun h => hy.2 (mem_iUnion.2
      ⟨none, hy.1, h⟩), fun hS => hy.2 ?_⟩) hT
    obtain ⟨z, hz⟩ := mem_iUnion.1 hS
    exact mem_iUnion.2 ⟨some z, hz⟩
  -- the functions
  set f : Option ι → Sp N → Tgt m := fun o => o.elim 0 fun z => cellCopy φ ε κ z.1
  have hfA : ∀ o, f o ∈ Aff0 (V o) := by
    rintro (_ | z)
    · exact zero_mem_Aff0 hRo
    · exact cellCopy_mem hφ hε z.1
  have hf0 : ∀ o, ∀ y ∉ V o, f o y = 0 := fun o => (Aff0.data (hfA o)).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.1
  set ψ := ∑ o, f o
  have hψloc : ∀ o, ∀ y ∈ V o, ψ =ᶠ[𝓝 y] f o := by
    intro o y hy
    filter_upwards [(hVo o).mem_nhds hy] with x hx
    simp only [ψ, Finset.sum_apply]
    exact Finset.sum_eq_single o (fun o' _ ho' => hf0 o' x fun h => (hVd ho').le_bot ⟨h, hx⟩)
      (by simp)
  refine ⟨ψ, sum_mem_Aff0_fintype hVo hVA hVd hVf hVc hfA, fun x => ?_, ?_⟩
  · -- the uniform bound `‖ψ‖ ≤ ε M`
    by_cases hx : ∃ o, x ∈ V o
    · obtain ⟨o, ho⟩ := hx
      rw [(hψloc o x ho).eq_of_nhds]
      rcases o with _ | z
      · simp only [f, Option.elim, Pi.zero_apply, norm_zero]
        exact mul_nonneg hε.le ((norm_nonneg _).trans (hM 0))
      · simp only [f, Option.elim, cellCopy, inv_inv, norm_smul, Real.norm_eq_abs,
          abs_of_pos hε]
        exact mul_le_mul_of_nonneg_left (hM _) hε.le
    · push Not at hx
      have : ψ x = 0 := by
        simp only [ψ, Finset.sum_apply]
        exact Finset.sum_eq_zero fun o _ => hf0 o x (hx o)
      rw [this, norm_zero]
      exact mul_nonneg hε.le ((norm_nonneg _).trans (hM 0))
  · -- the energy estimate
    rw [lintegral_eq_sum_pieces_fintype hVo hVA hVd hVc, Fintype.sum_option]
    have hR : ∫⁻ x in V none, L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x) ≤
        β * (1 + G ξ) * volume (A ∩ Metric.cthickening s Aᶜ) := by
      calc ∫⁻ x in V none, L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x)
          ≤ ∫⁻ x in V none, (β : ℝ≥0∞) * (1 + G ξ) := by
            refine setLIntegral_mono_ae' (hVo none).measurableSet
              (Eventually.of_forall fun x hx => ?_)
            rw [(hψloc none x hx).fderiv_eq]
            simp only [f, Option.elim]
            rw [show fderiv ℝ (0 : Sp N → Tgt m) x = 0 from fderiv_const_apply _, add_zero]
            exact hLξ _
        _ = β * (1 + G ξ) * volume R := setLIntegral_const _ _
        _ ≤ β * (1 + G ξ) * volume (A ∩ Metric.cthickening s Aᶜ) := by
            gcongr
            rintro y ⟨hyA, hyS⟩
            refine ⟨hyA, ?_⟩
            set zr : Fin N → ℤ := fun i => round (y i / s)
            have hy := mem_closure_gridCell_round hs y
            by_cases hcl : closure (gridCell s zr) ⊆ A
            · exact absurd (closure_mono (subset_iUnion C ⟨zr, (hΛ zr).2 hcl⟩) hy) hyS
            · obtain ⟨w, hw, hwA⟩ := not_subset.1 hcl
              exact Metric.mem_cthickening_of_dist_le y w s Aᶜ hwA
                (dist_le_of_mem_closure_cube hs hy hw)
    have hcells : ∑ z : ι, ∫⁻ x in V (some z), L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x) ≤ volume A * c := by
      have heq : ∀ z : ι, ∫⁻ x in V (some z), L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x) =
          ENNReal.ofReal (ε ^ N) * ∫⁻ y in cube κ 0, L y (ξ + fderiv ℝ φ y) := by
        intro z
        rw [← lintegral_cellCopy hL φ hε k z.1 ξ]
        refine setLIntegral_congr_fun (hVo (some z)).measurableSet fun x hx => ?_
        rw [(hψloc (some z) x hx).fderiv_eq]
        rfl
      simp_rw [heq]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc (Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal (ε ^ N) *
            ∫⁻ y in cube κ 0, L y (ξ + fderiv ℝ φ y))
          ≤ (Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal (ε ^ N) * (c * ENNReal.ofReal κ ^ N)) := by
            gcongr
        _ = c * volume S := by
            rw [measure_iUnion hCd fun z => (hCo z).measurableSet, tsum_fintype]
            simp only [C, gridCell, volume_cube, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [ENNReal.ofReal_mul hε.le, mul_pow, ENNReal.ofReal_pow hε.le]
            ring
        _ ≤ c * volume A := by gcongr; exact iUnion_subset hCA
        _ = volume A * c := mul_comm _ _
    calc (∫⁻ x in V none, L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x)) +
          ∑ z : ι, ∫⁻ x in V (some z), L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x)
        ≤ β * (1 + G ξ) * volume (A ∩ Metric.cthickening s Aᶜ) + volume A * c :=
          add_le_add hR hcells
      _ = _ := add_comm _ _

/-! ### Proposition `prop:densityHaff` -/

/-- **Proposition `prop:densityHaff`**, as in the article: no measurability is assumed on `L`
(the integrals are lower Lebesgue integrals). -/
theorem densityHaff_of_any (G : Mat m N → ℝ≥0∞) (α β : ℝ≥0) (L : Sp N → Mat m N → ℝ≥0∞)
    (hG : ConvexENN G) (hα : 0 < α) (hLper : IsPeriodic L) (hLgr : HasGGrowth G α β L)
    (A : Set (Sp N)) (hAo : IsOpen A) (hAb : Bornology.IsBounded A) (ξ : Mat m N) :
    ∃ ψ : ℝ → Sp N → Tgt m, (∀ ε, ψ ε ∈ Aff0 A) ∧ UnifSmall (𝓝[>] 0) ψ ∧
      limsup (fun ε => ∫⁻ x in A, L (ε⁻¹ • x) (ξ + fderiv ℝ (ψ ε) x)) (𝓝[>] 0) ≤
        volume A * Haff L ξ := by
  classical
  set H := Haff L ξ
  have hzero : (0 : Sp N → Tgt m) ∈ Aff0 A := zero_mem_Aff0 hAo
  have hsmall0 : UnifSmall (𝓝[>] (0 : ℝ)) fun _ : ℝ => (0 : Sp N → Tgt m) :=
    fun δ hδ => Eventually.of_forall fun _ y => by simp [hδ.le]
  by_cases hA0 : volume A = 0
  · refine ⟨fun _ => 0, fun _ => hzero, hsmall0, ?_⟩
    exact (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun ε =>
      (setLIntegral_measure_zero _ _ hA0).le)).trans zero_le
  by_cases hH : H = ⊤
  · refine ⟨fun _ => 0, fun _ => hzero, hsmall0, ?_⟩
    rw [hH, ENNReal.mul_top hA0]; exact le_top
  have hHt : H < ⊤ := lt_top_iff_ne_top.2 hH
  have hAt : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  have hGξ : G ξ < ⊤ := by
    have h := ((hLgr.Haff hG) 0 ξ).1
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top (by simpa using hα.ne')] at h
    exact hH (top_le_iff.1 h)
  have hLξ : ∀ x, L x ξ ≤ β * (1 + G ξ) := fun x => (hLgr x ξ).2
  set ηs : ℕ → ℝ≥0∞ := fun j => ((j : ℝ≥0∞) + 1)⁻¹
  have hηs : ∀ j, 0 < ηs j := fun j => ENNReal.inv_pos.2 (by simp)
  -- Step 1: near-optimal cell correctors
  have hstep1 : ∀ j, ∃ k : ℕ, ∃ φ ∈ (Aff0 (cube ((k : ℝ) + 1) 0) : Set (Sp N → Tgt m)),
      ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ξ + fderiv ℝ φ y) ≤
        (H + ηs j) * ENNReal.ofReal ((k : ℝ) + 1) ^ N := by
    intro j
    have hlt : H < H + ηs j := ENNReal.lt_add_right hH (hηs j).ne'
    obtain ⟨k, hk⟩ := iInf_lt_iff.1 hlt
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [ENNReal.div_lt_iff (Or.inl (volume_cube_pos hk1 0).ne')
      (Or.inl (volume_cube_ne_top _ 0))] at hk
    obtain ⟨φ, hφ, hlt'⟩ : ∃ φ ∈ (Aff0 (cube ((k : ℝ) + 1) 0) : Set (Sp N → Tgt m)),
        ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ξ + fderiv ℝ φ y) <
          (H + ηs j) * volume (cube ((k : ℝ) + 1) (0 : Sp N)) := by
      simpa [Yt, iInf_lt_iff] using hk
    exact ⟨k, φ, hφ, by rw [← volume_cube]; exact hlt'.le⟩
  choose kk φs hφs hI using hstep1
  have hMφ : ∀ j, ∃ M, ∀ y, ‖φs j y‖ ≤ M := fun j => by
    obtain ⟨⟨K, hK⟩, h0, -⟩ := hφs j
    have hcs : HasCompactSupport (φs j) :=
      HasCompactSupport.intro (isBounded_cube _ 0).isCompact_closure
        fun y hy => h0 y fun h => hy (subset_closure h)
    exact hK.continuous.bounded_above_of_compact_support hcs
  choose Ms hMs using hMφ
  -- Steps 2–4
  have hcomp : ∀ (j : ℕ) (ε : ℝ), ∃ ψ : Sp N → Tgt m, ψ ∈ Aff0 A ∧ (0 < ε →
      (∀ x, ‖ψ x‖ ≤ ε * Ms j) ∧ ∫⁻ x in A, L (ε⁻¹ • x) (ξ + fderiv ℝ ψ x) ≤
        volume A * (H + ηs j) +
          β * (1 + G ξ) * volume (A ∩ Metric.cthickening (ε * ((kk j : ℝ) + 1)) Aᶜ)) := by
    intro j ε
    by_cases hε : 0 < ε
    · obtain ⟨ψ, h1, h2, h3⟩ :=
        exists_cell_competitor hLper hLξ hAo hAb (hφs j) (hMs j) (hI j) hε
      exact ⟨ψ, h1, fun _ => ⟨h2, h3⟩⟩
    · exact ⟨0, hzero, fun h => absurd h hε⟩
  choose ψs hψA hψb using hcomp
  -- the boundary layer has vanishing measure
  have hlayer : ∀ j, Tendsto (fun ε : ℝ =>
      volume (A ∩ Metric.cthickening (ε * ((kk j : ℝ) + 1)) Aᶜ)) (𝓝[>] 0) (𝓝 0) := by
    intro j
    have : IsFiniteMeasure (volume.restrict A) :=
      isFiniteMeasure_restrict.2 hAt
    have h := tendsto_measure_cthickening_of_isClosed (μ := volume.restrict A) (s := Aᶜ)
      ⟨1, one_pos, measure_ne_top _ _⟩ hAo.isClosed_compl
    rw [Measure.restrict_apply' hAo.measurableSet, compl_inter_self, measure_empty] at h
    have hr : Tendsto (fun ε : ℝ => ε * ((kk j : ℝ) + 1)) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_mul_const ((kk j : ℝ) + 1)).tendsto (0 : ℝ)
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine (h.comp hr).congr fun ε => ?_
    simp only [Function.comp]
    rw [Measure.restrict_apply' hAo.measurableSet, inter_comm]
  -- Step 5: diagonal argument in `η`
  let P : ℕ → ℝ → Prop := fun j ε => (∀ x, ‖ψs j ε x‖ ≤ 1 / ((j : ℝ) + 1)) ∧
    ∫⁻ x in A, L (ε⁻¹ • x) (ξ + fderiv ℝ (ψs j ε) x) ≤ volume A * (H + ηs j) + ηs j
  have hP : ∀ j, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P j ε := by
    intro j
    have hsm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * Ms j ≤ 1 / ((j : ℝ) + 1) := by
      have := (continuous_mul_const (Ms j)).tendsto (0 : ℝ)
      rw [zero_mul] at this
      exact ((this.mono_left nhdsWithin_le_nhds).eventually_lt_const
        (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))).mono fun _ h => h.le
    have hc : (β : ℝ≥0∞) * (1 + G ξ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hGξ.ne⟩)
    have hlay : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (β : ℝ≥0∞) * (1 + G ξ) *
        volume (A ∩ Metric.cthickening (ε * ((kk j : ℝ) + 1)) Aᶜ) ≤ ηs j := by
      have h := ENNReal.Tendsto.const_mul (hlayer j) (Or.inr hc)
      rw [mul_zero] at h
      exact (h.eventually_lt_const (hηs j)).mono fun _ h => h.le
    filter_upwards [self_mem_nhdsWithin, hsm, hlay] with ε hε h1 h2
    obtain ⟨hb, hE⟩ := hψb j ε hε
    exact ⟨fun x => (hb x).trans h1, hE.trans (add_le_add le_rfl h2)⟩
  obtain ⟨κ, hκ, hPκ⟩ := exists_diagonal_nhdsGT P hP
  refine ⟨fun ε => ψs (κ ε) ε, fun ε => hψA _ ε, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hδ
    filter_upwards [hPκ, hκ.eventually_ge_atTop J] with ε hε hJε y
    refine (hε.1 y).trans (le_trans ?_ hJ.le)
    gcongr
  · have hη0 : Tendsto (fun ε => ηs (κ ε)) (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      have h' : Tendsto ηs atTop (𝓝 0) := h.congr fun k => by simp [ηs, Function.comp]
      exact h'.comp hκ
    have hlim : Tendsto (fun ε => volume A * (H + ηs (κ ε)) + ηs (κ ε)) (𝓝[>] 0)
        (𝓝 (volume A * (H + 0) + 0)) :=
      (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hη0) (Or.inr hAt)).add hη0
    rw [add_zero, add_zero] at hlim
    exact (limsup_le_limsup (hPκ.mono fun ε h => h.2)).trans hlim.limsup_eq.le


/-- **Proposition `prop:densityHaff`**, in the form `DensityHaff` used by the main theorem (the
measurability hypothesis of `DensityHaff` is not used). -/
theorem densityHaff : DensityHaff N m :=
  fun G α β L hG hα _ hLper hLgr A hAo hAb ξ =>
    densityHaff_of_any G α β L hG hα hLper hLgr A hAo hAb ξ

/-- **Theorem `main-Ggrowth`, with Steps 3, 4 and Proposition `prop:densityHaff` formalized.**
The only remaining hypotheses are the results cited from other papers. -/
theorem main_Ggrowth_formalized [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (N : ℝ) < p) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} (hW : Hypotheses p G W)
    (hAHM : CitedAHM14 N m p) (hApprox : CitedAffineApprox N m p)
    (hLip : CitedZaffLocLip N m) (hZ : CitedDensityZaff N m) (hV : CitedVitaliEnvelope N) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W) (intHom (Whom p W)) :=
  main_Ggrowth_of_cited p hp hΩ hW hAHM hApprox hLip hZ hV densityHaff

end Homogenization
