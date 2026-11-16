import Homogenization.DensityZaff

/-!
# `𝒵_aff L` is finite everywhere (Lemma `lemmaree`)

Formalization of Lemma `lemmaree` of `Homogenization_beyond_convex_growthV1.tex`: if `N ≤ m` and
`L : 𝕄^{m×N} → [0,∞]` is finite at every matrix of rank `N`, then `𝒵_aff L` is finite everywhere
(`lemmaree`).

* `polyPyramid_mem_Aff0`: the pyramid `φ = (1 - ∑ wᵢ|xᵢ|)⁺ a` on the cross-polytope
  `D_w = {∑ wᵢ|xᵢ| < 1}` belongs to `Aff₀(D_w)`, with gradient `c_σ ⊗ a` on each of the `2ᴺ`
  sectors (`volume_frontier_polyDom`: `|∂D_w| = 0`).
* `exists_polyWeights`: for `e ≠ 0` the weights can be chosen with `⟨c_σ, e⟩ ≠ 0` for all `σ`
  (the explicit choice of the paper: weight `1` at a coordinate where `|e_j|` is maximal).
* `Zaff_ne_top_of_pyramid`: finiteness of `𝒵_aff L` at the `2ᴺ` matrices `ξ + c_σ ⊗ a` gives
  finiteness at `ξ`. The paper argues directly with near-optimal correctors on each sector; here
  the idempotence `Zaff_Zaff` and the domain independence `Zaff_le_normalized_Yt` are applied to
  `𝒵_aff L`, which is legitimate because neither requires measurability.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- Level sets of a nonzero linear form are Lebesgue-null. -/
theorem volume_setOf_eq_null {f : Sp N →L[ℝ] ℝ} (hf : f ≠ 0) (c : ℝ) :
    volume {x : Sp N | f x = c} = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext h)
  set p : Sp N := (c / f v) • v
  have hp : f p = c := by simp [p, map_smul, div_mul_cancel₀ _ hv]
  have hker : (LinearMap.ker (f : Sp N →ₗ[ℝ] ℝ)) ≠ ⊤ := by
    intro h
    exact hv (LinearMap.mem_ker.1 (h ▸ Submodule.mem_top))
  have h0 := Measure.addHaar_submodule volume _ hker
  have e : {x : Sp N | f x = c} = (· + -p) ⁻¹' (LinearMap.ker (f : Sp N →ₗ[ℝ] ℝ) : Set (Sp N)) := by
    ext x
    simp [hp, sub_eq_zero, ← sub_eq_add_neg]
  rw [e, measure_preimage_add_right]
  exact h0

/-! ### The cross-polytope and its pyramid -/

/-- `±1` from a sign bit. -/
def sgnB (b : Bool) : ℝ := if b then 1 else -1

theorem sgnB_ne_zero (b : Bool) : sgnB b ≠ 0 := by cases b <;> simp [sgnB]

theorem sgnB_mul_self (b : Bool) : sgnB b * sgnB b = 1 := by cases b <;> simp [sgnB]

theorem abs_eq_sgnB_mul {b : Bool} {r : ℝ} (h : 0 ≤ sgnB b * r) : |r| = sgnB b * r := by
  cases b
  · simp only [sgnB, Bool.false_eq_true, if_false] at h ⊢
    rw [abs_of_nonpos (by linarith)]
    ring
  · simp only [sgnB, if_true] at h ⊢
    rw [abs_of_nonneg (by linarith)]
    ring

/-- `ψ_w(x) = 1 - ∑ᵢ wᵢ |xᵢ|`. -/
def polyFun (w : Fin N → ℝ) (x : Sp N) : ℝ := 1 - ∑ i, w i * |x i|

/-- The cross-polytope `D_w = {ψ_w > 0}`. -/
def polyDom (w : Fin N → ℝ) : Set (Sp N) := {x | 0 < polyFun w x}

/-- The sector `D_w^σ = {x ∈ D_w : σᵢ xᵢ > 0 for all i}`. -/
def polySector (w : Fin N → ℝ) (σ : Fin N → Bool) : Set (Sp N) :=
  {x | 0 < polyFun w x ∧ ∀ i, 0 < sgnB (σ i) * x i}

/-- The gradient `c_σ = -(σᵢ wᵢ)ᵢ` of `ψ_w` on `D_w^σ`. -/
noncomputable def polyGrad (w : Fin N → ℝ) (σ : Fin N → Bool) : Sp N →L[ℝ] ℝ :=
  ∑ i, (-(sgnB (σ i) * w i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i

theorem polyGrad_apply (w : Fin N → ℝ) (σ : Fin N → Bool) (x : Sp N) :
    polyGrad w σ x = -∑ i, sgnB (σ i) * w i * x i := by
  simp [polyGrad, ← Finset.sum_neg_distrib]

/-- The pyramid `φ = ψ_w⁺ a`. -/
noncomputable def polyPyramid (w : Fin N → ℝ) (a : Tgt m) (x : Sp N) : Tgt m :=
  max (polyFun w x) 0 • a

theorem continuous_polyFun (w : Fin N → ℝ) : Continuous (polyFun w) :=
  continuous_const.sub (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_apply i).abs)

theorem isOpen_polyDom (w : Fin N → ℝ) : IsOpen (polyDom (N := N) w) :=
  isOpen_lt continuous_const (continuous_polyFun w)

theorem isOpen_polySector (w : Fin N → ℝ) (σ : Fin N → Bool) :
    IsOpen (polySector (N := N) w σ) := by
  have : polySector w σ = polyDom w ∩ ⋂ i, {x : Sp N | 0 < sgnB (σ i) * x i} := by
    ext x; simp [polySector, polyDom]
  rw [this]
  exact (isOpen_polyDom w).inter (isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_const.mul (continuous_apply i)))

theorem zero_mem_polyDom (w : Fin N → ℝ) : (0 : Sp N) ∈ polyDom w := by
  simp [polyDom, polyFun]

theorem polyFun_eq_on_sector {w : Fin N → ℝ} {σ : Fin N → Bool} {x : Sp N}
    (hx : ∀ i, 0 < sgnB (σ i) * x i) : polyFun w x = 1 + polyGrad w σ x := by
  rw [polyGrad_apply, polyFun, sub_eq_add_neg]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  have : |x i| = sgnB (σ i) * x i := abs_eq_sgnB_mul (hx i).le
  rw [this]; ring

theorem isBounded_polyDom {w : Fin N → ℝ} (hw : ∀ i, 0 < w i) :
    Bornology.IsBounded (polyDom (N := N) w) := by
  refine (Metric.isBounded_closedBall (x := (0 : Sp N)) (r := ∑ i, (w i)⁻¹)).subset ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => (inv_pos.2 (hw i)).le)).2
    fun i => ?_
  have hsum : w i * |x i| ≤ ∑ j, w j * |x j| :=
    Finset.single_le_sum (f := fun j => w j * |x j|)
      (fun j _ => mul_nonneg (hw j).le (abs_nonneg _)) (Finset.mem_univ i)
  have h1 : w i * |x i| < 1 := by
    have : 0 < polyFun w x := hx
    simp only [polyFun] at this
    linarith
  rw [Real.norm_eq_abs]
  calc |x i| = (w i)⁻¹ * (w i * |x i|) := by
        rw [← mul_assoc, inv_mul_cancel₀ (hw i).ne', one_mul]
    _ ≤ (w i)⁻¹ * 1 := by have := hw i; gcongr
    _ = (w i)⁻¹ := mul_one _
    _ ≤ ∑ j, (w j)⁻¹ := Finset.single_le_sum (f := fun j => (w j)⁻¹)
        (fun j _ => (inv_pos.2 (hw j)).le) (Finset.mem_univ i)

theorem proj_ne_zero (i : Fin N) :
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i ≠ 0 := by
  intro h
  have := congrArg (fun f => f (Pi.single i 1)) h
  simp at this

/-- The coordinate hyperplanes are null. -/
theorem volume_coordHyperplanes : volume (⋃ i, {x : Sp N | x i = 0}) = 0 :=
  measure_iUnion_null fun i => volume_setOf_eq_null (proj_ne_zero i) 0

theorem polySector_subset (w : Fin N → ℝ) (σ : Fin N → Bool) :
    polySector (N := N) w σ ⊆ polyDom w := fun _ hx => hx.1

theorem disjoint_polySector (w : Fin N → ℝ) {σ τ : Fin N → Bool} (h : σ ≠ τ) :
    Disjoint (polySector (N := N) w σ) (polySector w τ) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have h1 := hx.2 i
  have h2 := hx'.2 i
  cases hσ : σ i <;> cases hτ : τ i <;> simp only [hσ, hτ, sgnB] at h1 h2 hi <;>
    simp at hi h1 h2 <;> linarith

/-- Off the coordinate hyperplanes, the sectors cover `D_w`. -/
theorem polyDom_diff_subset (w : Fin N → ℝ) :
    polyDom (N := N) w \ ⋃ σ, polySector w σ ⊆ ⋃ i, {x : Sp N | x i = 0} := by
  intro x ⟨hx, hxσ⟩
  by_contra h
  simp only [mem_iUnion, mem_ofPred_eq, not_exists] at h
  refine hxσ (mem_iUnion.2 ⟨fun i => decide (0 < x i), hx, fun i => ?_⟩)
  by_cases hp : 0 < x i
  · simp [hp, sgnB]
  · have hn : x i < 0 := lt_of_le_of_ne (not_lt.1 hp) (h i)
    simp [hp, sgnB, hn]

theorem polyDom_inter_frontier_sector_subset (w : Fin N → ℝ) (σ : Fin N → Bool) :
    polyDom (N := N) w ∩ frontier (polySector w σ) ⊆ ⋃ i, {x : Sp N | x i = 0} := by
  rintro x ⟨hxD, hxF⟩
  rw [(isOpen_polySector w σ).frontier_eq] at hxF
  obtain ⟨hcl, hnot⟩ := hxF
  have hcl' : ∀ i, 0 ≤ sgnB (σ i) * x i := by
    have hsub : polySector (N := N) w σ ⊆ {x | ∀ i, 0 ≤ sgnB (σ i) * x i} :=
      fun y hy i => (hy.2 i).le
    have hclosed : IsClosed {x : Sp N | ∀ i, 0 ≤ sgnB (σ i) * x i} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i =>
        isClosed_le continuous_const (continuous_const.mul (continuous_apply i))
    exact closure_minimal hsub hclosed hcl
  have : ¬ ∀ i, 0 < sgnB (σ i) * x i := fun h => hnot ⟨hxD, h⟩
  push Not at this
  obtain ⟨i, hi⟩ := this
  refine mem_iUnion.2 ⟨i, ?_⟩
  have h0 : sgnB (σ i) * x i = 0 := le_antisymm hi (hcl' i)
  exact (mul_eq_zero.1 h0).resolve_left (sgnB_ne_zero _)

/-- `∂D_w` is null. -/
theorem volume_frontier_polyDom [NeZero N] {w : Fin N → ℝ} (hw : ∀ i, 0 < w i) :
    volume (frontier (polyDom (N := N) w)) = 0 := by
  have hsub : frontier (polyDom (N := N) w) ⊆ ⋃ σ, {x : Sp N | polyGrad w σ x = -1} := by
    intro x hx
    have h0 : polyFun w x = 0 := by
      have := (continuous_polyFun w).frontier_preimage_subset (Ioi 0) hx
      simpa [frontier_Ioi] using this
    refine mem_iUnion.2 ⟨fun i => decide (0 ≤ x i), ?_⟩
    simp only [mem_ofPred_eq, polyGrad_apply, neg_inj]
    have : ∑ i, w i * |x i| = 1 := by simp only [polyFun] at h0; linarith
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_sgnB_mul (b := decide (0 ≤ x i))]
    · ring
    · by_cases hp : 0 ≤ x i
      · simp [hp, sgnB]
      · simp [hp, sgnB]; linarith
  refine measure_mono_null hsub (measure_iUnion_null fun σ => volume_setOf_eq_null ?_ _)
  intro h
  have := congrArg (fun f => f (Pi.single 0 1)) h
  simp only [polyGrad_apply, zero_apply] at this
  rw [Finset.sum_eq_single (0 : Fin N) (fun j _ hj => by simp [hj])
    (by simp)] at this
  simp only [Pi.single_eq_same, mul_one, neg_eq_zero, mul_eq_zero] at this
  exact this.elim (sgnB_ne_zero _) (hw 0).ne'

theorem polyPyramid_eq_zero {w : Fin N → ℝ} (a : Tgt m) {x : Sp N} (hx : x ∉ polyDom w) :
    polyPyramid w a x = 0 := by
  simp only [polyDom, mem_ofPred_eq, not_lt] at hx
  simp [polyPyramid, max_eq_right hx]

theorem polyPyramid_lipschitz {w : Fin N → ℝ} (hw : ∀ i, 0 < w i) (a : Tgt m) :
    LipschitzWith ⟨(∑ i, w i) * ‖a‖, by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (hw i).le
      positivity⟩ (polyPyramid w a) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [polyPyramid, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
  have h1 := abs_max_sub_max_le_abs (polyFun w x) (polyFun w y) 0
  have h2 : |polyFun w x - polyFun w y| ≤ (∑ i, w i) * ‖x - y‖ := by
    simp only [polyFun, sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib, ← mul_sub]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_of_pos (hw i)]
    refine mul_le_mul_of_nonneg_left ?_ (hw i).le
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [abs_sub_comm, ← Real.norm_eq_abs, ← Pi.sub_apply]
    exact norm_le_pi_norm (x - y) i
  calc |max (polyFun w x) 0 - max (polyFun w y) 0| * ‖a‖
      ≤ ((∑ i, w i) * ‖x - y‖) * ‖a‖ := by gcongr; exact h1.trans h2
    _ = (∑ i, w i) * ‖a‖ * ‖x - y‖ := by ring

theorem polyPyramid_hasFDerivAt (w : Fin N → ℝ) (σ : Fin N → Bool) (a : Tgt m) {y : Sp N}
    (hy : y ∈ polySector w σ) :
    HasFDerivAt (polyPyramid w a) ((polyGrad w σ).smulRight a) y := by
  have hlin : HasFDerivAt (fun x : Sp N => (1 + polyGrad w σ x) • a)
      ((polyGrad w σ).smulRight a) y := by
    have := ((hasFDerivAt_const (1 : ℝ) y).add (polyGrad w σ).hasFDerivAt).smul_const a
    simpa using this
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_polySector w σ).mem_nhds hy] with x hx
  simp only [polyPyramid]
  rw [max_eq_left hx.1.le, polyFun_eq_on_sector hx.2]

/-- The pyramid belongs to `Aff₀(D_w)`, with gradient `c_σ ⊗ a` on each sector. -/
theorem polyPyramid_mem_Aff0 {w : Fin N → ℝ} (hw : ∀ i, 0 < w i) (a : Tgt m) :
    polyPyramid w a ∈ Aff0 (polyDom (N := N) w) := by
  classical
  set e := Fintype.equivFin (Fin N → Bool)
  refine ⟨⟨_, polyPyramid_lipschitz hw a⟩, fun y hy => polyPyramid_eq_zero a hy,
    ⟨_, (polyPyramid_lipschitz hw a).lipschitzOnWith⟩, Fintype.card (Fin N → Bool),
    fun k => polySector w (e.symm k), fun k => (polyGrad w (e.symm k)).smulRight a,
    fun k => isOpen_polySector w _, fun k => polySector_subset w _, ?_, fun k => ?_, ?_,
    fun k y hy => polyPyramid_hasFDerivAt w _ a hy⟩
  · intro k l hkl
    exact disjoint_polySector w (fun h => hkl (e.symm.injective h))
  · exact measure_mono_null (polyDom_inter_frontier_sector_subset w _) volume_coordHyperplanes
  · refine measure_mono_null (fun x hx => polyDom_diff_subset w ⟨hx.1, fun h => hx.2 ?_⟩)
      volume_coordHyperplanes
    obtain ⟨σ, hσ⟩ := mem_iUnion.1 h
    exact mem_iUnion.2 ⟨e σ, by simpa using hσ⟩

/-! ### Generic weights -/

/-- For `e ≠ 0` there are weights `w > 0` with `⟨c_σ, e⟩ ≠ 0` for every sector `σ`: take
`w_j = 1` at a coordinate where `|e_j|` is maximal and `w_i = 1/(N+1)` elsewhere. -/
theorem exists_polyWeights {e : Sp N} (he : e ≠ 0) :
    ∃ w : Fin N → ℝ, (∀ i, 0 < w i) ∧ ∀ σ, polyGrad w σ e ≠ 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, e k ≠ 0 := by
    by_contra h
    push Not at h
    exact he (funext h)
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |e i|) ⟨k, Finset.mem_univ k⟩
  have hej : 0 < |e j| := (abs_pos.2 hk).trans_le (hj k (Finset.mem_univ k))
  set δ : ℝ := 1 / ((N : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  refine ⟨fun i => if i = j then 1 else δ, fun i => by dsimp only; split_ifs <;> positivity,
    fun σ => ?_⟩
  rw [polyGrad_apply, neg_ne_zero]
  set f : Fin N → ℝ := fun i => sgnB (σ i) * (if i = j then 1 else δ) * e i
  change ∑ i, f i ≠ 0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hfj : |f j| = |e j| := by
    simp only [f]
    cases σ j <;> simp [sgnB]
  have hrest : |∑ i ∈ Finset.univ.erase j, f i| ≤ N * (δ * |e j|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.univ.erase j, |f i| ≤ ∑ i ∈ Finset.univ.erase j, δ * |e j| := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hij : i ≠ j := Finset.ne_of_mem_erase hi
          simp only [f, if_neg hij, abs_mul, abs_of_pos hδ]
          have : |sgnB (σ i)| = 1 := by cases σ i <;> simp [sgnB]
          rw [this, one_mul]
          exact mul_le_mul_of_nonneg_left (hj i (Finset.mem_univ i)) hδ.le
      _ ≤ ∑ _i : Fin N, δ * |e j| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => by positivity
      _ = N * (δ * |e j|) := by simp
  have hlt : (N : ℝ) * (δ * |e j|) < |e j| := by
    have : (N : ℝ) * δ < 1 := by
      simp only [δ]
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    nlinarith
  intro h0
  have : |f j| = |∑ i ∈ Finset.univ.erase j, f i| := by
    rw [eq_neg_of_add_eq_zero_left h0, abs_neg]
  linarith

/-! ### One rank-one correction -/

/-- `𝒵_aff L(ξ) ≤ |D_w|⁻¹ ∫_{D_w} 𝒵_aff L(ξ + ∇φ)` with `φ` the pyramid (via `Zaff_Zaff` and the
domain independence `Zaff_le_normalized_Yt`, neither of which needs `L` measurable): if
`𝒵_aff L(ξ + c_σ ⊗ a) < ∞` for every sector `σ`, then `𝒵_aff L(ξ) < ∞`. -/
theorem Zaff_ne_top_of_pyramid [NeZero N] (L : Mat m N → ℝ≥0∞) {w : Fin N → ℝ}
    (hw : ∀ i, 0 < w i) (a : Tgt m) (ξ : Mat m N)
    (h : ∀ σ, Zaff L (ξ + (polyGrad w σ).smulRight a) ≠ ⊤) : Zaff L ξ ≠ ⊤ := by
  classical
  set D := polyDom (N := N) w
  have hD := isOpen_polyDom (N := N) w
  have hDb := isBounded_polyDom (N := N) hw
  have hDne : D.Nonempty := ⟨0, zero_mem_polyDom w⟩
  have hDf := volume_frontier_polyDom (N := N) hw
  set M := ∑ σ, Zaff L (ξ + (polyGrad w σ).smulRight a)
  have hM : M ≠ ⊤ := ENNReal.sum_ne_top.2 fun σ _ => h σ
  have hbound : ∀ᵐ y ∂(volume.restrict D),
      Zaff L (ξ + fderiv ℝ (polyPyramid w a) y) ≤ M := by
    rw [ae_restrict_iff' hD.measurableSet, ae_iff]
    refine measure_mono_null (fun y hy => ?_) volume_coordHyperplanes
    simp only [mem_ofPred_eq, Classical.not_imp] at hy
    obtain ⟨hyD, hyM⟩ := hy
    by_contra hyc
    have hU : y ∈ ⋃ σ, polySector w σ := by
      by_contra hns
      exact hyc (polyDom_diff_subset w ⟨hyD, hns⟩)
    obtain ⟨σ, hσ⟩ := mem_iUnion.1 hU
    apply hyM
    rw [(polyPyramid_hasFDerivAt w σ a hσ).fderiv]
    exact Finset.single_le_sum (f := fun σ => Zaff L (ξ + (polyGrad w σ).smulRight a))
      (fun _ _ => zero_le) (Finset.mem_univ σ)
  have h1 : Zaff L ξ ≤ (volume D)⁻¹ * Yt (fun _ => Zaff L) D ξ := by
    rw [← Zaff_Zaff L ξ]
    exact Zaff_le_normalized_Yt (Zaff L) hD hDb hDne hDf ξ
  have h2 : Yt (fun _ => Zaff L) D ξ ≤ M * volume D := by
    refine (iInf₂_le _ (polyPyramid_mem_Aff0 hw a)).trans ((lintegral_mono_ae hbound).trans ?_)
    rw [setLIntegral_const]
  refine ne_top_of_le_ne_top ?_ (h1.trans (by gcongr : _ ≤ (volume D)⁻¹ * (M * volume D)))
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (volume_pos_of_isOpen_nonempty hD hDne).ne')
    (ENNReal.mul_ne_top hM hDb.measure_lt_top.ne)

/-! ### Lemma `lemmaree` -/

/-- **Lemma `lemmaree`.** Let `N ≤ m` and let `L : 𝕄^{m×N} → [0,∞]` be finite at every matrix of
rank `N` (i.e. with trivial kernel). Then `𝒵_aff L(ξ) < ∞` for every `ξ`.

The paper states the hypothesis as `v(ζ) ≠ 0 ⟹ L(ζ) < ∞` with `v(ζ) = √det(ζᵀζ)`, which is
equivalent to `ker ζ = 0` (`properDomainJacobian_ne_zero_iff`); the paper's form is
`lemmaree_of_jacobian` (`LemmareeJacobian.lean`). The Borel measurability of
`L` assumed in the paper is not needed. The proof is by strong induction on `dim ker ξ`: one
rank-one correction `ξ + c_σ ⊗ a` (with `a ∉ range ξ` and `c_σ` nonzero on `ker ξ`) lowers the
dimension of the kernel, and `Zaff_ne_top_of_pyramid` transfers finiteness. -/
theorem lemmaree (hNm : N ≤ m) (L : Mat m N → ℝ≥0∞)
    (hL : ∀ ζ : Mat m N, LinearMap.ker (ζ : Sp N →ₗ[ℝ] Tgt m) = ⊥ → L ζ ≠ ⊤)
    (ξ : Mat m N) : Zaff L ξ ≠ ⊤ := by
  induction hk : Module.finrank ℝ (LinearMap.ker (ξ : Sp N →ₗ[ℝ] Tgt m))
    using Nat.strong_induction_on generalizing ξ with
  | _ k ih =>
  by_cases hker : LinearMap.ker (ξ : Sp N →ₗ[ℝ] Tgt m) = ⊥
  · exact ne_top_of_le_ne_top (hL ξ hker) (Zaff_le L ξ)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have : NeZero N := ⟨by rintro rfl; exact he0 (Subsingleton.elim _ _)⟩
  have hrange : LinearMap.range (ξ : Sp N →ₗ[ℝ] Tgt m) ≠ ⊤ := by
    intro htop
    have h1 := LinearMap.finrank_range_add_finrank_ker (ξ : Sp N →ₗ[ℝ] Tgt m)
    rw [htop, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
    have h2 : Module.finrank ℝ (LinearMap.ker (ξ : Sp N →ₗ[ℝ] Tgt m)) ≠ 0 :=
      fun h => hker (Submodule.finrank_eq_zero.1 h)
    omega
  obtain ⟨a, -, ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hrange)
  obtain ⟨w, hw, hwe⟩ := exists_polyWeights he0
  refine Zaff_ne_top_of_pyramid L hw a ξ fun σ => ?_
  set ζ : Mat m N := ξ + (polyGrad w σ).smulRight a
  have hlt : LinearMap.ker (ζ : Sp N →ₗ[ℝ] Tgt m) < LinearMap.ker (ξ : Sp N →ₗ[ℝ] Tgt m) := by
    refine lt_of_le_of_ne (fun x hx => ?_) (fun heq => ?_)
    · rw [LinearMap.mem_ker] at hx ⊢
      have hx' : ξ x + polyGrad w σ x • a = 0 := by simpa [ζ] using hx
      by_cases hc : polyGrad w σ x = 0
      · simpa [hc] using hx'
      · exfalso
        refine ha ⟨(-(polyGrad w σ x)⁻¹) • x, ?_⟩
        change ξ ((-(polyGrad w σ x)⁻¹) • x) = a
        rw [map_smul, eq_neg_of_add_eq_zero_left hx', smul_neg, neg_smul, neg_neg, smul_smul,
          inv_mul_cancel₀ hc, one_smul]
    · have hζe : e ∈ LinearMap.ker (ζ : Sp N →ₗ[ℝ] Tgt m) := heq ▸ he
      rw [LinearMap.mem_ker] at hζe he
      have : polyGrad w σ e • a = 0 := by simpa [ζ, he] using hζe
      rcases smul_eq_zero.1 this with h | h
      · exact hwe σ h
      · exact ha (h ▸ Submodule.zero_mem _)
  exact ih _ (hk ▸ Submodule.finrank_lt_finrank_of_lt hlt) ζ rfl

end Homogenization
