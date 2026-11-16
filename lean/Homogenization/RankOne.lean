import Homogenization.DensityZaff

/-!
# The rank-one inequality for the affine cell envelope (Appendix A, step (a))

For `L : 𝕄 → [0,∞]` finite on an open set `V ∋ ξ`, every `t ∈ ]0,1[` and every rank-one
direction `d ⊗ ν`,
`𝒵_aff L(ξ) ≤ t 𝒵_aff L(ξ + (1-t) s d⊗ν) + (1-t) 𝒵_aff L(ξ - t s d⊗ν)`.

The proof differs from the one in Appendix A of the paper in that no corrector is needed: by
`Zaff_Zaff` and `aff0_domainIndependence`, `𝒵_aff L(ξ) ≤ |U|⁻¹ ∫_U 𝒵_aff L(ξ + ∇ψ)` for every
`ψ ∈ Aff₀(U)`, so it suffices to build a laminate `ψ`.

* `U = Φ⁻¹(Y)` is a parallelepiped, where `Φ` is a linear isomorphism whose `j`-th coordinate is
  `x ↦ ν · x`, so that the layers `{a < ν · x < b}` are slabs in the coordinates of `Φ`.
* On each of the `n` layers, `ψ` is a *tent* `max(0, min_i fᵢ) • d` of finitely many affine
  functions: two for the lamination and `2N` for the faces of `U` (`tentVec`). Its pieces are the
  sets where one `fᵢ` is the strict minimum; their boundaries lie in hyperplanes, which are null.
* The phases of gradient `(1-t) D` and `-t D` have total volume at most `t|U|` and `(1-t)|U|`;
  the boundary-layer pieces have volume `O(1/(εn))`, and `L` is finite at the corresponding
  matrices `ξ ± ε D_l` (`ε` small). Letting `n → ∞` gives the inequality.

Consequences: `Zaff_rankOneConvexOn` (rank-one convexity of `𝒵_aff L` on the interior of its
domain) and `citedZaffLocLip`, which removes the hypothesis `CitedZaffLocLip` from the main
theorem (`main_Ggrowth_final_three`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### Affine hyperplanes are null -/

theorem volume_setOf_clm_eq {ℓ : Sp N →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) (a : ℝ) :
    volume {x : Sp N | ℓ x = a} = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext h)
  set w : Sp N := (a / ℓ v) • v with hw_def
  have hw : ℓ w = a := by
    rw [hw_def, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have hset : {x : Sp N | ℓ x = a} =
      (fun x => x + -w) ⁻¹' ((LinearMap.ker (ℓ : Sp N →ₗ[ℝ] ℝ) : Submodule ℝ (Sp N)) :
        Set (Sp N)) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, map_add, map_neg, hw]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  refine Measure.addHaar_submodule volume _ fun htop => hv ?_
  have : v ∈ LinearMap.ker (ℓ : Sp N →ₗ[ℝ] ℝ) := by rw [htop]; exact Submodule.mem_top
  simpa using this

/-! ### Tents: positive parts of minima of finitely many affine functions -/

section Tent

variable {J : Type*} [Fintype J] [Nonempty J]

variable (c : J → ℝ) (ℓ : J → (Sp N →L[ℝ] ℝ))

/-- The affine functions `fᵢ = cᵢ + ℓᵢ`. -/
def tentAff (i : J) (x : Sp N) : ℝ := c i + ℓ i x

/-- The tent `max(0, minᵢ fᵢ)`. -/
noncomputable def tentFun (x : Sp N) : ℝ :=
  max 0 (Finset.univ.inf' Finset.univ_nonempty fun i => tentAff c ℓ i x)

/-- The open polytope `{fᵢ > 0 for all i}`, support of the tent. -/
def tentSet : Set (Sp N) := {x | ∀ i, 0 < tentAff c ℓ i x}

/-- The piece where `fᵢ` is the strict minimum. -/
def tentPiece (i : J) : Set (Sp N) :=
  {x | x ∈ tentSet c ℓ ∧ ∀ l, l ≠ i → tentAff c ℓ i x < tentAff c ℓ l x}

/-- The vector tent `max(0, minᵢ fᵢ) • d`. -/
noncomputable def tentVec (d : Tgt m) (x : Sp N) : Tgt m := tentFun c ℓ x • d

/-- Pairs of distinct indices at which the two affine functions agree. -/
def tentBad (p : J × J) : Set (Sp N) := {x | p.1 ≠ p.2 ∧ tentAff c ℓ p.1 x = tentAff c ℓ p.2 x}

variable {c ℓ}

omit [Fintype J] [Nonempty J] in
theorem continuous_tentAff (i : J) : Continuous (tentAff c ℓ i) :=
  continuous_const.add (ℓ i).continuous

omit [Fintype J] [Nonempty J] in
theorem isOpen_tentSet [Finite J] : IsOpen (tentSet c ℓ) := by
  have := Fintype.ofFinite J
  have : tentSet c ℓ = ⋂ i, {x | 0 < tentAff c ℓ i x} := by ext x; simp [tentSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_tentAff i)

omit [Fintype J] [Nonempty J] in
theorem isOpen_tentPiece [Finite J] (i : J) : IsOpen (tentPiece c ℓ i) := by
  have := Fintype.ofFinite J
  have : tentPiece c ℓ i =
      tentSet c ℓ ∩ ⋂ l, {x | l ≠ i → tentAff c ℓ i x < tentAff c ℓ l x} := by
    ext x; simp [tentPiece]
  rw [this]
  refine isOpen_tentSet.inter (isOpen_iInter_of_finite fun l => ?_)
  by_cases h : l = i
  · simp [h]
  · simpa [h] using isOpen_lt (continuous_tentAff i) (continuous_tentAff l)

omit [Fintype J] [Nonempty J] in
theorem tentPiece_subset (i : J) : tentPiece c ℓ i ⊆ tentSet c ℓ := fun _ hx => hx.1

omit [Fintype J] [Nonempty J] in
theorem tentPiece_disjoint :
    Pairwise fun i l => Disjoint (tentPiece c ℓ i) (tentPiece c ℓ l) := by
  intro i l hil
  refine Set.disjoint_left.2 fun x hi hl => ?_
  have h1 := hi.2 l (Ne.symm hil)
  have h2 := hl.2 i hil
  linarith

theorem inf'_eq_of_mem_tentPiece {i : J} {x : Sp N} (hx : x ∈ tentPiece c ℓ i) :
    Finset.univ.inf' Finset.univ_nonempty (fun l => tentAff c ℓ l x) = tentAff c ℓ i x := by
  refine le_antisymm (Finset.inf'_le _ (Finset.mem_univ i)) (Finset.le_inf' _ _ fun l _ => ?_)
  by_cases h : l = i
  · rw [h]
  · exact (hx.2 l h).le

theorem tentFun_eq_of_mem_tentPiece {i : J} {x : Sp N} (hx : x ∈ tentPiece c ℓ i) :
    tentFun c ℓ x = tentAff c ℓ i x := by
  rw [tentFun, inf'_eq_of_mem_tentPiece hx]
  exact max_eq_right (hx.1 i).le

theorem tentFun_eq_zero {x : Sp N} (hx : x ∉ tentSet c ℓ) : tentFun c ℓ x = 0 := by
  simp only [tentSet, mem_ofPred_eq, not_forall, not_lt] at hx
  obtain ⟨i, hi⟩ := hx
  exact max_eq_left ((Finset.inf'_le _ (Finset.mem_univ i)).trans hi)

theorem tentVec_eq_zero (d : Tgt m) {x : Sp N} (hx : x ∉ tentSet c ℓ) :
    tentVec c ℓ d x = 0 := by
  simp [tentVec, tentFun_eq_zero hx]

theorem hasFDerivAt_tentVec (d : Tgt m) {i : J} {x : Sp N} (hx : x ∈ tentPiece c ℓ i) :
    HasFDerivAt (tentVec c ℓ d) ((ℓ i).smulRight d) x := by
  have hlocal : tentVec c ℓ d =ᶠ[𝓝 x] fun y => (c i + ℓ i y) • d := by
    filter_upwards [(isOpen_tentPiece i).mem_nhds hx] with y hy
    rw [tentVec, tentFun_eq_of_mem_tentPiece hy, tentAff]
  have h := ((hasFDerivAt_const (c i) x).add (ℓ i).hasFDerivAt).smul_const d
  rw [zero_add] at h
  exact h.congr_of_eventuallyEq hlocal

theorem abs_inf'_sub_inf'_le {g g' : J → ℝ} {C : ℝ} (hgg : ∀ i, |g i - g' i| ≤ C) :
    |Finset.univ.inf' Finset.univ_nonempty g - Finset.univ.inf' Finset.univ_nonempty g'| ≤ C := by
  have key : ∀ g g' : J → ℝ, (∀ i, |g i - g' i| ≤ C) →
      Finset.univ.inf' Finset.univ_nonempty g ≤ Finset.univ.inf' Finset.univ_nonempty g' + C := by
    intro g g' hgg
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := J)) g'
    rw [hi]
    exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (by linarith [(abs_le.1 (hgg i)).2])
  rw [abs_le]
  constructor
  · have := key g' g (fun i => by rw [abs_sub_comm]; exact hgg i); linarith
  · have := key g g' hgg; linarith

theorem lipschitzWith_tentFun : LipschitzWith (∑ i, ‖ℓ i‖₊) (tentFun c ℓ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hC : ∀ i, |tentAff c ℓ i x - tentAff c ℓ i y| ≤ (∑ i, ‖ℓ i‖) * dist x y := by
    intro i
    have h1 : tentAff c ℓ i x - tentAff c ℓ i y = ℓ i (x - y) := by
      simp only [tentAff, map_sub]; ring
    rw [h1, ← Real.norm_eq_abs, dist_eq_norm]
    exact ((ℓ i).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i => ‖ℓ i‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)) (norm_nonneg _))
  rw [Real.dist_eq, tentFun, tentFun, max_comm 0, max_comm 0]
  simp only [NNReal.coe_sum, coe_nnnorm]
  exact (abs_max_sub_max_le_abs _ _ _).trans (abs_inf'_sub_inf'_le hC)

theorem lipschitzWith_tentVec (d : Tgt m) :
    LipschitzWith ((∑ i, ‖ℓ i‖₊) * ‖d‖₊) (tentVec c ℓ d) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := (lipschitzWith_tentFun (c := c) (ℓ := ℓ)).dist_le_mul x y
  rw [dist_eq_norm, tentVec, tentVec, ← sub_smul, norm_smul, ← dist_eq_norm]
  push_cast
  calc dist (tentFun c ℓ x) (tentFun c ℓ y) * ‖d‖
      ≤ ((∑ i, ‖ℓ i‖₊ : ℝ≥0) * dist x y) * ‖d‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by push_cast; ring

omit [Fintype J] [Nonempty J] in
theorem volume_tentBad (hℓ : ∀ i l, i ≠ l → ℓ i ≠ ℓ l) (p : J × J) :
    volume (tentBad c ℓ p) = 0 := by
  by_cases hp : p.1 = p.2
  · have : tentBad c ℓ p = ∅ := by ext x; simp [tentBad, hp]
    rw [this, measure_empty]
  · refine measure_mono_null (fun x hx => ?_)
      (volume_setOf_clm_eq (sub_ne_zero.2 (hℓ _ _ hp)) (c p.2 - c p.1))
    simp only [mem_ofPred_eq, sub_apply]
    have := hx.2
    simp only [tentAff] at this
    linarith

omit [Fintype J] [Nonempty J] in
theorem tentSet_inter_frontier_tentPiece_subset [Finite J] (i : J) :
    tentSet c ℓ ∩ frontier (tentPiece c ℓ i) ⊆ ⋃ p, tentBad c ℓ p := by
  have := Fintype.ofFinite J
  rintro x ⟨hxS, hxF⟩
  rw [(isOpen_tentPiece i).frontier_eq] at hxF
  obtain ⟨hxc, hxP⟩ := hxF
  have hcl : closure (tentPiece c ℓ i) ⊆ {x | ∀ l, tentAff c ℓ i x ≤ tentAff c ℓ l x} := by
    apply closure_minimal
    · intro y hy l
      by_cases h : l = i
      · rw [h]
      · exact (hy.2 l h).le
    · have : {x | ∀ l, tentAff c ℓ i x ≤ tentAff c ℓ l x} =
          ⋂ l, {x | tentAff c ℓ i x ≤ tentAff c ℓ l x} := by ext; simp
      rw [this]
      exact isClosed_iInter fun l => isClosed_le (continuous_tentAff i) (continuous_tentAff l)
  have hle := hcl hxc
  simp only [tentPiece, mem_ofPred_eq, not_and, not_forall, not_lt, exists_prop] at hxP
  obtain ⟨l, hl, hli⟩ := hxP hxS
  exact mem_iUnion.2 ⟨(i, l), Ne.symm hl, le_antisymm (hle l) hli⟩

omit [Fintype J] in
theorem tentSet_diff_iUnion_subset [Finite J] :
    tentSet c ℓ \ ⋃ i, tentPiece c ℓ i ⊆ ⋃ p, tentBad c ℓ p := by
  have := Fintype.ofFinite J
  rintro x ⟨hxS, hxU⟩
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_min_image Finset.univ (fun i => tentAff c ℓ i x) Finset.univ_nonempty
  have hxP : x ∉ tentPiece c ℓ i := fun h => hxU (mem_iUnion.2 ⟨i, h⟩)
  simp only [tentPiece, mem_ofPred_eq, not_and, not_forall, not_lt, exists_prop] at hxP
  obtain ⟨l, hl, hli⟩ := hxP hxS
  exact mem_iUnion.2 ⟨(i, l), Ne.symm hl, le_antisymm (hi l (Finset.mem_univ l)) hli⟩

omit [Fintype J] [Nonempty J] in
theorem frontier_tentSet_subset [Finite J] : frontier (tentSet c ℓ) ⊆ ⋃ i, {x | ℓ i x = -c i} := by
  have := Fintype.ofFinite J
  intro x hx
  rw [isOpen_tentSet.frontier_eq] at hx
  obtain ⟨hxc, hxS⟩ := hx
  have hcl : closure (tentSet c ℓ) ⊆ {x | ∀ i, 0 ≤ tentAff c ℓ i x} := by
    apply closure_minimal (fun y hy i => (hy i).le)
    have : {x | ∀ i, 0 ≤ tentAff c ℓ i x} = ⋂ i, {x | 0 ≤ tentAff c ℓ i x} := by ext; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_tentAff i)
  simp only [tentSet, mem_ofPred_eq, not_forall, not_lt] at hxS
  obtain ⟨i, hi⟩ := hxS
  have h0 := hcl hxc i
  refine mem_iUnion.2 ⟨i, ?_⟩
  simp only [mem_ofPred_eq]
  simp only [tentAff] at hi h0
  linarith

omit [Fintype J] [Nonempty J] in
theorem volume_frontier_tentSet [Finite J] (hℓ0 : ∀ i, ℓ i ≠ 0) :
    volume (frontier (tentSet c ℓ)) = 0 := by
  have := Fintype.ofFinite J
  exact
  measure_mono_null frontier_tentSet_subset
    (measure_iUnion_null fun i => volume_setOf_clm_eq (hℓ0 i) _)

/-- A vector tent belongs to `Aff₀` of its support, with pieces `tentPiece`. -/
theorem tentVec_mem_Aff0 (hℓ : ∀ i l, i ≠ l → ℓ i ≠ ℓ l) (d : Tgt m) :
    tentVec c ℓ d ∈ Aff0 (tentSet c ℓ) := by
  have hnull : volume (⋃ p, tentBad c ℓ p) = 0 :=
    measure_iUnion_null fun p => volume_tentBad hℓ p
  refine ⟨⟨_, lipschitzWith_tentVec d⟩, fun x hx => tentVec_eq_zero d hx, ?_⟩
  exact isPWAffine_of_fintype (lipschitzWith_tentVec d).lipschitzOnWith (tentPiece c ℓ)
    (fun i => (ℓ i).smulRight d) isOpen_tentPiece tentPiece_subset tentPiece_disjoint
    (fun i => measure_mono_null (tentSet_inter_frontier_tentPiece_subset i) hnull)
    (measure_mono_null tentSet_diff_iUnion_subset hnull)
    (fun i y hy => hasFDerivAt_tentVec d hy)

/-- The energy of a vector tent is a finite sum over its pieces. -/
theorem lintegral_tentVec (hℓ : ∀ i l, i ≠ l → ℓ i ≠ ℓ l) (d : Tgt m)
    (F : Mat m N → ℝ≥0∞) :
    ∫⁻ y in tentSet c ℓ, F (fderiv ℝ (tentVec c ℓ d) y) =
      ∑ i, F ((ℓ i).smulRight d) * volume (tentPiece c ℓ i) := by
  have hnull : volume (⋃ p, tentBad c ℓ p) = 0 :=
    measure_iUnion_null fun p => volume_tentBad hℓ p
  rw [lintegral_eq_sum_pieces_fintype isOpen_tentPiece tentPiece_subset tentPiece_disjoint
    (measure_mono_null tentSet_diff_iUnion_subset hnull)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setLIntegral_congr_fun (isOpen_tentPiece i).measurableSet
      (g := fun _ => F ((ℓ i).smulRight d))
      fun y hy => by rw [(hasFDerivAt_tentVec d hy).fderiv],
    setLIntegral_const]

end Tent

/-! ### The laminate on a parallelepiped -/

section Laminate

/-- The `l`-th coordinate of `Φ`, as a linear functional. -/
noncomputable def coordFun (Φ : Sp N ≃L[ℝ] Sp N) (l : Fin N) : Sp N →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj l).comp (Φ : Sp N →L[ℝ] Sp N)

@[simp]
theorem coordFun_apply (Φ : Sp N ≃L[ℝ] Sp N) (l : Fin N) (x : Sp N) :
    coordFun Φ l x = Φ x l := rfl

/-- Indices of the affine functions of one layer: `inl true`, `inl false` for the lamination
(gradients `(1-t) ν` and `-t ν`), `inr (l, b)` for the two faces of `U` normal to the `l`-th
coordinate of `Φ`. -/
abbrev LamIdx (N : ℕ) := Bool ⊕ (Fin N × Bool)

/-- Slopes of the affine functions of one layer. -/
def lamCoef (t ε : ℝ) : LamIdx N → ℝ
  | Sum.inl true => 1 - t
  | Sum.inl false => -t
  | Sum.inr (_, true) => -ε
  | Sum.inr (_, false) => ε

/-- Coordinate of `Φ` on which each affine function depends. -/
def lamIdx (j : Fin N) : LamIdx N → Fin N
  | Sum.inl _ => j
  | Sum.inr (l, _) => l

/-- Constant terms of the affine functions of the layer `{a < Φⱼ < a + h}`. -/
noncomputable def lamConst (t ε a h : ℝ) : LamIdx N → ℝ
  | Sum.inl true => -(1 - t) * a
  | Sum.inl false => t * (a + h)
  | Sum.inr _ => ε / 2

/-- Linear parts of the affine functions of one layer. -/
noncomputable def lamLin (Φ : Sp N ≃L[ℝ] Sp N) (j : Fin N) (t ε : ℝ) (i : LamIdx N) :
    Sp N →L[ℝ] ℝ :=
  lamCoef t ε i • coordFun Φ (lamIdx j i)

/-- Left end of the `k`-th layer. -/
noncomputable def slabA (h : ℝ) {n : ℕ} (k : Fin n) : ℝ := -(1 / 2) + ((k : ℕ) : ℝ) * h

/-- The box `Y ∩ {α < yⱼ < β}` (as a product of intervals). -/
def slabPi (j : Fin N) (α β : ℝ) : Set (Sp N) :=
  Set.pi univ fun i => Ioo (if i = j then α else -(1 / 2)) (if i = j then β else 1 / 2)

theorem volume_slabPi (j : Fin N) (α β : ℝ) :
    volume (slabPi j α β) = ENNReal.ofReal (β - α) := by
  rw [slabPi, Real.volume_pi_Ioo,
    Finset.prod_eq_single j (fun i _ hi => by simp only [hi, if_false]; norm_num) (by simp)]
  simp

theorem mem_cube_one_zero_iff {y : Sp N} :
    y ∈ cube 1 0 ↔ ∀ l, -(1 / 2) < y l ∧ y l < 1 / 2 := by
  simp only [cube, Set.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply, zero_sub, zero_add,
    Set.mem_Ioo]

variable {Φ : Sp N ≃L[ℝ] Sp N} {j : Fin N} {t ε : ℝ}

theorem lamAff_apply (a h : ℝ) (i : LamIdx N) (x : Sp N) :
    tentAff (lamConst t ε a h) (lamLin Φ j t ε) i x =
      lamConst t ε a h i + lamCoef t ε i * Φ x (lamIdx j i) := rfl

theorem lamLin_apply_single (i : LamIdx N) (l : Fin N) :
    lamLin Φ j t ε i (Φ.symm (Pi.single l 1)) = if lamIdx j i = l then lamCoef t ε i else 0 := by
  simp only [lamLin, smul_apply, coordFun_apply,
    ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp

theorem lamCoef_ne_zero (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) (i : LamIdx N) :
    lamCoef t ε i ≠ 0 := by
  rcases i with b | ⟨l, b⟩ <;> cases b <;> simp only [lamCoef] <;> intro h <;> linarith

theorem lamLin_ne_zero (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) (i : LamIdx N) :
    lamLin Φ j t ε i ≠ 0 := by
  intro h
  have h1 := congrArg (fun f => f (Φ.symm (Pi.single (lamIdx j i) 1))) h
  simp only [lamLin_apply_single, if_true, zero_apply] at h1
  exact lamCoef_ne_zero ht0 ht1 hε0 i h1

theorem lamLin_injective (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) (hεt : ε < t)
    (hεt' : ε < 1 - t) (i i' : LamIdx N) (hne : i ≠ i') :
    lamLin Φ j t ε i ≠ lamLin Φ j t ε i' := by
  intro h
  have h1 := congrArg (fun f => f (Φ.symm (Pi.single (lamIdx j i) 1))) h
  simp only [lamLin_apply_single, if_true] at h1
  by_cases hidx : lamIdx j i' = lamIdx j i
  · rw [if_pos hidx] at h1
    apply hne
    rcases i with b | ⟨l, b⟩ <;> rcases i' with b' | ⟨l', b'⟩ <;> cases b <;> cases b' <;>
      simp only [lamCoef, lamIdx] at h1 hidx <;>
      first
        | rfl
        | (exfalso; linarith)
        | (subst hidx; rfl)
  · rw [if_neg hidx] at h1
    exact lamCoef_ne_zero ht0 ht1 hε0 i h1

/-- A point of a layer lies in the cube coordinates and in the layer. -/
theorem lamSet_props (ht1 : t < 1) (hε0 : 0 < ε) {a h : ℝ} {x : Sp N}
    (hx : x ∈ tentSet (lamConst t ε a h) (lamLin Φ j t ε)) (ht0 : 0 < t) :
    (∀ l, -(1 / 2) < Φ x l ∧ Φ x l < 1 / 2) ∧ a < Φ x j ∧ Φ x j < a + h := by
  have h1 := hx (Sum.inl true)
  have h2 := hx (Sum.inl false)
  simp only [lamAff_apply, lamConst, lamCoef, lamIdx] at h1 h2
  refine ⟨fun l => ?_, by nlinarith, by nlinarith⟩
  have h3 := hx (Sum.inr (l, true))
  have h4 := hx (Sum.inr (l, false))
  simp only [lamAff_apply, lamConst, lamCoef, lamIdx] at h3 h4
  constructor <;> nlinarith

theorem mem_lamSet (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) {a h : ℝ} {x : Sp N}
    (hcube : ∀ l, -(1 / 2) < Φ x l ∧ Φ x l < 1 / 2) (ha : a < Φ x j) (hb : Φ x j < a + h) :
    x ∈ tentSet (lamConst t ε a h) (lamLin Φ j t ε) := by
  intro i
  rcases i with b | ⟨l, b⟩
  · cases b <;> simp only [lamAff_apply, lamConst, lamCoef, lamIdx] <;> nlinarith
  · have hl := hcube l
    cases b <;> simp only [lamAff_apply, lamConst, lamCoef, lamIdx] <;> nlinarith

/-- The phase of gradient `(1-t) D` lies in `{a < Φⱼ < a + t h}`. -/
theorem lamPiece_true_sub (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) {a h : ℝ} {x : Sp N}
    (hx : x ∈ tentPiece (lamConst t ε a h) (lamLin Φ j t ε) (Sum.inl true)) :
    Φ x ∈ slabPi j a (a + t * h) := by
  obtain ⟨hcube, ha, -⟩ := lamSet_props ht1 hε0 hx.1 ht0
  have h1 := hx.2 (Sum.inl false) (by simp)
  simp only [lamAff_apply, lamConst, lamCoef, lamIdx] at h1
  intro i _
  by_cases hi : i = j
  · subst hi
    simp only [if_true, mem_Ioo]
    exact ⟨ha, by linarith⟩
  · simp only [hi, if_false, mem_Ioo]
    exact hcube i

/-- The phase of gradient `-t D` lies in `{a + t h < Φⱼ < a + h}`. -/
theorem lamPiece_false_sub (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) {a h : ℝ} {x : Sp N}
    (hx : x ∈ tentPiece (lamConst t ε a h) (lamLin Φ j t ε) (Sum.inl false)) :
    Φ x ∈ slabPi j (a + t * h) (a + h) := by
  obtain ⟨hcube, -, hb⟩ := lamSet_props ht1 hε0 hx.1 ht0
  have h1 := hx.2 (Sum.inl true) (by simp)
  simp only [lamAff_apply, lamConst, lamCoef, lamIdx] at h1
  intro i _
  by_cases hi : i = j
  · subst hi
    simp only [if_true, mem_Ioo]
    exact ⟨by linarith, hb⟩
  · simp only [hi, if_false, mem_Ioo]
    exact hcube i

/-- The boundary-layer pieces lie within `h / ε` of a face of `Y`, in the coordinates of `Φ`. -/
theorem lamPiece_face_sub (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) {a h : ℝ} (hh : 0 ≤ h)
    {l : Fin N} {b : Bool} {x : Sp N}
    (hx : x ∈ tentPiece (lamConst t ε a h) (lamLin Φ j t ε) (Sum.inr (l, b))) :
    Φ x ∈ (if b then slabPi l (1 / 2 - h / ε) (1 / 2)
      else slabPi l (-(1 / 2)) (-(1 / 2) + h / ε)) := by
  obtain ⟨hcube, -, -⟩ := lamSet_props ht1 hε0 hx.1 ht0
  have hg := hx.2 (Sum.inl true) (by simp)
  have hh' := hx.2 (Sum.inl false) (by simp)
  have htt : t * (1 - t) * h ≤ h := by nlinarith [sq_nonneg (t - 1 / 2)]
  have e1 := mul_lt_mul_of_pos_left hg ht0
  have e2 := mul_lt_mul_of_pos_left hh' (by linarith : (0 : ℝ) < 1 - t)
  cases b
  · simp only [lamAff_apply, lamConst, lamCoef, lamIdx] at e1 e2
    have key : (1 / 2 + Φ x l) * ε < h := by nlinarith
    have hlt : Φ x l < -(1 / 2) + h / ε := by
      have := (lt_div_iff₀ hε0).2 key
      linarith
    simp only [Bool.false_eq_true, if_false]
    intro i _
    by_cases hi : i = l
    · subst hi
      simp only [if_true, mem_Ioo]
      exact ⟨(hcube i).1, hlt⟩
    · simp only [hi, if_false, mem_Ioo]
      exact hcube i
  · simp only [lamAff_apply, lamConst, lamCoef, lamIdx] at e1 e2
    have key : (1 / 2 - Φ x l) * ε < h := by nlinarith
    have hlt : 1 / 2 - h / ε < Φ x l := by
      have := (lt_div_iff₀ hε0).2 key
      linarith
    simp only [if_true]
    intro i _
    by_cases hi : i = l
    · subst hi
      simp only [if_true, mem_Ioo]
      exact ⟨hlt, (hcube i).2⟩
    · simp only [hi, if_false, mem_Ioo]
      exact hcube i

theorem coordFun_ne_zero (Φ : Sp N ≃L[ℝ] Sp N) (l : Fin N) : coordFun Φ l ≠ 0 := by
  intro h
  have := congrArg (fun f => f (Φ.symm (Pi.single l 1))) h
  simp at this

theorem smulRight_smul_left (c : ℝ) (f : Sp N →L[ℝ] ℝ) (d : Tgt m) :
    (c • f).smulRight d = c • f.smulRight d := by
  ext x i
  simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem smulRight_smul_right (c : ℝ) (f : Sp N →L[ℝ] ℝ) (d : Tgt m) :
    f.smulRight (c • d) = c • f.smulRight d := by
  ext x i
  simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- **The laminate estimate.** For every `n ≥ 1`, with `D = (Φⱼ) ⊗ d`,
`𝒵_aff L(ξ) ≤ t 𝒵_aff L(ξ + (1-t) D) + (1-t) 𝒵_aff L(ξ - t D) + (1/(n ε)) ∑ 𝒵_aff L(ξ + D_p)`,
where the `D_p` are the gradients of the boundary layer. -/
theorem Zaff_le_laminate (L : Mat m N → ℝ≥0∞) (Φ : Sp N ≃L[ℝ] Sp N) (j : Fin N) (d : Tgt m)
    {t ε : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hε0 : 0 < ε) (hεt : ε < t) (hεt' : ε < 1 - t)
    {n : ℕ} (hn : 0 < n) (ξ : Mat m N) :
    Zaff L ξ ≤ ENNReal.ofReal t * Zaff L (ξ + (1 - t) • (coordFun Φ j).smulRight d) +
      ENNReal.ofReal (1 - t) * Zaff L (ξ - t • (coordFun Φ j).smulRight d) +
      ENNReal.ofReal (1 / n / ε) *
        ∑ p : Fin N × Bool, Zaff L (ξ + (lamLin Φ j t ε (Sum.inr p)).smulRight d) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℝ := 1 / n with hh_def
  have hh : 0 < h := by positivity
  have hnh : (n : ℝ) * h = 1 := by rw [hh_def]; field_simp
  set ℓ := lamLin Φ j t ε with hℓ_def
  set c : Fin n → LamIdx N → ℝ := fun k => lamConst t ε (slabA h k) h with hc_def
  set S : Fin n → Set (Sp N) := fun k => tentSet (c k) ℓ with hS_def
  set P : Fin n → LamIdx N → Set (Sp N) := fun k i => tentPiece (c k) ℓ i with hP_def
  set v : Fin n → Sp N → Tgt m := fun k => tentVec (c k) ℓ d with hv_def
  set ψ : Sp N → Tgt m := ∑ k, v k with hψ_def
  set U : Set (Sp N) := Φ ⁻¹' cube 1 0 with hU_def
  set cΦ : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det (Φ.symm : Sp N →ₗ[ℝ] Sp N)| with hcΦ_def
  have hvol : ∀ s, volume (Φ ⁻¹' s) = cΦ * volume s := fun s =>
    Measure.addHaar_preimage_continuousLinearEquiv volume Φ s
  have hℓ0 : ∀ i, ℓ i ≠ 0 := lamLin_ne_zero ht0 ht1 hε0
  have hℓd : ∀ i l, i ≠ l → ℓ i ≠ ℓ l := lamLin_injective ht0 ht1 hε0 hεt hεt'
  -- the layers form a partition of `U`
  have hSU : ∀ k, S k ⊆ U := fun k x hx =>
    mem_cube_one_zero_iff.2 (lamSet_props ht1 hε0 hx ht0).1
  have hSd : Pairwise fun k k' => Disjoint (S k) (S k') := by
    intro k k' hkk'
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨-, ha, hb⟩ := lamSet_props ht1 hε0 hx ht0
    obtain ⟨-, ha', hb'⟩ := lamSet_props ht1 hε0 hx' ht0
    simp only [slabA] at ha hb ha' hb'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkk') with hlt | hlt
    · have h1 : ((k : ℕ) : ℝ) + 1 ≤ ((k' : ℕ) : ℝ) := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_right h1 hh.le
      nlinarith
    · have h1 : ((k' : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_right h1 hh.le
      nlinarith
  have hSf : ∀ k, volume (U ∩ frontier (S k)) = 0 := fun k =>
    measure_mono_null inter_subset_right (volume_frontier_tentSet hℓ0)
  have hSc : volume (U \ ⋃ k, S k) = 0 := by
    refine measure_mono_null (t := ⋃ k : Fin n, {x | coordFun Φ j x = slabA h k}) ?_
      (measure_iUnion_null fun k => volume_setOf_clm_eq (coordFun_ne_zero Φ j) _)
    rintro x ⟨hxU, hxS⟩
    have hcube := mem_cube_one_zero_iff.1 hxU
    set r : ℝ := (Φ x j + 1 / 2) * n with hr_def
    have hr0 : 0 ≤ r := mul_nonneg (by linarith [(hcube j).1]) hn'.le
    have hrn : r < n := by
      have := (hcube j).2
      rw [hr_def]; nlinarith
    have hk : ⌊r⌋₊ < n := (Nat.floor_lt hr0).2 hrn
    have hkle : ((⌊r⌋₊ : ℕ) : ℝ) ≤ r := Nat.floor_le hr0
    have hklt : r < ((⌊r⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one r
    set kk : Fin n := ⟨⌊r⌋₊, hk⟩
    have hrh : r * h = Φ x j + 1 / 2 := by rw [hr_def, mul_assoc, hnh, mul_one]
    have ha : slabA h kk ≤ Φ x j := by
      have := mul_le_mul_of_nonneg_right hkle hh.le
      simp only [slabA, kk]
      linarith
    have hb : Φ x j < slabA h kk + h := by
      have := mul_lt_mul_of_pos_right hklt hh
      simp only [slabA, kk]
      linarith
    have heq : Φ x j = slabA h kk := by
      by_contra hne
      have hlt : slabA h kk < Φ x j := lt_of_le_of_ne ha (Ne.symm hne)
      exact hxS (mem_iUnion.2 ⟨kk, mem_lamSet ht0 ht1 hε0 hcube hlt hb⟩)
    exact mem_iUnion.2 ⟨kk, heq⟩
  have hψ : ψ ∈ Aff0 U :=
    sum_mem_Aff0_fintype (fun k => isOpen_tentSet) hSU hSd hSf hSc
      (fun k => tentVec_mem_Aff0 hℓd d)
  -- the parallelepiped `U`
  have hUo : IsOpen U := (isOpen_cube 1 0).preimage Φ.continuous
  have hUb : Bornology.IsBounded U := by
    rw [hU_def, ← ContinuousLinearEquiv.image_symm_eq_preimage]
    exact (Φ.symm : Sp N →L[ℝ] Sp N).lipschitz.isBounded_image (isBounded_cube 1 0)
  have hUne : U.Nonempty := ⟨0, by
    rw [hU_def, mem_preimage, map_zero, mem_cube_one_zero_iff]
    intro l; norm_num⟩
  have hUf : volume (frontier U) = 0 := by
    change volume (frontier (Φ.toHomeomorph ⁻¹' cube 1 0)) = 0
    rw [← Homeomorph.preimage_frontier]
    change volume (Φ ⁻¹' frontier (cube 1 0)) = 0
    rw [hvol, volume_frontier_cube, mul_zero]
  have hUvol : volume U = cΦ := by
    rw [hU_def, hvol, volume_cube]; simp
  have hc0 : cΦ ≠ 0 := hUvol ▸ (volume_pos_of_isOpen_nonempty hUo hUne).ne'
  have hctop : cΦ ≠ ⊤ := ENNReal.ofReal_ne_top
  -- energy of the laminate
  set F : LamIdx N → ℝ≥0∞ := fun i => Zaff L (ξ + (ℓ i).smulRight d) with hF_def
  have hE : ∫⁻ y in U, Zaff L (ξ + fderiv ℝ ψ y) = ∑ k, ∑ i, F i * volume (P k i) := by
    rw [lintegral_eq_sum_pieces_fintype (fun k => isOpen_tentSet) hSU hSd hSc]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Eq.trans ?_ (lintegral_tentVec hℓd d (fun Z => Zaff L (ξ + Z)))
    refine setLIntegral_congr_fun isOpen_tentSet.measurableSet fun y hy => ?_
    have hloc : ψ =ᶠ[𝓝 y] v k := by
      filter_upwards [isOpen_tentSet.mem_nhds hy] with z hz
      simp only [hψ_def, Finset.sum_apply]
      exact Finset.sum_eq_single k
        (fun k' _ hk' => tentVec_eq_zero d fun hz' => (hSd hk').le_bot ⟨hz', hz⟩) (by simp)
    rw [hloc.fderiv_eq]
  -- volumes of the phases
  have hA1 : ∑ k, volume (P k (Sum.inl true)) ≤ cΦ * ENNReal.ofReal t := by
    calc ∑ k, volume (P k (Sum.inl true)) ≤ ∑ _k : Fin n, cΦ * ENNReal.ofReal (t * h) := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine (measure_mono (t := Φ ⁻¹' slabPi j (slabA h k) (slabA h k + t * h))
            fun x hx => lamPiece_true_sub ht0 ht1 hε0 hx).trans ?_
          rw [hvol, volume_slabPi, add_sub_cancel_left]
      _ = cΦ * ENNReal.ofReal t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_left_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn'.le,
            show (n : ℝ) * (t * h) = t * (n * h) by ring, hnh, mul_one]
  have hA2 : ∑ k, volume (P k (Sum.inl false)) ≤ cΦ * ENNReal.ofReal (1 - t) := by
    calc ∑ k, volume (P k (Sum.inl false)) ≤ ∑ _k : Fin n, cΦ * ENNReal.ofReal ((1 - t) * h) := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine (measure_mono (t := Φ ⁻¹' slabPi j (slabA h k + t * h) (slabA h k + h))
            fun x hx => lamPiece_false_sub ht0 ht1 hε0 hx).trans ?_
          rw [hvol, volume_slabPi, show slabA h k + h - (slabA h k + t * h) = (1 - t) * h by ring]
      _ = cΦ * ENNReal.ofReal (1 - t) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_left_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn'.le,
            show (n : ℝ) * ((1 - t) * h) = (1 - t) * (n * h) by ring, hnh, mul_one]
  have hA3 : ∀ p : Fin N × Bool,
      ∑ k, volume (P k (Sum.inr p)) ≤ cΦ * ENNReal.ofReal (h / ε) := by
    rintro ⟨l, b⟩
    have hdisj : Pairwise fun k k' => Disjoint (P k (Sum.inr (l, b))) (P k' (Sum.inr (l, b))) :=
      fun k k' hkk' => (hSd hkk').mono (tentPiece_subset _) (tentPiece_subset _)
    have hU := measure_iUnion (μ := volume) hdisj fun k => (isOpen_tentPiece _).measurableSet
    rw [tsum_fintype] at hU
    rw [← hU]
    refine (measure_mono (t := Φ ⁻¹' (if b then slabPi l (1 / 2 - h / ε) (1 / 2)
      else slabPi l (-(1 / 2)) (-(1 / 2) + h / ε)))
      (iUnion_subset fun k x hx => lamPiece_face_sub ht0 ht1 hε0 hh.le hx)).trans ?_
    rw [hvol]
    cases b
    · simp only [Bool.false_eq_true, if_false, volume_slabPi, add_sub_cancel_left, le_refl]
    · simp only [if_true, volume_slabPi, sub_sub_cancel, le_refl]
  -- the gradients of the two phases
  have hG1 : (ℓ (Sum.inl true)).smulRight d = (1 - t) • (coordFun Φ j).smulRight d := by
    rw [hℓ_def, lamLin, smulRight_smul_left]; rfl
  have hG2 : ξ + (ℓ (Sum.inl false)).smulRight d = ξ - t • (coordFun Φ j).smulRight d := by
    rw [hℓ_def, lamLin, smulRight_smul_left]
    simp only [lamCoef, lamIdx]
    rw [sub_eq_add_neg]
    congr 1
    exact neg_smul t ((coordFun Φ j).smulRight d)
  -- assembling
  set X : ℝ≥0∞ := ENNReal.ofReal t * Zaff L (ξ + (1 - t) • (coordFun Φ j).smulRight d) +
      ENNReal.ofReal (1 - t) * Zaff L (ξ - t • (coordFun Φ j).smulRight d) +
      ENNReal.ofReal (h / ε) * ∑ p : Fin N × Bool, F (Sum.inr p) with hX_def
  have hsum : ∑ k, ∑ i, F i * volume (P k i) ≤ cΦ * X := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Fintype.sum_sum_type, Fintype.sum_bool]
    have hF1 : F (Sum.inl true) = Zaff L (ξ + (1 - t) • (coordFun Φ j).smulRight d) := by
      rw [hF_def]; dsimp only; rw [hG1]
    have hF2 : F (Sum.inl false) = Zaff L (ξ - t • (coordFun Φ j).smulRight d) := by
      rw [hF_def]; dsimp only; rw [hG2]
    calc F (Sum.inl true) * ∑ k, volume (P k (Sum.inl true)) +
          F (Sum.inl false) * ∑ k, volume (P k (Sum.inl false)) +
          ∑ p, F (Sum.inr p) * ∑ k, volume (P k (Sum.inr p))
        ≤ F (Sum.inl true) * (cΦ * ENNReal.ofReal t) +
          F (Sum.inl false) * (cΦ * ENNReal.ofReal (1 - t)) +
          ∑ p, F (Sum.inr p) * (cΦ * ENNReal.ofReal (h / ε)) :=
        add_le_add (add_le_add (by gcongr) (by gcongr))
          (Finset.sum_le_sum fun p _ => by gcongr; exact hA3 p)
      _ = cΦ * X := by
        rw [hX_def, hF1, hF2]
        have : ∑ p, F (Sum.inr p) * (cΦ * ENNReal.ofReal (h / ε)) =
            cΦ * (ENNReal.ofReal (h / ε) * ∑ p, F (Sum.inr p)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
        rw [this]
        ring
  have hdom := aff0_domainIndependence (Zaff L) hUo hUb hUne hUf ξ
  rw [Zaff_Zaff] at hdom
  have hYt : Yt (fun _ => Zaff L) U ξ ≤ ∫⁻ y in U, Zaff L (ξ + fderiv ℝ ψ y) := iInf₂_le ψ hψ
  calc Zaff L ξ = (volume U)⁻¹ * Yt (fun _ => Zaff L) U ξ := hdom.symm
    _ ≤ (volume U)⁻¹ * (cΦ * X) := by
        gcongr
        exact hYt.trans (hE ▸ hsum)
    _ = X := by rw [hUvol]; exact ENNReal.inv_mul_cancel_left hc0 hctop

end Laminate

/-! ### A linear isomorphism with prescribed `j`-th coordinate `x ↦ ν · x` -/

section NuEquiv

/-- `x ↦ x` with its `j`-th coordinate replaced by `ν · x`. -/
noncomputable def nuLin (ν : Sp N) (j : Fin N) : Sp N →ₗ[ℝ] Sp N where
  toFun x := Function.update x j (∑ i, ν i * x i)
  map_add' x y := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [mul_add, Finset.sum_add_distrib]
    · simp [Function.update_of_ne hi]
  map_smul' c x := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [Finset.mul_sum, mul_left_comm]
    · simp [Function.update_of_ne hi]

theorem nuLin_injective {ν : Sp N} {j : Fin N} (hj : ν j ≠ 0) : Injective (nuLin ν j) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hoff : ∀ i, i ≠ j → x i = 0 := fun i hi => by
    have := congrFun hx i
    simpa [nuLin, Function.update_of_ne hi] using this
  have hjj : ∑ i, ν i * x i = 0 := by
    have := congrFun hx j
    simpa [nuLin] using this
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [hoff i hi, mul_zero]) (by simp)] at hjj
  funext i
  by_cases hi : i = j
  · subst hi
    simpa [hj] using hjj
  · exact hoff i hi

/-- The continuous linear isomorphism `nuLin ν j`. -/
noncomputable def nuEquiv {ν : Sp N} {j : Fin N} (hj : ν j ≠ 0) : Sp N ≃L[ℝ] Sp N :=
  (LinearEquiv.ofInjectiveEndo (nuLin ν j) (nuLin_injective hj)).toContinuousLinearEquiv

theorem coordFun_nuEquiv {ν : Sp N} {j : Fin N} (hj : ν j ≠ 0) (x : Sp N) :
    coordFun (nuEquiv hj) j x = ∑ i, ν i * x i := by
  simp [coordFun_apply, nuEquiv, nuLin]

theorem rankOne_eq_smulRight (d : Tgt m) (ν : Sp N) (f : Sp N →L[ℝ] ℝ)
    (hf : ∀ q, f (Pi.single q 1) = ν q) : rankOne d ν = f.smulRight d := by
  apply (matCoordEquiv m N).injective
  funext ⟨i, q⟩
  rw [matCoordEquiv_rankOne, matCoordEquiv_apply]
  simp [hf, mul_comm]

end NuEquiv

/-! ### The rank-one inequality and its consequences -/

/-- **Rank-one inequality** (Appendix A of the paper, step (a)). If `L` is finite on an open set
`V ∋ ξ`, then for every `t ∈ ]0,1[`, every `d`, every `ν ≠ 0` and every `s`,
`𝒵_aff L(ξ) ≤ t 𝒵_aff L(ξ + (1-t)s d⊗ν) + (1-t) 𝒵_aff L(ξ - t s d⊗ν)`.
No measurability of `L` is required. -/
theorem Zaff.rankOneInequality (L : Mat m N → ℝ≥0∞) {V : Set (Mat m N)} (hV : IsOpen V)
    (hLV : ∀ Z ∈ V, L Z ≠ ⊤) {ξ : Mat m N} (hξ : ξ ∈ V) (d : Tgt m) {ν : Sp N} (hν : ν ≠ 0)
    (s : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Zaff L ξ ≤ ENNReal.ofReal t * Zaff L (ξ + ((1 - t) * s) • rankOne d ν) +
      ENNReal.ofReal (1 - t) * Zaff L (ξ - (t * s) • rankOne d ν) := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨j, hj⟩ : ∃ j, ν j ≠ 0 := by
    by_contra h
    push Not at h
    exact hν (funext h)
  set Φ := nuEquiv hj
  have hrank : rankOne d ν = (coordFun Φ j).smulRight d :=
    rankOne_eq_smulRight d ν _ fun q => by
      simp only [Φ, coordFun_nuEquiv]
      simp [Pi.single_apply]
  set D := (coordFun Φ j).smulRight (s • d) with hD_def
  have hD1 : ((1 - t) * s) • rankOne d ν = (1 - t) • D := by
    rw [hrank, hD_def, smulRight_smul_right, smul_smul]
  have hD2 : (t * s) • rankOne d ν = t • D := by
    rw [hrank, hD_def, smulRight_smul_right, smul_smul]
  rw [hD1, hD2]
  -- the width of the boundary layer
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hV ξ hξ
  set K : ℝ := ∑ l, ‖coordFun Φ l‖ * ‖s • d‖ + 1 with hK_def
  have hK : 0 < K := by positivity
  set ε : ℝ := min (min t (1 - t) / 2) (ρ / (2 * K)) with hε_def
  have hmin : 0 < min t (1 - t) := lt_min ht0 (by linarith)
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεt : ε < t := by
    have := min_le_left (min t (1 - t) / 2) (ρ / (2 * K))
    have := min_le_left t (1 - t)
    linarith
  have hεt' : ε < 1 - t := by
    have := min_le_left (min t (1 - t) / 2) (ρ / (2 * K))
    have := min_le_right t (1 - t)
    linarith
  have hεK : ε * K < ρ := by
    have h1 : ε ≤ ρ / (2 * K) := min_le_right _ _
    calc ε * K ≤ ρ / (2 * K) * K := mul_le_mul_of_nonneg_right h1 hK.le
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith
  set M : ℝ≥0∞ := ∑ p : Fin N × Bool, Zaff L (ξ + (lamLin Φ j t ε (Sum.inr p)).smulRight (s • d))
  have hM : M ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun p _ => ne_top_of_le_ne_top (hLV _ (hball ?_)) (Zaff_le L _)
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      ContinuousLinearMap.norm_smulRight_apply]
    obtain ⟨l, b⟩ := p
    have hcoef : ‖lamLin Φ j t ε (Sum.inr (l, b))‖ = ε * ‖coordFun Φ l‖ := by
      rw [lamLin, norm_smul]
      cases b <;> simp [lamCoef, lamIdx, abs_of_pos hε0]
    rw [hcoef]
    have hl : ‖coordFun Φ l‖ * ‖s • d‖ ≤ K - 1 := by
      rw [hK_def, add_sub_cancel_right]
      exact Finset.single_le_sum (f := fun l => ‖coordFun Φ l‖ * ‖s • d‖)
        (fun _ _ => by positivity) (Finset.mem_univ l)
    calc ε * ‖coordFun Φ l‖ * ‖s • d‖ = ε * (‖coordFun Φ l‖ * ‖s • d‖) := by ring
      _ ≤ ε * K := mul_le_mul_of_nonneg_left (by linarith) hε0.le
      _ < ρ := hεK
  -- letting the number of layers go to infinity
  set A : ℝ≥0∞ := ENNReal.ofReal t * Zaff L (ξ + (1 - t) • D) +
      ENNReal.ofReal (1 - t) * Zaff L (ξ - t • D)
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / n / ε) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).div_const ε
  have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / n / ε) * M) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hM)
  have h3 : Tendsto (fun n : ℕ => A + ENNReal.ofReal (1 / n / ε) * M) atTop (𝓝 A) := by
    simpa using (tendsto_const_nhds (x := A)).add h2
  refine ge_of_tendsto h3 (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  exact Zaff_le_laminate L Φ j (s • d) ht0 ht1 hε0 hεt hεt' (by omega) ξ

/-- `𝒵_aff L` is rank-one convex on the interior of its effective domain, for every `L`. -/
theorem Zaff_rankOneConvexOn (L : Mat m N → ℝ≥0∞) :
    RankOneConvexOn (interior (dom (Zaff L))) (Zaff L) := by
  intro A hA d _ ν hν s t ht
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  have hfin : ∀ Z ∈ interior (dom (Zaff L)), Zaff L Z ≠ ⊤ := fun Z hZ =>
    (lt_top_iff_ne_top.mp (by simpa [dom] using interior_subset hZ))
  have h := Zaff.rankOneInequality (Zaff L) isOpen_interior hfin hA d hν0 s ht
  simpa only [Zaff_Zaff] using h

/-- Ordinary convexity of an ENNReal-valued function implies rank-one convexity, including
the exact ENNReal barycentric weights used by `RankOneConvexOn`. -/
theorem ConvexENN.rankOneConvexOn {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {V : Set (Mat m N)} : RankOneConvexOn V G := by
  intro A hA d hd ν hν s t ht
  let τ : ℝ≥0 := ⟨t, ht.1.le⟩
  have hτle : τ ≤ 1 := by exact_mod_cast ht.2.le
  have hτreal : (τ : ℝ) = t := rfl
  have hcomplReal : ((1 - τ : ℝ≥0) : ℝ) = 1 - t := by
    rw [NNReal.coe_sub hτle, NNReal.coe_one, hτreal]
  have hbar : (τ : ℝ) • (A + ((1 - t) * s) • rankOne d ν) +
      ((1 - τ : ℝ≥0) : ℝ) • (A - (t * s) • rankOne d ν) = A := by
    rw [hτreal, hcomplReal]
    module
  have hτenn : (τ : ℝ≥0∞) = ENNReal.ofReal t := by
    rw [ENNReal.ofReal_eq_coe_nnreal ht.1.le]
    apply congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    apply Subtype.ext
    rfl
  have hcomplENN : ((1 - τ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 - t) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr ht.2.le)]
    apply congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    apply Subtype.ext
    exact hcomplReal
  have h := hG (A + ((1 - t) * s) • rankOne d ν)
      (A - (t * s) • rankOne d ν) τ hτle
  rw [hbar, hτenn, hcomplENN] at h
  exact h

/-- A finite convex ENNReal-valued integrand is continuous on the interior of its effective
domain. The proof passes through elementary matrix directions, coordinate convexity, and the
generic local-Lipschitz theorem; it does not use any cited regularity result. -/
theorem ConvexENN.continuousOn_interior_dom {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) : ContinuousOn G (interior (dom G)) := by
  have hfinite : ∀ A ∈ interior (dom G), G A ≠ ⊤ := by
    intro A hA
    exact (lt_top_iff_ne_top.mp (by simpa [dom] using interior_subset hA))
  have hcoord : CoordConvexOn (matCoordEquiv m N '' interior (dom G))
      (fun Z => G ((matCoordEquiv m N).symm Z)) :=
    (hG.rankOneConvexOn (V := interior (dom G))).coordConvex
  have hlocLip := locallyLipschitzOn_of_matCoordConvex (f := G) isOpen_interior
    hfinite hcoord
  intro A hA
  obtain ⟨K, s, hs, hKs⟩ := hlocLip A hA
  have hcont : ContinuousAt (fun Z => ENNReal.ofReal (G Z).toReal) A :=
    ENNReal.continuous_ofReal.continuousAt.comp (hKs.continuousOn.continuousAt hs)
  have heq : (fun Z => ENNReal.ofReal (G Z).toReal) =ᶠ[𝓝 A] G := by
    filter_upwards [isOpen_interior.mem_nhds hA] with Z hZ
    exact ENNReal.ofReal_toReal (interior_subset hZ).ne
  exact (hcont.congr heq).continuousWithinAt

/-- **Proposition `Zenvelopefacts-cite` (i)**, now proved: `𝒵_aff L` is locally Lipschitz on the
interior of its effective domain. -/
theorem citedZaffLocLip : CitedZaffLocLip N m :=
  CitedZaffLocLip_of_rankOneConvexOn Zaff_rankOneConvexOn

/-- **Theorem `main-Ggrowth`** with three cited results: `CitedZaffLocLip` is no longer a
hypothesis (`citedZaffLocLip`). -/
theorem main_Ggrowth_final_three [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (N : ℝ) < p) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} (hW : Hypotheses p G W)
    (hAHM : CitedAHM14 N m p) (hApprox : CitedAffineApprox N m p)
    (hV : CitedVitaliEnvelope N) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W) (intHom (Whom p W)) :=
  main_Ggrowth_final p hp hΩ hW hAHM hApprox citedZaffLocLip hV

end Homogenization
