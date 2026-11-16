import Homogenization.LemmareeJacobian
import Homogenization.RankOne
import Homogenization.Examples.ProperDomainEnvelopes

/-!
# A variant of Ben Belgacem's lemma (Lemma `lem:BB`)

Rank-one convexity (`RankOneConvex`) and the rank-one convex envelope `R₁ F` (`Rone`, the
supremum of the rank-one convex minorants of `F`) are defined as in Subsection `subsec:general`.

`lem_BB`: if `N ≤ m`, `G(ξ) = |ξ|^p + g̃(|ξ|²)` with `g̃` nondecreasing and satisfying the shift
condition of (Dg), and `F ≤ δ(1 + G)` on `{v ≥ γ}`, then `R₁ F ≤ β(1 + G)` on `𝕄`.

The lamination argument (`le_growth_of_split`) applies to every `f ≤ F` that splits along rank-one
segments (`RankOneSplit`), with a constant `β` independent of `f`. In Euclidean coordinates, with
an orthonormal eigenbasis `b` of `A†A` (`exists_orthCols`), the columns `A bᵢ` are orthogonal,
`v(A) = ∏ ‖A bᵢ‖` (`normDet_of_orthCols`) and `|A|_F² = ∑ ‖A bᵢ‖²`
(`matrixFrobeniusNorm_sq_eq`). Each column of norm `< γ` is replaced by `±γ u` with `u` a unit
vector orthogonal to the other columns (`exists_unit_col`, `col_update`), a rank-one
splitting; after at most `N` steps all leaves have `v ≥ γ^N ≥ γ` (`le_pow_two_mul_of_split`).

Application: `𝒵_aff W⁺` is rank-one convex because it is finite everywhere
(`Zaff_rankOneConvex`), hence `𝒵_aff W⁺ ≤ R₁ W⁺ ≤ β(1 + G)` (`properDomainWPlus_Zaff_le_growth`),
which gives the upper bound of `prop:separating` (iii) (`properDomainWv_Zaff_le_growth`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace Homogenization

variable {N m : ℕ}

theorem rankOne_apply' (d : Tgt m) (ν y : Sp N) : rankOne d ν y = (∑ j, ν j * y j) • d := by
  ext i
  have hy : y = ∑ j, y j • (Pi.single j (1 : ℝ) : Sp N) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h : ∀ j, rankOne d ν (Pi.single j 1) i = d i * ν j := fun j => by
    rw [← matCoordEquiv_apply, matCoordEquiv_rankOne]
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem matrixEuclideanLinearMap_apply (A : Mat m N) (x : EuclideanSpace ℝ (Fin N)) :
    matrixEuclideanLinearMap A x = WithLp.toLp 2 (A (WithLp.ofLp x)) := rfl

/-- The Euclidean rank-one matrix `u ⊗ e`, `x ↦ ⟪e, x⟫ u`. -/
noncomputable def eRankOne (u : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)) :
    Mat m N :=
  rankOne (WithLp.ofLp u) (WithLp.ofLp e)

theorem matrixEuclideanLinearMap_eRankOne (u : EuclideanSpace ℝ (Fin m))
    (e x : EuclideanSpace ℝ (Fin N)) :
    matrixEuclideanLinearMap (eRankOne u e) x = ⟪e, x⟫ • u := by
  rw [matrixEuclideanLinearMap_apply, eRankOne, rankOne_apply']
  ext i
  simp [PiLp.inner_apply, mul_comm]

theorem matrixEuclideanLinearMap_add_smul (A : Mat m N) (c : ℝ) (u : EuclideanSpace ℝ (Fin m))
    (e x : EuclideanSpace ℝ (Fin N)) :
    matrixEuclideanLinearMap (A + c • eRankOne u e) x =
      matrixEuclideanLinearMap A x + (c * ⟪e, x⟫) • u := by
  have := matrixEuclideanLinearMap_eRankOne u e x
  rw [matrixEuclideanLinearMap_apply, matrixEuclideanLinearMap_apply] at *
  simp only [add_apply, smul_apply, WithLp.toLp_add,
    WithLp.toLp_smul, this, smul_smul]

/-- Rank-one splitting for an envelope finite everywhere:
`𝒵_aff L(ξ) ≤ 𝒵_aff L(ξ + α d⊗ν) + 𝒵_aff L(ξ - β d⊗ν)` for `α, β > 0`. -/
theorem Zaff_le_add_of_rankOne {L : Mat m N → ℝ≥0∞} (hfin : ∀ ζ, Zaff L ζ ≠ ⊤) (ξ : Mat m N)
    (d : Tgt m) {ν : Sp N} (hν : ν ≠ 0) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Zaff L ξ ≤ Zaff L (ξ + α • rankOne d ν) + Zaff L (ξ - β • rankOne d ν) := by
  set t := β / (α + β)
  have hs : 0 < α + β := by linarith
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hβ hs, (div_lt_one hs).2 (by linarith)⟩
  have h := Zaff.rankOneInequality (Zaff L) isOpen_univ (fun Z _ => hfin Z) (mem_univ ξ) d hν
    (α + β) ht
  simp only [Zaff_Zaff] at h
  have e1 : (1 - t) * (α + β) = α := by simp only [t]; field_simp; ring
  have e2 : t * (α + β) = β := by simp only [t]; field_simp
  rw [e1, e2] at h
  refine h.trans (add_le_add ?_ ?_)
  · exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 ht.2.le)
  · exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 (by linarith [ht.1]))

/-- Rank-one convexity: for every `ξ`, `d`, `ν`, the function `s ↦ f(ξ + s d⊗ν)` is convex. -/
def RankOneConvex (f : Mat m N → ℝ≥0∞) : Prop :=
  ∀ (ξ : Mat m N) (d : Tgt m) (ν : Sp N) (s₁ s₂ t : ℝ), 0 ≤ t → t ≤ 1 →
    f (ξ + (t * s₁ + (1 - t) * s₂) • rankOne d ν) ≤
      ENNReal.ofReal t * f (ξ + s₁ • rankOne d ν) +
        ENNReal.ofReal (1 - t) * f (ξ + s₂ • rankOne d ν)

/-- The rank-one convex envelope `R₁ F`: the supremum of the rank-one convex minorants of `F`. -/
noncomputable def Rone (F : Mat m N → ℝ≥0∞) : Mat m N → ℝ≥0∞ :=
  fun ξ => ⨆ (f : Mat m N → ℝ≥0∞) (_ : RankOneConvex f ∧ f ≤ F), f ξ

theorem le_Rone {F f : Mat m N → ℝ≥0∞} (hf : RankOneConvex f) (hfF : f ≤ F) : f ≤ Rone F :=
  fun ξ => le_iSup₂_of_le (f := fun g (_ : RankOneConvex g ∧ g ≤ F) => g ξ) f ⟨hf, hfF⟩ le_rfl

theorem Rone_le (F : Mat m N → ℝ≥0∞) : Rone F ≤ F :=
  fun ξ => iSup₂_le fun _ hf => hf.2 ξ

/-- The pointwise supremum of rank-one convex minorants is rank-one convex: `R₁ F` is the largest
rank-one convex minorant of `F`. -/
theorem rankOneConvex_Rone (F : Mat m N → ℝ≥0∞) : RankOneConvex (Rone F) := by
  intro ξ d ν s₁ s₂ t ht0 ht1
  refine iSup₂_le fun f hf => ?_
  refine (hf.1 ξ d ν s₁ s₂ t ht0 ht1).trans ?_
  gcongr
  · exact le_Rone hf.1 hf.2 _
  · exact le_Rone hf.1 hf.2 _

/-- Splitting along rank-one segments, the only consequence of rank-one convexity used by the
lamination argument. -/
def RankOneSplit (f : Mat m N → ℝ≥0∞) : Prop :=
  ∀ (ξ : Mat m N) (d : Tgt m) (ν : Sp N) (α β : ℝ), 0 < α → 0 < β →
    f ξ ≤ f (ξ + α • rankOne d ν) + f (ξ - β • rankOne d ν)

theorem RankOneConvex.split {f : Mat m N → ℝ≥0∞} (hf : RankOneConvex f) : RankOneSplit f := by
  intro ξ d ν α β hα hβ
  set t := β / (α + β)
  have hs : 0 < α + β := by linarith
  have ht0 : 0 ≤ t := (div_pos hβ hs).le
  have ht1 : t ≤ 1 := (div_le_one hs).2 (by linarith)
  have h := hf ξ d ν α (-β) t ht0 ht1
  have e0 : t * α + (1 - t) * -β = 0 := by simp only [t]; field_simp; ring
  have e3 : ξ + -β • rankOne d ν = ξ - β • rankOne d ν := by module
  rw [e0, zero_smul, add_zero, e3] at h
  refine h.trans (add_le_add ?_ ?_)
  · exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 ht1)
  · exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 (by linarith))

/-- `𝒵_aff L` is rank-one convex on `𝕄` when it is finite everywhere (`Zaff.rankOneInequality`). -/
theorem Zaff_rankOneConvex {L : Mat m N → ℝ≥0∞} (hfin : ∀ ζ, Zaff L ζ ≠ ⊤) :
    RankOneConvex (Zaff L) := by
  intro ξ d ν s₁ s₂ t ht0 ht1
  set ξ' := ξ + (t * s₁ + (1 - t) * s₂) • rankOne d ν
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp [ξ']
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp [ξ']
  by_cases hν : ν = 0
  · subst hν
    have h0 : rankOne d (0 : Sp N) = 0 := by ext x i; simp [rankOne_apply']
    simp only [ξ', h0, smul_zero, add_zero]
    rw [← add_mul, ← ENNReal.ofReal_add ht0 (by linarith), add_sub_cancel, ENNReal.ofReal_one,
      one_mul]
  have h := Zaff.rankOneInequality (Zaff L) isOpen_univ (fun Z _ => hfin Z) (mem_univ ξ') d hν
    (s₁ - s₂) ⟨ht0', ht1'⟩
  simp only [Zaff_Zaff] at h
  have e1 : ξ' + ((1 - t) * (s₁ - s₂)) • rankOne d ν = ξ + s₁ • rankOne d ν := by
    simp only [ξ']; module
  have e2 : ξ' - (t * (s₁ - s₂)) • rankOne d ν = ξ + s₂ • rankOne d ν := by
    simp only [ξ']; module
  rwa [e1, e2] at h

/-- `𝒵_aff L ≤ R₁ L` when `𝒵_aff L` is finite everywhere. -/
theorem Zaff_le_Rone {L : Mat m N → ℝ≥0∞} (hfin : ∀ ζ, Zaff L ζ ≠ ⊤) : Zaff L ≤ Rone L :=
  le_Rone (Zaff_rankOneConvex hfin) (Zaff_le L)

local notation "EN" => EuclideanSpace ℝ (Fin N)
local notation "EM" => EuclideanSpace ℝ (Fin m)

/-- The columns `T bᵢ` of `T` in the orthonormal basis `b` are pairwise orthogonal. -/
def OrthCols (b : OrthonormalBasis (Fin N) ℝ EN) (T : EN →ₗ[ℝ] EM) : Prop :=
  ∀ i j, i ≠ j → ⟪T (b i), T (b j)⟫ = 0

/-- With orthogonal columns, the Jacobian is the product of the column norms. -/
theorem normDet_of_orthCols {b : OrthonormalBasis (Fin N) ℝ EN} {T : EN →ₗ[ℝ] EM}
    (hT : OrthCols b T) : T.normDet = ∏ i, ‖T (b i)‖ := by
  have h := T.normDet_sq_eq_det_gram b
  have hg : Matrix.gram ℝ (fun i => T (b i)) = Matrix.diagonal fun i => ‖T (b i)‖ ^ 2 := by
    ext i j
    rw [Matrix.gram_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, hT i j hij]
  rw [hg, Matrix.det_diagonal, Finset.prod_pow] at h
  have h' : T.normDet ^ 2 = (∏ i, ‖T (b i)‖) ^ 2 := by simpa using h
  exact (sq_eq_sq₀ (LinearMap.normDet_nonneg T)
    (Finset.prod_nonneg fun i _ => norm_nonneg _)).1 h'

/-- An orthonormal eigenbasis of `T†T` makes the columns of `T` orthogonal. -/
theorem exists_orthCols (T : EN →ₗ[ℝ] EM) :
    ∃ b : OrthonormalBasis (Fin N) ℝ EN, OrthCols b T := by
  have hS := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ EN = N := finrank_euclideanSpace_fin
  refine ⟨hS.eigenvectorBasis hn, fun i j hij => ?_⟩
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hS.apply_eigenvectorBasis,
    inner_smul_right, (hS.eigenvectorBasis hn).orthonormal.2 hij, mul_zero]

/-- `∑ᵢ ‖T bᵢ‖²` does not depend on the orthonormal basis `b` (Parseval twice). -/
theorem sum_norm_sq_orthonormalBasis (T : EN →ₗ[ℝ] EM) (b : OrthonormalBasis (Fin N) ℝ EN) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ k, ‖LinearMap.adjoint T (EuclideanSpace.basisFun (Fin m) ℝ k)‖ ^ 2 := by
  set f := EuclideanSpace.basisFun (Fin m) ℝ
  calc ∑ i, ‖T (b i)‖ ^ 2 = ∑ i, ∑ k, ‖⟪f k, T (b i)⟫‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => (f.sum_sq_norm_inner_right _).symm
    _ = ∑ k, ∑ i, ‖⟪b i, LinearMap.adjoint T (f k)⟫‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.adjoint_inner_right, real_inner_comm]
    _ = ∑ k, ‖LinearMap.adjoint T (f k)‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => b.sum_sq_norm_inner_right _

/-- `|A|_F² = ∑ᵢ ‖A bᵢ‖²` for every orthonormal basis `b` (Euclidean coordinates). -/
theorem matrixFrobeniusNorm_sq_eq (A : Mat m N) (b : OrthonormalBasis (Fin N) ℝ EN) :
    matrixFrobeniusNorm A ^ 2 = ∑ i, ‖matrixEuclideanLinearMap A (b i)‖ ^ 2 := by
  rw [sum_norm_sq_orthonormalBasis, ← sum_norm_sq_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin N) ℝ), matrixFrobeniusNorm_eq_sqrt_sum,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [matCoordEquiv_apply, matrixEuclideanLinearMap_apply, Real.norm_eq_abs, sq_abs]
  simp

/-- A unit vector carrying the column `T bⱼ` and orthogonal to the other columns (it exists
since `N ≤ m`). -/
theorem exists_unit_col (hNm : N ≤ m) {b : OrthonormalBasis (Fin N) ℝ EN} {T : EN →ₗ[ℝ] EM}
    (hT : OrthCols b T) (j : Fin N) :
    ∃ u : EM, ‖u‖ = 1 ∧ (∀ i, i ≠ j → ⟪T (b i), u⟫ = 0) ∧ T (b j) = ‖T (b j)‖ • u := by
  by_cases h0 : T (b j) = 0
  · set K : Submodule ℝ EM := Submodule.span ℝ (Set.range fun i : {i // i ≠ j} => T (b i))
    have hK : Module.finrank ℝ K < m := by
      have h1 : Module.finrank ℝ K ≤ Fintype.card {i // i ≠ j} :=
        finrank_range_le_card (R := ℝ) (fun i : {i // i ≠ j} => T (b i))
      have h2 : Fintype.card {i // i ≠ j} < Fintype.card (Fin N) :=
        Fintype.card_subtype_lt (p := fun i => i ≠ j) (x := j) (by simp)
      rw [Fintype.card_fin] at h2
      omega
    have hKo : Kᗮ ≠ ⊥ := by
      intro h
      have := K.finrank_add_finrank_orthogonal
      rw [h, finrank_bot, add_zero, finrank_euclideanSpace_fin] at this
      omega
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
    refine ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx0, fun i hi => ?_, by simp [h0]⟩
    exact K.inner_right_of_mem_orthogonal (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      (Kᗮ.smul_mem _ hx)
  · refine ⟨‖T (b j)‖⁻¹ • T (b j), norm_smul_inv_norm h0, fun i hi => ?_, ?_⟩
    · rw [inner_smul_right, hT i j hi, mul_zero]
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]

/-- Updating the column `j` along a unit vector orthogonal to the other columns. -/
theorem col_update {b : OrthonormalBasis (Fin N) ℝ EN} {A : Mat m N}
    (hT : OrthCols b (matrixEuclideanLinearMap A)) {j : Fin N} {u : EM}
    (hu : ∀ i, i ≠ j → ⟪matrixEuclideanLinearMap A (b i), u⟫ = 0) {w : ℝ}
    (hw : matrixEuclideanLinearMap A (b j) = w • u) (c : ℝ) :
    OrthCols b (matrixEuclideanLinearMap (A + c • eRankOne u (b j))) ∧
      matrixEuclideanLinearMap (A + c • eRankOne u (b j)) (b j) = (w + c) • u ∧
      ∀ i, i ≠ j → matrixEuclideanLinearMap (A + c • eRankOne u (b j)) (b i) =
        matrixEuclideanLinearMap A (b i) := by
  have hcol : ∀ i, i ≠ j → matrixEuclideanLinearMap (A + c • eRankOne u (b j)) (b i) =
      matrixEuclideanLinearMap A (b i) := by
    intro i hi
    rw [matrixEuclideanLinearMap_add_smul, b.orthonormal.2 (Ne.symm hi), mul_zero, zero_smul,
      add_zero]
  have hj : matrixEuclideanLinearMap (A + c • eRankOne u (b j)) (b j) = (w + c) • u := by
    rw [matrixEuclideanLinearMap_add_smul, hw, real_inner_self_eq_norm_sq, b.orthonormal.1 j,
      one_pow, mul_one, add_smul]
  refine ⟨fun i i' hii' => ?_, hj, hcol⟩
  by_cases hi : i = j
  · subst hi
    rw [hj, hcol i' (Ne.symm hii'), inner_smul_left, real_inner_comm, hu i' (Ne.symm hii'),
      mul_zero]
  · by_cases hi' : i' = j
    · subst hi'
      rw [hj, hcol i hi, inner_smul_right, hu i hi, mul_zero]
    · rw [hcol i hi, hcol i' hi']
      exact hT i i' hii'

/-- The columns of norm `< γ`. -/
noncomputable def smallCols (b : OrthonormalBasis (Fin N) ℝ EN) (γ : ℝ) (A : Mat m N) :
    Finset (Fin N) :=
  Finset.univ.filter fun i => ‖matrixEuclideanLinearMap A (b i)‖ < γ

/-- `∑ᵢ max(γ², ‖A bᵢ‖²)`, unchanged when a column of norm `< γ` is replaced by one of norm `γ`. -/
noncomputable def capSum (b : OrthonormalBasis (Fin N) ℝ EN) (γ : ℝ) (A : Mat m N) : ℝ :=
  ∑ i, max (γ ^ 2) (‖matrixEuclideanLinearMap A (b i)‖ ^ 2)

theorem small_capSum_update {b : OrthonormalBasis (Fin N) ℝ EN} {γ : ℝ} {A A' : Mat m N}
    {j : Fin N} (hj : ‖matrixEuclideanLinearMap A (b j)‖ < γ)
    (hj' : ‖matrixEuclideanLinearMap A' (b j)‖ = γ)
    (hcol : ∀ i, i ≠ j → matrixEuclideanLinearMap A' (b i) = matrixEuclideanLinearMap A (b i)) :
    smallCols b γ A' = (smallCols b γ A).erase j ∧ capSum b γ A' = capSum b γ A := by
  constructor
  · ext i
    by_cases hi : i = j
    · subst hi
      simp [smallCols, hj']
    · simp [smallCols, hi, hcol i hi]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = j
    · subst hi
      rw [hj', max_self, max_eq_left (pow_le_pow_left₀ (norm_nonneg _) hj.le 2)]
    · rw [hcol i hi]

/-- **The lamination tree.** If `f` splits along rank-one segments and is bounded by
`Φ(capSum)` at the matrices whose columns all have norm `≥ γ`, then `f(A) ≤ 2ⁿ Φ(capSum A)` when
`A` has orthogonal columns, `n` of them of norm `< γ`. -/
theorem le_pow_two_mul_of_split (hNm : N ≤ m) {f : Mat m N → ℝ≥0∞} (hsplit : RankOneSplit f)
    {b : OrthonormalBasis (Fin N) ℝ EN} {γ : ℝ} (Φ : ℝ → ℝ≥0∞)
    (hleaf : ∀ A, OrthCols b (matrixEuclideanLinearMap A) →
      (∀ i, γ ≤ ‖matrixEuclideanLinearMap A (b i)‖) → f A ≤ Φ (capSum b γ A)) :
    ∀ n : ℕ, ∀ A, OrthCols b (matrixEuclideanLinearMap A) → (smallCols b γ A).card = n →
      f A ≤ 2 ^ n * Φ (capSum b γ A) := by
  intro n
  induction n with
  | zero =>
    intro A hA hn
    rw [Finset.card_eq_zero, smallCols, Finset.filter_eq_empty_iff] at hn
    rw [pow_zero, one_mul]
    exact hleaf A hA fun i => not_lt.1 (hn (Finset.mem_univ i))
  | succ k ih =>
    intro A hA hn
    obtain ⟨j, hjs⟩ := Finset.card_pos.1 (by omega : 0 < (smallCols b γ A).card)
    have hj : ‖matrixEuclideanLinearMap A (b j)‖ < γ := (Finset.mem_filter.1 hjs).2
    set w := ‖matrixEuclideanLinearMap A (b j)‖
    have hw0 : 0 ≤ w := norm_nonneg _
    have hγ : 0 < γ := hw0.trans_lt hj
    obtain ⟨u, hu1, hu, huw⟩ := exists_unit_col hNm hA j
    obtain ⟨hA₁, hj₁, hc₁⟩ := col_update hA hu huw (γ - w)
    obtain ⟨hA₂, hj₂, hc₂⟩ := col_update hA hu huw (-(γ + w))
    have hn₁ : ‖matrixEuclideanLinearMap (A + (γ - w) • eRankOne u (b j)) (b j)‖ = γ := by
      rw [hj₁, norm_smul, hu1, mul_one, show w + (γ - w) = γ by ring, Real.norm_of_nonneg hγ.le]
    have hn₂ : ‖matrixEuclideanLinearMap (A + (-(γ + w)) • eRankOne u (b j)) (b j)‖ = γ := by
      rw [hj₂, norm_smul, hu1, mul_one, show w + -(γ + w) = -γ by ring, norm_neg,
        Real.norm_of_nonneg hγ.le]
    obtain ⟨hs₁, hS₁⟩ := small_capSum_update hj hn₁ hc₁
    obtain ⟨hs₂, hS₂⟩ := small_capSum_update hj hn₂ hc₂
    have hk₁ : (smallCols b γ (A + (γ - w) • eRankOne u (b j))).card = k := by
      rw [hs₁, Finset.card_erase_of_mem hjs, hn]; rfl
    have hk₂ : (smallCols b γ (A + (-(γ + w)) • eRankOne u (b j))).card = k := by
      rw [hs₂, Finset.card_erase_of_mem hjs, hn]; rfl
    have hsplit := hsplit A (WithLp.ofLp u) (WithLp.ofLp (b j)) (γ - w) (γ + w)
      (by linarith) (by linarith)
    have e2 : A - (γ + w) • rankOne (WithLp.ofLp u) (WithLp.ofLp (b j)) =
        A + (-(γ + w)) • eRankOne u (b j) := by
      ext x i; simp [eRankOne]; ring
    rw [e2] at hsplit
    calc f A ≤ f (A + (γ - w) • eRankOne u (b j)) +
          f (A + (-(γ + w)) • eRankOne u (b j)) := hsplit
      _ ≤ 2 ^ k * Φ (capSum b γ A) + 2 ^ k * Φ (capSum b γ A) := by
          gcongr
          · rw [← hS₁]; exact ih _ hA₁ hk₁
          · rw [← hS₂]; exact ih _ hA₂ hk₂
      _ = 2 ^ (k + 1) * Φ (capSum b γ A) := by rw [pow_succ]; ring

theorem add_rpow_le_two_rpow {x y q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 ≤ q) :
    (x + y) ^ q ≤ 2 ^ q * (x ^ q + y ^ q) := by
  have hmax : x + y ≤ 2 * max x y := by linarith [le_max_left x y, le_max_right x y]
  calc (x + y) ^ q ≤ (2 * max x y) ^ q := Real.rpow_le_rpow (by positivity) hmax hq
    _ = 2 ^ q * (max x y) ^ q := Real.mul_rpow (by norm_num) (le_max_of_le_left hx)
    _ ≤ 2 ^ q * (x ^ q + y ^ q) := by
        gcongr
        rcases le_total x y with h | h
        · rw [max_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg hx q)
        · rw [max_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hy q)

/-- `|A|_F^p = (|A|_F²)^{p/2}`. -/
theorem frob_rpow_eq (A : Mat m N) (p : ℝ) :
    matrixFrobeniusNorm A ^ p = (matrixFrobeniusNorm A ^ 2) ^ (p / 2) := by
  have h0 : 0 ≤ matrixFrobeniusNorm A := norm_nonneg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 1
  push_cast
  ring

/-- The growth function `G(ξ) = |ξ|^p + g̃(|ξ|²)` of (Dg), for arbitrary `p` and `g̃`. -/
noncomputable def bbG (p : ℝ) (gt : ℝ≥0 → ℝ≥0) (A : Mat m N) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixFrobeniusNorm A ^ p) +
    (gt ⟨matrixFrobeniusNorm A ^ 2, sq_nonneg _⟩ : ℝ≥0∞)

theorem properDomainG_eq_bbG (D : ProperDomainGData N) :
    (properDomainG D : Mat m N → ℝ≥0∞) = bbG D.p D.gTilde := rfl

/-- **The lamination argument of `lem:BB`.** Let `N ≤ m`, `p ≥ 0`, `g̃` nondecreasing with the
shift condition of (Dg), and `F : 𝕄 → [0,∞]` with `F ≤ δ(1 + G)` on `{v ≥ γ}`. Then there is `β`
such that every `f ≤ F` splitting along rank-one segments satisfies `f ≤ β(1 + G)`. -/
theorem le_growth_of_split [NeZero N] (hNm : N ≤ m) {p : ℝ} (hp : 0 ≤ p) {gt : ℝ≥0 → ℝ≥0}
    (hgt_mono : Monotone gt) (hgt_shift : ∀ c : ℝ≥0, ∃ A B : ℝ≥0, ∀ s : ℝ≥0,
      gt (c + s) ≤ A + B * gt s)
    {F : Mat m N → ℝ≥0∞} {γ δ : ℝ}
    (hBB : ∀ ζ : Mat m N, γ ≤ (properDomainJacobian ζ : ℝ) →
      F ζ ≤ ENNReal.ofReal δ * (1 + bbG p gt ζ)) :
    ∃ β : ℝ≥0, ∀ f : Mat m N → ℝ≥0∞, RankOneSplit f → (∀ ζ, f ζ ≤ F ζ) →
      ∀ ξ, f ξ ≤ β * (1 + bbG p gt ξ) := by
  set γ' := max γ 1
  have hγ'1 : 1 ≤ γ' := le_max_right _ _
  set q := p / 2
  have hq : 0 ≤ q := by positivity
  set g : ℝ → ℝ≥0∞ := fun s => (gt s.toNNReal : ℝ≥0∞)
  have hg : Monotone g := fun s t hst => by
    simp only [g]
    exact_mod_cast hgt_mono (Real.toNNReal_le_toNNReal hst)
  set Φ : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal δ * (1 + ENNReal.ofReal (s ^ q) + g s)
  have hG : ∀ ζ : Mat m N, bbG p gt ζ =
      ENNReal.ofReal ((matrixFrobeniusNorm ζ ^ 2) ^ q) + g (matrixFrobeniusNorm ζ ^ 2) := by
    intro ζ
    simp only [bbG, g, frob_rpow_eq ζ p]
    congr 3
    exact (Real.toNNReal_of_nonneg _).symm
  -- the leaves
  have hleaf : ∀ f : Mat m N → ℝ≥0∞, (∀ ζ, f ζ ≤ F ζ) →
      ∀ (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) (A : Mat m N),
      OrthCols b (matrixEuclideanLinearMap A) →
      (∀ i, γ' ≤ ‖matrixEuclideanLinearMap A (b i)‖) → f A ≤ Φ (capSum b γ' A) := by
    intro f hfF b A hA hcol
    have hjac : γ ≤ (properDomainJacobian A : ℝ) := by
      rw [properDomainJacobian_coe_eq_normDet, normDet_of_orthCols hA]
      calc γ ≤ γ' := le_max_left _ _
        _ ≤ γ' ^ N := le_self_pow₀ hγ'1 (NeZero.ne N)
        _ = ∏ _i : Fin N, γ' := by simp
        _ ≤ ∏ i, ‖matrixEuclideanLinearMap A (b i)‖ :=
            Finset.prod_le_prod (fun _ _ => by linarith) fun i _ => hcol i
    have hF : matrixFrobeniusNorm A ^ 2 ≤ capSum b γ' A := by
      rw [matrixFrobeniusNorm_sq_eq A b]
      exact Finset.sum_le_sum fun i _ => le_max_right _ _
    refine (hfF A).trans ((hBB A hjac).trans ?_)
    simp only [Φ]
    rw [hG A, ← add_assoc]
    gcongr
    exact hg hF
  -- the constants
  set c : ℝ := (N : ℝ) * γ' ^ 2
  have hc : 0 ≤ c := by positivity
  obtain ⟨Ac, Bc, hAB⟩ := hgt_shift c.toNNReal
  set K : ℝ≥0∞ := ENNReal.ofReal (1 + 2 ^ q * c ^ q) + Ac + ENNReal.ofReal (2 ^ q) + Bc
  have hK : K ≠ ⊤ := by simp [K, ENNReal.add_eq_top]
  set β : ℝ≥0∞ := 2 ^ N * (ENNReal.ofReal δ * K)
  have hβ : β ≠ ⊤ := by
    simp only [β]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK)
  refine ⟨β.toNNReal, fun f hsplit hfF ξ => ?_⟩
  rw [ENNReal.coe_toNNReal hβ]
  obtain ⟨b, hb⟩ := exists_orthCols (matrixEuclideanLinearMap ξ)
  have htree := le_pow_two_mul_of_split hNm hsplit Φ (hleaf f hfF b) _ ξ hb rfl
  have hF2 : 0 ≤ matrixFrobeniusNorm ξ ^ 2 := sq_nonneg _
  have hcap : capSum b γ' ξ ≤ c + matrixFrobeniusNorm ξ ^ 2 := by
    rw [matrixFrobeniusNorm_sq_eq ξ b]
    calc capSum b γ' ξ ≤ ∑ i, (γ' ^ 2 + ‖matrixEuclideanLinearMap ξ (b i)‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => max_le_add_of_nonneg (sq_nonneg _) (sq_nonneg _)
      _ = c + ∑ i, ‖matrixEuclideanLinearMap ξ (b i)‖ ^ 2 := by
          rw [Finset.sum_add_distrib]
          simp [c]
  have hcap0 : 0 ≤ capSum b γ' ξ :=
    Finset.sum_nonneg fun _ _ => (sq_nonneg γ').trans (le_max_left _ _)
  have hΦ : Φ (capSum b γ' ξ) ≤ Φ (c + matrixFrobeniusNorm ξ ^ 2) := by
    simp only [Φ]
    gcongr
    exact hg hcap
  have hpow : (2 : ℝ≥0∞) ^ (smallCols b γ' ξ).card ≤ 2 ^ N := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hK1 : ENNReal.ofReal (1 + 2 ^ q * c ^ q) + Ac ≤ K := by
    simp only [K]
    exact le_add_right (le_add_right le_rfl)
  have hK2 : ENNReal.ofReal (2 ^ q) ≤ K := by
    simp only [K]
    exact le_add_right (le_add_left le_rfl)
  have hK3 : (Bc : ℝ≥0∞) ≤ K := by
    simp only [K]
    exact le_add_left le_rfl
  have hfinal : Φ (c + matrixFrobeniusNorm ξ ^ 2) ≤
      ENNReal.ofReal δ * (K * (1 + bbG p gt ξ)) := by
    simp only [Φ]
    rw [hG ξ]
    gcongr ENNReal.ofReal δ * ?_
    have h1 : ENNReal.ofReal ((c + matrixFrobeniusNorm ξ ^ 2) ^ q) ≤
        ENNReal.ofReal (2 ^ q * c ^ q) +
          ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((matrixFrobeniusNorm ξ ^ 2) ^ q) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      exact ENNReal.ofReal_le_ofReal ((add_rpow_le_two_rpow hc hF2 hq).trans_eq (by ring))
    have h2 : g (c + matrixFrobeniusNorm ξ ^ 2) ≤ Ac + Bc * g (matrixFrobeniusNorm ξ ^ 2) := by
      simp only [g]
      rw [Real.toNNReal_add hc hF2]
      exact_mod_cast hAB _
    calc 1 + ENNReal.ofReal ((c + matrixFrobeniusNorm ξ ^ 2) ^ q) +
          g (c + matrixFrobeniusNorm ξ ^ 2)
        ≤ 1 + (ENNReal.ofReal (2 ^ q * c ^ q) +
            ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((matrixFrobeniusNorm ξ ^ 2) ^ q)) +
          (Ac + Bc * g (matrixFrobeniusNorm ξ ^ 2)) := by gcongr
      _ = (ENNReal.ofReal (1 + 2 ^ q * c ^ q) + Ac) * 1 +
            ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((matrixFrobeniusNorm ξ ^ 2) ^ q) +
            Bc * g (matrixFrobeniusNorm ξ ^ 2) := by
          rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
          ring
      _ ≤ K * 1 + K * ENNReal.ofReal ((matrixFrobeniusNorm ξ ^ 2) ^ q) +
            K * g (matrixFrobeniusNorm ξ ^ 2) := by
          gcongr
      _ = K * (1 + (ENNReal.ofReal ((matrixFrobeniusNorm ξ ^ 2) ^ q) +
            g (matrixFrobeniusNorm ξ ^ 2))) := by ring
  calc f ξ ≤ 2 ^ (smallCols b γ' ξ).card * Φ (capSum b γ' ξ) := htree
    _ ≤ 2 ^ N * Φ (c + matrixFrobeniusNorm ξ ^ 2) := by gcongr
    _ ≤ 2 ^ N * (ENNReal.ofReal δ * (K * (1 + bbG p gt ξ))) := by gcongr
    _ = β * (1 + bbG p gt ξ) := by simp only [β]; ring

/-- **Lemma `lem:BB`** (variant of Ben Belgacem's lemma). Let `N ≤ m`, `p ≥ 0`, `g̃ : [0,∞[ → [0,∞[`
nondecreasing such that for every `c ≥ 0` there are `A_c, B_c ≥ 0` with
`g̃(c + s) ≤ A_c + B_c g̃(s)` for all `s ≥ 0`, `G(ξ) = |ξ|^p + g̃(|ξ|²)`, and `F : 𝕄 → [0,∞]` with
`F ≤ δ(1 + G)` on `{v ≥ γ}`. Then `R₁ F ≤ β(1 + G)` on `𝕄` for some `β`.

The article (since 2026-10-15) assumes the same, with moreover `γ, δ > 0`, which is not used, and
`β > 0` in the conclusion (`lem_BB_paper`). -/
theorem lem_BB [NeZero N] (hNm : N ≤ m) {p : ℝ} (hp : 0 ≤ p) {gt : ℝ≥0 → ℝ≥0}
    (hgt_mono : Monotone gt) (hgt_shift : ∀ c : ℝ≥0, ∃ A B : ℝ≥0, ∀ s : ℝ≥0,
      gt (c + s) ≤ A + B * gt s)
    {F : Mat m N → ℝ≥0∞} {γ δ : ℝ}
    (hBB : ∀ ζ : Mat m N, γ ≤ (properDomainJacobian ζ : ℝ) →
      F ζ ≤ ENNReal.ofReal δ * (1 + bbG p gt ζ)) :
    ∃ β : ℝ≥0, ∀ ξ, Rone F ξ ≤ β * (1 + bbG p gt ξ) := by
  obtain ⟨β, hβ⟩ := le_growth_of_split hNm hp hgt_mono hgt_shift hBB
  exact ⟨β, hβ _ (rankOneConvex_Rone F).split (Rone_le F)⟩

/-- `𝒵_aff W⁺ ≤ R₁ W⁺ ≤ β(1 + G)` on all of `𝕄` (the bound `(eq:BB)` of the proof of `sep:iii`):
`𝒵_aff W⁺` is finite everywhere by `lemmaree_of_jacobian`, hence rank-one convex and below
`R₁ W⁺` (`Zaff_le_Rone`), and `lem_BB` bounds `R₁ W⁺`. -/
theorem properDomainWPlus_Zaff_le_growth [NeZero N] (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∃ β : ℝ≥0, ∀ ξ, Zaff (properDomainWPlus D KD HD CD) ξ ≤ β * (1 + properDomainG D ξ) := by
  have hp : 0 ≤ D.p := (Nat.cast_nonneg N).trans D.dim_lt_p.le
  obtain ⟨β, hβ⟩ := lem_BB KD.dim_le_m hp D.gTilde_monotone D.gTilde_shift
    (fun ζ hζ => properDomainWPlus_le_growth_of_jacobian_ge D KD HD CD ζ hζ)
  have hfin : ∀ ζ, Zaff (properDomainWPlus D KD HD CD) ζ ≠ ⊤ := fun ζ =>
    lemmaree_of_jacobian KD.dim_le_m _
      (fun ζ hζ => (properDomainWPlus_lt_top_of_jacobian_ne_zero D KD HD CD ζ hζ).ne) ζ
  exact ⟨β, fun ξ => (Zaff_le_Rone hfin ξ).trans (hβ ξ)⟩

/-- **`prop:separating` (iii), upper bound**: `𝒵_aff W_v(x,·) ≤ β(1 + G)` for every `x`. -/
theorem properDomainWv_Zaff_le_growth [NeZero N] (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) :
    ∃ β : ℝ≥0, ∀ x ξ, Zaff (properDomainWv D KD HD CD x) ξ ≤ β * (1 + properDomainG D ξ) := by
  obtain ⟨β, hβ⟩ := properDomainWPlus_Zaff_le_growth D KD HD CD
  exact ⟨β, fun x ξ => (properDomainWv_Zaff_le_WPlus D KD HD CD x ξ).trans (hβ ξ)⟩

end Homogenization
