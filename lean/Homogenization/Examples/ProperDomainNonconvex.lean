import Homogenization.Examples.ProperDomainGeometry

/-!
# Non-convexity in clause (ii) of `prop:properdomain`

The full-Jacobian set is non-convex once the domain dimension is positive and does not exceed
the target dimension. The same two witnesses, placed in the first row block and with zero in
the second block, prove non-convexity of the effective domain of the concrete `W♯` example.
-/

open Set
open scoped ENNReal

namespace Homogenization

variable {N m : ℕ}

/-- The coordinate inclusion from `ℝᴺ` into the first `N` coordinates of `ℝᵐ`. -/
noncomputable def properDomainCoordinateEmbedding (_hNm : N ≤ m) : Mat m N :=
  ContinuousLinearMap.pi fun i =>
    if hi : i.val < N then
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) ⟨i.val, hi⟩
    else 0

@[simp]
theorem properDomainCoordinateEmbedding_apply (hNm : N ≤ m) (x : Sp N) (j : Fin N) :
    properDomainCoordinateEmbedding hNm x (Fin.castLE hNm j) = x j := by
  simp [properDomainCoordinateEmbedding]

private theorem properDomainCoordinateEmbedding_injective (hNm : N ≤ m) :
    Function.Injective (properDomainCoordinateEmbedding hNm).toLinearMap := by
  intro x y h
  funext j
  have h' := congrFun h (Fin.castLE hNm j)
  simpa using h'

private theorem matrixEuclideanLinearMap_injective_of_matrix_injective
    (A : Mat m N) (hA : Function.Injective A.toLinearMap) :
    Function.Injective (matrixEuclideanLinearMap A) := by
  unfold matrixEuclideanLinearMap
  exact (WithLp.linearEquiv 2 ℝ (Tgt m)).symm.injective.comp
    (hA.comp (WithLp.linearEquiv 2 ℝ (Sp N)).injective)

private theorem properDomainJacobian_ne_zero_of_matrix_injective
    (A : Mat m N) (hA : Function.Injective A.toLinearMap) :
    properDomainJacobian A ≠ 0 := by
  have hinj := matrixEuclideanLinearMap_injective_of_matrix_injective A hA
  have hsing : ∀ i : Fin N, 0 < (matrixEuclideanLinearMap A).singularValues i := by
    intro i
    have h := (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos
      (matrixEuclideanLinearMap A)).mp hinj i
    simpa using h
  have hprod : 0 < ∏ i : Fin N, (matrixEuclideanLinearMap A).singularValues i :=
    Finset.prod_pos fun i _ => hsing i
  exact ne_of_gt hprod

theorem properDomainCoordinateEmbedding_mem_sigma (hNm : N ≤ m) :
    properDomainCoordinateEmbedding hNm ∈ properDomainSigma :=
  properDomainJacobian_ne_zero_of_matrix_injective _
    (properDomainCoordinateEmbedding_injective hNm)

theorem neg_properDomainCoordinateEmbedding_mem_sigma (hNm : N ≤ m) :
    -properDomainCoordinateEmbedding hNm ∈ properDomainSigma := by
  change properDomainJacobian (-properDomainCoordinateEmbedding hNm) ≠ 0
  apply properDomainJacobian_ne_zero_of_matrix_injective
  intro x y h
  apply properDomainCoordinateEmbedding_injective hNm
  have h' : -properDomainCoordinateEmbedding hNm x =
      -properDomainCoordinateEmbedding hNm y := by simpa using h
  exact neg_injective h'

theorem zero_not_mem_properDomainSigma (hN : 1 ≤ N) :
    (0 : Mat m N) ∉ properDomainSigma := by
  have hj0 : properDomainJacobian (0 : Mat m N) = 0 := by
    apply Subtype.ext
    simp [properDomainJacobian, matrixEuclideanLinearMap,
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN)]
  simp [properDomainSigma, hj0]

/-- Under the article's dimensional hypotheses `1 ≤ N ≤ m`, the set
`Σ={A | v(A)≠0}` is not convex. The witnesses are the coordinate inclusion and its negative;
their midpoint is zero, whose Jacobian vanishes. -/
theorem properDomainSigma_not_convex (hN : 1 ≤ N) (hNm : N ≤ m) :
    ¬ Convex ℝ (properDomainSigma (m := m) (N := N)) := by
  let E := properDomainCoordinateEmbedding hNm
  have hE : E ∈ properDomainSigma := properDomainCoordinateEmbedding_mem_sigma hNm
  have hneg : -E ∈ properDomainSigma := neg_properDomainCoordinateEmbedding_mem_sigma hNm
  have hzero : (0 : Mat m N) ∉ properDomainSigma := zero_not_mem_properDomainSigma hN
  intro hconv
  have hmid := (convex_iff_add_mem.mp hconv) hE hneg
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have : (1 / 2 : ℝ) • E + (1 / 2 : ℝ) • (-E) = 0 := by
    module
  rw [this] at hmid
  exact hzero hmid

variable {m₁ m₂ : ℕ}
variable (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
variable (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
variable (G₂ : Mat m₂ N → ℝ≥0∞) (x : Sp N)

/-- If the second-block domain contains zero, then the effective domain of `W♯(x,·)` is
non-convex under `1 ≤ N ≤ m₁`. The witnesses are the block matrices corresponding to
`(E,0)` and `(-E,0)`, whose midpoint corresponds to `(0,0)`. -/
theorem properDomainWSharp_domain_not_convex
    (hN : 1 ≤ N) (hzero₂ : (0 : Mat m₂ N) ∈ dom G₂) :
    ¬ Convex ℝ (dom (properDomainWSharp D KD HD CD G₂ x)) := by
  have hE : (properDomainCoordinateEmbedding KD.dim_le_m) ∈ properDomainSigma :=
    properDomainCoordinateEmbedding_mem_sigma KD.dim_le_m
  have hnegE : (-properDomainCoordinateEmbedding KD.dim_le_m) ∈ properDomainSigma :=
    neg_properDomainCoordinateEmbedding_mem_sigma KD.dim_le_m
  have hzero₁ : (0 : Mat m₁ N) ∉ properDomainSigma := zero_not_mem_properDomainSigma hN
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  let Aplus : Mat (m₁ + m₂) N :=
    e.symm (properDomainCoordinateEmbedding KD.dim_le_m, (0 : Mat m₂ N))
  let Aminus : Mat (m₁ + m₂) N := -Aplus
  have hAplus : Aplus ∈ dom (properDomainWSharp D KD HD CD G₂ x) := by
    rw [dom_properDomainWSharp]
    change e Aplus ∈ properDomainSigma ×ˢ dom G₂
    simp [Aplus, e, hE, hzero₂]
  have hAminus : Aminus ∈ dom (properDomainWSharp D KD HD CD G₂ x) := by
    rw [dom_properDomainWSharp]
    change e Aminus ∈ properDomainSigma ×ˢ dom G₂
    have heplus : e Aplus = (properDomainCoordinateEmbedding KD.dim_le_m, (0 : Mat m₂ N)) := by
      simp [Aplus]
    rw [show e Aminus = -(properDomainCoordinateEmbedding KD.dim_le_m, (0 : Mat m₂ N)) by
      simp [Aminus, heplus]]
    exact ⟨hnegE, by simpa using hzero₂⟩
  intro hconv
  have hmid := (convex_iff_add_mem.mp hconv) hAplus hAminus
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (1 / 2 : ℝ) • Aplus + (1 / 2 : ℝ) • Aminus = 0 := by
    simp [Aminus]
  rw [hcomb] at hmid
  rw [dom_properDomainWSharp] at hmid
  have hfirst : (0 : Mat m₁ N) ∈ properDomainSigma := by
    have h := hmid
    change e 0 ∈ properDomainSigma ×ˢ dom G₂ at h
    simpa [e] using h.1
  exact hzero₁ hfirst

variable [NeZero m₂]

/-- The concrete `W♯` from clause (ii) has non-convex effective domain. Its points are the
block matrices corresponding to `(E,0)` and `(-E,0)`; the midpoint corresponds to `(0,0)`. -/
theorem properDomainWSharpExample_domain_not_convex [NeZero N]
    (hN : 1 ≤ N) (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) (x : Sp N) :
    ¬ Convex ℝ (dom (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) (N := N) D KD HD CD x)) := by
  apply properDomainWSharp_domain_not_convex D KD HD CD
    (properDomainG2 D.p) x hN
  rw [mem_dom_properDomainG2_iff (m := m₂) (N := N) D.p]
  exact zero_mem_properDomainHalfSpace

end Homogenization
