import Mathlib

/-!
# Notation and envelopes

Formalization of §2 (`sec:notation`) and of the standing assumptions of §3 of
`Homogenization_beyond_convex_growthV1.tex`.

## Conventions and deviations from the paper

* `ℝᴺ` is `Sp N := Fin N → ℝ` with its Lebesgue measure `volume`, `ℝᵐ` is `Tgt m`.
* The matrix space `𝕄^{m×N}` is realized as `Mat m N := Sp N →L[ℝ] Tgt m`, so that the gradient of
  `φ` at `y` is literally `fderiv ℝ φ y`. Its norm is the operator norm instead of the Frobenius
  norm; the two are equivalent, which only changes the constant `c₀` in (Z4) and is invisible in
  `Lᵖ` spaces.
* Values in `[0,∞]` are `ℝ≥0∞`, integrals are lower Lebesgue integrals `∫⁻`.
* **Piecewise affine functions (`IsPWAffine`) are required to be Lipschitz.** This is not stated
  in the definition of `Aff(U;ℝᵐ)` in §2.2 of the paper, but it is necessary for the inclusion
  `Aff₀(U;ℝᵐ) ⊂ W^{1,∞}_0(U;ℝᵐ)` claimed in (2.1) (`eq:affinclusion`). Without it, for `N = m = 1`
  and `U = ]0,1[`, `φ(x) = c(x) - x` with `c` the Cantor function is continuous, vanishes on `∂U`,
  and has `φ' ≡ -1` on the open set `U ∖ K` (`K` the Cantor set), whose complement in `U` and
  whose boundary in `U` are null: `φ` satisfies the literal definition of `Aff₀(U)`, but
  `∫_U φ' = -1 ≠ 0`. With `aφ` in place of `φ` one gets `𝒵_aff f ≡ inf f`, contradicting
  `𝒵_aff G = G` for convex `G` (proof of Lemma `lem:consequences`(iii)).
* `φ ∈ Aff₀(U)` is encoded by its extension by `0` outside `U`, which is then globally Lipschitz
  (equivalent to "`φ` Lipschitz on `U` and `φ = 0` on `∂U`").
* `W^{1,p}_0(kY;ℝᵐ)` (only used on cubes, for `ℋ_p`) is encoded as the set of functions vanishing
  outside `kY` whose extension by `0` lies in `W^{1,p}(ℝᴺ;ℝᵐ)`; for a Lipschitz open set such as a
  cube this is the usual space.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

/-- The physical space `ℝᴺ`. -/
abbrev Sp (N : ℕ) := Fin N → ℝ
/-- The target space `ℝᵐ`. -/
abbrev Tgt (m : ℕ) := Fin m → ℝ
/-- The space of `m × N` matrices, realized as linear maps `ℝᴺ → ℝᵐ`. -/
abbrev Mat (m N : ℕ) := Sp N →L[ℝ] Tgt m

/-- The row-major coordinate identification of `m × N` matrices with scalar coordinates.
The first index is the target coordinate and the second is the domain coordinate. -/
noncomputable def matCoordLinearEquiv (m N : ℕ) : Mat m N ≃ₗ[ℝ] (Fin m × Fin N → ℝ) := by
  let hmat : Matrix (Fin m) (Fin N) ℝ ≃ₗ[ℝ] (Fin m × Fin N → ℝ) :=
    { toFun := fun A ij => A ij.1 ij.2
      invFun := fun A i j => A (i, j)
      left_inv := by intro A; ext i j; rfl
      right_inv := by intro A; funext ij; cases ij; rfl
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }
  exact
    (LinearMap.toContinuousLinearMap :
        (Sp N →ₗ[ℝ] Tgt m) ≃ₗ[ℝ] Mat m N).symm.trans <|
      (LinearMap.toMatrix (Pi.basisFun ℝ (Fin N)) (Pi.basisFun ℝ (Fin m))).trans hmat

/-- Continuous version of `matCoordLinearEquiv`. -/
noncomputable def matCoordEquiv (m N : ℕ) : Mat m N ≃L[ℝ] (Fin m × Fin N → ℝ) :=
  (matCoordLinearEquiv m N).toContinuousLinearEquiv

/-- Each scalar coordinate is the corresponding matrix coefficient. -/
theorem matCoordEquiv_apply (A : Mat m N) (i : Fin m) (j : Fin N) :
    matCoordEquiv m N A (i, j) = A (Pi.single j 1) i := by
  change LinearMap.toMatrix (Pi.basisFun ℝ (Fin N)) (Pi.basisFun ℝ (Fin m))
      A.toLinearMap i j = A (Pi.single j 1) i
  rw [LinearMap.toMatrix_apply]
  simp

/-- The coordinate sup norm of a matrix is bounded by its operator norm. Therefore transporting
a coordinate Lipschitz estimate to `Mat m N` through `matCoordEquiv` does not increase its
constant. -/
theorem matCoordEquiv_norm_le (A : Mat m N) : ‖matCoordEquiv m N A‖ ≤ ‖A‖ := by
  refine (pi_norm_le_iff_of_nonneg
    (x := (matCoordEquiv m N A : Fin m × Fin N → ℝ)) (r := ‖A‖)
    (norm_nonneg A)).2 ?_
  intro ij
  rw [Real.norm_eq_abs, matCoordEquiv_apply]
  have hsingle : ‖(Pi.single ij.2 (1 : ℝ) : Sp N)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro k
    by_cases hk : k = ij.2 <;> simp [hk]
  calc
    |A (Pi.single ij.2 (1 : ℝ)) ij.1| ≤ ‖A (Pi.single ij.2 (1 : ℝ))‖ :=
      norm_le_pi_norm (A (Pi.single ij.2 (1 : ℝ))) ij.1
    _ ≤ ‖A‖ * ‖(Pi.single ij.2 (1 : ℝ) : Sp N)‖ :=
      A.le_opNorm (Pi.single ij.2 (1 : ℝ))
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hsingle (norm_nonneg _)
    _ = ‖A‖ := by ring

/-- The rank-one operator `d ⊗ ν`, with convention `(d ⊗ ν) x = (ν · x) d`. -/
noncomputable def rankOne (d : Tgt m) (ν : Sp N) : Mat m N :=
  (matCoordEquiv m N).symm (fun ij => d ij.1 * ν ij.2)

@[simp]
theorem matCoordEquiv_rankOne (d : Tgt m) (ν : Sp N) (i : Fin m) (j : Fin N) :
    matCoordEquiv m N (rankOne d ν) (i, j) = d i * ν j := by
  simp [rankOne]

/-- In the standard coordinate directions, `rankOne` corresponds to a single matrix entry. -/
theorem matCoordEquiv_rankOne_single (i : Fin m) (j : Fin N) :
    matCoordEquiv m N (rankOne (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))) =
      Pi.single (i, j) (1 : ℝ) := by
  funext ij
  rcases ij with ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;>
    simp [matCoordEquiv_rankOne, hi, hj]

variable {N m : ℕ}

/-! ### Cubes -/

/-- The open cube `Q_ρ(x) = x + ρ Y`, `Y = ]-1/2,1/2[ᴺ`. -/
def cube (ρ : ℝ) (x : Sp N) : Set (Sp N) :=
  Set.pi univ fun i => Ioo (x i - ρ / 2) (x i + ρ / 2)

theorem isOpen_cube (ρ : ℝ) (x : Sp N) : IsOpen (cube ρ x) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

/-- A cube of nonpositive side length is empty. -/
theorem cube_eq_empty_of_nonpos [NeZero N] {ρ : ℝ} (hρ : ρ ≤ 0) (x : Sp N) :
    cube ρ x = ∅ := by
  rw [cube]
  refine Set.univ_pi_eq_empty (i := 0) ?_
  rw [Ioo_eq_empty]
  linarith

/-- The closure of a positive-radius cube is the corresponding product of closed intervals. -/
theorem cube_closure_pi_Icc [NeZero N] {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    closure (cube ρ x) = Set.pi univ (fun i => Icc (x i - ρ / 2) (x i + ρ / 2)) := by
  rw [cube, closure_pi_set]
  ext y
  simp only [Set.mem_pi, mem_univ, true_implies]
  have hIoo : ∀ i : Fin N, closure (Ioo (x i - ρ / 2) (x i + ρ / 2)) =
      Icc (x i - ρ / 2) (x i + ρ / 2) := by
    intro i
    exact closure_Ioo (by linarith [hρ])
  constructor
  · intro hy i
    simpa only [hIoo] using hy i
  · intro hy i
    simpa only [hIoo] using hy i

/-- Every boundary point of a positive-radius cube lies on at least one face. This isolates the
finite-face geometry used to build the local graph chart, including points where several faces
are active. -/
theorem exists_active_cube_face [NeZero N] {ρ : ℝ} (hρ : 0 < ρ) {c y : Sp N}
    (hy : y ∈ frontier (cube ρ c)) :
    ∃ i : Fin N, y i = c i - ρ / 2 ∨ y i = c i + ρ / 2 := by
  rw [frontier, (isOpen_cube ρ c).interior_eq] at hy
  rcases hy with ⟨hclosure, hnot⟩
  have hclosed : y ∈ Set.pi univ
      (fun i => Icc (c i - ρ / 2) (c i + ρ / 2)) := by
    rw [← cube_closure_pi_Icc hρ c]
    exact hclosure
  by_contra h
  simp only [not_exists, not_or] at h
  have hycube : y ∈ cube ρ c := by
    rw [cube, Set.mem_pi]
    intro i hi
    have hi' := (Set.mem_pi.mp hclosed) i (by simp)
    have hne := h i
    exact ⟨lt_of_le_of_ne hi'.1 (fun heq => hne.1 heq.symm),
      lt_of_le_of_ne hi'.2 hne.2⟩
  exact hnot hycube

/-- At each coordinate of a boundary point, exactly one of the two faces is active or the
coordinate lies strictly between the faces. This gives the complete finite active-face data used
in a corner chart. -/
theorem cube_boundary_coordinate_cases [NeZero N] {ρ : ℝ} (hρ : 0 < ρ) {c y : Sp N}
    (hy : y ∈ frontier (cube ρ c)) (i : Fin N) :
    y i = c i - ρ / 2 ∨ y i = c i + ρ / 2 ∨
      (c i - ρ / 2 < y i ∧ y i < c i + ρ / 2) := by
  have hclosure : y ∈ closure (cube ρ c) := frontier_subset_closure hy
  have hclosed : y ∈ Set.pi univ
      (fun j => Icc (c j - ρ / 2) (c j + ρ / 2)) := by
    rw [← cube_closure_pi_Icc hρ c]
    exact hclosure
  have hi := (Set.mem_pi.mp hclosed) i (by simp)
  rcases lt_or_eq_of_le hi.1 with hlow | hlow
  · rcases lt_or_eq_of_le hi.2 with hupp | hupp
    · exact Or.inr (Or.inr ⟨hlow, hupp⟩)
    · exact Or.inr (Or.inl hupp)
  · exact Or.inl hlow.symm

/-- The signed coordinate normal of a cube face, viewed in Euclidean coordinates. -/
noncomputable def cubeFaceNormal (c y : Sp N) (ρ : ℝ) (i : Fin N) :
    EuclideanSpace ℝ (Fin N) :=
  if y i = c i + ρ / 2 then EuclideanSpace.single i 1 else EuclideanSpace.single i (-1)

/-- A direction pointing strictly into the cube at every active face. -/
noncomputable def cubeInwardDirection (c y : Sp N) (ρ : ℝ) : Sp N := fun i =>
  if y i = c i + ρ / 2 then -1 else if y i = c i - ρ / 2 then 1 else 0

/-- Each active outward normal has strictly negative inner product with the inward direction. -/
theorem cubeFaceNormal_inner_inward [NeZero N] {ρ : ℝ} (hρ : 0 < ρ) {c y : Sp N}
    (i : Fin N) (hface : y i = c i - ρ / 2 ∨ y i = c i + ρ / 2) :
    inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 (cubeInwardDirection c y ρ)) = -1 := by
  rcases hface with hlo | hup
  · have hend : c i - ρ / 2 ≠ c i + ρ / 2 := by linarith
    simp [cubeFaceNormal, cubeInwardDirection, hlo, hend, PiLp.inner_apply]
  · have hend : c i + ρ / 2 ≠ c i - ρ / 2 := by linarith
    simp [cubeFaceNormal, cubeInwardDirection, hup, PiLp.inner_apply]

/-- The inward direction is nonzero at a boundary point because at least one face is active. -/
theorem cubeInwardDirection_ne_zero [NeZero N] {ρ : ℝ} (hρ : 0 < ρ) {c y : Sp N}
    (hy : y ∈ frontier (cube ρ c)) : cubeInwardDirection c y ρ ≠ 0 := by
  obtain ⟨i, hface⟩ := exists_active_cube_face hρ hy
  have hi : cubeInwardDirection c y ρ i ≠ 0 := by
    rcases hface with hlo | hup
    · have hend : c i - ρ / 2 ≠ c i + ρ / 2 := by linarith
      simp [cubeInwardDirection, hlo, hend]
    · simp [cubeInwardDirection, hup]
  intro h
  have hcoord := congrFun h i
  exact hi hcoord

/-- Any unit vector in Euclidean coordinates can be made the first vector of an orthonormal
basis. This is the verified Mathlib extension theorem used for the adapted corner coordinates. -/
theorem exists_orthonormalBasis_first [NeZero N]
    {e : EuclideanSpace ℝ (Fin N)} (he : ‖e‖ = 1) :
    ∃ b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), b 0 = e := by
  let s : Set (Fin N) := {0}
  let f : Fin N → EuclideanSpace ℝ (Fin N) := fun _ => e
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N) := by
    simp [finrank_euclideanSpace]
  have horth : Orthonormal ℝ (s.domRestrict f) := by
    refine ⟨?_, ?_⟩
    · intro i
      simpa [s, f] using he
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  refine ⟨b, ?_⟩
  simpa only [f] using hb 0 (by simp [s])

/-- The explicit continuous linear equivalence associated to an orthonormal frame, with all
coordinates negated so the interior vertical epigraph is a subgraph in the project's convention. -/
noncomputable def cubeAdaptedCoordinates (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) : Sp N ≃L[ℝ] Sp N :=
  (((WithLp.linearEquiv 2 ℝ (Sp N)).symm.trans b.repr.toLinearEquiv).trans
    (LinearEquiv.neg ℝ : EuclideanSpace ℝ (Fin N) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))).trans
      (WithLp.linearEquiv 2 ℝ (Sp N)) |>.toContinuousLinearEquiv

/-- Coordinate identity for the adapted transform. -/
theorem cubeAdaptedCoordinates_apply (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (w : Sp N) (i : Fin N) :
    cubeAdaptedCoordinates b w i = -inner ℝ (b i) (WithLp.toLp 2 w) := by
  simp [cubeAdaptedCoordinates, OrthonormalBasis.repr_apply_apply]

/-- The first coordinate direction, converted back to the project's `Sp N` representation. -/
noncomputable def cubeAdaptedVertical [NeZero N]
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) : Sp N :=
  WithLp.ofLp (b 0)

/-- The affine height required by one active face, evaluated on a horizontal coordinate. -/
noncomputable def cubeFaceGraphHeight [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (c y : Sp N) (ρ : ℝ) (i : Fin N) (z : Sp N) : ℝ :=
  inner ℝ (cubeFaceNormal c y ρ i)
      (WithLp.toLp 2 ((cubeAdaptedCoordinates b).symm (update z 0 0))) /
    (-inner ℝ (cubeFaceNormal c y ρ i) (b 0))

/-- The continuous linear projection that removes the first adapted coordinate. -/
noncomputable def cubeHorizontalProjection [NeZero N] : Sp N →L[ℝ] Sp N :=
  ContinuousLinearMap.id ℝ (Sp N) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) (0 : Fin N)).smulRight
      (Pi.single 0 (1 : ℝ))

@[simp]
theorem cubeHorizontalProjection_apply [NeZero N] (z : Sp N) :
    cubeHorizontalProjection z = update z 0 0 := by
  ext i
  by_cases hi : i = 0 <;> simp [cubeHorizontalProjection, hi]

/-- The height of a face is a continuous linear function of horizontal coordinates. The
operator norm gives an explicit finite Lipschitz constant in the project's `Pi` norm. -/
noncomputable def cubeFaceHeightMap [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (c y : Sp N) (ρ : ℝ) (i : Fin N) : Sp N →L[ℝ] ℝ :=
  (-inner ℝ (cubeFaceNormal c y ρ i) (b 0))⁻¹ •
    ((innerSL ℝ (cubeFaceNormal c y ρ i)).toContinuousLinearMap.comp
      (((WithLp.linearEquiv 2 ℝ (Sp N)).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((cubeAdaptedCoordinates b).symm.toContinuousLinearMap.comp cubeHorizontalProjection)))

theorem cubeFaceGraphHeight_eq_map [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (c y : Sp N) (ρ : ℝ) (i : Fin N) (z : Sp N) :
    cubeFaceGraphHeight b c y ρ i z = cubeFaceHeightMap b c y ρ i z := by
  simp [cubeFaceGraphHeight, cubeFaceHeightMap, div_eq_mul_inv, cubeHorizontalProjection_apply]
  ring

theorem cubeFaceGraphHeight_lipschitz [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (c y : Sp N) (ρ : ℝ) (i : Fin N) :
    LipschitzWith ‖cubeFaceHeightMap b c y ρ i‖₊ (cubeFaceGraphHeight b c y ρ i) := by
  have hfun : cubeFaceGraphHeight b c y ρ i = cubeFaceHeightMap b c y ρ i := by
    funext z
    exact cubeFaceGraphHeight_eq_map b c y ρ i z
  rw [hfun]
  exact (cubeFaceHeightMap b c y ρ i).lipschitz

/-- In adapted coordinates, the vertical unit vector has first coordinate `-1` and all
horizontal coordinates zero. -/
theorem cubeAdaptedCoordinates_vertical [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (i : Fin N) :
    cubeAdaptedCoordinates b (cubeAdaptedVertical b) i = if i = 0 then -1 else 0 := by
  rw [cubeAdaptedCoordinates_apply]
  by_cases hi : i = 0
  · subst i
    have hnorm := b.orthonormal.1 (0 : Fin N)
    simp [cubeAdaptedVertical, hnorm]
  · have horth := b.orthonormal.2 hi
    rw [if_neg hi]
    simp [cubeAdaptedVertical, horth]

/-- Every displacement splits into its horizontal component (first adapted coordinate zero) and
its vertical component along the first vector of the adapted orthonormal basis. The identity is
stated in the original `Sp N` coordinates so it can be used directly in local boundary charts. -/
theorem cubeAdaptedCoordinates_decomposition [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (w : Sp N) :
    w = (cubeAdaptedCoordinates b).symm
        (update (cubeAdaptedCoordinates b w) 0 0) +
      (-(cubeAdaptedCoordinates b w 0)) • cubeAdaptedVertical b := by
  apply (cubeAdaptedCoordinates b).injective
  rw [(cubeAdaptedCoordinates b).map_add, (cubeAdaptedCoordinates b).map_smul]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  ext i
  change cubeAdaptedCoordinates b w i =
    update (cubeAdaptedCoordinates b w) 0 0 i +
      (-(cubeAdaptedCoordinates b w 0)) * cubeAdaptedCoordinates b (cubeAdaptedVertical b) i
  rw [cubeAdaptedCoordinates_vertical]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [hi]

/-- A displacement satisfies one active face precisely when its vertical coordinate lies above
the affine height of that face. The denominator is the positive inward component of the face
normal. -/
theorem cubeFace_constraint_iff_height [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (c y w : Sp N) (ρ : ℝ) (i : Fin N)
    (hneg : inner ℝ (cubeFaceNormal c y ρ i) (b 0) < 0) :
    inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 w) < 0 ↔
      -(cubeAdaptedCoordinates b w 0) >
        cubeFaceGraphHeight b c y ρ i (cubeAdaptedCoordinates b w) := by
  let z := cubeAdaptedCoordinates b w
  let h := (cubeAdaptedCoordinates b).symm (update z 0 0)
  let t := -z 0
  have hdecomp : w = h + t • cubeAdaptedVertical b := by
    simpa [h, t, z] using cubeAdaptedCoordinates_decomposition b w
  have hvert : WithLp.toLp 2 (cubeAdaptedVertical b) = b 0 := by
    simp [cubeAdaptedVertical]
  have hformula : inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 w) =
      inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 h) +
        t * inner ℝ (cubeFaceNormal c y ρ i) (b 0) := by
    rw [hdecomp, WithLp.toLp_add, WithLp.toLp_smul, inner_add_right, inner_smul_right,
      hvert]
  have hden : 0 < -inner ℝ (cubeFaceNormal c y ρ i) (b 0) := by linarith
  change inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 w) < 0 ↔
    t > inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 h) /
      (-inner ℝ (cubeFaceNormal c y ρ i) (b 0))
  rw [hformula]
  have halg (q a : ℝ) (ha : 0 < a) (s : ℝ) :
      q + s * (-a) < 0 ↔ s > q / a := by
    constructor
    · intro hs
      have hmul : q < s * a := by nlinarith
      exact (div_lt_iff₀ ha).2 (by linarith)
    · intro hs
      have hmul : q < s * a := (div_lt_iff₀ ha).mp (by linarith)
      nlinarith
  simpa using halg (inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 h))
    (-inner ℝ (cubeFaceNormal c y ρ i) (b 0)) hden t

/-- The horizontal component in the preceding decomposition is orthogonal to its vertical
direction. -/
theorem cubeAdaptedCoordinates_horizontal_orthogonal [NeZero N] (b : OrthonormalBasis (Fin N) ℝ
    (EuclideanSpace ℝ (Fin N))) (w : Sp N) :
    inner ℝ (b 0)
      (WithLp.toLp 2
        ((cubeAdaptedCoordinates b).symm (update (cubeAdaptedCoordinates b w) 0 0))) = 0 := by
  have hcoord := cubeAdaptedCoordinates_apply b
    ((cubeAdaptedCoordinates b).symm (update (cubeAdaptedCoordinates b w) 0 0)) 0
  rw [(cubeAdaptedCoordinates b).apply_symm_apply] at hcoord
  simpa using hcoord

/-- The normalized inward direction extends to an orthonormal frame, with all active outward
normals having a negative first component in that frame. -/
theorem cube_boundary_adapted_orthonormalBasis [NeZero N] {ρ : ℝ} (hρ : 0 < ρ)
    {c y : Sp N} (hy : y ∈ frontier (cube ρ c)) :
    ∃ e : EuclideanSpace ℝ (Fin N), ∃ b : OrthonormalBasis (Fin N) ℝ
      (EuclideanSpace ℝ (Fin N)),
      ‖e‖ = 1 ∧ b 0 = e ∧
      ∀ i, (y i = c i - ρ / 2 ∨ y i = c i + ρ / 2) →
        inner ℝ (cubeFaceNormal c y ρ i) e < 0 := by
  let w : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (cubeInwardDirection c y ρ)
  have hw : w ≠ 0 := by
    intro h
    have hfun := congrArg WithLp.ofLp h
    have hdir : cubeInwardDirection c y ρ ≠ 0 := cubeInwardDirection_ne_zero hρ hy
    apply hdir
    simpa [w] using hfun
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let e : EuclideanSpace ℝ (Fin N) := ‖w‖⁻¹ • w
  have he : ‖e‖ = 1 := by
    calc
      ‖e‖ = ‖w‖⁻¹ * ‖w‖ := by simp [e, norm_smul]
      _ = 1 := inv_mul_cancel₀ hnorm.ne'
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_first he
  refine ⟨e, b, he, hb, ?_⟩
  intro i hface
  have hdot : inner ℝ (cubeFaceNormal c y ρ i) w = -1 := by
    simpa [w] using cubeFaceNormal_inner_inward hρ i hface
  rw [show e = ‖w‖⁻¹ • w from rfl, inner_smul_right, hdot]
  simpa using (neg_lt_zero.mpr (inv_pos.mpr hnorm))

/-- A finite pointwise supremum of real-valued Lipschitz functions is Lipschitz, with the maximum
of their constants. This applies to the finite collection of active-face affine graphs, including
at corners. -/
theorem LipschitzWith.finset_sup' {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]
    [Nonempty ι] {K : ι → ℝ≥0} {f : ι → X → ℝ}
    (hf : ∀ i, LipschitzWith (K i) (f i)) :
    LipschitzWith (Finset.univ.sup' Finset.univ_nonempty K)
      (fun x => Finset.univ.sup' Finset.univ_nonempty fun i => f i x) := by
  let Kmax := Finset.univ.sup' Finset.univ_nonempty K
  apply LipschitzWith.of_le_add_mul Kmax
  intro x y
  apply Finset.sup'_le Finset.univ_nonempty
  intro i hi
  have hKi : K i ≤ Kmax := Finset.le_sup' K hi
  calc
    f i x ≤ f i y + (K i : ℝ) * dist x y := (hf i).le_add_mul x y
    _ ≤ (Finset.univ.sup' Finset.univ_nonempty fun j => f j y) +
        (Kmax : ℝ) * dist x y := by
      apply add_le_add
      · exact Finset.le_sup' (fun j => f j y) hi
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hKi) dist_nonneg

/-- The indices of the active faces at a boundary point. -/
def cubeActiveFace (c y : Sp N) (ρ : ℝ) (i : Fin N) : Prop :=
  y i = c i - ρ / 2 ∨ y i = c i + ρ / 2

/-- A coordinatewise radius that keeps every inactive face and the opposite side of every active
face strictly satisfied. -/
noncomputable def cubeChartRadius (c y : Sp N) (ρ : ℝ) (i : Fin N) : ℝ :=
  by
    classical
    exact if cubeActiveFace c y ρ i then ρ / 2 else
      min (y i - (c i - ρ / 2)) ((c i + ρ / 2) - y i) / 2

theorem cubeChartRadius_pos [NeZero N] {ρ : ℝ} (hρ : 0 < ρ) {c y : Sp N}
    (hy : y ∈ frontier (cube ρ c)) (i : Fin N) : 0 < cubeChartRadius c y ρ i := by
  unfold cubeChartRadius
  split_ifs with hactive
  · exact half_pos hρ
  · have hcases := cube_boundary_coordinate_cases hρ hy i
    rcases hcases with hlo | hup | ⟨hlo, hup⟩
    · exact (hactive (Or.inl hlo)).elim
    · exact (hactive (Or.inr hup)).elim
    · positivity

/-- The product neighborhood used for a cube corner chart. -/
noncomputable def cubeChartNeighborhood (c y : Sp N) (ρ : ℝ) : Set (Sp N) :=
  Set.pi univ fun i => Ioo (y i - cubeChartRadius c y ρ i)
    (y i + cubeChartRadius c y ρ i)

theorem cubeChartNeighborhood_isOpen (c y : Sp N) (ρ : ℝ) :
    IsOpen (cubeChartNeighborhood c y ρ) := by
  exact isOpen_set_pi finite_univ fun i _ => isOpen_Ioo

theorem cubeChartNeighborhood_mem_nhds [NeZero N] {ρ : ℝ} (hρ : 0 < ρ) {c y : Sp N}
    (hy : y ∈ frontier (cube ρ c)) : cubeChartNeighborhood c y ρ ∈ 𝓝 y := by
  apply (cubeChartNeighborhood_isOpen c y ρ).mem_nhds
  rw [cubeChartNeighborhood, Set.mem_pi]
  intro i hi
  have hδ := cubeChartRadius_pos hρ hy i
  constructor <;> linarith

theorem cubeChartNeighborhood_opposite_faces [NeZero N] {ρ : ℝ} (hρ : 0 < ρ)
    {c y q : Sp N} (hy : y ∈ frontier (cube ρ c))
    (hq : q ∈ cubeChartNeighborhood c y ρ) (i : Fin N) :
    (y i = c i - ρ / 2 → q i < c i + ρ / 2) ∧
    (y i = c i + ρ / 2 → c i - ρ / 2 < q i) ∧
    (¬cubeActiveFace c y ρ i →
      c i - ρ / 2 < q i ∧ q i < c i + ρ / 2) := by
  have hqi := (Set.mem_pi.mp hq) i (by simp)
  change y i - cubeChartRadius c y ρ i < q i ∧
    q i < y i + cubeChartRadius c y ρ i at hqi
  rcases hqi with ⟨hqlo, hqhi⟩
  have hδ := cubeChartRadius_pos hρ hy i
  have hcases := cube_boundary_coordinate_cases hρ hy i
  constructor
  · intro hlo
    have hact : cubeActiveFace c y ρ i := Or.inl hlo
    rw [cubeChartRadius, if_pos hact] at hqhi
    linarith [hρ, hqhi]
  constructor
  · intro hup
    have hact : cubeActiveFace c y ρ i := Or.inr hup
    rw [cubeChartRadius, if_pos hact] at hqlo
    linarith [hρ, hqlo]
  · intro hinactive
    have hslack := hcases
    rcases hslack with hlo | hup | ⟨hlo, hup⟩
    · exact (hinactive (Or.inl hlo)).elim
    · exact (hinactive (Or.inr hup)).elim
    · have hnot : ¬cubeActiveFace c y ρ i := by
        rintro (e | e) <;> linarith
      rw [cubeChartRadius, if_neg hnot] at hqlo hqhi
      have hmpos : 0 ≤ min (y i - (c i - ρ / 2)) ((c i + ρ / 2) - y i) :=
        le_min (by linarith) (by linarith)
      constructor
      · have hm := min_le_left (y i - (c i - ρ / 2)) ((c i + ρ / 2) - y i)
        linarith [hmpos, hqlo]
      · have hm := min_le_right (y i - (c i - ρ / 2)) ((c i + ρ / 2) - y i)
        linarith [hmpos, hqhi]

theorem cube_mem_iff_active_constraints [NeZero N] {ρ : ℝ} (hρ : 0 < ρ)
    {c y q : Sp N} (hy : y ∈ frontier (cube ρ c))
    (hq : q ∈ cubeChartNeighborhood c y ρ) :
    (q ∈ cube ρ c ↔ ∀ i, (y i = c i - ρ / 2 → c i - ρ / 2 < q i) ∧
      (y i = c i + ρ / 2 → q i < c i + ρ / 2)) := by
  rw [cube, Set.mem_pi]
  constructor
  · intro h i
    have hi := h i (by simp)
    exact ⟨fun _ => hi.1, fun _ => hi.2⟩
  · intro h i _
    have hop := cubeChartNeighborhood_opposite_faces hρ hy hq i
    by_cases hlo : y i = c i - ρ / 2
    · exact ⟨(h i).1 hlo, hop.1 hlo⟩
    · by_cases hup : y i = c i + ρ / 2
      · exact ⟨hop.2.1 hup, (h i).2 hup⟩
      · have hinactive : ¬cubeActiveFace c y ρ i := by
          rintro (e | e) <;> contradiction
        exact hop.2.2 hinactive

theorem cubeFaceNormal_inner_sub [NeZero N] {ρ : ℝ} (hρ : 0 < ρ)
    {c y q : Sp N} (i : Fin N)
    (hface : cubeActiveFace c y ρ i) :
    inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 (q - y)) < 0 ↔
      ((y i = c i - ρ / 2 → c i - ρ / 2 < q i) ∧
       (y i = c i + ρ / 2 → q i < c i + ρ / 2)) := by
  rcases hface with hlo | hup
  · have hend : c i - ρ / 2 ≠ c i + ρ / 2 := by linarith
    have heq : inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 (q - y)) = y i - q i := by
      simp [cubeFaceNormal, hlo, hend, PiLp.inner_apply]
    constructor
    · intro h
      constructor
      · intro _
        have hlt : y i < q i := by linarith [heq, h]
        rw [hlo] at hlt
        exact hlt
      · intro heqface
        exact (hend (hlo.symm.trans heqface)).elim
    · intro h
      rw [heq]
      exact sub_neg.mpr (by rw [hlo]; exact h.1 hlo)
  · have hend : c i + ρ / 2 ≠ c i - ρ / 2 := by linarith
    have heq : inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 (q - y)) = q i - y i := by
      simp [cubeFaceNormal, hup, PiLp.inner_apply]
    constructor
    · intro h
      constructor
      · intro heqface
        exact (hend (hup.symm.trans heqface)).elim
      · intro _
        have hlt : q i < y i := by linarith [heq, h]
        rw [hup] at hlt
        exact hlt
    · intro h
      rw [heq]
      exact sub_neg.mpr (by rw [hup]; exact h.2 hup)

/-! ### Active-face graph for a cube corner -/

/-- The local graph determined by the active faces: in the project's sign convention the interior
is the strict subgraph of the negative of the largest active-face height. -/
noncomputable def cubeBoundaryGraph [NeZero N]
    (c y : Sp N) (ρ : ℝ)
    [Fintype {i : Fin N // cubeActiveFace c y ρ i}]
    [Nonempty {i : Fin N // cubeActiveFace c y ρ i}]
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    Sp N → ℝ :=
  fun z => -Finset.univ.sup' Finset.univ_nonempty
    (fun j : {i : Fin N // cubeActiveFace c y ρ i} =>
      cubeFaceGraphHeight b c y ρ j.1 z)

theorem cubeBoundaryGraph_lipschitz [NeZero N]
    (c y : Sp N) (ρ : ℝ)
    [Fintype {i : Fin N // cubeActiveFace c y ρ i}]
    [Nonempty {i : Fin N // cubeActiveFace c y ρ i}]
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    LipschitzWith
      (Finset.univ.sup' Finset.univ_nonempty
        (fun j : {i : Fin N // cubeActiveFace c y ρ i} =>
          ‖cubeFaceHeightMap b c y ρ j.1‖₊))
      (cubeBoundaryGraph c y ρ b) := by
  unfold cubeBoundaryGraph
  exact (LipschitzWith.finset_sup'
    (fun j : {i : Fin N // cubeActiveFace c y ρ i} =>
      cubeFaceGraphHeight_lipschitz b c y ρ j.1)).neg

theorem cubeBoundaryGraph_update [NeZero N]
    (c y : Sp N) (ρ : ℝ)
    [Fintype {i : Fin N // cubeActiveFace c y ρ i}]
    [Nonempty {i : Fin N // cubeActiveFace c y ρ i}]
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)))
    (z : Sp N) : cubeBoundaryGraph c y ρ b z = cubeBoundaryGraph c y ρ b (update z 0 0) := by
  unfold cubeBoundaryGraph
  apply congrArg (fun q : ℝ => -q)
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro j hj
  simp [cubeFaceGraphHeight]

theorem cube_mem_iff_adapted_subgraph [NeZero N] {ρ : ℝ} (hρ : 0 < ρ)
    {c y q : Sp N} (hy : y ∈ frontier (cube ρ c))
    (hq : q ∈ cubeChartNeighborhood c y ρ)
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)))
    [Fintype {i : Fin N // cubeActiveFace c y ρ i}]
    [Nonempty {i : Fin N // cubeActiveFace c y ρ i}]
    (hbneg : ∀ i, cubeActiveFace c y ρ i →
      inner ℝ (cubeFaceNormal c y ρ i) (b 0) < 0) :
    (q ∈ cube ρ c ↔ cubeAdaptedCoordinates b (q - y) 0 <
      cubeBoundaryGraph c y ρ b (cubeAdaptedCoordinates b (q - y))) := by
  classical
  rw [cube_mem_iff_active_constraints hρ hy hq]
  let w : Sp N := q - y
  let z : Sp N := cubeAdaptedCoordinates b w
  let t : ℝ := -z 0
  change (∀ i, (y i = c i - ρ / 2 → c i - ρ / 2 < q i) ∧
      (y i = c i + ρ / 2 → q i < c i + ρ / 2)) ↔
    z 0 < cubeBoundaryGraph c y ρ b z
  rw [cubeBoundaryGraph]
  change (∀ i, (y i = c i - ρ / 2 → c i - ρ / 2 < q i) ∧
      (y i = c i + ρ / 2 → q i < c i + ρ / 2)) ↔
    z 0 < -Finset.univ.sup' Finset.univ_nonempty
      (fun j : {i : Fin N // cubeActiveFace c y ρ i} =>
        cubeFaceGraphHeight b c y ρ j.1 z)
  rw [show z 0 = -t by simp [t]]
  have hneg : -t < -Finset.univ.sup' Finset.univ_nonempty
      (fun j : {i : Fin N // cubeActiveFace c y ρ i} =>
        cubeFaceGraphHeight b c y ρ j.1 z) ↔
      Finset.univ.sup' Finset.univ_nonempty
        (fun j : {i : Fin N // cubeActiveFace c y ρ i} =>
          cubeFaceGraphHeight b c y ρ j.1 z) < t := by
    constructor <;> intro h <;> linarith
  rw [hneg, Finset.sup'_lt_iff Finset.univ_nonempty]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro hcoords j
    have hnormal := (cubeFaceNormal_inner_sub hρ j.1 j.2).2 (hcoords j.1)
    have hheight := (cubeFace_constraint_iff_height b c y w ρ j.1
      (hbneg j.1 j.2)).1 hnormal
    simpa [w, z, t] using hheight
  · intro hheights i
    rcases cube_boundary_coordinate_cases hρ hy i with hlo | hup | ⟨hlo, hup⟩
    · have hi : cubeActiveFace c y ρ i := Or.inl hlo
      have hheight := hheights ⟨i, hi⟩
      have hnormal : inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 w) < 0 :=
        (cubeFace_constraint_iff_height b c y w ρ i (hbneg i hi)).2 (by
          simpa [w, z, t] using hheight)
      exact (cubeFaceNormal_inner_sub hρ i hi).1 hnormal
    · have hi : cubeActiveFace c y ρ i := Or.inr hup
      have hheight := hheights ⟨i, hi⟩
      have hnormal : inner ℝ (cubeFaceNormal c y ρ i) (WithLp.toLp 2 w) < 0 :=
        (cubeFace_constraint_iff_height b c y w ρ i (hbneg i hi)).2 (by
          simpa [w, z, t] using hheight)
      exact (cubeFaceNormal_inner_sub hρ i hi).1 hnormal
    · exact ⟨by intro h; linarith, by intro h; linarith⟩

theorem volume_cube (ρ : ℝ) (x : Sp N) :
    volume (cube ρ x) = ENNReal.ofReal ρ ^ N := by
  simp [cube, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ]

theorem cube_add (ρ : ℝ) (x z : Sp N) : cube ρ (x + z) = (fun y => y - z) ⁻¹' cube ρ x := by
  ext y
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, mem_preimage, Pi.add_apply,
    Pi.sub_apply]
  exact forall_congr' fun i => by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-! ### Piecewise affine functions -/

/-- `φ` is (Lipschitz) continuous piecewise affine on `U`: there are finitely many pairwise
disjoint open sets `Vᵢ ⊂ U` with `|U ∩ ∂Vᵢ| = 0` and `|U ∖ ⋃ Vᵢ| = 0`, on which `∇φ ≡ ξᵢ`. -/
def IsPWAffine (U : Set (Sp N)) (φ : Sp N → Tgt m) : Prop :=
  (∃ K, LipschitzOnWith K φ U) ∧
  ∃ (n : ℕ) (V : Fin n → Set (Sp N)) (ξ : Fin n → Mat m N),
    (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U) ∧ Pairwise (fun i j => Disjoint (V i) (V j)) ∧
    (∀ i, volume (U ∩ frontier (V i)) = 0) ∧ volume (U \ ⋃ i, V i) = 0 ∧
    ∀ i, ∀ y ∈ V i, HasFDerivAt φ (ξ i) y

/-- `Aff₀(U;ℝᵐ)`: piecewise affine functions on `U` vanishing on `∂U` (extended by `0`). -/
def Aff0 (U : Set (Sp N)) : Set (Sp N → Tgt m) :=
  {φ | (∃ K, LipschitzWith K φ) ∧ (∀ y ∉ U, φ y = 0) ∧ IsPWAffine U φ}

/-! ### Envelopes -/

/-- The affine Dirichlet problem `𝒴 L(U,ξ) = inf_{φ ∈ Aff₀(U)} ∫_U L(y, ξ + ∇φ(y)) dy`
(Definition `def:cell` with `θ = Aff`). -/
noncomputable def Yt (L : Sp N → Mat m N → ℝ≥0∞) (U : Set (Sp N)) (ξ : Mat m N) : ℝ≥0∞ :=
  ⨅ φ ∈ (Aff0 U : Set (Sp N → Tgt m)), ∫⁻ y in U, L y (ξ + fderiv ℝ φ y)

/-- The local (blow-up) envelope `𝒴_loc L(x,ξ) = limsup_{ρ→0} 𝒴 L(Q_ρ(x),ξ)/|Q_ρ(x)|`. -/
noncomputable def Ytloc (L : Sp N → Mat m N → ℝ≥0∞) (x : Sp N) (ξ : Mat m N) : ℝ≥0∞ :=
  limsup (fun ρ : ℝ => Yt L (cube ρ x) ξ / volume (cube ρ x)) (𝓝[>] 0)

/-- The multi-cell envelope on the affine class,
`ℋ_aff L(ξ) = inf_{k ≥ 1} 𝒴 L(kY,ξ)/|kY|`. -/
noncomputable def Haff (L : Sp N → Mat m N → ℝ≥0∞) (ξ : Mat m N) : ℝ≥0∞ :=
  ⨅ k : ℕ, Yt L (cube ((k : ℝ) + 1) 0) ξ / volume (cube ((k : ℝ) + 1) (0 : Sp N))

/-- The one-cell envelope `𝒵_aff L₀(ξ) = 𝒴 L₀(Y,ξ)`. -/
noncomputable def Zaff (L₀ : Mat m N → ℝ≥0∞) (ξ : Mat m N) : ℝ≥0∞ :=
  Yt (fun _ => L₀) (cube 1 0) ξ

/-- `g` is a weak gradient of `φ` on the open set `U`:
`∫ φ ∂ᵥψ = -∫ ψ (g·v)` for all `ψ ∈ C_c^∞(U)` and all directions `v`. -/
def HasWeakGrad (U : Set (Sp N)) (φ : Sp N → Tgt m) (g : Sp N → Mat m N) : Prop :=
  ∀ ψ : Sp N → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∀ v : Sp N, ∫ y, fderiv ℝ ψ y v • φ y = -∫ y, ψ y • g y v

/-- `W^{1,p}_0(U;ℝᵐ)` (for `U` a cube): pairs `(φ, ∇φ)` with `φ = 0` off `U` and
`φ ∈ W^{1,p}(ℝᴺ;ℝᵐ)`. -/
def W1p0 (p : ℝ≥0∞) (U : Set (Sp N)) : Set ((Sp N → Tgt m) × (Sp N → Mat m N)) :=
  {φg | (∀ y ∉ U, φg.1 y = 0) ∧ MemLp φg.1 p volume ∧ MemLp φg.2 p volume ∧
    HasWeakGrad univ φg.1 φg.2}

/-- The affine Dirichlet problem on the Sobolev class, `𝒴_p L(U,ξ)`. -/
noncomputable def Ytp (p : ℝ≥0∞) (L : Sp N → Mat m N → ℝ≥0∞) (U : Set (Sp N)) (ξ : Mat m N) :
    ℝ≥0∞ :=
  ⨅ φg ∈ (W1p0 p U : Set ((Sp N → Tgt m) × (Sp N → Mat m N))), ∫⁻ y in U, L y (ξ + φg.2 y)

/-- The multi-cell (homogenization) envelope `ℋ L = ℋ_p L` on the Sobolev class. -/
noncomputable def Hp (p : ℝ≥0∞) (L : Sp N → Mat m N → ℝ≥0∞) (ξ : Mat m N) : ℝ≥0∞ :=
  ⨅ k : ℕ, Ytp p L (cube ((k : ℝ) + 1) 0) ξ / volume (cube ((k : ℝ) + 1) (0 : Sp N))

/-- The radial envelope `f̂(ξ) = liminf_{t→1⁻} f(tξ)`. -/
noncomputable def radial (f : Mat m N → ℝ≥0∞) (ξ : Mat m N) : ℝ≥0∞ :=
  liminf (fun t : ℝ => f (t • ξ)) (𝓝[<] 1)

/-- Uniform radial upper semicontinuity relative to `0` (`ru-usc`) with constant `c`:
`limsup_{t→1⁻} Δ_f^c(t) ≤ 0`, where
`Δ_f^c(t) = sup_x sup_{ξ ∈ dom f(x,·)} (f(x,tξ) - f(x,ξ)) / (c + f(x,ξ))`.
Written equivalently as: for every `η > 0`, for `t` close to `1⁻`,
`f(x,tξ) ≤ f(x,ξ) + η (c + f(x,ξ))` whenever `f(x,ξ) < ∞`. -/
def RUUSCWith (c : ℝ≥0) (f : Sp N → Mat m N → ℝ≥0∞) : Prop :=
  ∀ η : ℝ≥0, 0 < η → ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ x ξ, f x ξ < ⊤ →
    f x (t • ξ) ≤ f x ξ + η * (c + f x ξ)

/-- `f` is uniformly ru-usc relative to `0` (for some constant `c > 0`). -/
def RUUSC (f : Sp N → Mat m N → ℝ≥0∞) : Prop := ∃ c : ℝ≥0, 0 < c ∧ RUUSCWith c f

/-- Convexity of a `[0,∞]`-valued function. -/
def ConvexENN (G : Mat m N → ℝ≥0∞) : Prop :=
  ∀ ξ ζ : Mat m N, ∀ t : ℝ≥0, t ≤ 1 →
    G ((t : ℝ) • ξ + ((1 - t : ℝ≥0) : ℝ) • ζ) ≤ t * G ξ + (1 - t : ℝ≥0) * G ζ

/-- Effective domain. -/
def dom (f : Mat m N → ℝ≥0∞) : Set (Mat m N) := {ξ | f ξ < ⊤}

/-- `(α,β)`-`G`-growth (Definition `def:Ggrowth`). -/
def HasGGrowth (G : Mat m N → ℝ≥0∞) (α β : ℝ≥0) (L : Sp N → Mat m N → ℝ≥0∞) : Prop :=
  ∀ x ξ, (α : ℝ≥0∞) * G ξ ≤ L x ξ ∧ L x ξ ≤ β * (1 + G ξ)

/-- `1`-periodicity in the space variable. -/
def IsPeriodic (L : Sp N → Mat m N → ℝ≥0∞) : Prop :=
  ∀ (z : Fin N → ℤ) x ξ, L (x + fun i => (z i : ℝ)) ξ = L x ξ

/-- `p`-coercivity: `c₀ |ξ|ᵖ ≤ L(x,ξ)`. -/
def IsCoercive (p : ℝ) (c₀ : ℝ≥0) (L : Sp N → Mat m N → ℝ≥0∞) : Prop :=
  ∀ x ξ, ENNReal.ofReal (c₀ * ‖ξ‖ ^ p) ≤ L x ξ

/-! ### The domain `Ω` -/

/-- `Ω` has Lipschitz boundary: near each boundary point, after an affine change of variables,
`Ω` is the strict subgraph `{z₀ < g(z)}` of a Lipschitz function `g` not depending on `z₀`. -/
def HasLipschitzBoundary [NeZero N] (Ω : Set (Sp N)) : Prop :=
  ∀ x ∈ frontier Ω, ∃ (T : Sp N ≃L[ℝ] Sp N) (g : Sp N → ℝ) (K : ℝ≥0) (U : Set (Sp N)),
    U ∈ 𝓝 x ∧ LipschitzWith K g ∧ (∀ z, g z = g (update z 0 0)) ∧
    ∀ y ∈ U, (y ∈ Ω ↔ T (y - x) 0 < g (T (y - x)))

/-- Degenerate cubes have empty frontier, hence satisfy the project's Lipschitz-boundary
condition vacuously. -/
theorem HasLipschitzBoundary.cube_of_nonpos [NeZero N] {ρ : ℝ} (hρ : ρ ≤ 0)
    (x : Sp N) : HasLipschitzBoundary (cube ρ x) := by
  rw [cube_eq_empty_of_nonpos hρ x]
  simp [HasLipschitzBoundary]

/-- Positive-radius cubes have Lipschitz boundary, including their corners. The active face
heights form a finite maximum in coordinates adapted to a common strict inward direction. -/
theorem HasLipschitzBoundary.cube_of_pos [NeZero N] {ρ : ℝ} (hρ : 0 < ρ)
    (x : Sp N) : HasLipschitzBoundary (cube ρ x) := by
  intro y hy
  obtain ⟨i₀, hface₀⟩ := exists_active_cube_face hρ hy
  let : Fintype {i : Fin N // cubeActiveFace x y ρ i} := Fintype.ofFinite _
  let : Nonempty {i : Fin N // cubeActiveFace x y ρ i} := ⟨⟨i₀, hface₀⟩⟩
  obtain ⟨e, b, he, hb, hbneg⟩ := cube_boundary_adapted_orthonormalBasis hρ hy
  have hbneg' : ∀ i, cubeActiveFace x y ρ i →
      inner ℝ (cubeFaceNormal x y ρ i) (b 0) < 0 := by
    intro i hi
    simpa [hb] using hbneg i hi
  let T := cubeAdaptedCoordinates b
  let g := cubeBoundaryGraph x y ρ b
  let K : ℝ≥0 := Finset.univ.sup' Finset.univ_nonempty
    (fun j : {i : Fin N // cubeActiveFace x y ρ i} =>
      ‖cubeFaceHeightMap b x y ρ j.1‖₊)
  let U := cubeChartNeighborhood x y ρ
  refine ⟨T, g, K, U, ?_, ?_, ?_, ?_⟩
  · exact cubeChartNeighborhood_mem_nhds hρ hy
  · simpa [K, g] using cubeBoundaryGraph_lipschitz x y ρ b
  · intro z
    exact cubeBoundaryGraph_update x y ρ b z
  · intro q hq
    exact cube_mem_iff_adapted_subgraph hρ hy hq b hbneg'

/-- Every cube, including the degenerate empty cases, has Lipschitz boundary in the project's
local graph convention. -/
theorem HasLipschitzBoundary.cube [NeZero N] (ρ : ℝ) (x : Sp N) :
    HasLipschitzBoundary (cube ρ x) := by
  by_cases hρ : ρ ≤ 0
  · exact HasLipschitzBoundary.cube_of_nonpos hρ x
  · exact HasLipschitzBoundary.cube_of_pos (lt_of_not_ge hρ) x

open scoped Pointwise in
/-- Strong star-shapedness (`eq:strongstar`): `closure (-x₀ + Ω) ⊆ t • (-x₀ + Ω)`
for all `t > 1`. -/
def IsStronglyStarShaped (Ω : Set (Sp N)) : Prop :=
  ∃ x₀ ∈ Ω, ∀ t : ℝ, 1 < t →
    closure ((fun y => y - x₀) '' Ω) ⊆ t • ((fun y => y - x₀) '' Ω)

/-- The standing assumptions on `Ω` (§3.1). -/
structure StandingDomain [NeZero N] (Ω : Set (Sp N)) : Prop where
  isOpen : IsOpen Ω
  bounded : Bornology.IsBounded Ω
  nonempty : Ω.Nonempty
  lipschitz : HasLipschitzBoundary Ω
  starShaped : IsStronglyStarShaped Ω

/-! ### `W^{1,p}(Ω;ℝᵐ)` with the `Lᵖ` topology -/

/-- An element of `W^{1,p}(Ω;ℝᵐ)`: a function with a weak gradient, both in `Lᵖ(Ω)`. -/
structure W1p (N m : ℕ) (p : ℝ≥0∞) (Ω : Set (Sp N)) where
  toFun : Sp N → Tgt m
  grad : Sp N → Mat m N
  memLp : MemLp toFun p (volume.restrict Ω)
  memLp_grad : MemLp grad p (volume.restrict Ω)
  weak : HasWeakGrad Ω toFun grad

namespace W1p

variable {p : ℝ≥0∞} {Ω : Set (Sp N)}

/-- The image in `Lᵖ(Ω;ℝᵐ)`. -/
noncomputable def toLp (u : W1p N m p Ω) : Lp (Tgt m) p (volume.restrict Ω) := u.memLp.toLp

/-- `W^{1,p}(Ω;ℝᵐ)` carries the (pseudo-)distance of `Lᵖ(Ω;ℝᵐ)`. -/
noncomputable instance [Fact (1 ≤ p)] : PseudoEMetricSpace (W1p N m p Ω) :=
  PseudoEMetricSpace.induced toLp inferInstance

theorem edist_def [Fact (1 ≤ p)] (u v : W1p N m p Ω) :
    edist u v = eLpNorm (u.toFun - v.toFun) p (volume.restrict Ω) := by
  change edist u.toLp v.toLp = _
  exact Lp.edist_toLp_toLp _ _ _ _

end W1p

/-- The piecewise affine elements of `W^{1,p}(Ω;ℝᵐ)`, i.e. `Aff(Ω;ℝᵐ)`. -/
def AffSet (p : ℝ≥0∞) (Ω : Set (Sp N)) : Set (W1p N m p Ω) :=
  {u | IsPWAffine Ω u.toFun ∧ u.grad =ᵐ[volume.restrict Ω] fderiv ℝ u.toFun}

/-- The integral functional `u ↦ ∫_Ω L(x/ε, ∇u(x)) dx`. -/
noncomputable def intFun {p : ℝ≥0∞} {Ω : Set (Sp N)} (L : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ)
    (u : W1p N m p Ω) : ℝ≥0∞ :=
  ∫⁻ x in Ω, L (ε⁻¹ • x) (u.grad x)

/-- An integral functional with an `x`-independent density, `u ↦ ∫_Ω f(∇u(x)) dx`. -/
noncomputable def intHom {p : ℝ≥0∞} {Ω : Set (Sp N)} (f : Mat m N → ℝ≥0∞) (u : W1p N m p Ω) :
    ℝ≥0∞ :=
  ∫⁻ x in Ω, f (u.grad x)

end Homogenization
