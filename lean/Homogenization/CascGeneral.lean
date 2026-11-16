import Homogenization.Casc

/-!
# Lemma `lemmacasc` for arbitrary open sets, and for Euclidean balls

`Casc.lean` proves `lemmacasc` with the balls of the sup norm of `Sp N`. The article uses the open
Euclidean balls `B_r(y) = {x ∈ ℝᴺ : |x - y| < r}`. Of the balls, the proof only uses that they are
open sets containing their centre (together with the translation invariance of Lebesgue measure,
the density of `ℚᴺ` and the disjointness of the integer translates of `Y`). This file proves the
lemma for `D = ⋃_{z ∈ ℤᴺ} ⋃_j (q_j + z + B_j)` with arbitrary open sets `B_j ∋ 0`
(`lemmacasc_of_isOpen`), and deduces the statement of the article with Euclidean balls
(`lemmacasc_euclidean`, `exists_cascData_euclidean`).
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ}

/-- The translate `c + S = {x | x - c ∈ S}`. -/
def translSet (c : Sp N) (S : Set (Sp N)) : Set (Sp N) := {x | x - c ∈ S}

/-- The open set `D = ⋃_{z ∈ ℤᴺ} ⋃_j (q_j + z + B_j)`. -/
def cascSetOf (q : ℕ → Sp N) (B : ℕ → Set (Sp N)) : Set (Sp N) :=
  ⋃ (z : Fin N → ℤ) (j : ℕ), translSet (q j + intVec z) (B j)

/-- The coefficient `a = 1 + 1_D`. -/
noncomputable def cascCoeffOf (q : ℕ → Sp N) (B : ℕ → Set (Sp N)) (x : Sp N) : ℝ :=
  1 + (cascSetOf q B).indicator (fun _ => (1 : ℝ)) x

theorem isOpen_cascSetOf (q : ℕ → Sp N) {B : ℕ → Set (Sp N)} (hB : ∀ j, IsOpen (B j)) :
    IsOpen (cascSetOf q B) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun j =>
    (hB j).preimage (continuous_id.sub continuous_const)

theorem add_intVec_mem_cascSetOf_iff (q : ℕ → Sp N) (B : ℕ → Set (Sp N)) (x : Sp N)
    (z : Fin N → ℤ) : x + intVec z ∈ cascSetOf q B ↔ x ∈ cascSetOf q B := by
  have key : ∀ (x : Sp N) (z : Fin N → ℤ), x ∈ cascSetOf q B → x + intVec z ∈ cascSetOf q B := by
    intro x z hx
    simp only [cascSetOf, mem_iUnion] at hx ⊢
    obtain ⟨z', j, h⟩ := hx
    refine ⟨z' + z, j, ?_⟩
    change x + intVec z - (q j + intVec (z' + z)) ∈ B j
    have e : x + intVec z - (q j + intVec (z' + z)) = x - (q j + intVec z') := by
      rw [intVec_add]; abel
    rw [e]
    exact h
  refine ⟨fun h => ?_, key x z⟩
  have := key _ (-z) h
  rwa [add_assoc, ← intVec_add, add_neg_cancel, show intVec (0 : Fin N → ℤ) = 0 by
    ext i; simp [intVec], add_zero] at this

/-- `∑_z |Y ∩ (c + z + S)| ≤ |S|` for every measurable `S`. -/
theorem tsum_volume_cube_inter_translSet_le (c : Sp N) {S : Set (Sp N)} (hS : MeasurableSet S) :
    ∑' z : Fin N → ℤ, volume (cube 1 (0 : Sp N) ∩ translSet (c + intVec z) S) ≤ volume S := by
  have hT : MeasurableSet (translSet c S) := hS.preimage (measurable_id.sub_const c)
  have e : ∀ z : Fin N → ℤ, volume (cube 1 (0 : Sp N) ∩ translSet (c + intVec z) S) =
      volume ((· + intVec z) ⁻¹' cube 1 (0 : Sp N) ∩ translSet c S) := by
    intro z
    rw [← measure_preimage_add_right volume (intVec z)]
    congr 1
    ext x
    simp [translSet]
  simp_rw [e]
  rw [← measure_iUnion]
  · calc volume (⋃ z : Fin N → ℤ, (· + intVec z) ⁻¹' cube 1 (0 : Sp N) ∩ translSet c S)
        ≤ volume (translSet c S) := measure_mono (iUnion_subset fun _ => inter_subset_right)
      _ = volume S := by
          change volume ((· + (-c)) ⁻¹' S) = volume S
          · exact measure_preimage_add_right volume (-c) S
  · intro z z' hzz'
    exact (disjoint_preimage_add_intVec_cube hzz').mono inter_subset_left inter_subset_left
  · exact fun z => ((isOpen_cube 1 0).preimage (continuous_add_const _)).measurableSet.inter hT

/-- **Lemma `lemmacasc`, for arbitrary open sets.** Let `0 ≤ ϱ`, let `B_j` be open sets containing
`0` with `∑_j |B_j| ≤ ϱ`, and `(q_j)` such that `{q_j + z : j ∈ ℕ, z ∈ ℤᴺ} ⊇ ℚᴺ`. Then
`a = 1 + 1_D`, `D = ⋃_{z,j} (q_j + z + B_j)`, is Borel measurable, `1`-periodic, lower
semicontinuous, `1 ≤ a ≤ 2`, discontinuous at every point of `ℝᴺ \ D`, and
`|Y \ D| ≥ 1 - ϱ` with `Y = ]-1/2,1/2[ᴺ`. -/
theorem lemmacasc_of_isOpen {q : ℕ → Sp N} {B : ℕ → Set (Sp N)} {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hBo : ∀ j, IsOpen (B j)) (hB0 : ∀ j, (0 : Sp N) ∈ B j)
    (hq : ∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ))
    (hsum : ∑' j, volume (B j) ≤ ENNReal.ofReal ϱ) :
    Measurable (cascCoeffOf q B) ∧
      (∀ (z : Fin N → ℤ) x, cascCoeffOf q B (x + intVec z) = cascCoeffOf q B x) ∧
      LowerSemicontinuous (cascCoeffOf q B) ∧
      (∀ x, 1 ≤ cascCoeffOf q B x ∧ cascCoeffOf q B x ≤ 2) ∧
      (∀ x ∉ cascSetOf q B, ¬ ContinuousAt (cascCoeffOf q B) x) ∧
      ENNReal.ofReal (1 - ϱ) ≤ volume (cube 1 (0 : Sp N) \ cascSetOf q B) := by
  have hD := isOpen_cascSetOf q hBo
  have hlsc : LowerSemicontinuous (cascCoeffOf q B) :=
    lowerSemicontinuous_const.add (hD.lowerSemicontinuous_indicator zero_le_one)
  have hb : ∀ x, 1 ≤ cascCoeffOf q B x ∧ cascCoeffOf q B x ≤ 2 := by
    intro x
    simp only [cascCoeffOf]
    by_cases hx : x ∈ cascSetOf q B
    · simp [indicator_of_mem hx]; norm_num
    · simp [indicator_of_notMem hx]
  have hdense : Dense (cascSetOf q B) := by
    have hQ : Dense (range fun v : Fin N → ℚ => fun i => (v i : ℝ)) := by
      have : DenseRange (fun v : Fin N → ℚ => fun i => (v i : ℝ)) :=
        DenseRange.piMap fun _ => Rat.denseRange_cast
      exact this
    refine hQ.mono ?_
    rintro _ ⟨v, rfl⟩
    obtain ⟨j, z, hjz⟩ := hq v
    change (fun i => (v i : ℝ)) ∈ _
    rw [← hjz]
    refine mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨j, ?_⟩⟩
    change q j + intVec z - (q j + intVec z) ∈ B j
    rw [sub_self]
    exact hB0 j
  refine ⟨hlsc.measurable, fun z x => ?_, hlsc, hb, fun x hx hcont => ?_, ?_⟩
  · simp only [cascCoeffOf]
    congr 1
    by_cases hx : x ∈ cascSetOf q B
    · rw [indicator_of_mem hx, indicator_of_mem ((add_intVec_mem_cascSetOf_iff q B x z).2 hx)]
    · rw [indicator_of_notMem hx,
        indicator_of_notMem (mt (add_intVec_mem_cascSetOf_iff q B x z).1 hx)]
  · have hx1 : cascCoeffOf q B x = 1 := by simp [cascCoeffOf, indicator_of_notMem hx]
    have hev : ∀ᶠ y in 𝓝 x, cascCoeffOf q B y < 3 / 2 :=
      hcont.eventually (gt_mem_nhds (by rw [hx1]; norm_num))
    obtain ⟨y, hyD, hy⟩ := ((mem_closure_iff_frequently.1 (hdense x)).and_eventually hev).exists
    have : cascCoeffOf q B y = 2 := by
      simp only [cascCoeffOf, indicator_of_mem hyD]
      norm_num
    linarith
  · have hYD : volume (cube 1 (0 : Sp N) ∩ cascSetOf q B) ≤ ENNReal.ofReal ϱ := by
      calc volume (cube 1 (0 : Sp N) ∩ cascSetOf q B)
          ≤ ∑' z : Fin N → ℤ, ∑' j,
              volume (cube 1 (0 : Sp N) ∩ translSet (q j + intVec z) (B j)) := by
            simp only [cascSetOf, inter_iUnion]
            exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun z => measure_iUnion_le _)
        _ = ∑' j, ∑' z : Fin N → ℤ,
              volume (cube 1 (0 : Sp N) ∩ translSet (q j + intVec z) (B j)) :=
            ENNReal.tsum_comm
        _ ≤ ∑' j, volume (B j) := ENNReal.tsum_le_tsum fun j =>
            tsum_volume_cube_inter_translSet_le _ (hBo j).measurableSet
        _ ≤ _ := hsum
    have hY : volume (cube 1 (0 : Sp N)) = 1 := by rw [volume_cube]; simp
    calc ENNReal.ofReal (1 - ϱ) = 1 - ENNReal.ofReal ϱ := by
          rw [ENNReal.ofReal_sub _ hϱ, ENNReal.ofReal_one]
      _ ≤ volume (cube 1 (0 : Sp N)) - volume (cube 1 (0 : Sp N) ∩ cascSetOf q B) := by
          rw [hY]
          exact tsub_le_tsub_left hYD 1
      _ ≤ volume (cube 1 (0 : Sp N) \ (cube 1 (0 : Sp N) ∩ cascSetOf q B)) := le_measure_sdiff
      _ = volume (cube 1 (0 : Sp N) \ cascSetOf q B) := by rw [Set.sdiff_self_inter]

/-! ### Euclidean balls -/

/-- The Euclidean norm `|x| = (∑ᵢ xᵢ²)^{1/2}` of `x ∈ ℝᴺ`. -/
noncomputable def euclNorm (x : Sp N) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The open Euclidean ball `B(c,r) = {x ∈ ℝᴺ : |x - c| < r}`. -/
def euclBall (c : Sp N) (r : ℝ) : Set (Sp N) := {x | euclNorm (x - c) < r}

theorem continuous_euclNorm : Continuous (euclNorm (N := N)) := by
  unfold euclNorm
  fun_prop

theorem isOpen_euclBall (c : Sp N) (r : ℝ) : IsOpen (euclBall c r) :=
  isOpen_lt (continuous_euclNorm.comp (continuous_id.sub continuous_const)) continuous_const

theorem translSet_euclBall_zero (c : Sp N) (r : ℝ) :
    translSet c (euclBall 0 r) = euclBall c r := by
  ext x
  simp [translSet, euclBall]

/-- With `B_j = B_{r_j}(0)` Euclidean, `D = ⋃_{z ∈ ℤᴺ} ⋃_j B_{r_j}(q_j + z)` as in (eq:defa). -/
theorem cascSetOf_euclBall (q : ℕ → Sp N) (r : ℕ → ℝ) :
    cascSetOf q (fun j => euclBall 0 (r j)) =
      ⋃ (z : Fin N → ℤ) (j : ℕ), euclBall (q j + intVec z) (r j) := by
  simp only [cascSetOf, translSet_euclBall_zero]

/-- The Euclidean ball is contained in the sup-norm ball of the same radius. -/
theorem euclBall_zero_subset_ball (r : ℝ) : euclBall (0 : Sp N) r ⊆ ball 0 r := by
  intro x hx
  change euclNorm (x - 0) < r at hx
  rw [sub_zero] at hx
  have hr : 0 < r := lt_of_le_of_lt (Real.sqrt_nonneg _) hx
  rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
  intro i
  rw [Real.norm_eq_abs]
  calc |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ k, x k ^ 2) := Real.sqrt_le_sqrt
        (Finset.single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i))
    _ < r := hx

/-- **Lemma `lemmacasc`, as in the article (Euclidean balls).** Let `0 ≤ ϱ`, `r_j > 0` with
`∑_j |B_{r_j}(0)| ≤ ϱ` for the open Euclidean balls, and `(q_j)` such that
`{q_j + z : j ∈ ℕ, z ∈ ℤᴺ} ⊇ ℚᴺ`. Then `a_ϱ = 1 + 1_{D_ϱ}`, with
`D_ϱ = ⋃_{z ∈ ℤᴺ} ⋃_j B_{r_j}(q_j + z)` (`cascSetOf_euclBall`), is Borel measurable, `1`-periodic,
lower semicontinuous, `1 ≤ a_ϱ ≤ 2`, discontinuous at every point of `ℝᴺ \ D_ϱ`, and
`|Y \ D_ϱ| ≥ 1 - ϱ`. -/
theorem lemmacasc_euclidean {q : ℕ → Sp N} {r : ℕ → ℝ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (hr : ∀ j, 0 < r j)
    (hq : ∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ))
    (hsum : ∑' j, volume (euclBall (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ) :
    Measurable (cascCoeffOf q fun j => euclBall 0 (r j)) ∧
      (∀ (z : Fin N → ℤ) x, cascCoeffOf q (fun j => euclBall 0 (r j)) (x + intVec z) =
        cascCoeffOf q (fun j => euclBall 0 (r j)) x) ∧
      LowerSemicontinuous (cascCoeffOf q fun j => euclBall 0 (r j)) ∧
      (∀ x, 1 ≤ cascCoeffOf q (fun j => euclBall 0 (r j)) x ∧
        cascCoeffOf q (fun j => euclBall 0 (r j)) x ≤ 2) ∧
      (∀ x ∉ cascSetOf q (fun j => euclBall 0 (r j)),
        ¬ ContinuousAt (cascCoeffOf q fun j => euclBall 0 (r j)) x) ∧
      ENNReal.ofReal (1 - ϱ) ≤
        volume (cube 1 (0 : Sp N) \ cascSetOf q fun j => euclBall 0 (r j)) :=
  lemmacasc_of_isOpen hϱ (fun j => isOpen_euclBall 0 (r j))
    (fun j => by change euclNorm (0 - 0) < r j; simp [euclNorm, hr j]) hq hsum

/-- Admissible data for `lemmacasc_euclidean` exist, for every `ϱ > 0`. -/
theorem exists_cascData_euclidean [NeZero N] {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ∃ (q : ℕ → Sp N) (r : ℕ → ℝ), (∀ j, 0 < r j) ∧
      (∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ)) ∧
      ∑' j, volume (euclBall (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ := by
  obtain ⟨q, r, hr, hq, hsum⟩ := exists_cascData (N := N) hϱ
  exact ⟨q, r, hr, hq, (ENNReal.tsum_le_tsum fun j =>
    measure_mono (euclBall_zero_subset_ball (r j))).trans hsum⟩

end Homogenization
