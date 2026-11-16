import Homogenization.Basic

/-!
# A lower semicontinuous coefficient discontinuous on a set of large measure

Formalization of Lemma `lemmacasc` of `Homogenization_beyond_convex_growthV1.tex`: for
`D_ϱ = ⋃_{z ∈ ℤᴺ} ⋃_j B_{r_j}(q_j + z)` with `{q_j + z} ⊇ ℚᴺ` and `∑_j |B_{r_j}(0)| ≤ ϱ`, the
coefficient `a_ϱ = 1 + 1_{D_ϱ}` is Borel measurable, `1`-periodic, lower semicontinuous,
`1 ≤ a_ϱ ≤ 2`, discontinuous at every point of `ℝᴺ \ D_ϱ`, and `|Y \ D_ϱ| ≥ 1 - ϱ`.

The balls are those of `Sp N = Fin N → ℝ` (sup norm), and `Y = cube 1 0 = ]-1/2,1/2[ᴺ`. The paper
takes `(q_j)` an enumeration of `ℚᴺ ∩ Y`; here only the property `{q_j + z} ⊇ ℚᴺ` used in its proof
is assumed (`hq`). `exists_cascData` shows that admissible data exist.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ}

/-- The integer translate `x + z`, `z ∈ ℤᴺ`. -/
def intVec (z : Fin N → ℤ) : Sp N := fun i => (z i : ℝ)

/-- The open set `D_ϱ = ⋃_{z ∈ ℤᴺ} ⋃_j B_{r_j}(q_j + z)`. -/
def cascSet (q : ℕ → Sp N) (r : ℕ → ℝ) : Set (Sp N) :=
  ⋃ (z : Fin N → ℤ) (j : ℕ), ball (q j + intVec z) (r j)

/-- The coefficient `a_ϱ = 1 + 1_{D_ϱ}`. -/
noncomputable def cascCoeff (q : ℕ → Sp N) (r : ℕ → ℝ) (x : Sp N) : ℝ :=
  1 + (cascSet q r).indicator (fun _ => (1 : ℝ)) x

theorem isOpen_cascSet (q : ℕ → Sp N) (r : ℕ → ℝ) : IsOpen (cascSet q r) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem intVec_add (z z' : Fin N → ℤ) : intVec (z + z') = intVec z + intVec z' := by
  ext i
  simp [intVec]

theorem add_intVec_mem_cascSet_iff (q : ℕ → Sp N) (r : ℕ → ℝ) (x : Sp N) (z : Fin N → ℤ) :
    x + intVec z ∈ cascSet q r ↔ x ∈ cascSet q r := by
  have key : ∀ (x : Sp N) (z : Fin N → ℤ), x ∈ cascSet q r → x + intVec z ∈ cascSet q r := by
    intro x z hx
    simp only [cascSet, mem_iUnion, mem_ball] at hx ⊢
    obtain ⟨z', j, h⟩ := hx
    refine ⟨z' + z, j, ?_⟩
    rwa [intVec_add, ← add_assoc, dist_add_right]
  refine ⟨fun h => ?_, key x z⟩
  have := key _ (-z) h
  rwa [add_assoc, ← intVec_add, add_neg_cancel, show intVec (0 : Fin N → ℤ) = 0 by
    ext i; simp [intVec], add_zero] at this

/-- Translates of `Y = ]-1/2,1/2[ᴺ` by distinct integer vectors are disjoint. -/
theorem disjoint_preimage_add_intVec_cube {z z' : Fin N → ℤ} (h : z ≠ z') :
    Disjoint ((· + intVec z) ⁻¹' cube 1 (0 : Sp N)) ((· + intVec z') ⁻¹' cube 1 (0 : Sp N)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have h1 := hx i (mem_univ _)
  have h2 := hx' i (mem_univ _)
  simp only [Pi.add_apply, intVec, Pi.zero_apply, zero_sub, zero_add] at h1 h2
  have hlt : |((z i : ℤ) : ℝ) - (z' i : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hz : |z i - z' i| < 1 := by exact_mod_cast hlt
  have : z i - z' i = 0 := by
    rw [abs_lt] at hz
    omega
  exact hi (by omega)

/-- `∑_z |Y ∩ B(c + z, ρ)| ≤ |B(c, ρ)|`. -/
theorem tsum_volume_cube_inter_ball_le (c : Sp N) (ρ : ℝ) :
    ∑' z : Fin N → ℤ, volume (cube 1 (0 : Sp N) ∩ ball (c + intVec z) ρ) ≤ volume (ball c ρ) := by
  have e : ∀ z : Fin N → ℤ, volume (cube 1 (0 : Sp N) ∩ ball (c + intVec z) ρ) =
      volume ((· + intVec z) ⁻¹' cube 1 (0 : Sp N) ∩ ball c ρ) := by
    intro z
    rw [← measure_preimage_add_right volume (intVec z)]
    congr 1
    ext x
    simp
  simp_rw [e]
  rw [← measure_iUnion]
  · exact measure_mono (iUnion_subset fun _ => inter_subset_right)
  · intro z z' hzz'
    exact (disjoint_preimage_add_intVec_cube hzz').mono inter_subset_left inter_subset_left
  · exact fun z => ((isOpen_cube 1 0).preimage (continuous_add_const _)).measurableSet.inter
      measurableSet_ball

/-- **Lemma `lemmacasc`.** Let `0 ≤ ϱ`, `r_j > 0` with `∑_j |B_{r_j}(0)| ≤ ϱ`, and `(q_j)` such that
`{q_j + z : j ∈ ℕ, z ∈ ℤᴺ} ⊇ ℚᴺ`. Then `a_ϱ = 1 + 1_{D_ϱ}` is Borel measurable, `1`-periodic,
lower semicontinuous, `1 ≤ a_ϱ ≤ 2`, discontinuous at every point of `ℝᴺ \ D_ϱ`, and
`|Y \ D_ϱ| ≥ 1 - ϱ` with `Y = ]-1/2,1/2[ᴺ`. -/
theorem lemmacasc {q : ℕ → Sp N} {r : ℕ → ℝ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (hr : ∀ j, 0 < r j)
    (hq : ∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ))
    (hsum : ∑' j, volume (ball (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ) :
    Measurable (cascCoeff q r) ∧
      (∀ (z : Fin N → ℤ) x, cascCoeff q r (x + intVec z) = cascCoeff q r x) ∧
      LowerSemicontinuous (cascCoeff q r) ∧
      (∀ x, 1 ≤ cascCoeff q r x ∧ cascCoeff q r x ≤ 2) ∧
      (∀ x ∉ cascSet q r, ¬ ContinuousAt (cascCoeff q r) x) ∧
      ENNReal.ofReal (1 - ϱ) ≤ volume (cube 1 (0 : Sp N) \ cascSet q r) := by
  have hD := isOpen_cascSet q r
  have hlsc : LowerSemicontinuous (cascCoeff q r) :=
    lowerSemicontinuous_const.add (hD.lowerSemicontinuous_indicator zero_le_one)
  have hb : ∀ x, 1 ≤ cascCoeff q r x ∧ cascCoeff q r x ≤ 2 := by
    intro x
    simp only [cascCoeff]
    by_cases hx : x ∈ cascSet q r
    · simp [indicator_of_mem hx]; norm_num
    · simp [indicator_of_notMem hx]
  -- density of `D_ϱ`
  have hdense : Dense (cascSet q r) := by
    have hQ : Dense (range fun v : Fin N → ℚ => fun i => (v i : ℝ)) := by
      have : DenseRange (fun v : Fin N → ℚ => fun i => (v i : ℝ)) :=
        DenseRange.piMap fun _ => Rat.denseRange_cast
      exact this
    refine hQ.mono ?_
    rintro _ ⟨v, rfl⟩
    obtain ⟨j, z, hjz⟩ := hq v
    change (fun i => (v i : ℝ)) ∈ _
    rw [← hjz]
    exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨j, mem_ball_self (hr j)⟩⟩
  refine ⟨hlsc.measurable, fun z x => ?_, hlsc, hb, fun x hx hcont => ?_, ?_⟩
  · simp only [cascCoeff]
    congr 1
    by_cases hx : x ∈ cascSet q r
    · rw [indicator_of_mem hx, indicator_of_mem ((add_intVec_mem_cascSet_iff q r x z).2 hx)]
    · rw [indicator_of_notMem hx,
        indicator_of_notMem (mt (add_intVec_mem_cascSet_iff q r x z).1 hx)]
  · have hx1 : cascCoeff q r x = 1 := by simp [cascCoeff, indicator_of_notMem hx]
    have hev : ∀ᶠ y in 𝓝 x, cascCoeff q r y < 3 / 2 :=
      hcont.eventually (gt_mem_nhds (by rw [hx1]; norm_num))
    obtain ⟨y, hyD, hy⟩ := ((mem_closure_iff_frequently.1 (hdense x)).and_eventually hev).exists
    have : cascCoeff q r y = 2 := by
      simp only [cascCoeff, indicator_of_mem hyD]
      norm_num
    linarith
  · have hYD : volume (cube 1 (0 : Sp N) ∩ cascSet q r) ≤ ENNReal.ofReal ϱ := by
      calc volume (cube 1 (0 : Sp N) ∩ cascSet q r)
          ≤ ∑' z : Fin N → ℤ, ∑' j, volume (cube 1 (0 : Sp N) ∩ ball (q j + intVec z) (r j)) := by
            simp only [cascSet, inter_iUnion]
            exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun z => measure_iUnion_le _)
        _ = ∑' j, ∑' z : Fin N → ℤ, volume (cube 1 (0 : Sp N) ∩ ball (q j + intVec z) (r j)) :=
            ENNReal.tsum_comm
        _ ≤ ∑' j, volume (ball (q j) (r j)) :=
            ENNReal.tsum_le_tsum fun j => tsum_volume_cube_inter_ball_le _ _
        _ = ∑' j, volume (ball (0 : Sp N) (r j)) := by
            simp_rw [Measure.addHaar_ball_center]
        _ ≤ _ := hsum
    have hY : volume (cube 1 (0 : Sp N)) = 1 := by rw [volume_cube]; simp
    calc ENNReal.ofReal (1 - ϱ) = 1 - ENNReal.ofReal ϱ := by
          rw [ENNReal.ofReal_sub _ hϱ, ENNReal.ofReal_one]
      _ ≤ volume (cube 1 (0 : Sp N)) - volume (cube 1 (0 : Sp N) ∩ cascSet q r) := by
          rw [hY]
          exact tsub_le_tsub_left hYD 1
      _ ≤ volume (cube 1 (0 : Sp N) \ (cube 1 (0 : Sp N) ∩ cascSet q r)) := le_measure_sdiff
      _ = volume (cube 1 (0 : Sp N) \ cascSet q r) := by rw [Set.sdiff_self_inter]

/-- Admissible data for `lemmacasc` exist: `q` enumerates `ℚᴺ` and `r_j = min ϱ 1 / 4 · 2⁻ʲ`. -/
theorem exists_cascData [NeZero N] {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ∃ (q : ℕ → Sp N) (r : ℕ → ℝ), (∀ j, 0 < r j) ∧
      (∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ)) ∧
      ∑' j, volume (ball (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (Fin N → ℚ)
  set ϱ' := min ϱ 1
  have hϱ' : 0 < ϱ' := lt_min hϱ one_pos
  set g : ℕ → ℝ := fun j => ϱ' / 2 * (1 / 2) ^ j
  have hg0 : ∀ j, 0 ≤ g j := fun j => by positivity
  have hg1 : ∀ j, g j ≤ 1 := fun j => by
    have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : ϱ' ≤ 1 := min_le_right _ _
    calc g j ≤ ϱ' / 2 * 1 := by simp only [g]; gcongr
      _ ≤ 1 := by linarith
  refine ⟨fun j i => (f j i : ℝ), fun j => g j / 2, fun j => by positivity, fun v => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := hf v
    exact ⟨j, 0, by ext i; simp [intVec]⟩
  · have hsumg : HasSum g ϱ' := by
      have := (hasSum_geometric_two).mul_left (ϱ' / 2)
      simpa [g] using this
    calc ∑' j, volume (ball (0 : Sp N) (g j / 2))
        ≤ ∑' j, ENNReal.ofReal (g j) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_cancel₀ _ two_ne_zero]
          exact pow_le_of_le_one (hg0 j) (hg1 j) (NeZero.ne N)
      _ = ENNReal.ofReal ϱ' := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hsumg.summable, hsumg.tsum_eq]
      _ ≤ ENNReal.ofReal ϱ := ENNReal.ofReal_le_ofReal (min_le_left _ _)

end Homogenization
