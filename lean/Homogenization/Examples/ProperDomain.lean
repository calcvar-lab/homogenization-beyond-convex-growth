import Homogenization.Basic

/-!
# The half-space example with a singular boundary term

This is the finite-dimensional datum `G₂` used in the proper-effective-domain example in
Subsection `properdomain` of the paper. Its power term uses the Frobenius norm, as required by
(DG2). The file formalizes the definition, Frobenius growth bound, effective domain, lower
semicontinuity, convexity, and radial blow-up. The surrounding integrand `W♯` and the full
Proposition `prop:properdomain` are not formalized here.
-/

open Filter Set Topology
open scoped ENNReal NNReal

namespace Homogenization

variable {m N : ℕ} [NeZero m] [NeZero N]

/-- The scalar singular term from the paper: it blows up at and beyond `1`. -/
noncomputable def boundarySingularity (s : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - s))⁻¹

/-- The half-space `χ₁₁ < 1` in matrix space. -/
def properDomainHalfSpace : Set (Mat m N) :=
  {χ | χ (Pi.single 0 1) 0 < 1}

/-- The Frobenius norm of a matrix: the Euclidean norm of its coefficient array, i.e.
`√(∑ i j, (matCoordEquiv m N χ (i, j))^2)`. The ambient norm on `Mat m N` remains the
operator norm; this explicit coefficient norm is the one used in the article's `G₂`. -/
noncomputable def matrixFrobeniusNorm (χ : Mat m N) : ℝ :=
  ‖(WithLp.toLp 2 (matCoordEquiv m N χ) : EuclideanSpace ℝ (Fin m × Fin N))‖

omit [NeZero m] [NeZero N] in
/-- The coordinate formula for `matrixFrobeniusNorm`; this is the usual Frobenius norm. -/
theorem matrixFrobeniusNorm_eq_sqrt_sum (χ : Mat m N) :
    matrixFrobeniusNorm χ =
      Real.sqrt (∑ ij : Fin m × Fin N, (matCoordEquiv m N χ ij) ^ 2) := by
  simp [matrixFrobeniusNorm, PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs]

/-- The example integrand `|χ|_F^p + g₀(χ₁₁)` as an extended nonnegative real. -/
noncomputable def properDomainG2 (p : ℝ) (χ : Mat m N) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixFrobeniusNorm χ ^ p) +
    boundarySingularity (χ (Pi.single 0 1) 0)

/-- The power term gives exactly the Frobenius-norm growth required in (DG2). -/
theorem properDomainG2_ge_frobenius_rpow (p : ℝ) (χ : Mat m N) :
    ENNReal.ofReal (matrixFrobeniusNorm χ ^ p) ≤ properDomainG2 p χ := by
  exact le_add_of_nonneg_right bot_le

@[simp]
theorem boundarySingularity_ne_top_iff {s : ℝ} :
    boundarySingularity s ≠ ⊤ ↔ s < 1 := by
  simp [boundarySingularity]

/-- Lower semicontinuity of the singular term, including its infinite value on `[1,∞)`. -/
theorem boundarySingularity_lowerSemicontinuous :
    LowerSemicontinuous boundarySingularity := by
  rw [← lowerSemicontinuousOn_univ_iff, lowerSemicontinuousOn_iff_preimage_Ioi]
  intro a
  refine ⟨{s | ENNReal.ofReal (1 - s) < a⁻¹}, ?_, ?_⟩
  · exact isOpen_lt (ENNReal.continuous_ofReal.comp (by fun_prop)) continuous_const
  · ext s
    simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_Ioi]
    change a < (ENNReal.ofReal (1 - s))⁻¹ ↔ ENNReal.ofReal (1 - s) < a⁻¹
    exact ENNReal.lt_inv_iff_lt_inv

/-- The singularity tends to `+∞` from the left at its boundary point. -/
theorem boundarySingularity_tendsto_top :
    Tendsto boundarySingularity (𝓝[<] (1 : ℝ)) (𝓝 (⊤ : ℝ≥0∞)) := by
  have hden0 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_right (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa using hc.sub hid
  have hden : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hden0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (by simpa using ht)
  have hinv : Tendsto (fun t : ℝ => (1 - t)⁻¹) (𝓝[<] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  have htop : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 - t)⁻¹))
      (𝓝[<] (1 : ℝ)) (𝓝 (⊤ : ℝ≥0∞)) := ENNReal.tendsto_ofReal_nhds_top.2 hinv
  have heq : (fun t : ℝ => boundarySingularity t) =ᶠ[𝓝[<] (1 : ℝ)]
      fun t => ENNReal.ofReal ((1 - t)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [boundarySingularity]
    rw [← ENNReal.ofReal_inv_of_pos (sub_pos.mpr ht)]
  exact htop.congr' heq.symm

/-- Lower semicontinuity of `G₂`; the only noncontinuous summand is handled by
`boundarySingularity_lowerSemicontinuous`. -/
theorem properDomainG2_lowerSemicontinuous (p : ℝ) (hp : 0 ≤ p) :
    LowerSemicontinuous (properDomainG2 (m := m) (N := N) p) := by
  have hnorm : Continuous (matrixFrobeniusNorm (m := m) (N := N)) := by
    unfold matrixFrobeniusNorm
    fun_prop
  have hpow : Continuous (fun χ : Mat m N => matrixFrobeniusNorm χ ^ p) :=
    hnorm.rpow_const (fun _ => Or.inr hp)
  have hbase : Continuous (fun χ : Mat m N => ENNReal.ofReal (matrixFrobeniusNorm χ ^ p)) :=
    ENNReal.continuous_ofReal.comp hpow
  have hentry : Continuous (fun χ : Mat m N => χ (Pi.single 0 1) 0) := by fun_prop
  have hsing : LowerSemicontinuous (fun χ : Mat m N =>
      boundarySingularity (χ (Pi.single 0 1) 0)) :=
    boundarySingularity_lowerSemicontinuous.comp hentry
  exact LowerSemicontinuous.add' hbase.lowerSemicontinuous
    hsing (by intro χ; fun_prop)

omit [NeZero m] [NeZero N] in
/-- The operator-norm power is convex for `p ≥ 1`; `G₂` uses the Frobenius-norm power below. -/
theorem norm_rpow_convexOn (p : ℝ) (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun χ : Mat m N => ‖χ‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro χ _ ζ _ a b ha hb hab
  have hpow := (convexOn_rpow hp).2 (norm_nonneg χ) (norm_nonneg ζ) ha hb hab
  have hnorm : ‖a • χ + b • ζ‖ ≤ a * ‖χ‖ + b * ‖ζ‖ := by
    calc
      ‖a • χ + b • ζ‖ ≤ ‖a • χ‖ + ‖b • ζ‖ := norm_add_le _ _
      _ = a * ‖χ‖ + b * ‖ζ‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hmono := Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans (by positivity) hp)
  have hpow' : (a * ‖χ‖ + b * ‖ζ‖) ^ p ≤ a * ‖χ‖ ^ p + b * ‖ζ‖ ^ p := by
    simpa [smul_eq_mul] using hpow
  have hmono' : ‖a • χ + b • ζ‖ ^ p ≤ (a * ‖χ‖ + b * ‖ζ‖) ^ p := by
    exact hmono (a := ‖a • χ + b • ζ‖) (b := a * ‖χ‖ + b * ‖ζ‖)
      (norm_nonneg _) (Set.mem_Ici.mpr (by positivity)) hnorm
  exact hmono'.trans hpow'

omit [NeZero m] [NeZero N] in
/-- The Frobenius-norm power is convex for exponents `p ≥ 1`. -/
theorem frobeniusNorm_rpow_convexOn (p : ℝ) (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun χ : Mat m N => matrixFrobeniusNorm χ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro χ _ ζ _ a b ha hb hab
  have hpow := (convexOn_rpow hp).2
    (norm_nonneg (WithLp.toLp 2 (matCoordEquiv m N χ)))
    (norm_nonneg (WithLp.toLp 2 (matCoordEquiv m N ζ))) ha hb hab
  have hcoord :
      (WithLp.toLp 2 (matCoordEquiv m N (a • χ + b • ζ)) :
        EuclideanSpace ℝ (Fin m × Fin N)) =
        a • (WithLp.toLp 2 (matCoordEquiv m N χ) : EuclideanSpace ℝ (Fin m × Fin N)) +
        b • (WithLp.toLp 2 (matCoordEquiv m N ζ) : EuclideanSpace ℝ (Fin m × Fin N)) := by
    ext ij
    simp [map_add, map_smul]
  have hnorm : matrixFrobeniusNorm (a • χ + b • ζ) ≤
      a * matrixFrobeniusNorm χ + b * matrixFrobeniusNorm ζ := by
    change ‖WithLp.toLp 2 (matCoordEquiv m N (a • χ + b • ζ))‖ ≤ _
    rw [hcoord]
    calc
      _ ≤ ‖a • (WithLp.toLp 2 (matCoordEquiv m N χ) :
            EuclideanSpace ℝ (Fin m × Fin N))‖ +
          ‖b • (WithLp.toLp 2 (matCoordEquiv m N ζ) :
            EuclideanSpace ℝ (Fin m × Fin N))‖ := norm_add_le _ _
      _ = _ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
          matrixFrobeniusNorm]
  have hmono := Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans (by positivity) hp)
  have hFχ : 0 ≤ matrixFrobeniusNorm χ := norm_nonneg _
  have hFζ : 0 ≤ matrixFrobeniusNorm ζ := norm_nonneg _
  have hFmix : 0 ≤ a * matrixFrobeniusNorm χ + b * matrixFrobeniusNorm ζ :=
    add_nonneg (mul_nonneg ha hFχ) (mul_nonneg hb hFζ)
  have hpow' : (a * matrixFrobeniusNorm χ + b * matrixFrobeniusNorm ζ) ^ p ≤
      a * matrixFrobeniusNorm χ ^ p + b * matrixFrobeniusNorm ζ ^ p := by
    simpa [smul_eq_mul, matrixFrobeniusNorm] using hpow
  have hmono' : matrixFrobeniusNorm (a • χ + b • ζ) ^ p ≤
      (a * matrixFrobeniusNorm χ + b * matrixFrobeniusNorm ζ) ^ p :=
    hmono (a := matrixFrobeniusNorm (a • χ + b • ζ))
      (b := a * matrixFrobeniusNorm χ + b * matrixFrobeniusNorm ζ)
      (by change 0 ≤ ‖(WithLp.toLp 2
        (matCoordEquiv m N (a • χ + b • ζ)) : EuclideanSpace ℝ (Fin m × Fin N))‖
          exact norm_nonneg _)
      (Set.mem_Ici.mpr hFmix) hnorm
  exact hmono'.trans hpow'

omit [NeZero m] [NeZero N] in
/-- Converting a nonnegative real convex function to `ℝ≥0∞` preserves convexity. -/
theorem convexENN_of_nonneg_convexOn {f : Mat m N → ℝ}
    (hf : ∀ χ, 0 ≤ f χ) (hconv : ConvexOn ℝ Set.univ f) :
    ConvexENN (fun χ => ENNReal.ofReal (f χ)) := by
  intro χ ζ t ht
  have ha : 0 ≤ (t : ℝ) := by exact_mod_cast t.2
  have hb : 0 ≤ ((1 - t : ℝ≥0) : ℝ) := by
    exact_mod_cast (show 0 ≤ (1 - t : ℝ≥0) from (1 - t).property)
  have hab : (t : ℝ) + ((1 - t : ℝ≥0) : ℝ) = 1 := by
    rw [NNReal.coe_sub ht]
    simp
  have h := hconv.2 (Set.mem_univ χ) (Set.mem_univ ζ) ha hb hab
  have h₁ : 0 ≤ (t : ℝ) * f χ := mul_nonneg (by exact_mod_cast t.2) (hf χ)
  have h₂ : 0 ≤ ((1 - t : ℝ≥0) : ℝ) * f ζ :=
    mul_nonneg (by exact_mod_cast (show 0 ≤ (1 - t : ℝ≥0) from (1 - t).property)) (hf ζ)
  calc
    ENNReal.ofReal (f ((t : ℝ) • χ + ((1 - t : ℝ≥0) : ℝ) • ζ))
        ≤ ENNReal.ofReal ((t : ℝ) * f χ + ((1 - t : ℝ≥0) : ℝ) * f ζ) :=
          ENNReal.ofReal_le_ofReal h
    _ = (t : ℝ≥0∞) * ENNReal.ofReal (f χ) + (1 - t : ℝ≥0∞) * ENNReal.ofReal (f ζ) := by
      rw [ENNReal.ofReal_add h₁ h₂, ENNReal.ofReal_mul (by exact_mod_cast t.2),
        ENNReal.ofReal_mul (by exact_mod_cast (show 0 ≤ (1 - t : ℝ≥0) from (1 - t).property))]
      simp [ENNReal.ofReal_coe_nnreal]

/-- The real reciprocal is convex on the interval where its denominator is positive. -/
theorem reciprocal_left_convexOn :
    ConvexOn ℝ (Set.Iio (1 : ℝ)) (fun s : ℝ => 1 / (1 - s)) := by
  refine ⟨convex_Iio _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hA : 0 < 1 - x := sub_pos.mpr hx
  have hB : 0 < 1 - y := sub_pos.mpr hy
  have hD : 0 < a * (1 - x) + b * (1 - y) := by
    rcases ha.eq_or_lt with ha0 | haPos
    · subst a
      have hb1 : b = 1 := by linarith
      subst b
      simpa using hB
    · rcases hb.eq_or_lt with hb0 | hbPos
      · subst b
        have ha1 : a = 1 := by linarith
        subst a
        simpa using hA
      · exact add_pos (mul_pos haPos hA) (mul_pos hbPos hB)
  have hden : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
    calc
      1 - (a * x + b * y) = (a + b) - (a * x + b * y) := by rw [hab]
      _ = a * (1 - x) + b * (1 - y) := by ring
  have hbEq : b = 1 - a := by linarith
  change 1 / (1 - (a * x + b * y)) ≤ a * (1 / (1 - x)) + b * (1 / (1 - y))
  rw [hden]
  have hformula : a / (1 - x) + b / (1 - y) -
      1 / (a * (1 - x) + b * (1 - y)) =
    a * b * ((1 - x) - (1 - y)) ^ 2 /
        ((1 - x) * (1 - y) * (a * (1 - x) + b * (1 - y))) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hD, hab]
    rw [hbEq]
    ring
  have hnonneg : 0 ≤ a * b * ((1 - x) - (1 - y)) ^ 2 /
      ((1 - x) * (1 - y) * (a * (1 - x) + b * (1 - y))) := by
    positivity
  have hdiff : 0 ≤ a / (1 - x) + b / (1 - y) -
      1 / (a * (1 - x) + b * (1 - y)) := by rw [hformula]; exact hnonneg
  simp only [div_eq_mul_inv] at hdiff ⊢
  linarith

private theorem boundarySingularity_eq_ofReal_reciprocal {s : ℝ} (hs : s < 1) :
    boundarySingularity s = ENNReal.ofReal (1 / (1 - s)) := by
  simp only [boundarySingularity]
  rw [← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hs)]
  rw [one_div]

/-- The extended singular term remains convex across its infinite-valued region. -/
private theorem boundarySingularity_convexENN :
    ConvexENN (fun χ : Mat m N => boundarySingularity (χ (Pi.single 0 1) 0)) := by
  intro χ ζ t ht
  by_cases ht0 : t = 0
  · subst t
    simp
  by_cases ht1 : t = 1
  · subst t
    simp
  have htPos : 0 < t := lt_of_le_of_ne (show 0 ≤ t by positivity) (Ne.symm ht0)
  have ha : 0 < (t : ℝ) := by exact_mod_cast htPos
  have htlt : t < 1 := lt_of_le_of_ne ht ht1
  have hbNN : 0 < (1 - t : ℝ≥0) := by
    rw [← NNReal.coe_pos, NNReal.coe_sub ht]
    exact sub_pos.mpr (by exact_mod_cast htlt)
  have hb : 0 < ((1 - t : ℝ≥0) : ℝ) := by exact_mod_cast hbNN
  have ha0 : 0 ≤ (t : ℝ) := le_of_lt ha
  have hb0 : 0 ≤ ((1 - t : ℝ≥0) : ℝ) := le_of_lt hb
  have hab : (t : ℝ) + ((1 - t : ℝ≥0) : ℝ) = 1 := by
    simp only [NNReal.coe_sub ht, NNReal.coe_one]
    ring
  let x := χ (Pi.single 0 1) 0
  let y := ζ (Pi.single 0 1) 0
  let z := ((t : ℝ) • χ + ((1 - t : ℝ≥0) : ℝ) • ζ) (Pi.single 0 1) 0
  have hz : z = (t : ℝ) * x + ((1 - t : ℝ≥0) : ℝ) * y := by
    simp [z, x, y, smul_apply, Pi.smul_apply, smul_eq_mul]
  change boundarySingularity z ≤ (t : ℝ≥0∞) * boundarySingularity x +
    (1 - t : ℝ≥0∞) * boundarySingularity y
  by_cases hx : x < 1
  · by_cases hy : y < 1
    · have hzdom : z < 1 := by
        rw [hz]
        calc
          (t : ℝ) * x + ((1 - t : ℝ≥0) : ℝ) * y
              < (t : ℝ) * 1 + ((1 - t : ℝ≥0) : ℝ) * 1 :=
                add_lt_add (mul_lt_mul_of_pos_left hx ha) (mul_lt_mul_of_pos_left hy hb)
          _ = 1 := by simpa only [mul_one] using hab
      have hreal := (reciprocal_left_convexOn).2 hx hy ha0 hb0 hab
      have hreal' : 1 / (1 - z) ≤ (t : ℝ) * (1 / (1 - x)) +
          ((1 - t : ℝ≥0) : ℝ) * (1 / (1 - y)) := by
        simpa [hz, smul_eq_mul] using hreal
      have hleft : boundarySingularity z = ENNReal.ofReal (1 / (1 - z)) :=
        boundarySingularity_eq_ofReal_reciprocal hzdom
      have hχ : boundarySingularity x = ENNReal.ofReal (1 / (1 - x)) :=
        boundarySingularity_eq_ofReal_reciprocal hx
      have hζ : boundarySingularity y = ENNReal.ofReal (1 / (1 - y)) :=
        boundarySingularity_eq_ofReal_reciprocal hy
      rw [hleft, hχ, hζ]
      calc
        ENNReal.ofReal (1 / (1 - z))
            ≤ ENNReal.ofReal ((t : ℝ) * (1 / (1 - x)) +
              ((1 - t : ℝ≥0) : ℝ) * (1 / (1 - y))) :=
                ENNReal.ofReal_le_ofReal hreal'
        _ = (t : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - x)) +
              (1 - t : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - y)) := by
          rw [ENNReal.ofReal_add (mul_nonneg ha0 (by positivity))
            (mul_nonneg hb0 (by positivity)), ENNReal.ofReal_mul (by exact_mod_cast t.2),
            ENNReal.ofReal_mul (by exact_mod_cast (show 0 ≤ (1 - t : ℝ≥0) from (1 - t).property))]
          simp [ENNReal.ofReal_coe_nnreal]
    · have htop : boundarySingularity y = ⊤ := by
        by_contra hne
        exact hy ((boundarySingularity_ne_top_iff).mp hne)
      have hcoef : (1 : ℝ≥0∞) - (t : ℝ≥0∞) ≠ 0 := by
        exact ne_of_gt (tsub_pos_iff_lt.mpr (by exact_mod_cast htlt))
      rw [htop, ← ENNReal.coe_one, ← ENNReal.coe_sub]
      simp [hcoef]
  · have htop : boundarySingularity x = ⊤ := by
      by_contra hne
      exact hx ((boundarySingularity_ne_top_iff).mp hne)
    have hcoef : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt htPos)
    rw [htop]
    simp [hcoef]

/-- The example integrand is convex as an extended nonnegative-valued function for every `p ≥ 1`.
This is the exponent condition needed for convexity of the Frobenius-norm power. -/
theorem properDomainG2_convexENN_of_one_le (p : ℝ) (hp1 : 1 ≤ p) :
    ConvexENN (properDomainG2 (m := m) (N := N) p) := by
  have hpow := convexENN_of_nonneg_convexOn
    (f := fun χ : Mat m N => matrixFrobeniusNorm χ ^ p)
    (fun χ => Real.rpow_nonneg (norm_nonneg
      (WithLp.toLp 2 (matCoordEquiv m N χ))) p)
    (frobeniusNorm_rpow_convexOn p hp1)
  have hsing := boundarySingularity_convexENN (m := m) (N := N)
  intro χ ζ t ht
  change ENNReal.ofReal (matrixFrobeniusNorm ((t : ℝ) • χ +
      ((1 - t : ℝ≥0) : ℝ) • ζ) ^ p) +
      boundarySingularity (((t : ℝ) • χ + ((1 - t : ℝ≥0) : ℝ) • ζ) (Pi.single 0 1) 0) ≤ _
  calc
    _ ≤ ((t : ℝ≥0∞) * ENNReal.ofReal (matrixFrobeniusNorm χ ^ p) +
          (1 - t : ℝ≥0∞) * ENNReal.ofReal (matrixFrobeniusNorm ζ ^ p)) +
        ((t : ℝ≥0∞) * boundarySingularity (χ (Pi.single 0 1) 0) +
          (1 - t : ℝ≥0∞) * boundarySingularity (ζ (Pi.single 0 1) 0)) :=
      add_le_add (hpow χ ζ t ht) (hsing χ ζ t ht)
    _ = (t : ℝ≥0∞) * properDomainG2 p χ +
        (1 - t : ℝ≥0∞) * properDomainG2 p ζ := by
      simp [properDomainG2, mul_add, add_assoc, add_left_comm]

/-- The article assumes `p > N`; this gives the exponent bound needed for convexity. -/
theorem properDomainG2_convexENN (p : ℝ) (hp : (N : ℝ) < p) :
    ConvexENN (properDomainG2 (m := m) (N := N) p) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  exact properDomainG2_convexENN_of_one_le p
    (le_trans (by exact_mod_cast hN) hp.le)

@[simp]
theorem mem_properDomainHalfSpace_iff (χ : Mat m N) :
    χ ∈ properDomainHalfSpace ↔ χ (Pi.single 0 1) 0 < 1 := Iff.rfl

@[simp]
theorem mem_dom_properDomainG2_iff (p : ℝ) (χ : Mat m N) :
    χ ∈ dom (properDomainG2 p) ↔ χ ∈ properDomainHalfSpace := by
  change properDomainG2 p χ < ⊤ ↔ χ ∈ properDomainHalfSpace
  simp only [properDomainG2, ENNReal.add_lt_top, ENNReal.ofReal_lt_top, true_and]
  rw [lt_top_iff_ne_top, boundarySingularity_ne_top_iff]
  rfl

theorem properDomainHalfSpace_isOpen : IsOpen (properDomainHalfSpace (m := m) (N := N)) := by
  change IsOpen {χ : Mat m N | χ (Pi.single 0 1) 0 < 1}
  exact isOpen_lt (by fun_prop) continuous_const

theorem properDomainHalfSpace_isConvex :
    Convex ℝ (properDomainHalfSpace (m := m) (N := N)) := by
  intro χ hχ ζ hζ a b ha hb hab
  change (a • χ + b • ζ) (Pi.single 0 1) 0 < 1
  simp only [add_apply, smul_apply]
  change a * (χ (Pi.single 0 1) 0) + b * (ζ (Pi.single 0 1) 0) < 1
  have hχ' : χ (Pi.single 0 1) 0 < 1 := hχ
  have hζ' : ζ (Pi.single 0 1) 0 < 1 := hζ
  rcases ha.eq_or_lt with rfl | haPos
  · simp only [zero_add] at hab
    rw [hab]
    simpa using hζ'
  · calc
      a * (χ (Pi.single 0 1) 0) + b * (ζ (Pi.single 0 1) 0)
          < a + b := add_lt_add_of_lt_of_le
            (by simpa using mul_lt_mul_of_pos_left hχ' haPos)
            (by simpa using mul_le_mul_of_nonneg_left hζ'.le hb)
      _ = 1 := hab

theorem zero_mem_properDomainHalfSpace :
    (0 : Mat m N) ∈ properDomainHalfSpace := by
  simp [properDomainHalfSpace]

theorem properDomainHalfSpace_ne_univ :
    properDomainHalfSpace (m := m) (N := N) ≠ Set.univ := by
  let e := rankOne (Pi.single (0 : Fin m) (1 : ℝ)) (Pi.single (0 : Fin N) (1 : ℝ))
  intro h
  have he : e ∈ properDomainHalfSpace := by rw [h]; simp
  change e (Pi.single 0 1) 0 < 1 at he
  have heval : e (Pi.single 0 1) 0 = 1 := by
    rw [← matCoordEquiv_apply (m := m) (N := N) (A := e) (i := 0) (j := 0)]
    simp [e, matCoordEquiv_rankOne]
  rw [heval] at he
  exact (lt_irrefl 1) he

/-- The open half-space in the example is unbounded, as required in (DG2). -/
theorem properDomainHalfSpace_not_isBounded :
    ¬ Bornology.IsBounded (properDomainHalfSpace (m := m) (N := N)) := by
  intro hbounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  let e := rankOne (Pi.single (0 : Fin m) (1 : ℝ))
    (Pi.single (0 : Fin N) (1 : ℝ))
  have heval : e (Pi.single 0 1) 0 = 1 := by
    rw [← matCoordEquiv_apply (m := m) (N := N) (A := e) (i := 0) (j := 0)]
    simp [e, matCoordEquiv_rankOne]
  obtain ⟨n, hn⟩ := exists_nat_gt C
  let χ := -(n : ℝ) • e
  have hmem : χ ∈ properDomainHalfSpace := by
    change χ (Pi.single 0 1) 0 < 1
    rw [show χ (Pi.single 0 1) 0 = -(n : ℝ) by simp [χ, smul_apply, Pi.smul_apply, heval]]
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hentry : χ (Pi.single 0 1) 0 = -(n : ℝ) := by
    simp [χ, smul_apply, Pi.smul_apply, heval]
  have hnorm_lower : (n : ℝ) ≤ ‖χ‖ := by
    calc
      (n : ℝ) = |-(n : ℝ)| := by simp
      _ = |matCoordEquiv m N χ (0, 0)| := by rw [matCoordEquiv_apply, hentry]
      _ ≤ ‖matCoordEquiv m N χ‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (matCoordEquiv m N χ) (0, 0)
      _ ≤ ‖χ‖ := matCoordEquiv_norm_le χ
  have hnorm_upper := hC χ hmem
  exact (not_le_of_gt hn) (le_trans hnorm_lower hnorm_upper)

/-- The effective domain of `G₂` is unbounded, by its identification with the half-space. -/
theorem dom_properDomainG2_not_isBounded (p : ℝ) :
    ¬ Bornology.IsBounded (dom (properDomainG2 (m := m) (N := N) p)) := by
  have hdom : dom (properDomainG2 (m := m) (N := N) p) =
      properDomainHalfSpace (m := m) (N := N) := by
    ext χ
    exact mem_dom_properDomainG2_iff p χ
  rw [hdom]
  exact properDomainHalfSpace_not_isBounded

/-- The boundary of this open half-space is exactly the hyperplane `χ₁₁ = 1`. -/
theorem firstEntry_eq_one_of_mem_frontier {χ : Mat m N}
    (hχ : χ ∈ frontier (properDomainHalfSpace (m := m) (N := N))) :
    χ (Pi.single 0 1) 0 = 1 := by
  rw [frontier, properDomainHalfSpace_isOpen.interior_eq] at hχ
  rcases hχ with ⟨hclosure, hnot⟩
  have hclosed : IsClosed {ζ : Mat m N | ζ (Pi.single 0 1) 0 ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  have hle : χ (Pi.single 0 1) 0 ≤ 1 := by
    apply closure_minimal _ hclosed hclosure
    intro ζ hζ
    change ζ (Pi.single 0 1) 0 < 1 at hζ
    exact hζ.le
  have hge : 1 ≤ χ (Pi.single 0 1) 0 := le_of_not_gt hnot
  exact le_antisymm hle hge

/-- The singular term is bounded above by `G₂` along a ray ending at the boundary. -/
theorem boundarySingularity_le_properDomainG2_smul (p t : ℝ) (χ : Mat m N)
    (hχ : χ (Pi.single 0 1) 0 = 1) :
    boundarySingularity t ≤ properDomainG2 p (t • χ) := by
  simp only [properDomainG2, smul_apply, Pi.smul_apply, smul_eq_mul, hχ]
  have hcoord : t * 1 = t := mul_one t
  rw [hcoord]
  exact le_add_of_nonneg_left (by positivity)

/-- The full radial blow-up required in (DG2): for every boundary point `χ`,
`G₂(tχ) → +∞` as `t → 1⁻`. -/
theorem properDomainG2_radial_tendsto_top (p : ℝ) {χ : Mat m N}
    (hχ : χ ∈ frontier (properDomainHalfSpace (m := m) (N := N))) :
    Tendsto (fun t : ℝ => properDomainG2 p (t • χ)) (𝓝[<] (1 : ℝ)) (𝓝 (⊤ : ℝ≥0∞)) := by
  apply ENNReal.tendsto_nhds_top
  intro n
  filter_upwards [ENNReal.tendsto_nhds_top_iff_nat.mp boundarySingularity_tendsto_top n] with t ht
  exact lt_of_lt_of_le ht
    (boundarySingularity_le_properDomainG2_smul p t χ
      (firstEntry_eq_one_of_mem_frontier hχ))

end Homogenization
