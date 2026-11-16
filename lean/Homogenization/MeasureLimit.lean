import Homogenization.LowerBound

/-!
# The cited result (c) `CitedMeasureLimit`, proved

`citedMeasureLimit_holds`: for `O ⊆ ℝᴺ` open and bounded and `gₙ ≥ 0` with
`sup_n ∫_O gₙ < ∞`, a subsequence of the measures `gₙ dx` on `O` has a limit `μ`, a finite measure
carried by `O`, with `μ(U) ≤ liminf ∫_U g_{φ n}` for `U ⊆ O` open and
`limsup ∫_K g_{φ n} ≤ μ(K)` for `K ⊆ O` compact.

Proof: the normalized measures are probability measures carried by the compact `cl O` (or a Dirac
mass when `gₙ dx = 0`), hence tight; Prokhorov's theorem (`isCompact_closure_of_isTightMeasureSet`)
and the metrizability of the space of probability measures give a subsequence along which the
normalized measures and the masses converge; the portmanteau inequalities
(`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`,
`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`) then pass to the products.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ}

/-- **Result (c), proved**: weak-* compactness of bounded sequences of measures `gₙ dx` on a
bounded open set, with the two Alexandrov (portmanteau) inequalities. -/
theorem citedMeasureLimit_holds [NeZero N] : CitedMeasureLimit N := by
  intro O hOo hOb g hg ⟨C, hC, hgC⟩
  -- the finite measures `gₙ dx` on `O`
  set m : ℕ → Measure (Sp N) := fun n => (volume.restrict O).withDensity (g n)
  have hmU : ∀ n U, MeasurableSet U → U ⊆ O → m n U = ∫⁻ x in U, g n x := by
    intro n U hU hUO
    simp only [m]
    rw [withDensity_apply _ hU, Measure.restrict_restrict hU, inter_eq_left.2 hUO]
  have hmcompl : ∀ n, m n Oᶜ = 0 := by
    intro n
    simp only [m]
    rw [withDensity_apply _ hOo.measurableSet.compl, Measure.restrict_restrict
      hOo.measurableSet.compl, compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]
  have hmuniv : ∀ n, m n univ = ∫⁻ x in O, g n x := by
    intro n
    simp only [m]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfin : ∀ n, IsFiniteMeasure (m n) := fun n =>
    ⟨by rw [hmuniv]; exact (hgC n).trans_lt hC⟩
  let ν : ℕ → FiniteMeasure (Sp N) := fun n => ⟨m n, hfin n⟩
  let c : ℕ → ℝ≥0 := fun n => (ν n).mass
  -- normalized measures (a Dirac mass when `gₙ dx = 0`)
  set xs : Sp N := (inferInstance : Nonempty (Sp N)).some
  let δx : ProbabilityMeasure (Sp N) := ⟨Measure.dirac xs, inferInstance⟩
  let P : ℕ → ProbabilityMeasure (Sp N) := fun n => if c n = 0 then δx else (ν n).normalize
  have hmP : ∀ n s, m n s = (c n : ℝ≥0∞) * (P n : Measure (Sp N)) s := by
    intro n s
    by_cases h0 : c n = 0
    · have hν : ν n = 0 := (FiniteMeasure.mass_zero_iff _).1 h0
      have hms : m n s = 0 := by
        change ((ν n : Measure (Sp N))) s = 0
        rw [hν]; rfl
      rw [hms, h0, ENNReal.coe_zero, zero_mul]
    · have h := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) ((ν n).self_eq_mass_mul_normalize s)
      simp only [ENNReal.coe_mul, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
      simp only [P, if_neg h0]
      exact h
  have hcC : ∀ n, (c n : ℝ≥0∞) ≤ C := by
    intro n
    rw [FiniteMeasure.ennreal_mass]
    exact (hmuniv n).le.trans (hgC n)
  -- tightness: every `P n` lives on the compact `cl O ∪ {xs}`
  set K₀ : Set (Sp N) := closure O ∪ {xs}
  have hK₀ : IsCompact K₀ := hOb.isCompact_closure.union isCompact_singleton
  have hPsupp : ∀ n, (P n : Measure (Sp N)) K₀ᶜ = 0 := by
    intro n
    by_cases h0 : c n = 0
    · simp only [P, if_pos h0]
      change Measure.dirac xs K₀ᶜ = 0
      rw [Measure.dirac_apply' _ (hK₀.isClosed.measurableSet.compl)]
      simp [K₀]
    · have hm0 : m n K₀ᶜ = 0 := measure_mono_null
        (compl_subset_compl.2 (subset_closure.trans subset_union_left)) (hmcompl n)
      rw [hmP] at hm0
      exact (mul_eq_zero.1 hm0).resolve_left (by exact_mod_cast h0)
  have hT : IsTightMeasureSet
      {((μ : ProbabilityMeasure (Sp N)) : Measure (Sp N)) | μ ∈ range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε _
    refine ⟨K₀, hK₀, ?_⟩
    rintro μ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [hPsupp n]
    exact zero_le
  -- extraction of a subsequence along which masses and normalized measures converge
  have hcl : IsCompact (Icc (0 : ℝ≥0) C.toNNReal ×ˢ closure (range P)) :=
    isCompact_Icc.prod (isCompact_closure_of_isTightMeasureSet hT)
  have hmem : ∀ n, (c n, P n) ∈ Icc (0 : ℝ≥0) C.toNNReal ×ˢ closure (range P) := by
    intro n
    refine ⟨⟨zero_le, ?_⟩, subset_closure ⟨n, rfl⟩⟩
    have := ENNReal.toNNReal_mono hC.ne (hcC n)
    simpa using this
  obtain ⟨⟨c₀, P₀⟩, -, φ, hφ, hlim⟩ := hcl.tendsto_subseq hmem
  have hc : Tendsto (fun n => (c (φ n) : ℝ≥0∞)) atTop (𝓝 (c₀ : ℝ≥0∞)) :=
    ENNReal.tendsto_coe.2 ((continuous_fst.tendsto _).comp hlim)
  have hP : Tendsto (fun n => P (φ n)) atTop (𝓝 P₀) := (continuous_snd.tendsto _).comp hlim
  refine ⟨φ, (c₀ • (P₀ : Measure (Sp N))).restrict O, hφ, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.restrict_apply hOo.measurableSet.compl, compl_inter_self, measure_empty]
  · intro U hU hUO
    rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.2 hUO,
      Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have heq : (fun n => ∫⁻ x in U, g (φ n) x) =
        fun n => (c (φ n) : ℝ≥0∞) * (P (φ n) : Measure (Sp N)) U := by
      funext n; rw [← hmU _ U hU.measurableSet hUO, hmP]
    rw [heq]
    calc (c₀ : ℝ≥0∞) * (P₀ : Measure (Sp N)) U
        ≤ liminf (fun n => (c (φ n) : ℝ≥0∞)) atTop *
            liminf (fun n => (P (φ n) : Measure (Sp N)) U) atTop :=
          mul_le_mul' hc.liminf_eq.ge (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hP hU)
      _ ≤ _ := ENNReal.le_liminf_mul
  · intro K hK hKO
    rw [Measure.restrict_apply hK.measurableSet, inter_eq_left.2 hKO,
      Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have heq : (fun n => ∫⁻ x in K, g (φ n) x) =
        fun n => (c (φ n) : ℝ≥0∞) * (P (φ n) : Measure (Sp N)) K := by
      funext n; rw [← hmU _ K hK.measurableSet hKO, hmP]
    rw [heq]
    have hPK : limsup (fun n => (P (φ n) : Measure (Sp N)) K) atTop ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => prob_le_one))
    calc limsup (fun n => (c (φ n) : ℝ≥0∞) * (P (φ n) : Measure (Sp N)) K) atTop
        ≤ limsup (fun n => (c (φ n) : ℝ≥0∞)) atTop *
            limsup (fun n => (P (φ n) : Measure (Sp N)) K) atTop :=
          ENNReal.limsup_mul_le' (Or.inr hPK)
            (Or.inl (by rw [hc.limsup_eq]; exact ENNReal.coe_ne_top))
      _ ≤ (c₀ : ℝ≥0∞) * (P₀ : Measure (Sp N)) K :=
          mul_le_mul' hc.limsup_eq.le
            (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hP hK.isClosed)

end Homogenization
