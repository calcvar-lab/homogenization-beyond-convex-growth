import Homogenization.Step3
import Homogenization.Examples.ProperDomainBlocks

/-!
# Affine-envelope decoupling for row-block sums

This file formalizes the admissible-corrector operations used in `decouplresult`: continuous
linear projections preserve `Aff0`, and two `Aff0` correctors can be combined on the common
refinement of their affine partitions. No measurability is assumed on the two summands: for an
`Aff0` corrector, `y ↦ F (A + Dφ(y))` coincides a.e. with a finite sum of indicators of the open
pieces of `φ` (`Aff0.aemeasurable_comp_fderiv`), which gives the additivity of the integral.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Homogenization

variable {N m m₁ m₂ : ℕ}

/-- A continuous linear map on the target sends `Aff0` correctors to `Aff0` correctors. -/
theorem Aff0.comp_continuousLinearMap {U : Set (Sp N)} {φ : Sp N → Tgt m}
    (hφ : φ ∈ Aff0 U) (P : Tgt m →L[ℝ] Tgt m₁) :
    (fun y => P (φ y)) ∈ Aff0 U := by
  obtain ⟨K, n, V, ξ, hLip, hzero, hVo, hVU, hVd, hVf, hVc, hder⟩ := Aff0.data hφ
  have hLip' : LipschitzWith (‖P‖₊ * K) (fun y => P (φ y)) :=
    P.lipschitz.comp hLip
  refine ⟨⟨_, hLip'⟩, ?_, ?_⟩
  · intro y hy
    simp [hzero y hy]
  · refine ⟨⟨_, hLip'.lipschitzOnWith⟩, n, V, fun i => P.comp (ξ i), hVo, hVU,
      hVd, hVf, hVc, ?_⟩
    intro i y hy
    exact (P.hasFDerivAt).comp y (hder i y hy)

noncomputable def properDomainFirstBlockProjection (m₁ m₂ : ℕ) :
    Tgt (m₁ + m₂) →L[ℝ] Tgt m₁ :=
  (ContinuousLinearMap.fst ℝ (Tgt m₁) (Tgt m₂)).comp
    (targetBlockSplitEquiv m₁ m₂).toContinuousLinearMap

noncomputable def properDomainSecondBlockProjection (m₁ m₂ : ℕ) :
    Tgt (m₁ + m₂) →L[ℝ] Tgt m₂ :=
  (ContinuousLinearMap.snd ℝ (Tgt m₁) (Tgt m₂)).comp
    (targetBlockSplitEquiv m₁ m₂).toContinuousLinearMap

/-- The first target block of an `Aff0` corrector remains admissible. -/
theorem Aff0.firstBlock {U : Set (Sp N)} {φ : Sp N → Tgt (m₁ + m₂)}
    (hφ : φ ∈ Aff0 U) :
    (fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).1) ∈ Aff0 U := by
  simpa [properDomainFirstBlockProjection] using
    (Aff0.comp_continuousLinearMap hφ (properDomainFirstBlockProjection m₁ m₂))

/-- The second target block of an `Aff0` corrector remains admissible. -/
theorem Aff0.secondBlock {U : Set (Sp N)} {φ : Sp N → Tgt (m₁ + m₂)}
    (hφ : φ ∈ Aff0 U) :
    (fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).2) ∈ Aff0 U := by
  simpa [properDomainSecondBlockProjection] using
    (Aff0.comp_continuousLinearMap hφ (properDomainSecondBlockProjection m₁ m₂))

/-- Two correctors on the same open set can be assembled into a corrector with the stacked
target. The affine pieces are the common refinement `Uᵢ ∩ Vⱼ` of the two finite partitions. -/
theorem Aff0.assembleBlocks {U : Set (Sp N)}
    {φ₁ : Sp N → Tgt m₁} {φ₂ : Sp N → Tgt m₂}
    (hφ₁ : φ₁ ∈ Aff0 U) (hφ₂ : φ₂ ∈ Aff0 U) :
    (fun y => (targetBlockSplitEquiv m₁ m₂).symm (φ₁ y, φ₂ y)) ∈ Aff0 U := by
  obtain ⟨K₁, n₁, U₁, A, hLip₁, hzero₁, hU₁o, hU₁U, hU₁d, hU₁f, hU₁c, hφ₁U⟩ :=
    Aff0.data hφ₁
  obtain ⟨K₂, n₂, V₂, B, hLip₂, hzero₂, hV₂o, hV₂U, hV₂d, hV₂f, hV₂c, hφ₂V⟩ :=
    Aff0.data hφ₂
  let e := targetBlockSplitEquiv m₁ m₂
  let pairFun : Sp N → Tgt m₁ × Tgt m₂ := fun y => (φ₁ y, φ₂ y)
  let φ : Sp N → Tgt (m₁ + m₂) := fun y => e.symm (pairFun y)
  have hpair : LipschitzWith (max K₁ K₂) pairFun := by
    intro x y
    rw [Prod.edist_eq]
    apply max_le
    · exact le_trans (hLip₁ x y) (by gcongr; exact le_max_left K₁ K₂)
    · exact le_trans (hLip₂ x y) (by gcongr; exact le_max_right K₁ K₂)
  have hLip : LipschitzWith (‖e.symm.toContinuousLinearMap‖₊ * max K₁ K₂) φ := by
    simpa [φ, pairFun, Function.comp_def] using
      e.symm.toContinuousLinearMap.lipschitz.comp hpair
  let W : Fin n₁ × Fin n₂ → Set (Sp N) := fun ij => U₁ ij.1 ∩ V₂ ij.2
  let C : Fin n₁ × Fin n₂ → Mat (m₁ + m₂) N := fun ij =>
    e.symm.toContinuousLinearMap.comp ((A ij.1).prod (B ij.2))
  have hWo : ∀ ij, IsOpen (W ij) := fun ij => (hU₁o ij.1).inter (hV₂o ij.2)
  have hWU : ∀ ij, W ij ⊆ U := fun ij y hy => hU₁U ij.1 hy.1
  have hWd : Pairwise fun ij ij' => Disjoint (W ij) (W ij') := by
    intro ij ij' hne
    by_cases hfirst : ij.1 = ij'.1
    · have hsecond : ij.2 ≠ ij'.2 := by
        intro heq
        exact hne (Prod.ext hfirst heq)
      apply Set.disjoint_left.2
      intro y hy hy'
      exact (hV₂d hsecond).le_bot ⟨hy.2, hy'.2⟩
    · apply Set.disjoint_left.2
      intro y hy hy'
      exact (hU₁d hfirst).le_bot ⟨hy.1, hy'.1⟩
  have hWf : ∀ ij, volume (U ∩ frontier (W ij)) = 0 := by
    intro ij
    apply measure_mono_null
      (t := (U ∩ frontier (U₁ ij.1)) ∪ (U ∩ frontier (V₂ ij.2)))
    · intro y hy
      obtain ⟨hyU, hyfr⟩ := hy
      have hyfr' : y ∈ frontier (U₁ ij.1 ∩ V₂ ij.2) := by simpa [W] using hyfr
      rcases frontier_inter_subset (U₁ ij.1) (V₂ ij.2) hyfr' with hleft | hright
      · exact Or.inl ⟨hyU, hleft.1⟩
      · exact Or.inr ⟨hyU, hright.2⟩
    · exact measure_union_null (hU₁f ij.1) (hV₂f ij.2)
  have hWc : volume (U \ ⋃ ij, W ij) = 0 := by
    apply measure_mono_null (t := (U \ ⋃ i, U₁ i) ∪ (U \ ⋃ j, V₂ j))
    · intro y hy
      by_cases hleft : y ∈ ⋃ i, U₁ i
      · right
        refine ⟨hy.1, ?_⟩
        intro hright
        obtain ⟨i, hi⟩ := mem_iUnion.mp hleft
        obtain ⟨j, hj⟩ := mem_iUnion.mp hright
        exact hy.2 (mem_iUnion.mpr ⟨(i, j), ⟨hi, hj⟩⟩)
      · exact Or.inl ⟨hy.1, hleft⟩
    · exact measure_union_null hU₁c hV₂c
  have hder : ∀ ij, ∀ y ∈ W ij, HasFDerivAt φ (C ij) y := by
    intro ij y hy
    have hpairDer : HasFDerivAt pairFun ((A ij.1).prod (B ij.2)) y :=
      (hφ₁U ij.1 y hy.1).prodMk (hφ₂V ij.2 y hy.2)
    simpa [φ, pairFun, C, Function.comp_def] using
      (e.symm.toContinuousLinearMap.hasFDerivAt).comp y hpairDer
  have hPW : IsPWAffine U φ :=
    isPWAffine_of_fintype hLip.lipschitzOnWith W C hWo hWU hWd hWf hWc hder
  refine ⟨⟨_, hLip⟩, ?_, hPW⟩
  intro y hy
  simp [hzero₁ y hy, hzero₂ y hy]

private theorem firstBlock_fderiv_eq_of_hasFDerivAt {φ : Sp N → Tgt (m₁ + m₂)}
    {M : Mat (m₁ + m₂) N} {y : Sp N} (hφ : HasFDerivAt φ M y) :
    fderiv ℝ (fun z => (targetBlockSplitEquiv m₁ m₂ (φ z)).1) y =
      (matBlockSplitLinearEquiv m₁ m₂ N M).1 := by
  have hproj :=
    (properDomainFirstBlockProjection m₁ m₂).hasFDerivAt.comp y hφ
  calc
    fderiv ℝ (fun z => (targetBlockSplitEquiv m₁ m₂ (φ z)).1) y =
        (properDomainFirstBlockProjection m₁ m₂).comp M := hproj.fderiv
    _ = (matBlockSplitLinearEquiv m₁ m₂ N M).1 := by
      ext x i
      simp [properDomainFirstBlockProjection, matBlockSplitLinearEquiv_apply_left]

private theorem secondBlock_fderiv_eq_of_hasFDerivAt {φ : Sp N → Tgt (m₁ + m₂)}
    {M : Mat (m₁ + m₂) N} {y : Sp N} (hφ : HasFDerivAt φ M y) :
    fderiv ℝ (fun z => (targetBlockSplitEquiv m₁ m₂ (φ z)).2) y =
      (matBlockSplitLinearEquiv m₁ m₂ N M).2 := by
  have hproj :=
    (properDomainSecondBlockProjection m₁ m₂).hasFDerivAt.comp y hφ
  calc
    fderiv ℝ (fun z => (targetBlockSplitEquiv m₁ m₂ (φ z)).2) y =
        (properDomainSecondBlockProjection m₁ m₂).comp M := hproj.fderiv
    _ = (matBlockSplitLinearEquiv m₁ m₂ N M).2 := by
      ext x i
      simp [properDomainSecondBlockProjection, matBlockSplitLinearEquiv_apply_right]

private theorem ennreal_iInf₂_add_iInf₂ {ι κ : Type*} (p : ι → Prop) (q : κ → Prop)
    (f : ∀ i, p i → ℝ≥0∞) (g : ∀ j, q j → ℝ≥0∞) :
    (⨅ i, ⨅ hi, f i hi) + (⨅ j, ⨅ hj, g j hj) =
      ⨅ i, ⨅ hi, ⨅ j, ⨅ hj, f i hi + g j hj := by
  rw [ENNReal.iInf_add]
  simp_rw [ENNReal.iInf_add]
  simp_rw [ENNReal.add_iInf]

/-- For `φ ∈ Aff0 U` on a measurable set `U`, the function `y ↦ F (A + Dφ(y))` is a.e.
measurable on `U` for every `F`, measurable or not: it coincides a.e. on `U` with the finite sum
`∑ᵢ F (A + ξᵢ) 1_{Vᵢ}` over the open pieces `Vᵢ` of `φ`. -/
theorem Aff0.aemeasurable_comp_fderiv {U : Set (Sp N)} (hUm : MeasurableSet U)
    {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 U) (F : Mat m N → ℝ≥0∞) (A : Mat m N) :
    AEMeasurable (fun y => F (A + fderiv ℝ φ y)) (volume.restrict U) := by
  classical
  obtain ⟨K, n, V, ξ, -, -, hVo, -, hVd, -, hVc, hder⟩ := Aff0.data hφ
  refine ⟨fun y => ∑ i, (V i).indicator (fun _ => F (A + ξ i)) y, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hVo i).measurableSet
  · have hcover : ∀ᵐ y ∂volume.restrict U, y ∈ ⋃ i, V i := by
      rw [ae_restrict_iff' hUm, ae_iff]
      have hbad : {y | ¬ (y ∈ U → y ∈ ⋃ i, V i)} = U \ ⋃ i, V i := by
        ext y
        simp [Classical.not_imp]
      rw [hbad, hVc]
    filter_upwards [hcover] with y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    rw [Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem
        (fun hyj => (hVd hji).ne_of_mem hyj hyi rfl) _) (by simp),
      indicator_of_mem hyi, (hder i y hyi).fderiv]

/-- Generic `decouplresult` for the affine envelope on the block decomposition of matrices, with
no measurability assumption on `F` and `G` (`Aff0.aemeasurable_comp_fderiv`). The ENNReal
infimum identities cover infinite values as well as finite ones. -/
theorem Zaff_separatedSum_matBlockSplit
    (F : Mat m₁ N → ℝ≥0∞) (G : Mat m₂ N → ℝ≥0∞) :
    Zaff (fun A : Mat (m₁ + m₂) N =>
      separatedSum F G (matBlockSplitLinearEquiv m₁ m₂ N A)) =
      fun A => Zaff F (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
        Zaff G (matBlockSplitLinearEquiv m₁ m₂ N A).2 := by
  classical
  let U : Set (Sp N) := cube 1 0
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  let L : Mat (m₁ + m₂) N → ℝ≥0∞ := fun M => separatedSum F G (e M)
  let E : Mat (m₁ + m₂) N → (Sp N → Tgt (m₁ + m₂)) → ℝ≥0∞ := fun A φ =>
    ∫⁻ y in U, L (A + fderiv ℝ φ y)
  let E₁ : Mat m₁ N → (Sp N → Tgt m₁) → ℝ≥0∞ := fun A φ =>
    ∫⁻ y in U, F (A + fderiv ℝ φ y)
  let E₂ : Mat m₂ N → (Sp N → Tgt m₂) → ℝ≥0∞ := fun A φ =>
    ∫⁻ y in U, G (A + fderiv ℝ φ y)
  have hU : IsOpen U := by simp [U, isOpen_cube]
  have hUm : MeasurableSet U := hU.measurableSet
  have henergy (A : Mat (m₁ + m₂) N) (φ : Sp N → Tgt (m₁ + m₂))
      (hφ : φ ∈ Aff0 U) :
      E A φ = E₁ (e A).1 (fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).1) +
        E₂ (e A).2 (fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).2) := by
    obtain ⟨K, n, V, ξ, hLip, hzero, hVo, hVU, hVd, hVf, hVc, hder⟩ := Aff0.data hφ
    let φ₁ : Sp N → Tgt m₁ := fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).1
    let φ₂ : Sp N → Tgt m₂ := fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).2
    have hφ₁ : φ₁ ∈ Aff0 U := Aff0.firstBlock hφ
    have hφ₂ : φ₂ ∈ Aff0 U := Aff0.secondBlock hφ
    have hcover : ∀ᵐ y ∂volume.restrict U, y ∈ ⋃ i, V i := by
      apply (ae_restrict_iff' hUm).2
      have hbad : {y | ¬ (y ∈ U → y ∈ ⋃ i, V i)} = U \ ⋃ i, V i := by
        ext y
        simp [Classical.not_imp]
      rw [ae_iff]
      rw [hbad, hVc]
    have hAE : (fun y => L (A + fderiv ℝ φ y)) =ᵐ[volume.restrict U]
        (fun y => F ((e A).1 + fderiv ℝ φ₁ y) +
          G ((e A).2 + fderiv ℝ φ₂ y)) := by
      filter_upwards [hcover, ae_restrict_mem hUm] with y hyV hyU
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyV
      have hblock₁ : (e (A + fderiv ℝ φ y)).1 = (e A).1 + fderiv ℝ φ₁ y := by
        have hder₁ : (e (fderiv ℝ φ y)).1 = fderiv ℝ φ₁ y := by
          calc
            (e (fderiv ℝ φ y)).1 = (e (ξ i)).1 := by
              rw [(hder i y hyi).fderiv]
            _ = fderiv ℝ φ₁ y :=
              (firstBlock_fderiv_eq_of_hasFDerivAt (hder i y hyi)).symm
        rw [map_add]
        simp only [Prod.fst_add, hder₁]
      have hblock₂ : (e (A + fderiv ℝ φ y)).2 = (e A).2 + fderiv ℝ φ₂ y := by
        have hder₂ : (e (fderiv ℝ φ y)).2 = fderiv ℝ φ₂ y := by
          calc
            (e (fderiv ℝ φ y)).2 = (e (ξ i)).2 := by
              rw [(hder i y hyi).fderiv]
            _ = fderiv ℝ φ₂ y :=
              (secondBlock_fderiv_eq_of_hasFDerivAt (hder i y hyi)).symm
        rw [map_add]
        simp only [Prod.snd_add, hder₂]
      change F (e (A + fderiv ℝ φ y)).1 + G (e (A + fderiv ℝ φ y)).2 = _
      rw [hblock₁, hblock₂]
    have hmeas₁ : AEMeasurable (fun y => F ((e A).1 + fderiv ℝ φ₁ y)) (volume.restrict U) :=
      Aff0.aemeasurable_comp_fderiv hUm hφ₁ F (e A).1
    calc
      E A φ = ∫⁻ y in U, F ((e A).1 + fderiv ℝ φ₁ y) +
          G ((e A).2 + fderiv ℝ φ₂ y) := by
        exact lintegral_congr_ae hAE
      _ = E₁ (e A).1 φ₁ + E₂ (e A).2 φ₂ := by
        simp only [E₁, E₂]
        rw [MeasureTheory.lintegral_add_left' hmeas₁]
  have hlow (A : Mat (m₁ + m₂) N) :
      Zaff F (e A).1 + Zaff G (e A).2 ≤ Zaff L A := by
    simp only [Zaff, Yt]
    apply le_iInf₂
    intro φ hφ
    change (⨅ ψ ∈ Aff0 U, E₁ (e A).1 ψ) + (⨅ ψ ∈ Aff0 U, E₂ (e A).2 ψ) ≤ E A φ
    rw [henergy A φ hφ]
    exact add_le_add
      (iInf₂_le (fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).1)
        (Aff0.firstBlock hφ))
      (iInf₂_le (fun y => (targetBlockSplitEquiv m₁ m₂ (φ y)).2)
        (Aff0.secondBlock hφ))
  have hhigh (A : Mat (m₁ + m₂) N) :
      Zaff L A ≤ Zaff F (e A).1 + Zaff G (e A).2 := by
    simp only [Zaff, Yt]
    rw [ennreal_iInf₂_add_iInf₂]
    refine le_iInf fun φ₁ => ?_
    refine le_iInf fun hφ₁ => ?_
    refine le_iInf fun φ₂ => ?_
    refine le_iInf fun hφ₂ => ?_
    let φ := fun y => (targetBlockSplitEquiv m₁ m₂).symm (φ₁ y, φ₂ y)
    have hφ : φ ∈ Aff0 U := Aff0.assembleBlocks hφ₁ hφ₂
    calc
      Zaff L A ≤ E A φ := iInf₂_le φ hφ
      _ = E₁ (e A).1 φ₁ + E₂ (e A).2 φ₂ := by
        simpa [E₁, E₂, φ] using henergy A φ hφ
  funext A
  exact le_antisymm (hhigh A) (hlow A)

end Homogenization
