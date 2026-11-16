import Homogenization.Examples.ProperDomainData

/-!
# Convexity and geometry of the `G♯` example

This file formalizes clause (i) of `prop:properdomain` for the concrete `G₂` example.
-/

open Filter Set Topology
open scoped ENNReal NNReal

namespace Homogenization

variable {N m₁ m₂ : ℕ} [NeZero N] [NeZero m₁] [NeZero m₂]

private noncomputable def properDomainGtildeReal (D : ProperDomainGData N) (s : ℝ) : ℝ :=
  (D.gTilde (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) : ℝ)

omit [NeZero N] in
private theorem properDomainGtildeReal_convex (D : ProperDomainGData N) :
    ConvexOn ℝ Set.univ (properDomainGtildeReal D) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let u : ℝ≥0 := ⟨max x 0, le_max_right x 0⟩
  let v : ℝ≥0 := ⟨max y 0, le_max_right y 0⟩
  let t : ℝ≥0 := ⟨a, ha⟩
  let s : ℝ≥0 := ⟨b, hb⟩
  have habNN : t + s = 1 := by
    apply NNReal.eq
    change a + b = 1
    exact hab
  have ht : t ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    change a ≤ 1
    linarith
  have hbmax : max (a * x + b * y) 0 ≤ a * max x 0 + b * max y 0 := by
    apply max_le
    · exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left x 0) ha)
        (mul_le_mul_of_nonneg_left (le_max_left y 0) hb)
    · exact add_nonneg
        (mul_nonneg ha (le_max_right x 0))
        (mul_nonneg hb (le_max_right y 0))
  have harg : (⟨max (a * x + b * y) 0, le_max_right _ _⟩ : ℝ≥0) ≤
      t * u + (1 - t : ℝ≥0) * v := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub ht]
    have hbEq : b = 1 - a := by linarith
    change max (a * x + b * y) 0 ≤ (t : ℝ) * (u : ℝ) +
      (1 - (t : ℝ)) * (v : ℝ)
    have htval : (t : ℝ) = a := rfl
    rw [htval, hbEq]
    change max (a * x + (1 - a) * y) 0 ≤
      a * max x 0 + (1 - a) * max y 0
    rw [show b = 1 - a by linarith] at hbmax
    exact hbmax
  have hmono := D.gTilde_monotone harg
  have hcv := D.gTilde_convex u v t ht
  change (D.gTilde ⟨max (a * x + b * y) 0, le_max_right _ _⟩ : ℝ) ≤ _
  calc
    _ ≤ (D.gTilde (t * u + (1 - t) * v) : ℝ) := by exact_mod_cast hmono
    _ ≤ (t : ℝ) * (D.gTilde u : ℝ) + (1 - (t : ℝ)) * (D.gTilde v : ℝ) := hcv
    _ = a * properDomainGtildeReal D x + b * properDomainGtildeReal D y := by
      have hta : (t : ℝ) = a := rfl
      simp only [properDomainGtildeReal, u, v]
      rw [hta]
      rw [show b = 1 - a by linarith]

omit [NeZero N] in
private theorem properDomainGtildeReal_continuous (D : ProperDomainGData N) :
    Continuous (properDomainGtildeReal D) :=
  (properDomainGtildeReal_convex D).locallyLipschitz.continuous

omit [NeZero N] in
private theorem properDomainGtildeReal_mono (D : ProperDomainGData N) :
    Monotone (properDomainGtildeReal D) := by
  intro x y hxy
  have hmax : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
  have harg : (⟨max x 0, le_max_right x 0⟩ : ℝ≥0) ≤
      ⟨max y 0, le_max_right y 0⟩ := by exact_mod_cast hmax
  exact_mod_cast D.gTilde_monotone harg

noncomputable def properDomainGFinite (D : ProperDomainGData N) (A : Mat m₁ N) : ℝ :=
  matrixFrobeniusNorm A ^ D.p +
    properDomainGtildeReal D (matrixFrobeniusNorm A ^ 2)

omit [NeZero N] [NeZero m₁] in
theorem properDomainG_eq_ofReal (D : ProperDomainGData N) (A : Mat m₁ N) :
    properDomainG D A = ENNReal.ofReal (properDomainGFinite D A) := by
  have hnorm : 0 ≤ matrixFrobeniusNorm A := norm_nonneg _
  have hp : 0 ≤ matrixFrobeniusNorm A ^ D.p := Real.rpow_nonneg hnorm _
  have hsquare : 0 ≤ matrixFrobeniusNorm A ^ 2 := sq_nonneg _
  have hg : 0 ≤ properDomainGtildeReal D (matrixFrobeniusNorm A ^ 2) := by
    simp [properDomainGtildeReal]
  rw [properDomainGFinite, ENNReal.ofReal_add hp hg]
  simp [properDomainG, properDomainGtildeReal, max_eq_left hsquare,
    ENNReal.ofReal_coe_nnreal]

omit [NeZero m₁] in
theorem properDomainG_lowerSemicontinuous (D : ProperDomainGData N) :
    LowerSemicontinuous (properDomainG (m := m₁) D) := by
  have hnorm : Continuous (matrixFrobeniusNorm (m := m₁) (N := N)) := by
    unfold matrixFrobeniusNorm
    fun_prop
  have hp : Continuous (fun A : Mat m₁ N => matrixFrobeniusNorm A ^ D.p) := by
    have hNpos : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    have hp0 : 0 ≤ D.p := le_trans (by norm_num) (lt_of_le_of_lt hNpos D.dim_lt_p).le
    exact hnorm.rpow_const (fun _ => Or.inr hp0)
  have hsquare : Continuous (fun A : Mat m₁ N => matrixFrobeniusNorm A ^ 2) :=
    hnorm.pow 2
  have hg := (properDomainGtildeReal_continuous D).comp hsquare
  have hreal : Continuous (properDomainGFinite (m₁ := m₁) D) := by
    exact hp.add hg
  have hrepr : properDomainG (m := m₁) D =
      fun A => ENNReal.ofReal (properDomainGFinite (m₁ := m₁) D A) := by
    funext A
    exact properDomainG_eq_ofReal (m₁ := m₁) D A
  rw [hrepr]
  exact (ENNReal.continuous_ofReal.comp hreal).lowerSemicontinuous

omit [NeZero m₁] in
theorem properDomainGFinite_convexOn (D : ProperDomainGData N) :
    ConvexOn ℝ Set.univ (properDomainGFinite (m₁ := m₁) D) := by
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hp1 : 1 ≤ D.p := le_trans hNpos D.dim_lt_p.le
  have hpower := frobeniusNorm_rpow_convexOn (m := m₁) (N := N) D.p hp1
  have hscalar : ConvexOn ℝ Set.univ (fun A : Mat m₁ N =>
      properDomainGtildeReal D (matrixFrobeniusNorm A ^ 2)) := by
    refine ⟨convex_univ, ?_⟩
    intro A _ B _ a b ha hb hab
    let FA := matrixFrobeniusNorm A
    let FB := matrixFrobeniusNorm B
    let FC := matrixFrobeniusNorm (a • A + b • B)
    have hcoord :
        (WithLp.toLp 2 (matCoordEquiv m₁ N (a • A + b • B)) :
          EuclideanSpace ℝ (Fin m₁ × Fin N)) =
          a • (WithLp.toLp 2 (matCoordEquiv m₁ N A) : EuclideanSpace ℝ (Fin m₁ × Fin N)) +
          b • (WithLp.toLp 2 (matCoordEquiv m₁ N B) : EuclideanSpace ℝ (Fin m₁ × Fin N)) := by
      ext ij
      simp [map_add, map_smul]
    have hnorm : FC ≤ a * FA + b * FB := by
      change ‖WithLp.toLp 2 (matCoordEquiv m₁ N (a • A + b • B))‖ ≤ _
      rw [hcoord]
      calc
        _ ≤ ‖a • (WithLp.toLp 2 (matCoordEquiv m₁ N A) :
              EuclideanSpace ℝ (Fin m₁ × Fin N))‖ +
            ‖b • (WithLp.toLp 2 (matCoordEquiv m₁ N B) :
              EuclideanSpace ℝ (Fin m₁ × Fin N))‖ := norm_add_le _ _
        _ = _ := by
          simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
            matrixFrobeniusNorm, FA, FB]
    have hsq : FC ^ 2 ≤ a * FA ^ 2 + b * FB ^ 2 := by
      have hFA : 0 ≤ FA := norm_nonneg _
      have hFB : 0 ≤ FB := norm_nonneg _
      have hFC : 0 ≤ FC := norm_nonneg _
      have havg : 0 ≤ a * FA + b * FB := by positivity
      have hnormsq : FC ^ 2 ≤ (a * FA + b * FB) ^ 2 := by nlinarith
      have hvar : a * FA ^ 2 + b * FB ^ 2 - (a * FA + b * FB) ^ 2 =
          a * b * (FA - FB) ^ 2 := by
        calc
          _ = (a + b) * (a * FA ^ 2 + b * FB ^ 2) -
              (a * FA + b * FB) ^ 2 := by rw [hab]; ring
          _ = _ := by ring
      have hweighted : (a * FA + b * FB) ^ 2 ≤ a * FA ^ 2 + b * FB ^ 2 := by
        have habNonneg : 0 ≤ a * b * (FA - FB) ^ 2 := by positivity
        linarith [hvar]
      exact hnormsq.trans hweighted
    have hmono := (properDomainGtildeReal_mono D) hsq
    have hconv := (properDomainGtildeReal_convex D).2
      (Set.mem_univ (FA ^ 2)) (Set.mem_univ (FB ^ 2)) ha hb hab
    calc
      properDomainGtildeReal D (FC ^ 2) ≤
          properDomainGtildeReal D (a * FA ^ 2 + b * FB ^ 2) := hmono
      _ ≤ a * properDomainGtildeReal D (FA ^ 2) +
          b * properDomainGtildeReal D (FB ^ 2) := hconv
  change ConvexOn ℝ Set.univ
    (fun A : Mat m₁ N => matrixFrobeniusNorm A ^ D.p +
      properDomainGtildeReal D (matrixFrobeniusNorm A ^ 2))
  exact hpower.add hscalar

omit [NeZero m₁] in
theorem properDomainG_convexENN (D : ProperDomainGData N) :
    ConvexENN (properDomainG (m := m₁) D) := by
  have hconv := properDomainGFinite_convexOn (m₁ := m₁) D
  have hnonneg : ∀ A : Mat m₁ N, 0 ≤ properDomainGFinite (m₁ := m₁) D A := by
    intro A
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (NNReal.coe_nonneg (D.gTilde ⟨max _ 0, le_max_right _ _⟩))
  have hreal := convexENN_of_nonneg_convexOn hnonneg hconv
  intro A B t ht
  have hA := properDomainG_eq_ofReal (m₁ := m₁) D A
  have hB := properDomainG_eq_ofReal (m₁ := m₁) D B
  have hmix := properDomainG_eq_ofReal (m₁ := m₁) D
    ((t : ℝ) • A + ((1 - t : ℝ≥0) : ℝ) • B)
  rw [hA, hB, hmix]
  exact hreal A B t ht

omit [NeZero m₁] in
theorem properDomainGSharpExample_convexENN (D : ProperDomainGData N) :
    ConvexENN (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D) := by
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  intro A B t ht
  simp only [properDomainGSharpExample, properDomainGSharp, separatedSum]
  simp only [map_add, map_smul]
  have h₁ := properDomainG_convexENN (m₁ := m₁) D
    (e A).1 (e B).1 t ht
  have h₂ := properDomainG2_convexENN (m := m₂) (N := N) D.p D.dim_lt_p
    (e A).2 (e B).2 t ht
  calc
    _ ≤ (t : ℝ≥0∞) * properDomainG D (e A).1 +
          (1 - t : ℝ≥0∞) * properDomainG D (e B).1 +
        ((t : ℝ≥0∞) * properDomainG2 D.p (e A).2 +
          (1 - t : ℝ≥0∞) * properDomainG2 D.p (e B).2) :=
      add_le_add h₁ h₂
    _ = (t : ℝ≥0∞) *
          (properDomainG D (e A).1 + properDomainG2 D.p (e A).2) +
        (1 - t : ℝ≥0∞) *
          (properDomainG D (e B).1 + properDomainG2 D.p (e B).2) := by ring

omit [NeZero m₁] in
theorem properDomainGSharpExample_lowerSemicontinuous (D : ProperDomainGData N) :
    LowerSemicontinuous (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D) := by
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  have h₁ : LowerSemicontinuous
      (fun z : Mat m₁ N × Mat m₂ N => properDomainG (m := m₁) D z.1) := by
    exact (properDomainG_lowerSemicontinuous (m₁ := m₁) D).comp continuous_fst
  have h₂ : LowerSemicontinuous
      (fun z : Mat m₁ N × Mat m₂ N => properDomainG2 D.p z.2) := by
    have hNpos : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    have hp1 : 1 ≤ D.p := le_trans hNpos D.dim_lt_p.le
    have hp0 : 0 ≤ D.p := le_trans (by norm_num) hp1
    exact (properDomainG2_lowerSemicontinuous (m := m₂) (N := N) D.p hp0).comp
      continuous_snd
  have hsum : LowerSemicontinuous
      (fun z : Mat m₁ N × Mat m₂ N =>
        properDomainG (m := m₁) D z.1 + properDomainG2 D.p z.2) :=
    LowerSemicontinuous.add' h₁ h₂ (by intro z; fun_prop)
  have hcomp := hsum.comp e.continuous
  change LowerSemicontinuous
    (fun A : Mat (m₁ + m₂) N =>
      separatedSum (properDomainG (m := m₁) D) (properDomainG2 D.p) (e A))
  exact hcomp

omit [NeZero m₁] in
theorem dom_properDomainGSharpExample_isOpen (D : ProperDomainGData N) :
    IsOpen (dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)) := by
  rw [dom_properDomainGSharpExample]
  exact (isOpen_univ.prod
    (properDomainHalfSpace_isOpen (m := m₂) (N := N))).preimage
      (matBlockSplitLinearEquiv m₁ m₂ N).continuous

omit [NeZero m₁] in
theorem dom_properDomainGSharpExample_isConvex (D : ProperDomainGData N) :
    Convex ℝ (dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)) := by
  rw [dom_properDomainGSharpExample]
  exact (convex_univ.prod
    (properDomainHalfSpace_isConvex (m := m₂) (N := N))).linear_preimage
      (matBlockSplitLinearEquiv m₁ m₂ N).toLinearMap

omit [NeZero m₁] in
theorem zero_mem_dom_properDomainGSharpExample (D : ProperDomainGData N) :
    (0 : Mat (m₁ + m₂) N) ∈ dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D) := by
  rw [dom_properDomainGSharpExample]
  simp [zero_mem_properDomainHalfSpace (m := m₂) (N := N)]

omit [NeZero m₁] in
theorem dom_properDomainGSharpExample_ne_univ (D : ProperDomainGData N) :
    dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D) ≠ Set.univ := by
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  let B := rankOne (Pi.single (0 : Fin m₂) (1 : ℝ))
    (Pi.single (0 : Fin N) (1 : ℝ))
  have hB : B (Pi.single 0 1) 0 = 1 := by
    rw [← matCoordEquiv_apply (m := m₂) (N := N) (A := B) (i := 0) (j := 0)]
    simp [B, matCoordEquiv_rankOne]
  let z : Mat m₁ N × Mat m₂ N := (0, B)
  let A := e.symm z
  intro heq
  have hA : A ∈ dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D) := by
    rw [heq]
    simp
  rw [dom_properDomainGSharpExample] at hA
  have hz : e A ∈ (Set.univ : Set (Mat m₁ N)) ×ˢ
      properDomainHalfSpace (m := m₂) (N := N) := hA
  have hmem : B ∈ properDomainHalfSpace (m := m₂) (N := N) := by
    have hz₂ : (e A).2 ∈ properDomainHalfSpace (m := m₂) (N := N) := hz.2
    change (e A).2 (Pi.single 0 1) 0 < 1 at hz₂
    simpa [A, z, e] using hz₂
  change B (Pi.single 0 1) 0 < 1 at hmem
  rw [hB] at hmem
  exact (lt_irrefl 1) hmem

theorem dom_properDomainGSharpExample_not_isBounded (D : ProperDomainGData N) :
    ¬ Bornology.IsBounded
      (dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)) := by
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  let C := properDomainHalfSpace (m := m₂) (N := N)
  have himage : e '' dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D) =
      (Set.univ : Set (Mat m₁ N)) ×ˢ C := by
    ext z
    constructor
    · rintro ⟨A, hA, rfl⟩
      rw [dom_properDomainGSharpExample] at hA
      exact hA
    · intro hz
      refine ⟨e.symm z, ?_, by simp⟩
      rw [dom_properDomainGSharpExample]
      change e (e.symm z) ∈ (Set.univ : Set (Mat m₁ N)) ×ˢ C
      simpa only [e.apply_symm_apply] using hz
  intro hbounded
  have hprod : Bornology.IsBounded
      ((Set.univ : Set (Mat m₁ N)) ×ˢ C) := by
    rw [← himage]
    exact Bornology.IsBounded.image e.toContinuousLinearMap hbounded
  have huniv : Bornology.IsBounded (Set.univ : Set (Mat m₁ N)) := by
    apply hprod.image_fst.subset
    intro A _
    exact ⟨(A, 0), ⟨Set.mem_univ _,
      zero_mem_properDomainHalfSpace (m := m₂) (N := N)⟩, rfl⟩
  exact properDomainHalfSpace_not_isBounded (m := m₁) (N := N)
    (huniv.subset (subset_univ _))

theorem properDomainHalfSpace_frontier_eq :
    frontier (properDomainHalfSpace (m := m₂) (N := N)) =
      {A : Mat m₂ N | A (Pi.single 0 1) 0 = 1} := by
  ext A
  constructor
  · exact firstEntry_eq_one_of_mem_frontier (m := m₂) (N := N)
  · intro hA
    rw [frontier, properDomainHalfSpace_isOpen.interior_eq]
    constructor
    · apply (mem_closure_iff_seq_limit).2
      let E := rankOne (Pi.single (0 : Fin m₂) (1 : ℝ))
        (Pi.single (0 : Fin N) (1 : ℝ))
      have hE : E (Pi.single 0 1) 0 = 1 := by
        rw [← matCoordEquiv_apply (m := m₂) (N := N) (A := E) (i := 0) (j := 0)]
        simp [E, matCoordEquiv_rankOne]
      let seq : ℕ → Mat m₂ N := fun n =>
        A - (1 / ((n : ℝ) + 1)) • E
      refine ⟨seq, ?_, ?_⟩
      · intro n
        change A (Pi.single 0 1) 0 = 1 at hA
        change A (Pi.single 0 1) 0 -
          (1 / ((n : ℝ) + 1)) * E (Pi.single 0 1) 0 < 1
        rw [hA, hE]
        have hn : 0 < (1 / ((n : ℝ) + 1)) := by positivity
        linarith
      · have hcoeff : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
            atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
        have hsmul : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • E)
            atTop (𝓝 (0 : Mat m₂ N)) := by
          simpa using hcoeff.smul_const E
        have hseq : Tendsto seq atTop (𝓝 A) := by
          simpa [seq] using tendsto_const_nhds.sub hsmul
        exact hseq
    · change ¬ A (Pi.single 0 1) 0 < 1
      rw [hA]
      exact lt_irrefl 1

omit [NeZero m₁] in
theorem dom_properDomainGSharpExample_frontier_eq (D : ProperDomainGData N) :
    frontier (dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)) =
      (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹'
        ((Set.univ : Set (Mat m₁ N)) ×ˢ
          {B : Mat m₂ N | B (Pi.single 0 1) 0 = 1}) := by
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  calc
    frontier (dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D)) =
        frontier (e ⁻¹' ((Set.univ : Set (Mat m₁ N)) ×ˢ
          properDomainHalfSpace (m := m₂) (N := N))) := by
            rw [dom_properDomainGSharpExample]
    _ = e ⁻¹' frontier ((Set.univ : Set (Mat m₁ N)) ×ˢ
          properDomainHalfSpace (m := m₂) (N := N)) :=
      (e.toHomeomorph.preimage_frontier _).symm
    _ = e ⁻¹' ((Set.univ : Set (Mat m₁ N)) ×ˢ
          {B : Mat m₂ N | B (Pi.single 0 1) 0 = 1}) := by
            rw [frontier_univ_prod_eq, properDomainHalfSpace_frontier_eq]

omit [NeZero m₁] in
theorem dom_properDomainGSharpExample_frontier_nonempty (D : ProperDomainGData N) :
    (frontier (dom (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D))).Nonempty := by
  rw [dom_properDomainGSharpExample_frontier_eq]
  let B := rankOne (Pi.single (0 : Fin m₂) (1 : ℝ))
    (Pi.single (0 : Fin N) (1 : ℝ))
  have hB : B (Pi.single 0 1) 0 = 1 := by
    rw [← matCoordEquiv_apply (m := m₂) (N := N) (A := B) (i := 0) (j := 0)]
    simp [B, matCoordEquiv_rankOne]
  refine ⟨(matBlockSplitLinearEquiv m₁ m₂ N).symm (0, B), ?_⟩
  simp [hB]

end Homogenization
