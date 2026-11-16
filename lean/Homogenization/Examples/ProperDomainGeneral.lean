import Homogenization.Examples.ProperDomainSharpIV
import Homogenization.HypothesesRemarks

/-!
# Proposition `prop:properdomain` for a general `G₂` satisfying (DG2)

The files `ProperDomainGeometry`, `ProperDomainSharpLoc`, `ProperDomainSharpUpper` and
`ProperDomainSharpIV` prove `prop:properdomain` for the concrete half-space example
`G₂(χ) = |χ|_F^p + g₀(χ₁₁)`. This file proves the four clauses for every `G₂` satisfying (DG2),
as in the article:

* `ProperDomainG2Data`: the hypothesis (DG2) on `G₂` (the condition `d ≤ m₁` is carried by
  `ProperDomainKData.dim_le_m`);
* `properDomainG2Data_example`: the half-space example satisfies (DG2);
* `properDomainGSharp_pd_i`, `properDomainWSharp_pd_ii`, `properDomainWSharp_pd_iii`,
  `properDomainWSharp_pd_iv`: clauses (i)–(iv).

(H8) is obtained from `prop_Z3suff_paper`, whose radial condition is required on the frontier of
`dom G♯` only, exactly as in (DG2).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m₁ m₂ : ℕ}

/-- The hypothesis (DG2) on the second-block integrand `G₂ : 𝕄^{m₂×N} → [0,∞]`: convex, lower
semicontinuous, `G₂ ≥ |·|_F^p`, with effective domain `C₂` open, unbounded, containing `0`,
different from the whole space, and `G₂(tχ) → ∞` as `t → 1⁻` for every `χ ∈ ∂C₂`. The dimension
condition `N ≤ m₁` of (DG2) is not a field of this structure: it is `ProperDomainKData.dim_le_m`. -/
structure ProperDomainG2Data (N m₂ : ℕ) (p : ℝ) where
  G₂ : Mat m₂ N → ℝ≥0∞
  convex : ConvexENN G₂
  lowerSemicontinuous : LowerSemicontinuous G₂
  ge_frobenius : ∀ χ : Mat m₂ N, ENNReal.ofReal (matrixFrobeniusNorm χ ^ p) ≤ G₂ χ
  isOpen_dom : IsOpen (dom G₂)
  not_isBounded_dom : ¬ Bornology.IsBounded (dom G₂)
  zero_mem_dom : (0 : Mat m₂ N) ∈ dom G₂
  dom_ne_univ : dom G₂ ≠ univ
  tendsto_top : ∀ χ ∈ frontier (dom G₂),
    Tendsto (fun t : ℝ => G₂ (t • χ)) (𝓝[<] 1) (𝓝 ⊤)

namespace ProperDomainG2Data

variable {p : ℝ} (G2 : ProperDomainG2Data N m₂ p)

/-- A convex function with open effective domain is upper semicontinuous. -/
theorem upperSemicontinuous : UpperSemicontinuous G2.G₂ :=
  G2.convex.upperSemicontinuous_of_isOpen_dom G2.isOpen_dom

/-- `𝒵_aff G₂ = G₂`, by Jensen's inequality (`eq:ZaffG2`). -/
theorem Zaff_eq : Zaff G2.G₂ = G2.G₂ := G2.convex.Zaff_eq

/-- `G₂(tχ) ≤ G₂(χ) + (1 - t) G₂(0)` for `t ∈ ]0,1[`, by convexity. -/
theorem smul_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (χ : Mat m₂ N) :
    G2.G₂ (t • χ) ≤ G2.G₂ χ + ENNReal.ofReal (1 - t) * G2.G₂ 0 := by
  have hconv := G2.convex χ 0 t.toNNReal (by rw [Real.toNNReal_le_one]; exact ht1.le)
  have e1 : ((t.toNNReal : ℝ) • χ + ((1 - t.toNNReal : ℝ≥0) : ℝ) • (0 : Mat m₂ N)) = t • χ := by
    rw [smul_zero, add_zero, Real.coe_toNNReal _ ht0.le]
  rw [e1] at hconv
  refine hconv.trans (add_le_add ?_ (le_of_eq ?_))
  · calc ((t.toNNReal : ℝ≥0) : ℝ≥0∞) * G2.G₂ χ ≤ 1 * G2.G₂ χ := by
          gcongr; exact_mod_cast Real.toNNReal_le_one.2 ht1.le
      _ = G2.G₂ χ := one_mul _
  · rw [ENNReal.ofReal_sub _ ht0.le, ENNReal.ofReal_one, ENNReal.coe_sub, ENNReal.coe_one]
    rfl

end ProperDomainG2Data

theorem dom_properDomainG2_eq [NeZero N] [NeZero m₂] (p : ℝ) :
    dom (properDomainG2 (m := m₂) (N := N) p) = properDomainHalfSpace :=
  Set.ext fun χ => mem_dom_properDomainG2_iff p χ

/-- The half-space example `G₂(χ) = |χ|_F^p + g₀(χ₁₁)` satisfies (DG2), for every `p > N`. -/
noncomputable def properDomainG2Data_example [NeZero N] [NeZero m₂] (p : ℝ) (hp : (N : ℝ) < p) :
    ProperDomainG2Data N m₂ p where
  G₂ := properDomainG2 p
  convex := properDomainG2_convexENN p hp
  lowerSemicontinuous :=
    properDomainG2_lowerSemicontinuous p (le_trans (Nat.cast_nonneg N) hp.le)
  ge_frobenius := properDomainG2_ge_frobenius_rpow p
  isOpen_dom := by rw [dom_properDomainG2_eq]; exact properDomainHalfSpace_isOpen
  not_isBounded_dom := dom_properDomainG2_not_isBounded p
  zero_mem_dom := by rw [dom_properDomainG2_eq]; exact zero_mem_properDomainHalfSpace
  dom_ne_univ := by rw [dom_properDomainG2_eq]; exact properDomainHalfSpace_ne_univ
  tendsto_top := fun χ hχ => by
    rw [dom_properDomainG2_eq] at hχ
    exact properDomainG2_radial_tendsto_top p hχ

variable {p : ℝ} [NeZero N]

/-! ### Clause (i) -/

theorem properDomainGSharp_convexENN (D : ProperDomainGData N) (G2 : ProperDomainG2Data N m₂ p) :
    ConvexENN (properDomainGSharp (m₁ := m₁) D G2.G₂) := by
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  intro A B t ht
  simp only [properDomainGSharp, separatedSum]
  simp only [map_add, map_smul]
  have h₁ := properDomainG_convexENN (m₁ := m₁) D (e A).1 (e B).1 t ht
  have h₂ := G2.convex (e A).2 (e B).2 t ht
  calc
    _ ≤ (t : ℝ≥0∞) * properDomainG D (e A).1 + (1 - t : ℝ≥0∞) * properDomainG D (e B).1 +
        ((t : ℝ≥0∞) * G2.G₂ (e A).2 + (1 - t : ℝ≥0∞) * G2.G₂ (e B).2) :=
      add_le_add h₁ h₂
    _ = (t : ℝ≥0∞) * (properDomainG D (e A).1 + G2.G₂ (e A).2) +
        (1 - t : ℝ≥0∞) * (properDomainG D (e B).1 + G2.G₂ (e B).2) := by ring

theorem properDomainGSharp_lowerSemicontinuous (D : ProperDomainGData N)
    (G2 : ProperDomainG2Data N m₂ p) :
    LowerSemicontinuous (properDomainGSharp (m₁ := m₁) D G2.G₂) := by
  let e := matBlockSplitLinearEquiv m₁ m₂ N
  have h₁ : LowerSemicontinuous fun z : Mat m₁ N × Mat m₂ N => properDomainG (m := m₁) D z.1 :=
    (properDomainG_lowerSemicontinuous (m₁ := m₁) D).comp continuous_fst
  have h₂ : LowerSemicontinuous fun z : Mat m₁ N × Mat m₂ N => G2.G₂ z.2 :=
    G2.lowerSemicontinuous.comp continuous_snd
  have hsum : LowerSemicontinuous
      (fun z : Mat m₁ N × Mat m₂ N => properDomainG (m := m₁) D z.1 + G2.G₂ z.2) :=
    LowerSemicontinuous.add' h₁ h₂ (by intro z; fun_prop)
  exact hsum.comp e.continuous

/-- **Proposition `prop:properdomain` (i).** `G♯` is convex and lower semicontinuous, and
`dom G♯ = 𝕄^{m₁×N} × C₂` (through the row-splitting equivalence) is open, convex, unbounded,
contains `0`, is a proper subset, and has non-empty frontier `𝕄^{m₁×N} × ∂C₂`. -/
theorem properDomainGSharp_pd_i (D : ProperDomainGData N) (G2 : ProperDomainG2Data N m₂ p) :
    ConvexENN (properDomainGSharp (m₁ := m₁) D G2.G₂) ∧
      LowerSemicontinuous (properDomainGSharp (m₁ := m₁) D G2.G₂) ∧
      dom (properDomainGSharp (m₁ := m₁) D G2.G₂) =
        (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹' (univ ×ˢ dom G2.G₂) ∧
      IsOpen (dom (properDomainGSharp (m₁ := m₁) D G2.G₂)) ∧
      Convex ℝ (dom (properDomainGSharp (m₁ := m₁) D G2.G₂)) ∧
      ¬ Bornology.IsBounded (dom (properDomainGSharp (m₁ := m₁) D G2.G₂)) ∧
      (0 : Mat (m₁ + m₂) N) ∈ dom (properDomainGSharp (m₁ := m₁) D G2.G₂) ∧
      dom (properDomainGSharp (m₁ := m₁) D G2.G₂) ≠ univ ∧
      frontier (dom (properDomainGSharp (m₁ := m₁) D G2.G₂)) =
        (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹' (univ ×ˢ frontier (dom G2.G₂)) ∧
      (frontier (dom (properDomainGSharp (m₁ := m₁) D G2.G₂))).Nonempty := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  have hconv := properDomainGSharp_convexENN (m₁ := m₁) D G2
  have hdom := dom_properDomainGSharp (m₁ := m₁) D G2.G₂
  have hfr : frontier (dom (properDomainGSharp (m₁ := m₁) D G2.G₂)) =
      e ⁻¹' (univ ×ˢ frontier (dom G2.G₂)) := by
    rw [hdom, ← frontier_univ_prod_eq]
    exact (e.toHomeomorph.preimage_frontier _).symm
  have hne : dom (properDomainGSharp (m₁ := m₁) D G2.G₂) ≠ univ := by
    intro h
    apply G2.dom_ne_univ
    refine eq_univ_of_forall fun χ => ?_
    have hA : (matBlockSplitLinearEquiv m₁ m₂ N).symm (0, χ) ∈
        dom (properDomainGSharp (m₁ := m₁) D G2.G₂) := by rw [h]; trivial
    rw [hdom] at hA
    simpa using hA.2
  refine ⟨hconv, properDomainGSharp_lowerSemicontinuous D G2, hdom, ?_, hconv.convex_dom, ?_, ?_,
    hne, hfr, ?_⟩
  · rw [hdom]
    exact (isOpen_univ.prod G2.isOpen_dom).preimage e.continuous
  · intro hb
    apply G2.not_isBounded_dom
    have himg : Bornology.IsBounded (e '' dom (properDomainGSharp (m₁ := m₁) D G2.G₂)) :=
      hb.image e.toContinuousLinearMap
    refine himg.image_snd.subset fun χ hχ =>
      ⟨(0, χ), ⟨(matBlockSplitLinearEquiv m₁ m₂ N).symm (0, χ), ?_, by simp [e]⟩, rfl⟩
    rw [hdom]
    simpa using hχ
  · rw [hdom]
    simpa using G2.zero_mem_dom
  · rw [nonempty_frontier_iff]
    refine ⟨⟨0, ?_⟩, hne⟩
    rw [hdom]
    simpa using G2.zero_mem_dom

/-! ### Clause (ii) -/

/-- **Proposition `prop:properdomain` (ii).** For every `x`, `dom W♯(x,·) = Σ × C₂` (through the
row-splitting equivalence), and this set is not convex. -/
theorem properDomainWSharp_pd_ii (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G2 : ProperDomainG2Data N m₂ p) (x : Sp N) :
    dom (properDomainWSharp D KD HD CD G2.G₂ x) =
        (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹' (properDomainSigma ×ˢ dom G2.G₂) ∧
      ¬ Convex ℝ (dom (properDomainWSharp D KD HD CD G2.G₂ x)) :=
  ⟨dom_properDomainWSharp D KD HD CD G2.G₂ x,
    properDomainWSharp_domain_not_convex D KD HD CD G2.G₂ x
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) G2.zero_mem_dom⟩

/-! ### Clause (iii) -/

omit [NeZero N] in
/-- `𝒵_aff W♯(x,·)(ξ) = 𝒵_aff W_v(x,·)(ξ¹) + G₂(ξ²)` for every `x` (`decouplresult` and
`eq:ZaffG2`). -/
theorem properDomainWSharp_Zaff_eq (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G2 : ProperDomainG2Data N m₂ p) (x : Sp N) (A : Mat (m₁ + m₂) N) :
    Zaff (properDomainWSharp D KD HD CD G2.G₂ x) A =
      Zaff (properDomainWv D KD HD CD x) (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
        G2.G₂ (matBlockSplitLinearEquiv m₁ m₂ N A).2 := by
  have hA := congrFun (Zaff_separatedSum_matBlockSplit (properDomainWv D KD HD CD x) G2.G₂) A
  change Zaff (fun B : Mat (m₁ + m₂) N =>
      separatedSum (properDomainWv D KD HD CD x) G2.G₂ (matBlockSplitLinearEquiv m₁ m₂ N B)) A = _
  rw [hA, G2.Zaff_eq]

/-- `G♯ ≤ 𝒵_aff W♯(x,·)` for every `x`. -/
theorem properDomainWSharp_Zaff_lower (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G2 : ProperDomainG2Data N m₂ p) (x : Sp N) :
    properDomainGSharp (m₁ := m₁) D G2.G₂ ≤ Zaff (properDomainWSharp D KD HD CD G2.G₂ x) := by
  calc
    _ = Zaff (properDomainGSharp (m₁ := m₁) D G2.G₂) :=
      (ConvexENN.Zaff_eq (properDomainGSharp_convexENN D G2)).symm
    _ ≤ Zaff (properDomainWSharp D KD HD CD G2.G₂ x) := Zaff_mono fun A => by
        change separatedSum (properDomainG (m := m₁) D) G2.G₂
            (matBlockSplitLinearEquiv m₁ m₂ N A) ≤
          separatedSum (properDomainWv D KD HD CD x) G2.G₂ (matBlockSplitLinearEquiv m₁ m₂ N A)
        apply add_le_add _ le_rfl
        unfold properDomainWv
        rw [add_assoc]
        exact le_self_add

omit [NeZero N] in
/-- `W♯` as a four-term sum `1·G(ξ¹) + b·K(ξ¹) + a·H(v(ξ¹)) + 1·G₂(ξ²)`. -/
theorem properDomainWSharp_eq_sumW (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G₂ : Mat m₂ N → ℝ≥0∞) :
    properDomainWSharp D KD HD CD G₂ =
      sumW ![fun _ => 1, CD.coeffB, CD.coeffA, fun _ => 1]
        ![fun A => properDomainG D (matBlockSplitLinearEquiv m₁ m₂ N A).1,
          fun A => (KD.K (matBlockSplitLinearEquiv m₁ m₂ N A).1 : ℝ≥0∞),
          fun A => HD.H (properDomainJacobian (matBlockSplitLinearEquiv m₁ m₂ N A).1),
          fun A => G₂ (matBlockSplitLinearEquiv m₁ m₂ N A).2] := by
  funext x ξ
  simp [sumW, Fin.sum_univ_four, properDomainWSharp, separatedSum, properDomainWv, add_assoc]

omit [NeZero N] in
theorem properDomainWSharp_coeff_range (CD : ProperDomainCoeffData N) :
    ∀ (k : Fin 4) (x : Sp N),
      min 1 CD.eta ≤ (![fun _ => 1, CD.coeffB, CD.coeffA, fun _ => 1] : Fin 4 → Sp N → ℝ) k x ∧
        (![fun _ => 1, CD.coeffB, CD.coeffA, fun _ => 1] : Fin 4 → Sp N → ℝ) k x ≤
          max 1 CD.Lambda := by
  intro k x
  fin_cases k
  · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · exact ⟨(min_le_right _ _).trans (CD.b_range x).1, (CD.b_range x).2.trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (CD.a_range x).1, (CD.a_range x).2.trans (le_max_right _ _)⟩
  · exact ⟨min_le_left _ _, le_max_left _ _⟩

omit [NeZero N] in
theorem properDomainWSharp_terms_usc (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (G2 : ProperDomainG2Data N m₂ p) :
    ∀ k : Fin 4, UpperSemicontinuous
      ((![fun A => properDomainG D (matBlockSplitLinearEquiv m₁ m₂ N A).1,
          fun A => (KD.K (matBlockSplitLinearEquiv m₁ m₂ N A).1 : ℝ≥0∞),
          fun A => HD.H (properDomainJacobian (matBlockSplitLinearEquiv m₁ m₂ N A).1),
          fun A => G2.G₂ (matBlockSplitLinearEquiv m₁ m₂ N A).2]) k) := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  have h1 : Continuous fun A : Mat (m₁ + m₂) N => (e A).1 := continuous_fst.comp e.continuous
  have h2 : Continuous fun A : Mat (m₁ + m₂) N => (e A).2 := continuous_snd.comp e.continuous
  intro k
  fin_cases k
  · exact (upperSemicontinuous_properDomainG D).comp h1
  · exact (ENNReal.continuous_coe.comp_upperSemicontinuous KD.upperSemicontinuous
      ENNReal.coe_mono).comp h1
  · exact (HD.upperSemicontinuous.comp continuous_properDomainJacobian).comp h1
  · exact G2.upperSemicontinuous.comp h2

/-- **Proposition `prop:properdomain` (iii).** There is a single null set of `x` outside which
`𝒴_loc W♯(x,·) = 𝒵_aff W♯(x,·) ≤ W♯(x,·)`, `𝒴_loc W♯(x,·)` is upper semicontinuous, and
`𝒴_loc W♯(x,ξ) = 𝒵_aff W_v(x,ξ¹) + G₂(ξ²)`; for every `x`, `G♯ ≤ 𝒵_aff W♯(x,·)`; and for every
`β` as in `sep:iii`, `𝒵_aff W♯(x,·) ≤ β♯(1 + G♯)` with `β♯ = max(β,1)`. -/
theorem properDomainWSharp_pd_iii (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G2 : ProperDomainG2Data N m₂ p) :
    (∀ᵐ x, Ytloc (properDomainWSharp D KD HD CD G2.G₂) x =
          Zaff (properDomainWSharp D KD HD CD G2.G₂ x) ∧
        Zaff (properDomainWSharp D KD HD CD G2.G₂ x) ≤ properDomainWSharp D KD HD CD G2.G₂ x ∧
        UpperSemicontinuous (Ytloc (properDomainWSharp D KD HD CD G2.G₂) x) ∧
        ∀ A : Mat (m₁ + m₂) N, Ytloc (properDomainWSharp D KD HD CD G2.G₂) x A =
          Zaff (properDomainWv D KD HD CD x) (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
            G2.G₂ (matBlockSplitLinearEquiv m₁ m₂ N A).2) ∧
      (∀ x, properDomainGSharp (m₁ := m₁) D G2.G₂ ≤
        Zaff (properDomainWSharp D KD HD CD G2.G₂ x)) ∧
      ∀ β : ℝ≥0, (∀ x (B : Mat m₁ N),
          Zaff (properDomainWv D KD HD CD x) B ≤ (β : ℝ≥0∞) * (1 + properDomainG D B)) →
        ∀ x (A : Mat (m₁ + m₂) N), Zaff (properDomainWSharp D KD HD CD G2.G₂ x) A ≤
          (max β 1 : ℝ≥0∞) * (1 + properDomainGSharp (m₁ := m₁) D G2.G₂ A) := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  refine ⟨?_, properDomainWSharp_Zaff_lower D KD HD CD G2, fun β hβ x A => ?_⟩
  · have h := lem_sumosc (lt_min one_pos CD.eta_pos) (properDomainWSharp_coeff_range CD)
      (fun k => by
        fin_cases k
        · exact lowerSemicontinuous_const
        · exact CD.b_lowerSemicontinuous
        · exact CD.a_lowerSemicontinuous
        · exact lowerSemicontinuous_const)
      (properDomainWSharp_terms_usc D KD HD G2)
    have h' : ∀ᵐ x, Ytloc (properDomainWSharp D KD HD CD G2.G₂) x =
          Zaff (properDomainWSharp D KD HD CD G2.G₂ x) ∧
        Zaff (properDomainWSharp D KD HD CD G2.G₂ x) ≤ properDomainWSharp D KD HD CD G2.G₂ x ∧
        UpperSemicontinuous (Ytloc (properDomainWSharp D KD HD CD G2.G₂) x) := by
      rw [properDomainWSharp_eq_sumW]
      exact h
    filter_upwards [h'] with x hx
    refine ⟨hx.1, hx.2.1, hx.2.2, fun A => ?_⟩
    rw [hx.1]
    exact properDomainWSharp_Zaff_eq D KD HD CD G2 x A
  · rw [properDomainWSharp_Zaff_eq D KD HD CD G2 x A]
    have hb : (β : ℝ≥0∞) ≤ (max β 1 : ℝ≥0∞) := by exact_mod_cast le_max_left β 1
    have h1 : (1 : ℝ≥0∞) ≤ (max β 1 : ℝ≥0∞) := by exact_mod_cast le_max_right β 1
    calc Zaff (properDomainWv D KD HD CD x) (e A).1 + G2.G₂ (e A).2
        ≤ (max β 1 : ℝ≥0∞) * (1 + properDomainG D (e A).1) +
            (max β 1 : ℝ≥0∞) * G2.G₂ (e A).2 := by
          gcongr
          · exact (hβ x _).trans (by gcongr)
          · calc G2.G₂ (e A).2 = 1 * G2.G₂ (e A).2 := (one_mul _).symm
              _ ≤ _ := by gcongr
      _ = (max β 1 : ℝ≥0∞) * (1 + properDomainGSharp (m₁ := m₁) D G2.G₂ A) := by
          simp only [properDomainGSharp, separatedSum]
          ring

/-! ### Clause (iv) -/

omit [NeZero N] in
/-- (H6) for `W♯`: `(x,ξ) ↦ 𝒴_loc W♯(x,ξ)` is jointly Borel measurable. -/
theorem properDomainWSharp_measurable_Ytloc (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G2 : ProperDomainG2Data N m₂ p) :
    Measurable (uncurry (Ytloc (properDomainWSharp D KD HD CD G2.G₂))) := by
  rw [properDomainWSharp_eq_sumW]
  refine measurable_Ytloc_sumW (lt_min one_pos CD.eta_pos) (Λ := max 1 CD.Lambda)
    (properDomainWSharp_coeff_range CD) (fun k => ?_) (properDomainWSharp_terms_usc D KD HD G2)
  fin_cases k
  · exact measurable_const
  · exact CD.b_measurable
  · exact CD.a_measurable
  · exact measurable_const

/-- (H3) for `W♯`, with `α = 1`. -/
theorem properDomainWSharp_setGrowth (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G2 : ProperDomainG2Data N m₂ p) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ ξ (U : Set (Sp N)), IsOpen U → Bornology.IsBounded U →
      ((1 : ℝ≥0) : ℝ≥0∞) * volume U * properDomainGSharp (m₁ := m₁) D G2.G₂ ξ ≤
          Yt (properDomainWSharp D KD HD CD G2.G₂) U ξ ∧
        Yt (properDomainWSharp D KD HD CD G2.G₂) U ξ ≤
          (β : ℝ≥0∞) * volume U * (1 + properDomainGSharp (m₁ := m₁) D G2.G₂ ξ) := by
  obtain ⟨β, hβ⟩ := properDomainWPlus_Zaff_le_growth D KD HD CD
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  set Wp : Mat (m₁ + m₂) N → ℝ≥0∞ := fun B =>
    separatedSum (properDomainWPlus D KD HD CD) G2.G₂ (e B)
  have hWp : ∀ A, Zaff Wp A ≤
      ((β + 1 : ℝ≥0) : ℝ≥0∞) * (1 + properDomainGSharp (m₁ := m₁) D G2.G₂ A) := fun A => by
    rw [congrFun (Zaff_separatedSum_matBlockSplit _ G2.G₂) A, G2.Zaff_eq]
    change _ ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) * (1 + (properDomainG D (e A).1 + G2.G₂ (e A).2))
    have h1 : (1 : ℝ≥0∞) ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_add_self
    calc Zaff (properDomainWPlus D KD HD CD) (e A).1 + G2.G₂ (e A).2
        ≤ ((β + 1 : ℝ≥0) : ℝ≥0∞) * (1 + properDomainG D (e A).1) +
            ((β + 1 : ℝ≥0) : ℝ≥0∞) * G2.G₂ (e A).2 := by
          gcongr
          · exact (hβ _).trans (by gcongr; exact_mod_cast le_self_add)
          · calc G2.G₂ (e A).2 = 1 * G2.G₂ (e A).2 := (one_mul _).symm
              _ ≤ _ := by gcongr
      _ = _ := by ring
  refine ⟨β + 1, by positivity, fun ξ U hUo hUb => ⟨?_, ?_⟩⟩
  · rw [ENNReal.coe_one, one_mul]
    refine ((properDomainGSharp_convexENN (m₁ := m₁) D G2).volume_mul_le_Yt_of_isOpen
      hUo hUb ξ).trans (Yt_mono (fun y ζ => ?_) U ξ)
    change properDomainG D (e ζ).1 + G2.G₂ (e ζ).2 ≤
      properDomainWv D KD HD CD y (e ζ).1 + G2.G₂ (e ζ).2
    gcongr
    change properDomainG D (e ζ).1 ≤ properDomainG D (e ζ).1 + _ + _
    rw [add_assoc]
    exact le_self_add
  · by_cases hU0 : volume U = 0
    · refine (iInf₂_le (0 : Sp N → Tgt (m₁ + m₂)) (zero_mem_Aff0 hUo)).trans ?_
      rw [Measure.restrict_eq_zero.2 hU0, lintegral_zero_measure]
      exact zero_le
    calc Yt (properDomainWSharp D KD HD CD G2.G₂) U ξ
        ≤ Yt (fun _ => Wp) U ξ :=
          Yt_mono (fun y B => add_le_add (properDomainWv_le_WPlus D KD HD CD y _) le_rfl) U ξ
      _ ≤ volume U * Zaff Wp ξ := Yt_le_volume_mul_Zaff _ hUo hUb hU0 ξ
      _ ≤ volume U * (((β + 1 : ℝ≥0) : ℝ≥0∞) *
            (1 + properDomainGSharp (m₁ := m₁) D G2.G₂ ξ)) := by gcongr; exact hWp ξ
      _ = ((β + 1 : ℝ≥0) : ℝ≥0∞) * volume U *
            (1 + properDomainGSharp (m₁ := m₁) D G2.G₂ ξ) := by ring

/-- (H5) for `W♯` itself: uniform ru-usc relative to `0`. -/
theorem properDomainWSharp_ruuscWith (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G2 : ProperDomainG2Data N m₂ p) :
    RUUSCWith (((properDomainG D (0 : Mat m₁ N)).toNNReal + 1) + ((G2.G₂ 0).toNNReal + 1))
      (properDomainWSharp D KD HD CD G2.G₂) := by
  intro η hη
  have hη' : (0 : ℝ) < η := hη
  have h2 : ∀ᶠ t in 𝓝 (1 : ℝ), 1 - (η : ℝ) < t ∧ 0 < t :=
    (lt_mem_nhds (by linarith)).and (lt_mem_nhds one_pos)
  filter_upwards [properDomainWv_ruuscWith D KD HD CD η hη, nhdsWithin_le_nhds h2,
    self_mem_nhdsWithin] with t hWv ⟨ht1, ht0⟩ (htlt : t < 1) x A hfin
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  set c₁ : ℝ≥0 := (properDomainG D (0 : Mat m₁ N)).toNNReal + 1
  set c₂ : ℝ≥0 := (G2.G₂ 0).toNNReal + 1
  set W1 := properDomainWv D KD HD CD x (e A).1
  set W2 := G2.G₂ (e A).2
  have hfin' : W1 + W2 < ⊤ := hfin
  have hW1 : W1 < ⊤ := (ENNReal.add_lt_top.1 hfin').1
  have hG2 : G2.G₂ (t • (e A).2) ≤ W2 + η * c₂ := by
    refine (G2.smul_le ht0 htlt _).trans (add_le_add le_rfl ?_)
    have h1t : ENNReal.ofReal (1 - t) ≤ η := by
      calc ENNReal.ofReal (1 - t) ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)
        _ = η := ENNReal.ofReal_coe_nnreal
    have hG0 : G2.G₂ 0 ≤ c₂ := by
      have h : ((G2.G₂ 0).toNNReal : ℝ≥0∞) = G2.G₂ 0 :=
        ENNReal.coe_toNNReal G2.zero_mem_dom.ne
      calc G2.G₂ 0 = _ := h.symm
        _ ≤ c₂ := by exact_mod_cast le_self_add
    exact mul_le_mul' h1t hG0
  have hsplit : properDomainWSharp D KD HD CD G2.G₂ x (t • A) =
      properDomainWv D KD HD CD x (t • (e A).1) + G2.G₂ (t • (e A).2) := by
    change properDomainWv D KD HD CD x (e (t • A)).1 + G2.G₂ (e (t • A)).2 = _
    rw [map_smul]
    rfl
  rw [hsplit]
  change _ ≤ (W1 + W2) + (η : ℝ≥0∞) * (((c₁ + c₂ : ℝ≥0) : ℝ≥0∞) + (W1 + W2))
  calc properDomainWv D KD HD CD x (t • (e A).1) + G2.G₂ (t • (e A).2)
      ≤ (W1 + η * (c₁ + W1)) + (W2 + η * c₂) := add_le_add (hWv x _ hW1) hG2
    _ ≤ (W1 + W2) + (η : ℝ≥0∞) * (((c₁ + c₂ : ℝ≥0) : ℝ≥0∞) + (W1 + W2)) := by
        push_cast
        calc (W1 + η * (c₁ + W1)) + (W2 + η * c₂)
            = (W1 + W2) + (η : ℝ≥0∞) * ((c₁ + c₂) + W1) := by ring
          _ ≤ _ := by gcongr; exact le_self_add

omit [NeZero N] in
/-- (H4) for `G♯`: `c₀ ‖A‖^p ≤ G♯(A)`, from `G ≥ |ξ¹|_F^p` and `G₂ ≥ |ξ²|_F^p`. -/
theorem exists_coercive_properDomainGSharp (D : ProperDomainGData N)
    (G2 : ProperDomainG2Data N m₂ D.p) :
    ∃ c₀ : ℝ≥0, 0 < c₀ ∧ ∀ A : Mat (m₁ + m₂) N,
      ENNReal.ofReal (c₀ * ‖A‖ ^ D.p) ≤ properDomainGSharp (m₁ := m₁) D G2.G₂ A := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_frobenius (m := m₁) (N := N)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_le_frobenius (m := m₂) (N := N)
  set E : ℝ := ‖(e.symm : (Mat m₁ N × Mat m₂ N) →L[ℝ] Mat (m₁ + m₂) N)‖
  set K : ℝ := E * max C₁ C₂ + 1
  have hE : 0 ≤ E := by positivity
  have hK : 0 < K := by positivity
  have hp : 0 ≤ D.p := le_trans (Nat.cast_nonneg N) D.dim_lt_p.le
  have hKp : 0 < K ^ D.p := Real.rpow_pos_of_pos hK _
  refine ⟨((K ^ D.p)⁻¹).toNNReal, Real.toNNReal_pos.2 (inv_pos.2 hKp), fun A => ?_⟩
  set f₁ := matrixFrobeniusNorm (e A).1
  set f₂ := matrixFrobeniusNorm (e A).2
  have hf₁ : 0 ≤ f₁ := by unfold f₁ matrixFrobeniusNorm; positivity
  have hf₂ : 0 ≤ f₂ := by unfold f₂ matrixFrobeniusNorm; positivity
  set M := max f₁ f₂
  have hM : 0 ≤ M := le_max_of_le_left hf₁
  have hnorm : ‖A‖ ≤ K * M := by
    have h1 : ‖e A‖ ≤ max C₁ C₂ * M := by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · calc ‖(e A).1‖ ≤ C₁ * f₁ := h₁ _
          _ ≤ max C₁ C₂ * M := mul_le_mul (le_max_left _ _) (le_max_left _ _) hf₁
              (hC₁.le.trans (le_max_left _ _))
      · calc ‖(e A).2‖ ≤ C₂ * f₂ := h₂ _
          _ ≤ max C₁ C₂ * M := mul_le_mul (le_max_right _ _) (le_max_right _ _) hf₂
              (hC₁.le.trans (le_max_left _ _))
    calc ‖A‖ = ‖(e.symm : (Mat m₁ N × Mat m₂ N) →L[ℝ] Mat (m₁ + m₂) N) (e A)‖ := by simp
      _ ≤ E * ‖e A‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ E * (max C₁ C₂ * M) := by gcongr
      _ ≤ K * M := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) hM
  have hMp : M ^ D.p ≤ f₁ ^ D.p + f₂ ^ D.p := by
    rcases max_cases f₁ f₂ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [show M = f₁ from h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hf₂ _)
    · rw [show M = f₂ from h]; exact le_add_of_nonneg_left (Real.rpow_nonneg hf₁ _)
  have hreal : ((K ^ D.p)⁻¹).toNNReal * ‖A‖ ^ D.p ≤ f₁ ^ D.p + f₂ ^ D.p := by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hKp.le)]
    calc (K ^ D.p)⁻¹ * ‖A‖ ^ D.p ≤ (K ^ D.p)⁻¹ * (K * M) ^ D.p := by
          gcongr
      _ = M ^ D.p := by
          rw [Real.mul_rpow hK.le hM, ← mul_assoc, inv_mul_cancel₀ hKp.ne', one_mul]
      _ ≤ _ := hMp
  calc ENNReal.ofReal (((K ^ D.p)⁻¹).toNNReal * ‖A‖ ^ D.p)
      ≤ ENNReal.ofReal (f₁ ^ D.p + f₂ ^ D.p) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (f₁ ^ D.p) + ENNReal.ofReal (f₂ ^ D.p) :=
        ENNReal.ofReal_add (Real.rpow_nonneg hf₁ _) (Real.rpow_nonneg hf₂ _)
    _ ≤ properDomainG D (e A).1 + G2.G₂ (e A).2 :=
        add_le_add le_self_add (G2.ge_frobenius _)

/-- Radial blow-up of `G♯` on the frontier of its domain: for `ξ ∈ ∂(dom G♯)`, `ξ² ∈ ∂C₂` and
`G♯(tξ) ≥ G₂(tξ²) → ∞` as `t → 1⁻`. -/
theorem properDomainGSharp_tendsto_top (D : ProperDomainGData N)
    (G2 : ProperDomainG2Data N m₂ p) {ξ : Mat (m₁ + m₂) N}
    (hξ : ξ ∈ frontier (dom (properDomainGSharp (m₁ := m₁) D G2.G₂))) :
    Tendsto (fun t : ℝ => properDomainGSharp (m₁ := m₁) D G2.G₂ (t • ξ)) (𝓝[<] 1) (𝓝 ⊤) := by
  set e := matBlockSplitLinearEquiv m₁ m₂ N
  rw [(properDomainGSharp_pd_i (m₁ := m₁) D G2).2.2.2.2.2.2.2.2.1] at hξ
  refine tendsto_nhds_top_mono (G2.tendsto_top _ hξ.2) (Eventually.of_forall fun t => ?_)
  change G2.G₂ (t • (e ξ).2) ≤ properDomainG D (e (t • ξ)).1 + G2.G₂ (e (t • ξ)).2
  rw [map_smul]
  exact le_add_self

/-- **Proposition `prop:properdomain` (iv), hypotheses (H1)–(H8).** `W♯` satisfies the standing
hypotheses of the main theorem with `G♯` and `α = 1`, for every `G₂` satisfying (DG2); (H8)
through `prop_Z3suff_paper`, with the radial condition on `∂(dom G♯)` given by (DG2). -/
theorem properDomainWSharp_hypotheses (D : ProperDomainGData N)
    [Fact (1 ≤ ENNReal.ofReal D.p)] (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (G2 : ProperDomainG2Data N m₂ D.p) :
    Hypotheses D.p (properDomainGSharp (m₁ := m₁) D G2.G₂)
      (properDomainWSharp D KD HD CD G2.G₂) := by
  obtain ⟨hG, hGlsc, -, hGo, -, -, h0, -, -, -⟩ := properDomainGSharp_pd_i (m₁ := m₁) D G2
  have hper : IsPeriodic (properDomainWSharp D KD HD CD G2.G₂) := fun z x ξ => by
    simp only [properDomainWSharp, separatedSum, properDomainWv, CD.a_periodic, CD.b_periodic]
  obtain ⟨β, hβ, hset⟩ := properDomainWSharp_setGrowth D KD HD CD G2
  have hgr := HasGGrowth.Ytloc hset
  have hYm := properDomainWSharp_measurable_Ytloc D KD HD CD G2
  have hloc := (properDomainWSharp_pd_iii D KD HD CD G2).1
  obtain ⟨c₀, hc₀, hcoerG⟩ := exists_coercive_properDomainGSharp (m₁ := m₁) D G2
  refine
    { measurable_G := hGlsc.measurable
      measurable_W := ?_
      convex := hG
      lsc := hGlsc
      zero_mem_interior := by rw [hGo.interior_eq]; exact h0
      periodic := hper
      setGrowth := ⟨1, β, one_pos, hβ, hset⟩
      coercive := ⟨c₀, hc₀, fun x ξ => (hcoerG ξ).trans (by simpa using (hgr x ξ).1)⟩
      ruusc := ⟨_, by positivity, (properDomainWSharp_ruuscWith D KD HD CD G2).Ytloc⟩
      measurable_Ytloc := hYm
      Ytloc_le := ?_
      Zaff_Haff_le := fun ξ => prop_Z3suff_paper (p := D.p) hG hGlsc hGo
        (fun ξ hξ => properDomainGSharp_tendsto_top D G2 hξ) one_pos hset hYm
        (hloc.mono fun x hx => hx.2.2.1) ξ }
  · set e := matBlockSplitLinearEquiv m₁ m₂ N
    have hK : Measurable fun A : Mat m₁ N => (KD.K A : ℝ≥0∞) :=
      KD.upperSemicontinuous.measurable.coe_nnreal_ennreal
    have hH : Measurable fun A : Mat m₁ N => HD.H (properDomainJacobian A) :=
      HD.upperSemicontinuous.measurable.comp continuous_properDomainJacobian.measurable
    have h1 : Measurable fun p : Sp N × Mat (m₁ + m₂) N => (e p.2).1 :=
      measurable_fst.comp (e.continuous.measurable.comp measurable_snd)
    have h2 : Measurable fun p : Sp N × Mat (m₁ + m₂) N => (e p.2).2 :=
      measurable_snd.comp (e.continuous.measurable.comp measurable_snd)
    change Measurable fun p : Sp N × Mat (m₁ + m₂) N => (properDomainG D (e p.2).1 +
      ENNReal.ofReal (CD.coeffB p.1) * (KD.K (e p.2).1 : ℝ≥0∞) +
        ENNReal.ofReal (CD.coeffA p.1) * HD.H (properDomainJacobian (e p.2).1)) +
      G2.G₂ (e p.2).2
    exact ((((measurable_properDomainG D).comp h1).add
      ((CD.b_measurable.comp measurable_fst).ennreal_ofReal.mul (hK.comp h1))).add
      ((CD.a_measurable.comp measurable_fst).ennreal_ofReal.mul (hH.comp h1))).add
        (G2.lowerSemicontinuous.measurable.comp h2)
  · filter_upwards [hloc] with x hx ξ
    rw [hx.1]
    exact hx.2.1 ξ

/-- **Proposition `prop:properdomain` (iv).** For every `G₂` satisfying (DG2), `W♯` satisfies
(H1)–(H8), and, without cited hypothesis (`main_Ggrowth_final_unconditional`),
`∫_Ω W♯(x/ε, ∇u)` Γ(Lᵖ)-converges to `∫_Ω \widehat{ℋ(𝒵_aff W♯)}(∇u)`. -/
theorem properDomainWSharp_pd_iv (D : ProperDomainGData N)
    [Fact (1 ≤ ENNReal.ofReal D.p)] (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (G2 : ProperDomainG2Data N m₂ D.p)
    {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) :
    Hypotheses D.p (properDomainGSharp (m₁ := m₁) D G2.G₂) (properDomainWSharp D KD HD CD G2.G₂) ∧
      Whom D.p (properDomainWSharp D KD HD CD G2.G₂) =
        radial (Hp (ENNReal.ofReal D.p)
          (fun x ξ => Zaff (properDomainWSharp D KD HD CD G2.G₂ x) ξ)) ∧
      GammaConverges (X := W1p N (m₁ + m₂) (ENNReal.ofReal D.p) Ω)
        (intFun (properDomainWSharp D KD HD CD G2.G₂))
        (intHom (Whom D.p (properDomainWSharp D KD HD CD G2.G₂))) := by
  have hW := properDomainWSharp_hypotheses D KD HD CD G2
  refine ⟨hW, ?_, main_Ggrowth_final_unconditional D.p D.dim_lt_p hΩ hW⟩
  simp only [Whom]
  rw [Hp_congr_ae ((properDomainWSharp_pd_iii D KD HD CD G2).1.mono fun x hx ξ => by rw [hx.1])]

end Homogenization
