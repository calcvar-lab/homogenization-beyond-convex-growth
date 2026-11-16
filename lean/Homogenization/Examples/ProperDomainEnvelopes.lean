import Homogenization.Examples.ProperDomainNonconvex
import Homogenization.Examples.ProperDomainDecoupling
import Homogenization.Jensen

/-!
# Affine-envelope consequences for clause (iii) of `prop:properdomain`

This file records consequences of the already proved convexity of the concrete `G₂` and `G♯`.
The generic affine-envelope decoupling lemma (`decouplresult`, no measurability assumption)
applies to `W♯`. The upper bound uses `sep:iii` (`ProperDomainSharpUpper.lean`), and the
local-to-cell identity is `ProperDomainSharpLoc.lean`.
-/

open Set
open scoped ENNReal NNReal

namespace Homogenization

variable {N m₁ m₂ : ℕ} [NeZero N] [NeZero m₁] [NeZero m₂]

/-- The concrete convex integrand `G₂` is fixed by its affine envelope, as required in the proof
of clause (iii). This uses only the article assumption `N < p` already stored in `D`. -/
theorem properDomainG2_Zaff_eq (D : ProperDomainGData N) :
    Zaff (properDomainG2 (m := m₂) (N := N) D.p) =
      properDomainG2 (m := m₂) (N := N) D.p := by
  exact ConvexENN.Zaff_eq
    (properDomainG2_convexENN (m := m₂) (N := N) D.p D.dim_lt_p)

omit [NeZero m₁] in
/-- The lower half of `sep:iii`, for the concrete data: `W_v ≥ G` and convexity of `G` imply
`G = Zaff G ≤ Zaff W_v` by monotonicity of the affine envelope. -/
theorem properDomainWv_Zaff_lower (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (x : Sp N) :
    properDomainG D ≤ Zaff (properDomainWv D KD HD CD x) := by
  calc
    properDomainG D = Zaff (properDomainG D) := by
      symm
      exact ConvexENN.Zaff_eq (properDomainG_convexENN D)
    _ ≤ Zaff (properDomainWv D KD HD CD x) := Zaff_mono fun A => by
      unfold properDomainWv
      calc
        _ ≤ properDomainG D A +
            ENNReal.ofReal (CD.coeffB x) * (KD.K A : ℝ≥0∞) :=
          le_add_of_nonneg_right (by positivity)
        _ ≤ _ := le_add_of_nonneg_right (by positivity)

omit [NeZero N] [NeZero m₁] in
/-- Monotonicity transfers the pointwise majorant `W_v ≤ W⁺` to their affine envelopes. This is
the reduction used in the upper half of `sep:iii`; it does not estimate `Zaff W⁺`. -/
theorem properDomainWv_Zaff_le_WPlus (D : ProperDomainGData N)
    (KD : ProperDomainKData N m₁ D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (x : Sp N) :
    Zaff (properDomainWv D KD HD CD x) ≤ Zaff (properDomainWPlus D KD HD CD) :=
  Zaff_mono (properDomainWv_le_WPlus D KD HD CD x)

omit [NeZero N] [NeZero m₁] in
/-- On `{B | v(B) ≥ γ}`, the preparatory comparison gives
`Zaff W_v ≤ Zaff W⁺ ≤ W⁺ ≤ δ̃ (1 + G)`. This does not prove the global bound in `sep:iii`:
the low-Jacobian region still requires the article's `lem:BB` and `lemmaree` arguments. -/
theorem properDomainWv_Zaff_le_growth_of_jacobian_ge
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) (x : Sp N)
    (B : Mat m₁ N) (hB : HD.gamma ≤ (properDomainJacobian B : ℝ)) :
    Zaff (properDomainWv D KD HD CD x) B ≤
      ENNReal.ofReal (1 + CD.Lambda * KD.C_K + CD.Lambda * HD.delta) *
        (1 + properDomainG D B) := by
  calc
    Zaff (properDomainWv D KD HD CD x) B ≤
        Zaff (properDomainWPlus D KD HD CD) B :=
      properDomainWv_Zaff_le_WPlus D KD HD CD x B
    _ ≤ properDomainWPlus D KD HD CD B := Zaff_le _ _
    _ ≤ _ := properDomainWPlus_le_growth_of_jacobian_ge D KD HD CD B hB

omit [NeZero m₁] in
/-- For the concrete example, the affine envelope of `W♯` is bounded below by `G♯`. This is the
lower estimate in clause (iii); it needs no measurability or oscillation assumptions. -/
theorem properDomainWSharpExample_Zaff_lower
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) (x : Sp N) :
    properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D ≤
      Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) := by
  calc
    _ = Zaff (properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D) :=
      (ConvexENN.Zaff_eq
        (properDomainGSharpExample_convexENN (m₁ := m₁) (m₂ := m₂) D)).symm
    _ ≤ Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) :=
      Zaff_mono fun A => by
        change separatedSum (properDomainG (m := m₁) D) (properDomainG2 D.p)
            (matBlockSplitLinearEquiv m₁ m₂ N A) ≤
          separatedSum (properDomainWv D KD HD CD x) (properDomainG2 D.p)
            (matBlockSplitLinearEquiv m₁ m₂ N A)
        apply add_le_add
        · unfold properDomainWv
          calc
            properDomainG D ((matBlockSplitLinearEquiv m₁ m₂ N A).1) ≤
                properDomainG D ((matBlockSplitLinearEquiv m₁ m₂ N A).1) +
                  ENNReal.ofReal (CD.coeffB x) *
                    (KD.K ((matBlockSplitLinearEquiv m₁ m₂ N A).1) : ℝ≥0∞) :=
              le_add_of_nonneg_right (by positivity)
            _ ≤ _ := le_add_of_nonneg_right (by positivity)
        · exact le_rfl

omit [NeZero m₁] in
/-- Specialization of `decouplresult` to `W♯`; convexity of `G₂` then replaces its affine
envelope by `G₂` itself. -/
theorem properDomainWSharpExample_Zaff_eq
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) (x : Sp N) :
    ∀ A : Mat (m₁ + m₂) N,
      Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) A =
        Zaff (properDomainWv D KD HD CD x) (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
          properDomainG2 (m := m₂) D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2 := by
  have hsplit := Zaff_separatedSum_matBlockSplit
    (F := properDomainWv D KD HD CD x) (G := properDomainG2 (m := m₂) D.p)
  intro A
  have hA := congrFun hsplit A
  change Zaff (fun B : Mat (m₁ + m₂) N =>
      separatedSum (properDomainWv D KD HD CD x) (properDomainG2 (m := m₂) D.p)
        (matBlockSplitLinearEquiv m₁ m₂ N B)) A = _
  rw [hA, properDomainG2_Zaff_eq (m₂ := m₂) D]

omit [NeZero m₁] in
/-- The upper estimate in clause (iii), conditional on the remaining upper bound (sep:iii) for
`W_v`. The affine-envelope decoupling is obtained from `decouplresult`. The value
`β♯=max(β,1)` is exactly the article's constant. -/
theorem properDomainWSharpExample_Zaff_upper_of_Wv_bound
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N) (x : Sp N)
    (β : ℝ≥0)
    (hWv : ∀ B : Mat m₁ N,
      Zaff (properDomainWv D KD HD CD x) B ≤
        (β : ℝ≥0∞) * (1 + properDomainG D B)) :
    ∀ A : Mat (m₁ + m₂) N,
      Zaff (properDomainWSharpExample (m₁ := m₁) (m₂ := m₂) D KD HD CD x) A ≤
        (max β 1 : ℝ≥0∞) *
          (1 + properDomainGSharpExample (m₁ := m₁) (m₂ := m₂) D A) := by
  intro A
  rw [properDomainWSharpExample_Zaff_eq
    (m₁ := m₁) (m₂ := m₂) D KD HD CD x A]
  let betaSharp : ℝ≥0 := max β 1
  have hβ : (β : ℝ≥0∞) ≤ (betaSharp : ℝ≥0∞) := by
    exact_mod_cast (le_max_left β 1)
  have h1 : (1 : ℝ≥0∞) ≤ (betaSharp : ℝ≥0∞) := by
    exact_mod_cast (le_max_right β 1)
  have hG2 : (properDomainG2 D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2) ≤
      (betaSharp : ℝ≥0∞) * properDomainG2 D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2 := by
    calc
      _ = 1 * properDomainG2 D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
  calc
    _ ≤ (betaSharp : ℝ≥0∞) *
          (1 + properDomainG D (matBlockSplitLinearEquiv m₁ m₂ N A).1) +
        (betaSharp : ℝ≥0∞) * properDomainG2 D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2 :=
      add_le_add (le_trans (hWv _) (by gcongr)) hG2
    _ = (betaSharp : ℝ≥0∞) *
          (1 + properDomainG D (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
            properDomainG2 D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2) := by
      calc
        _ = (betaSharp : ℝ≥0∞) * 1 +
              ((betaSharp : ℝ≥0∞) * properDomainG D
                (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
                (betaSharp : ℝ≥0∞) * properDomainG2 D.p
                  (matBlockSplitLinearEquiv m₁ m₂ N A).2) := by
          rw [mul_add]
          simp [add_assoc]
        _ = (betaSharp : ℝ≥0∞) *
              (1 + properDomainG D (matBlockSplitLinearEquiv m₁ m₂ N A).1 +
                properDomainG2 D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2) := by
          rw [mul_add, mul_add]
          simp [add_assoc]
    _ = _ := by
      simp [properDomainGSharpExample, properDomainGSharp, separatedSum, betaSharp,
        mul_add, add_assoc]

end Homogenization
