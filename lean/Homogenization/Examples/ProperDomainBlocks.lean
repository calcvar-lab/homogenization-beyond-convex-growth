import Homogenization.Examples.ProperDomainProduct

/-!
# Row-block decomposition of matrix spaces

The target dimension is split as `m₁ + m₂` exactly as in subsection `properdomain` of the paper.
-/

open Set
open scoped ENNReal

namespace Homogenization

/-- Split a target vector into its first `m₁` and last `m₂` coordinates. -/
def targetBlockSplitLinearEquiv (m₁ m₂ : ℕ) :
    Tgt (m₁ + m₂) ≃ₗ[ℝ] (Tgt m₁ × Tgt m₂) where
  toFun v :=
    (fun i => v (Fin.castAdd m₂ i), fun j => v (Fin.natAdd m₁ j))
  invFun v := Fin.addCases v.1 v.2
  left_inv v := by
    funext i
    change Fin.addCases (fun j => v (Fin.castAdd m₂ j))
      (fun j => v (Fin.natAdd m₁ j)) i = v i
    obtain ⟨s, hs⟩ := (finSumFinEquiv (m := m₁) (n := m₂)).surjective i
    cases s with
    | inl j => rw [← hs, finSumFinEquiv_apply_left]; simp
    | inr j => rw [← hs, finSumFinEquiv_apply_right]; simp
  right_inv v := by
    cases v with
    | mk v₁ v₂ =>
      apply Prod.ext <;> funext i <;> simp [Fin.addCases]
  map_add' v w := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' c v := by
    apply Prod.ext <;> funext i <;> rfl

/-- Continuous version of `targetBlockSplitLinearEquiv`. -/
noncomputable def targetBlockSplitEquiv (m₁ m₂ : ℕ) :
    Tgt (m₁ + m₂) ≃L[ℝ] (Tgt m₁ × Tgt m₂) :=
  (targetBlockSplitLinearEquiv m₁ m₂).toContinuousLinearEquiv

@[simp]
theorem targetBlockSplitEquiv_apply_left (m₁ m₂ : ℕ)
    (v : Tgt (m₁ + m₂)) (i : Fin m₁) :
    (targetBlockSplitEquiv m₁ m₂ v).1 i = v (Fin.castAdd m₂ i) := rfl

@[simp]
theorem targetBlockSplitEquiv_apply_right (m₁ m₂ : ℕ)
    (v : Tgt (m₁ + m₂)) (i : Fin m₂) :
    (targetBlockSplitEquiv m₁ m₂ v).2 i = v (Fin.natAdd m₁ i) := rfl

@[simp]
theorem targetBlockSplitEquiv_symm_apply (m₁ m₂ : ℕ)
    (v : Tgt m₁ × Tgt m₂) (i : Fin (m₁ + m₂)) :
    (targetBlockSplitEquiv m₁ m₂).symm v i = Fin.addCases v.1 v.2 i := rfl

/-- Combine two continuous linear maps by pairing their outputs. -/
def continuousLinearMapProdLinearEquiv (E F G : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ((E →L[ℝ] F) × (E →L[ℝ] G)) ≃ₗ[ℝ] (E →L[ℝ] F × G) where
  toFun fg := fg.1.prod fg.2
  invFun h :=
    ((ContinuousLinearMap.fst ℝ F G).comp h, (ContinuousLinearMap.snd ℝ F G).comp h)
  left_inv fg := by
    apply Prod.ext <;> ext x <;> rfl
  right_inv h := by
    ext x <;> simp
  map_add' fg gh := by
    ext x <;> simp
  map_smul' c fg := by
    ext x <;> simp

/-- Identify a matrix with the pair consisting of its first `m₁` and last `m₂` rows. -/
noncomputable def matBlockSplitLinearEquiv (m₁ m₂ N : ℕ) :
    Mat (m₁ + m₂) N ≃L[ℝ] (Mat m₁ N × Mat m₂ N) := by
  let outputEquiv := targetBlockSplitEquiv m₁ m₂
  let mapEquiv := continuousLinearMapProdLinearEquiv (Sp N) (Tgt m₁) (Tgt m₂)
  exact (ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ (Sp N)) outputEquiv).trans
    mapEquiv.toContinuousLinearEquiv.symm

@[simp]
theorem matBlockSplitLinearEquiv_apply_left (m₁ m₂ N : ℕ)
    (A : Mat (m₁ + m₂) N) (x : Sp N) :
    (matBlockSplitLinearEquiv m₁ m₂ N A).1 x =
      fun i => A x (Fin.castAdd m₂ i) := by
  rfl

@[simp]
theorem matBlockSplitLinearEquiv_apply_right (m₁ m₂ N : ℕ)
    (A : Mat (m₁ + m₂) N) (x : Sp N) :
    (matBlockSplitLinearEquiv m₁ m₂ N A).2 x =
      fun i => A x (Fin.natAdd m₁ i) := by
  rfl

@[simp]
theorem matBlockSplitLinearEquiv_symm_apply (m₁ m₂ N : ℕ)
    (A : Mat m₁ N × Mat m₂ N) (x : Sp N) :
    (matBlockSplitLinearEquiv m₁ m₂ N).symm A x = Fin.addCases (A.1 x) (A.2 x) := by
  rfl

/-- For matrix-valued integrands, `dom` is exactly the generic finite-valued domain. -/
theorem dom_eq_effectiveDomain (m N : ℕ) (f : Mat m N → ℝ≥0∞) :
    dom f = effectiveDomain f := rfl

/-- Pulling back an extended nonnegative integrand along any map pulls its effective domain back
by the same map. The legacy name keeps existing uses source-compatible; no equivalence is needed. -/
theorem effectiveDomain_comp_equiv {α β : Type*} (e : α → β) (f : β → ℝ≥0∞) :
    effectiveDomain (fun x => f (e x)) = e ⁻¹' effectiveDomain f := by
  rfl

/-- The domain of a separated sum pulled back to a matrix space is the inverse image of the
product of the block domains under the row splitting equivalence. -/
theorem dom_matBlockSeparatedSum (m₁ m₂ N : ℕ)
    (F : Mat m₁ N → ℝ≥0∞) (G : Mat m₂ N → ℝ≥0∞) :
    dom (fun A : Mat (m₁ + m₂) N =>
      separatedSum F G (matBlockSplitLinearEquiv m₁ m₂ N A)) =
        (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹' (dom F ×ˢ dom G) := by
  let e : Mat (m₁ + m₂) N ≃ (Mat m₁ N × Mat m₂ N) :=
    matBlockSplitLinearEquiv m₁ m₂ N
  calc
    dom (fun A : Mat (m₁ + m₂) N => separatedSum F G (e A)) =
        effectiveDomain (fun A : Mat (m₁ + m₂) N => separatedSum F G (e A)) :=
      dom_eq_effectiveDomain (m₁ + m₂) N _
    _ = e ⁻¹' effectiveDomain (separatedSum F G) :=
      effectiveDomain_comp_equiv e (separatedSum F G)
    _ = e ⁻¹' (effectiveDomain F ×ˢ effectiveDomain G) := by
      rw [dom_separatedSum]
    _ = e ⁻¹' (dom F ×ˢ dom G) := by
      rw [← dom_eq_effectiveDomain m₁ N F, ← dom_eq_effectiveDomain m₂ N G]

end Homogenization
