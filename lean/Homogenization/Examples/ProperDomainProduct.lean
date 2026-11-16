import Homogenization.Basic

/-!
# Effective domains of separated sums

This is the first product-domain step in the proof of `prop:properdomain`: for nonnegative
extended-real integrands depending on separate variables, the effective domain of their sum is
the Cartesian product of their effective domains. The theorem is stated for arbitrary types so it
can later be applied after the article's block decomposition of matrix rows is formalized.
-/

open Set
open scoped ENNReal

namespace Homogenization

/-- The finite-valued set of an extended nonnegative function, i.e. its effective domain. -/
def effectiveDomain {α : Type*} (F : α → ℝ≥0∞) : Set α := {x | F x < ⊤}

/-- Sum of two extended nonnegative integrands on separate variables. -/
def separatedSum {α β : Type*} (F : α → ℝ≥0∞) (G : β → ℝ≥0∞) : α × β → ℝ≥0∞ :=
  fun z => F z.1 + G z.2

/-- The effective domain of a separated sum is the product of the effective domains.
No finiteness, regularity, or convexity assumptions are needed because both summands take values
in `ℝ≥0∞`, so their sum is finite exactly when each summand is finite. -/
theorem mem_dom_separatedSum_iff {α β : Type*} (F : α → ℝ≥0∞) (G : β → ℝ≥0∞)
    (x : α × β) :
    x ∈ effectiveDomain (separatedSum F G) ↔
      x.1 ∈ effectiveDomain F ∧ x.2 ∈ effectiveDomain G := by
  simp [effectiveDomain, separatedSum, ENNReal.add_lt_top]

/-- Set form of `mem_dom_separatedSum_iff`. -/
theorem dom_separatedSum {α β : Type*} (F : α → ℝ≥0∞) (G : β → ℝ≥0∞) :
    effectiveDomain (separatedSum F G) = effectiveDomain F ×ˢ effectiveDomain G := by
  ext x
  exact mem_dom_separatedSum_iff F G x

end Homogenization
