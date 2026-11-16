import Homogenization.Examples.ProperDomainNonconvex
import Homogenization.Domains

/-!
# The determinant integrand of the introduction

* `properDomainJacobian_eq_abs_det`: for square matrices (`m = N`), the Jacobian
  `v(ξ) = √det(ξᵀξ)` of `(eq:jacobian)` equals `|det ξ|`, so that the integrand
  `W_det(x,ξ) = G(ξ) + a(x) H(det ξ)` of `(equationasWdet-intro)`, with `H(s) = 1/|s|`, is the
  integrand `W_v` of `prop:separating` for `m = N`.
* `properDomainWv_no_convex_growth`: no convex `G'` and `α' > 0`, `β'` give a two-sided bound
  `α' G' ≤ W_v(x,·) ≤ β' (1 + G')`, because such a bound forces `dom G' = Σ`, which is not convex
  (`properDomainSigma_not_convex`).
-/

open MeasureTheory Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- For square matrices, `v(ξ) = |det ξ|`. -/
theorem properDomainJacobian_eq_abs_det (A : Mat N N) :
    (properDomainJacobian A : ℝ) = |LinearMap.det (A : Sp N →ₗ[ℝ] Sp N)| := by
  rw [properDomainJacobian_coe_eq_normDet, LinearMap.normDet_eq_norm_det, Real.norm_eq_abs]
  congr 1
  unfold matrixEuclideanLinearMap
  exact LinearMap.det_conj (A : Sp N →ₗ[ℝ] Sp N) (WithLp.linearEquiv 2 ℝ (Sp N)).symm

/-- **No convex growth for `W_v`** (introduction, and `prop:separating` (i)): for every `x`, there
is no convex `G'` with `α' G' ≤ W_v(x,·) ≤ β' (1 + G')` for some `α' > 0` and `β'`. -/
theorem properDomainWv_no_convex_growth [NeZero N] (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (x : Sp N) :
    ¬ ∃ (G' : Mat m N → ℝ≥0∞) (α' β' : ℝ≥0), ConvexENN G' ∧ 0 < α' ∧
      ∀ ξ, (α' : ℝ≥0∞) * G' ξ ≤ properDomainWv D KD HD CD x ξ ∧
        properDomainWv D KD HD CD x ξ ≤ β' * (1 + G' ξ) := by
  rintro ⟨G', α', β', hG', hα', hb⟩
  have hdom : dom G' = properDomainSigma (m := m) (N := N) := by
    rw [← dom_properDomainWv D KD HD CD x]
    ext ξ
    change G' ξ < ⊤ ↔ properDomainWv D KD HD CD x ξ < ⊤
    constructor
    · intro h
      exact (hb ξ).2.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
        (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, h⟩))
    · intro h
      have h1 := (hb ξ).1.trans_lt h
      by_contra hc
      rw [not_lt, top_le_iff] at hc
      rw [hc, ENNReal.mul_top (by exact_mod_cast hα'.ne')] at h1
      exact lt_irrefl _ h1
  exact properDomainSigma_not_convex (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) KD.dim_le_m
    (hdom ▸ hG'.convex_dom)

end Homogenization
