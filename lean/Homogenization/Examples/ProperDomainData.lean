import Homogenization.Examples.ProperDomain
import Homogenization.Examples.ProperDomainBlocks

/-!
# Data and integrands for the Jacobian-constraint example

This file formalizes the data definitions (Dg), (DH), (DK), (Dab) and (sepW) used by
`prop:properdomain`, before proving any of the envelope or regularity conclusions.
-/

open Set
open scoped ENNReal NNReal

namespace Homogenization

variable {m N : ℕ}

/-- The Dg datum: exponent `p>N` and the finite, nonnegative scalar perturbation `g̃` on
`[0,∞)`, together with the convexity, monotonicity and shift-growth assumptions from (Dg). -/
structure ProperDomainGData (N : ℕ) where
  p : ℝ
  dim_lt_p : (N : ℝ) < p
  gTilde : ℝ≥0 → ℝ≥0
  gTilde_convex : ∀ x y : ℝ≥0, ∀ t : ℝ≥0, t ≤ 1 →
    (gTilde (t * x + (1 - t) * y) : ℝ) ≤
      (t : ℝ) * (gTilde x : ℝ) + (1 - (t : ℝ)) * (gTilde y : ℝ)
  gTilde_monotone : Monotone gTilde
  gTilde_shift : ∀ c : ℝ≥0, ∃ A B : ℝ≥0, ∀ s : ℝ≥0,
    gTilde (c + s) ≤ A + B * gTilde s

/-- The article's finite datum `G(ξ)=|ξ|_F^p+g̃(|ξ|_F²)`, embedded in `[0,∞]`.
The scalar term `g̃` is the finite perturbation in (Dg); the Jacobian singularity belongs to
`W_v` through `H∘v`, not to `G`. -/
noncomputable def properDomainG (D : ProperDomainGData N) (A : Mat m N) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixFrobeniusNorm A ^ D.p) +
    (D.gTilde ⟨matrixFrobeniusNorm A ^ 2, sq_nonneg _⟩ : ℝ≥0∞)

/-- `G` is finite everywhere, as stipulated by (Dg). -/
theorem properDomainG_lt_top (D : ProperDomainGData N) (A : Mat m N) :
    properDomainG D A < ⊤ := by
  simp [properDomainG, ENNReal.add_lt_top]

/-- `G` is Borel measurable: its finite scalar perturbation is monotone, while the Frobenius
norm, its square and its `p`-power are continuous. -/
theorem measurable_properDomainG (D : ProperDomainGData N) :
    Measurable (properDomainG D : Mat m N → ℝ≥0∞) := by
  have hnorm : Continuous (matrixFrobeniusNorm (m := m) (N := N)) := by
    unfold matrixFrobeniusNorm
    fun_prop
  have hp : 0 ≤ D.p := le_trans (Nat.cast_nonneg N) D.dim_lt_p.le
  have hpow : Continuous (fun A : Mat m N => matrixFrobeniusNorm A ^ D.p) :=
    hnorm.rpow_const (fun _ => Or.inr hp)
  have hbase : Measurable (fun A : Mat m N =>
      ENNReal.ofReal (matrixFrobeniusNorm A ^ D.p)) :=
    ENNReal.continuous_ofReal.measurable.comp hpow.measurable
  have hsquare : Continuous (fun A : Mat m N => matrixFrobeniusNorm A ^ 2) := by
    fun_prop
  have harg : Continuous (fun A : Mat m N =>
      (⟨matrixFrobeniusNorm A ^ 2, sq_nonneg _⟩ : ℝ≥0)) :=
    hsquare.subtype_mk (fun _ => sq_nonneg _)
  have htilde : Measurable (fun A : Mat m N =>
      (D.gTilde ⟨matrixFrobeniusNorm A ^ 2, sq_nonneg _⟩ : ℝ≥0∞)) :=
    (D.gTilde_monotone.measurable.coe_nnreal_ennreal).comp harg.measurable
  change Measurable (fun A : Mat m N =>
    ENNReal.ofReal (matrixFrobeniusNorm A ^ D.p) +
      (D.gTilde ⟨matrixFrobeniusNorm A ^ 2, sq_nonneg _⟩ : ℝ≥0∞))
  exact hbase.add htilde

/-- The Euclidean-coordinate linear map represented by `A`; this uses Euclidean norms on both
coordinate spaces, so its singular values agree with those of the matrix in the article. -/
noncomputable def matrixEuclideanLinearMap (A : Mat m N) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (WithLp.linearEquiv 2 ℝ (Tgt m)).symm.toLinearMap.comp
    (A.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (Sp N)).toLinearMap)

private noncomputable def matrixEuclideanContinuousLinearMap (A : Mat m N) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (A.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).toContinuousLinearMap)

private theorem matrixEuclideanContinuousLinearMap_toLinearMap (A : Mat m N) :
    (matrixEuclideanContinuousLinearMap A).toLinearMap = matrixEuclideanLinearMap A := rfl

/-- The `N`-dimensional Jacobian, defined as the product of the `N` singular values of the
Euclidean-coordinate matrix map, as in (2.9) of the article. -/
noncomputable def properDomainJacobian (A : Mat m N) : ℝ≥0 :=
  ⟨∏ i : Fin N, (matrixEuclideanLinearMap A).singularValues i,
    Finset.prod_nonneg fun i _ =>
      LinearMap.singularValues_nonneg (matrixEuclideanLinearMap A) i⟩

/-- The Jacobian is the norm determinant of the Euclidean-coordinate matrix map. This follows
from Mathlib's product formula for singular values, with no assumption `N ≤ m`; when the rank is
smaller than `N`, the product and the norm determinant both vanish. -/
theorem properDomainJacobian_coe_eq_normDet (A : Mat m N) :
    (properDomainJacobian A : ℝ) = (matrixEuclideanLinearMap A).normDet := by
  change (∏ i : Fin N, (matrixEuclideanLinearMap A).singularValues i) = _
  rw [LinearMap.normDet_eq_prod_singularValues]
  simpa [finrank_euclideanSpace] using
    (Fin.prod_univ_eq_prod_range
      (fun i : ℕ => (matrixEuclideanLinearMap A).singularValues i) N)

/-- The Jacobian is continuous: its norm-determinant square is the determinant of the Gram
operator `A†A`, and the Euclidean matrix map depends continuously on `A`. -/
theorem continuous_properDomainJacobian :
    Continuous (properDomainJacobian (m := m) (N := N)) := by
  have hmap : Continuous (fun A : Mat m N => matrixEuclideanContinuousLinearMap A) := by
    unfold matrixEuclideanContinuousLinearMap
    fun_prop
  have hadj : Continuous (fun A : Mat m N =>
      (matrixEuclideanContinuousLinearMap A).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp hmap
  have hgram : Continuous (fun A : Mat m N =>
      (matrixEuclideanContinuousLinearMap A).adjoint.comp
        (matrixEuclideanContinuousLinearMap A)) := hadj.clm_comp hmap
  have hdet : Continuous (fun A : Mat m N =>
      ((matrixEuclideanContinuousLinearMap A).adjoint.comp
        (matrixEuclideanContinuousLinearMap A)).det) :=
    ContinuousLinearMap.continuous_det.comp hgram
  have hsqrt := Real.continuous_sqrt.comp hdet
  have hreal : Continuous (fun A : Mat m N => (properDomainJacobian A : ℝ)) := by
    have hEq : (fun A : Mat m N => (properDomainJacobian A : ℝ)) =
        (fun A => Real.sqrt ((matrixEuclideanContinuousLinearMap A).adjoint.comp
          (matrixEuclideanContinuousLinearMap A)).det) := by
      funext A
      rw [properDomainJacobian_coe_eq_normDet, ← matrixEuclideanContinuousLinearMap_toLinearMap A]
      calc
        (matrixEuclideanContinuousLinearMap A).toLinearMap.normDet =
            Real.sqrt ((matrixEuclideanContinuousLinearMap A).toLinearMap.normDet ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (LinearMap.normDet_nonneg _)]
        _ = Real.sqrt ((matrixEuclideanContinuousLinearMap A).adjoint.comp
              (matrixEuclideanContinuousLinearMap A)).det := by
          congr 1
          exact ContinuousLinearMap.normDet_sq (matrixEuclideanContinuousLinearMap A)
    rw [hEq]
    exact hsqrt
  exact hreal.subtype_mk (fun A => (properDomainJacobian A).property)

/-- The set of full `N`-dimensional Jacobian, `Σ={A | v(A)≠0}`. -/
def properDomainSigma : Set (Mat m N) := {A | properDomainJacobian A ≠ 0}

/-- The DH datum: extended-valued `H` with effective domain exactly `(0,∞)`, and the upper
semicontinuity, tail bound and radial scaling assumptions of (DH). -/
structure ProperDomainHData (N : ℕ) where
  H : ℝ≥0 → ℝ≥0∞
  dom_iff_pos : ∀ s, H s < ⊤ ↔ s ≠ 0
  upperSemicontinuous : UpperSemicontinuous H
  gamma : ℝ
  delta : ℝ
  kappa : ℝ
  gamma_pos : 0 < gamma
  delta_pos : 0 < delta
  kappa_pos : 0 < kappa
  tail_bound : ∀ s : ℝ≥0, gamma ≤ s → H s ≤ ENNReal.ofReal delta
  scaling : ∀ (t : ℝ) (s : ℝ≥0), (ht : 0 < t) → t ≤ 1 → s ≠ 0 →
    H ⟨t ^ N * (s : ℝ), mul_nonneg (pow_nonneg (le_of_lt ht) _) s.2⟩ ≤
      ENNReal.ofReal (t ^ (-kappa)) * H s

/-- The DK datum: finite-valued `K`, upper semicontinuity, growth by `G`, and monotonicity along
rays. -/
structure ProperDomainKData (N m : ℕ) (D : ProperDomainGData N) where
  dim_le_m : N ≤ m
  K : Mat m N → ℝ≥0
  upperSemicontinuous : UpperSemicontinuous K
  C_K : ℝ
  C_K_pos : 0 < C_K
  growth : ∀ A, (K A : ℝ) ≤ C_K * (1 + (properDomainG D A).toReal)
  ray_mono : ∀ (t : ℝ) (A : Mat m N), 0 ≤ t → t ≤ 1 → K (t • A) ≤ K A

/-- The Dab datum: positive bounded Borel coefficients, periodic and lower semicontinuous.
Periodicity is expressed by invariance under integer translations in `Sp N`. -/
structure ProperDomainCoeffData (N : ℕ) where
  eta : ℝ
  Lambda : ℝ
  eta_pos : 0 < eta
  eta_le_Lambda : eta ≤ Lambda
  coeffA : Sp N → ℝ
  coeffB : Sp N → ℝ
  a_range : ∀ x : Sp N, eta ≤ coeffA x ∧ coeffA x ≤ Lambda
  b_range : ∀ x : Sp N, eta ≤ coeffB x ∧ coeffB x ≤ Lambda
  a_measurable : Measurable coeffA
  b_measurable : Measurable coeffB
  a_lowerSemicontinuous : LowerSemicontinuous coeffA
  b_lowerSemicontinuous : LowerSemicontinuous coeffB
  a_periodic : ∀ x : Sp N, ∀ z : Fin N → ℤ,
    coeffA (x + fun i => (z i : ℝ)) = coeffA x
  b_periodic : ∀ x : Sp N, ∀ z : Fin N → ℤ,
    coeffB (x + fun i => (z i : ℝ)) = coeffB x

/-- The integrand `W_v(x,A)=G(A)+b(x)K(A)+a(x)H(v(A))` from (sepW), for the supplied data. -/
noncomputable def properDomainWv (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (x : Sp N) (A : Mat m N) : ℝ≥0∞ :=
  properDomainG D A + ENNReal.ofReal (CD.coeffB x) * (KD.K A : ℝ≥0∞) +
    ENNReal.ofReal (CD.coeffA x) * HD.H (properDomainJacobian A)

/-- The spatially uniform majorant `W⁺ = G + Λ K + Λ H∘v` used in the proof of
`sep:iii`. This pointwise majorant is only an intermediate step: no growth estimate for its affine
envelope is asserted here. -/
noncomputable def properDomainWPlus (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (A : Mat m N) : ℝ≥0∞ :=
  properDomainG D A + ENNReal.ofReal CD.Lambda * (KD.K A : ℝ≥0∞) +
    ENNReal.ofReal CD.Lambda * HD.H (properDomainJacobian A)

/-- `W_v(x,·) ≤ W⁺` uniformly in `x`, by the upper bounds `a,b ≤ Λ` in (Dab). -/
theorem properDomainWv_le_WPlus (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (x : Sp N) :
    properDomainWv D KD HD CD x ≤ properDomainWPlus D KD HD CD := by
  intro A
  unfold properDomainWv properDomainWPlus
  have hb : ENNReal.ofReal (CD.coeffB x) ≤ ENNReal.ofReal CD.Lambda :=
    ENNReal.ofReal_le_ofReal (CD.b_range x).2
  have ha : ENNReal.ofReal (CD.coeffA x) ≤ ENNReal.ofReal CD.Lambda :=
    ENNReal.ofReal_le_ofReal (CD.a_range x).2
  apply add_le_add
  · apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  · exact mul_le_mul_of_nonneg_right ha (by positivity)

/-- The majorant `W⁺` is Borel measurable. This verifies the measurability input used by
`lemmaree` and the Ben Belgacem argument, but does not prove either of those envelope results. -/
theorem measurable_properDomainWPlus (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) :
    Measurable (properDomainWPlus D KD HD CD) := by
  have hK : Measurable (fun A : Mat m N => (KD.K A : ℝ≥0∞)) :=
    KD.upperSemicontinuous.measurable.coe_nnreal_ennreal
  have hH : Measurable (fun A : Mat m N => HD.H (properDomainJacobian A)) :=
    HD.upperSemicontinuous.measurable.comp continuous_properDomainJacobian.measurable
  change Measurable (fun A : Mat m N =>
    properDomainG D A + ENNReal.ofReal CD.Lambda * (KD.K A : ℝ≥0∞) +
      ENNReal.ofReal CD.Lambda * HD.H (properDomainJacobian A))
  exact ((measurable_properDomainG D).add (measurable_const.mul hK)).add
    (measurable_const.mul hH)

/-- The article's `W⁺` is finite at every matrix of maximal Jacobian rank. The extension of this
fact to finiteness of `Zaff W⁺` on all matrices is the separate geometric lemma `lemmaree`, which
is not proved here. -/
theorem properDomainWPlus_lt_top_of_jacobian_ne_zero (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (A : Mat m N)
    (hA : properDomainJacobian A ≠ 0) : properDomainWPlus D KD HD CD A < ⊤ := by
  have hG := properDomainG_lt_top D A
  have hH : HD.H (properDomainJacobian A) < ⊤ :=
    (HD.dom_iff_pos _).2 (by exact_mod_cast hA)
  simp [properDomainWPlus, ENNReal.add_lt_top, ENNReal.mul_lt_top, hG, hH]

/-- The effective domain of `W⁺` is the full-rank set `Σ`, just as for `W_v`, since its
coefficient of `H∘v` is the strictly positive constant `Λ`. This does not imply that the domain
of `Zaff W⁺` is all matrices; that is the content of the still unformalized `lemmaree`. -/
theorem dom_properDomainWPlus (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) :
    dom (properDomainWPlus D KD HD CD) = properDomainSigma := by
  ext A
  change properDomainWPlus D KD HD CD A < ⊤ ↔ properDomainJacobian A ≠ 0
  have hG : properDomainG D A < ⊤ := properDomainG_lt_top D A
  have hΛ_pos : 0 < CD.Lambda := lt_of_lt_of_le CD.eta_pos CD.eta_le_Lambda
  have hΛ_top : ENNReal.ofReal CD.Lambda < ⊤ := ENNReal.ofReal_lt_top
  have hΛ_ne : ENNReal.ofReal CD.Lambda ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hΛ_pos
  have hLamK : ENNReal.ofReal CD.Lambda * (KD.K A : ℝ≥0∞) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
  simp only [properDomainWPlus, ENNReal.add_lt_top, hG, hLamK, true_and,
    ENNReal.mul_lt_top_iff, hΛ_top, hΛ_ne, false_or]
  constructor
  · rintro (hfinite | hzero)
    · exact (HD.dom_iff_pos (properDomainJacobian A)).mp hfinite
    · apply (HD.dom_iff_pos (properDomainJacobian A)).mp
      rw [hzero]
      exact ENNReal.zero_lt_top
  · intro hne
    exact Or.inl ((HD.dom_iff_pos (properDomainJacobian A)).mpr hne)

/-- On the region `v(A) ≥ γ`, the pointwise majorant `W⁺` has the article's `G`-growth.
The remaining part of `sep:iii` is extending this control through the affine envelope to all
matrices, including `v(A) < γ`. -/
theorem properDomainWPlus_le_growth_of_jacobian_ge (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (A : Mat m N)
    (hA : HD.gamma ≤ (properDomainJacobian A : ℝ)) :
    properDomainWPlus D KD HD CD A ≤
      ENNReal.ofReal (1 + CD.Lambda * KD.C_K + CD.Lambda * HD.delta) *
        (1 + properDomainG D A) := by
  have hG : properDomainG D A < ⊤ := properDomainG_lt_top D A
  have hCK0 : 0 ≤ KD.C_K := KD.C_K_pos.le
  have hΛ0 : 0 ≤ CD.Lambda := le_trans CD.eta_pos.le CD.eta_le_Lambda
  have hδ0 : 0 ≤ HD.delta := HD.delta_pos.le
  have hK : (KD.K A : ℝ≥0∞) ≤ ENNReal.ofReal KD.C_K *
      (1 + properDomainG D A) := by
    have hsumtop : (1 : ℝ≥0∞) + properDomainG D A ≠ ⊤ :=
      ne_of_lt (ENNReal.add_lt_top.2 ⟨by simp, hG⟩)
    have hKtop : ENNReal.ofReal KD.C_K * (1 + properDomainG D A) ≠ ⊤ :=
      ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_top_iff_ne_top.mpr hsumtop))
    apply (ENNReal.toReal_le_toReal (a := (KD.K A : ℝ≥0∞))
      (b := ENNReal.ofReal KD.C_K * (1 + properDomainG D A)) (by simp) hKtop).mp
    rw [ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCK0,
      ENNReal.toReal_add ENNReal.one_ne_top (ne_of_lt hG)]
    simp only [ENNReal.toReal_one]
    simpa using KD.growth A
  have hH : HD.H (properDomainJacobian A) ≤ ENNReal.ofReal HD.delta :=
    HD.tail_bound _ hA
  have hpoint : properDomainWPlus D KD HD CD A ≤
      properDomainG D A +
        (ENNReal.ofReal CD.Lambda * ENNReal.ofReal KD.C_K) *
          (1 + properDomainG D A) +
        ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta := by
    unfold properDomainWPlus
    calc
      _ ≤ properDomainG D A +
          ENNReal.ofReal CD.Lambda *
            (ENNReal.ofReal KD.C_K * (1 + properDomainG D A)) +
          ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta := by
        apply add_le_add
        · apply add_le_add le_rfl
          exact mul_le_mul_of_nonneg_left hK (by positivity)
        · exact mul_le_mul_of_nonneg_left hH (by positivity)
      _ = _ := by rw [← mul_assoc]
  calc
    properDomainWPlus D KD HD CD A ≤ _ := hpoint
    _ ≤ ENNReal.ofReal (1 + CD.Lambda * KD.C_K + CD.Lambda * HD.delta) *
        (1 + properDomainG D A) := by
      have hcoeff : ENNReal.ofReal (1 + CD.Lambda * KD.C_K + CD.Lambda * HD.delta) =
          1 + ENNReal.ofReal CD.Lambda * ENNReal.ofReal KD.C_K +
            ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul hΛ0, ENNReal.ofReal_mul hΛ0]
        simp
      rw [hcoeff]
      have hG_le : properDomainG D A ≤ 1 + properDomainG D A := by
        exact le_add_of_nonneg_left (by simp)
      have hδ_le : ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta ≤
          (ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta) *
            (1 + properDomainG D A) := by
        have h1 : (1 : ℝ≥0∞) ≤ 1 + properDomainG D A := by
          exact le_add_of_nonneg_right (by positivity)
        calc
          _ = 1 * (ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta) := by simp
          _ ≤ (1 + properDomainG D A) *
              (ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = _ := by ac_rfl
      calc
        _ ≤ (1 + properDomainG D A) +
              (ENNReal.ofReal CD.Lambda * ENNReal.ofReal KD.C_K) *
                (1 + properDomainG D A) +
              (ENNReal.ofReal CD.Lambda * ENNReal.ofReal HD.delta) *
                (1 + properDomainG D A) := by
          exact add_le_add (add_le_add hG_le le_rfl) hδ_le
        _ = _ := by ring

/-- At each fixed spatial point, `W_v` is Borel measurable in the matrix variable. Upper
semicontinuity of `K` and `H` gives measurability of those terms, and `v` is continuous by
`continuous_properDomainJacobian`. The coefficient bounds are not needed for this measurability
claim. -/
theorem measurable_properDomainWv (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (x : Sp N) :
    Measurable (properDomainWv D KD HD CD x) := by
  have hK : Measurable (fun A : Mat m N => (KD.K A : ℝ≥0∞)) :=
    KD.upperSemicontinuous.measurable.coe_nnreal_ennreal
  have hB : Measurable (fun A : Mat m N =>
      ENNReal.ofReal (CD.coeffB x) * (KD.K A : ℝ≥0∞)) :=
    measurable_const.mul hK
  have hH : Measurable (fun A : Mat m N => HD.H (properDomainJacobian A)) :=
    HD.upperSemicontinuous.measurable.comp continuous_properDomainJacobian.measurable
  have hA : Measurable (fun A : Mat m N =>
      ENNReal.ofReal (CD.coeffA x) * HD.H (properDomainJacobian A)) :=
    measurable_const.mul hH
  change Measurable (fun A : Mat m N =>
    properDomainG D A + ENNReal.ofReal (CD.coeffB x) * (KD.K A : ℝ≥0∞) +
      ENNReal.ofReal (CD.coeffA x) * HD.H (properDomainJacobian A))
  exact ((measurable_properDomainG D).add hB).add hA

/-- Under the domain part of (DH) and the strict lower bound `a≥η>0` from (Dab), the effective
domain of `W_v(x,·)` is exactly `Σ={A | v(A)≠0}`. The remaining Dg–Dab regularity assumptions
are carried by the data structures but are not needed for this domain identity. -/
theorem dom_properDomainWv (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N)
    (CD : ProperDomainCoeffData N) (x : Sp N) :
    dom (properDomainWv D KD HD CD x) = properDomainSigma := by
  ext A
  change properDomainWv D KD HD CD x A < ⊤ ↔ properDomainJacobian A ≠ 0
  have hG : properDomainG D A < ⊤ := properDomainG_lt_top D A
  have ha_pos : 0 < CD.coeffA x := by
    have heta : 0 < CD.eta := CD.eta_pos
    exact lt_of_lt_of_le heta (CD.a_range x).1
  have ha_top : ENNReal.ofReal (CD.coeffA x) < ⊤ := ENNReal.ofReal_lt_top
  have ha_ne : ENNReal.ofReal (CD.coeffA x) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr ha_pos
  have hbK : ENNReal.ofReal (CD.coeffB x) * (KD.K A : ℝ≥0∞) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
  simp only [properDomainWv, ENNReal.add_lt_top, hG, hbK, true_and,
    ENNReal.mul_lt_top_iff, ha_top, ha_ne, false_or]
  constructor
  · rintro (hfinite | hzero)
    · exact HD.dom_iff_pos (properDomainJacobian A) |>.mp hfinite
    · apply (HD.dom_iff_pos (properDomainJacobian A)).mp
      rw [hzero]
      exact ENNReal.zero_lt_top
  · intro hne
    exact Or.inl ((HD.dom_iff_pos (properDomainJacobian A)).mpr hne)

/-! ### Integrands on the stacked matrix space -/

/-- The first-block integrand `G` pulled back to a stacked matrix and added to an arbitrary
second-block integrand, exactly as in equation `eq:sepWsharp`. The row split is the
article's identification `Mat (m₁+m₂) N ≃ Mat m₁ N × Mat m₂ N`. -/
noncomputable def properDomainGSharp {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) (G₂ : Mat m₂ N → ℝ≥0∞)
    (A : Mat (m₁ + m₂) N) : ℝ≥0∞ :=
  separatedSum (properDomainG D) G₂ (matBlockSplitLinearEquiv m₁ m₂ N A)

/-- The integrand `W♯(x,A)=W_v(x,A¹)+G₂(A²)` from `eq:sepWsharp`, transported to the matrix space
of stacked rows. Here `D`, `KD`, `HD`, and `CD` are the data defining `G` and `W_v` on the first
block, while `G₂` is the second-block integrand. -/
noncomputable def properDomainWSharp {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G₂ : Mat m₂ N → ℝ≥0∞) (x : Sp N)
    (A : Mat (m₁ + m₂) N) : ℝ≥0∞ :=
  separatedSum (properDomainWv D KD HD CD x) G₂
    (matBlockSplitLinearEquiv m₁ m₂ N A)

/-- The example choice of the second-block integrand in (DG2), using the exponent from (Dg). -/
noncomputable abbrev properDomainGSharpExample {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) [NeZero m₂] [NeZero N]
    (A : Mat (m₁ + m₂) N) : ℝ≥0∞ :=
  properDomainGSharp D (properDomainG2 D.p) A

/-- The corresponding `W♯` formed with the concrete half-space example `G₂`. -/
noncomputable abbrev properDomainWSharpExample {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    [NeZero m₂] [NeZero N] (x : Sp N) (A : Mat (m₁ + m₂) N) : ℝ≥0∞ :=
  properDomainWSharp D KD HD CD (properDomainG2 D.p) x A

/-- Since the first-block `G` in (Dg) is finite everywhere, the effective domain of `G♯` is
the inverse image of the product of the full first-block space with the second-block domain.
This is the product-domain statement in clause (i), expressed through the explicit block
equivalence. -/
theorem dom_properDomainGSharp {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) (G₂ : Mat m₂ N → ℝ≥0∞) :
    dom (properDomainGSharp D G₂) =
      (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹' (Set.univ ×ˢ dom G₂) := by
  change dom (fun A : Mat (m₁ + m₂) N =>
    separatedSum (properDomainG D) G₂ (matBlockSplitLinearEquiv m₁ m₂ N A)) = _
  have hsplit := dom_matBlockSeparatedSum m₁ m₂ N (properDomainG D) G₂
  rw [hsplit]
  have hG : dom (properDomainG (m := m₁) D) =
      (Set.univ : Set (Mat m₁ N)) := by
    ext A
    simp [dom, properDomainG_lt_top (D := D) (A := A)]
  rw [hG]

/-- For the concrete choice `G₂=properDomainG2 D.p`, clause (i)'s domain is the inverse image of
the full first block times the half-space `C₂={χ | χ₁₁<1}`. The assumptions `m₂,N ≠ 0` are the
ones required to define the article's `(1,1)` entry. -/
theorem dom_properDomainGSharpExample {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) [NeZero m₂] [NeZero N] :
    dom (properDomainGSharpExample (N := N) D) =
      (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹'
        (Set.univ ×ˢ properDomainHalfSpace (m := m₂) (N := N)) := by
  rw [dom_properDomainGSharp]
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
  exact (mem_dom_properDomainG2_iff D.p (matBlockSplitLinearEquiv m₁ m₂ N A).2)

/-- The effective domain of `W♯` is the inverse image of `Σ × dom(G₂)` under the row-splitting
equivalence. Equivalently, after the article's identification of stacked matrices with pairs, it
is exactly `Σ × C₂`, where `Σ={A | v(A)≠0}` and `C₂=dom(G₂)`. -/
theorem dom_properDomainWSharp {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (G₂ : Mat m₂ N → ℝ≥0∞) (x : Sp N) :
    dom (properDomainWSharp D KD HD CD G₂ x) =
      (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹' (properDomainSigma ×ˢ dom G₂) := by
  change dom (fun A : Mat (m₁ + m₂) N =>
    separatedSum (properDomainWv D KD HD CD x) G₂
      (matBlockSplitLinearEquiv m₁ m₂ N A)) = _
  have hsplit := dom_matBlockSeparatedSum m₁ m₂ N
    (properDomainWv D KD HD CD x) G₂
  rw [hsplit]
  rw [dom_properDomainWv]

/-- Establishes the effective-domain identity in clause (ii) for the concrete half-space example:
the domain of `W♯(x,·)` is the inverse image of `Σ × C₂` under the block equivalence. This is the
domain identity only; it does not assert the separate nonconvexity claim in that clause. -/
theorem dom_properDomainWSharpExample {m₁ m₂ : ℕ}
    (D : ProperDomainGData N) (KD : ProperDomainKData N m₁ D)
    (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    [NeZero m₂] [NeZero N] (x : Sp N) :
    dom (properDomainWSharpExample (N := N) D KD HD CD x) =
      (matBlockSplitLinearEquiv m₁ m₂ N) ⁻¹'
        (properDomainSigma ×ˢ properDomainHalfSpace (m := m₂) (N := N)) := by
  rw [dom_properDomainWSharp]
  ext A
  simp only [Set.mem_preimage, Set.mem_prod]
  constructor
  · rintro ⟨hfirst, h₂⟩
    exact ⟨hfirst, (mem_dom_properDomainG2_iff D.p
      (matBlockSplitLinearEquiv m₁ m₂ N A).2).mp h₂⟩
  · rintro ⟨hfirst, h₂⟩
    exact ⟨hfirst, (mem_dom_properDomainG2_iff D.p
      (matBlockSplitLinearEquiv m₁ m₂ N A).2).mpr h₂⟩

end Homogenization
