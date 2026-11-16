import Homogenization.DensityZaff

/-!
# Properties of the lower integral (Lemma `lem:lowerint`)

The integral of §2.1 of the paper, `∫_E f = sup {∫_E g : g Borel, g ≤ f}`, is Mathlib's lower
Lebesgue integral `∫⁻`, defined for every `f : ℝᴺ → [0,∞]` as the supremum of the integrals of the
measurable simple functions below `f`; this supremum equals the paper's supremum over Borel
functions below `f`, since every Borel `g ≤ f` is the supremum of the simple functions below it.
Lemma `lem:lowerint` lists the
properties used in the paper for non-measurable integrands; each item below is the corresponding
statement for `∫⁻`. No measurability of `f` is assumed.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ}

/-- **Lemma `lem:lowerint` (i)**: monotonicity on a Borel set. -/
theorem lowerint_mono {E : Set (Sp N)} (hE : MeasurableSet E) {f f' : Sp N → ℝ≥0∞}
    (h : ∀ x ∈ E, f x ≤ f' x) : ∫⁻ x in E, f x ≤ ∫⁻ x in E, f' x :=
  setLIntegral_mono' hE h

/-- **Lemma `lem:lowerint` (ii)**: functions that coincide a.e. on `E` have the same integral
(the paper takes `g` Lebesgue measurable; here `g` is arbitrary). -/
theorem lowerint_congr_ae {E : Set (Sp N)} {f g : Sp N → ℝ≥0∞}
    (h : f =ᵐ[volume.restrict E] g) : ∫⁻ x in E, f x = ∫⁻ x in E, g x :=
  lintegral_congr_ae h

/-- **Lemma `lem:lowerint` (iii)**: countable additivity over pairwise disjoint Borel sets. -/
theorem lowerint_iUnion {ι : Type*} [Countable ι] {E : ι → Set (Sp N)}
    (hE : ∀ k, MeasurableSet (E k)) (hd : Pairwise (Function.onFun Disjoint E))
    (f : Sp N → ℝ≥0∞) : ∫⁻ x in ⋃ k, E k, f x = ∑' k, ∫⁻ x in E k, f x :=
  lintegral_iUnion hE hd f

/-- **Lemma `lem:lowerint` (iv)**: `∫_{a + rE} f((y - a)/r) dy = r^N ∫_E f` for `r > 0`. -/
theorem lowerint_homothety {E : Set (Sp N)} (hE : MeasurableSet E) (a : Sp N) {r : ℝ}
    (hr : 0 < r) (f : Sp N → ℝ≥0∞) :
    ∫⁻ y in (fun x => a + r • x) '' E, f (r⁻¹ • (y - a)) =
      ENNReal.ofReal (r ^ N) * ∫⁻ x in E, f x := by
  have himg : (fun x => a + r • x) '' E = affMap r a ⁻¹' E := by
    ext y
    simp only [mem_image, mem_preimage, affMap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1
      rw [smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      abel
    · intro hy
      refine ⟨r⁻¹ • y + -(r⁻¹ • a), hy, ?_⟩
      rw [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, smul_neg, smul_smul,
        mul_inv_cancel₀ hr.ne', one_smul]
      abel
  have hfun : (fun y => f (r⁻¹ • (y - a))) = fun y => f (affMap r a y) := by
    funext y
    simp only [affMap, sub_eq_add_neg, smul_add, smul_neg]
  rw [himg, hfun]
  exact setLIntegral_comp_affMap hr a hE f

/-- **Lemma `lem:lowerint` (v)**: `∫_E (s f + c) = s ∫_E f + c |E|`. The paper takes `E` Borel,
`s ∈ ]0,∞[` and `c ∈ [0,∞[`; here `E` is arbitrary, `s = 0` is allowed and `c = ∞` as well. -/
theorem lowerint_affine_comb (E : Set (Sp N)) (f : Sp N → ℝ≥0∞) {s : ℝ≥0∞} (hs : s ≠ ∞)
    (c : ℝ≥0∞) :
    ∫⁻ x in E, (s * f x + c) = s * (∫⁻ x in E, f x) + c * volume E := by
  rw [lintegral_add_right' _ aemeasurable_const, lintegral_const_mul' _ _ hs, setLIntegral_const]

end Homogenization
