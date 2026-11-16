import Homogenization.Basic

/-!
# Piecewise affine (Kuhn) interpolation and approximation in `Aff₀`

`exists_Aff0_approx_of_contDiff`: for `U` bounded open and `f` of class `C¹` with compact support
in `U`, every `ε > 0` admits `φ ∈ Aff₀(U)` with `‖φ - f‖_∞ ≤ ε` and `‖∇φ - ∇f‖ ≤ ε` a.e.

This is the first step towards replacing the former cited `CitedApproxConvexZero`
(`lemme_approx_convex_zero`, [duerinckx-gloria16, Prop. A.16]); it does not prove that statement.
Only `C¹` functions with compact support are treated here: the approximation of general
`W^{1,p}_0` functions, the constraint `∇φ ∈ int(dom Ψ)` and the convergence of the energies
`∫ Ψ(∇φ)` are not addressed in this file.

The interpolant is written without an explicit triangulation, as an average over diagonal shifts
of the rounding to the grid `hℤᴺ` (the Lovász extension form of the Kuhn interpolation):
`I_h f(x) = ∫₀¹ f(h ⌈x/h - t⌉) dt` (`pwInterp`).
* `lipschitzWith_pwInterp`: `I_h f` is `K N`-Lipschitz if `f` is `K`-Lipschitz, from
  `∫₀¹ |⌈a - t⌉ - ⌈b - t⌉| dt = |a - b|`;
* `norm_pwInterp_sub_le`, `pwInterp_eq_zero`: uniform error `K h`, and `I_h f(x)` only depends
  on `f` within `h` of `x`;
* `pwInterp_eq_on_kuhnPiece`, `hasFDerivAt_pwInterp_of_mem_kuhnPiece`: on the open Kuhn simplex
  `kuhnPiece h k σ` (`1 > y_{σ 0} > ⋯ > y_{σ (N-1)} > 0`, `y` the fractional coordinates),
  `I_h f` is affine with gradient `kuhnGrad h f k σ`;
* `norm_kuhnGrad_sub_fderiv_le`: `‖kuhnGrad - ∇f(x)‖ ≤ N ε` when `∇f` oscillates by at most `ε`
  on the ball of radius `h` around `x` (mean value inequality on the edges `v_j v_{j+1}`);
* `volume_kuhnBad`, `exists_mem_kuhnPiece`, `kuhnPiece_eq_of_mem`: the simplices are pairwise
  disjoint and cover `ℝᴺ` up to a finite union of families of hyperplanes;
* `pwInterp_mem_Aff0`: `I_h f ∈ Aff₀(U)` when `f` vanishes within `h` of `ℝᴺ \ U`.
-/

open MeasureTheory Filter Topology Set Function intervalIntegral
open scoped ENNReal NNReal

namespace Homogenization

/-- `t ↦ ⌈a - t⌉` is antitone. -/
theorem antitone_ceil_sub (a : ℝ) : Antitone fun t : ℝ => (⌈a - t⌉ : ℝ) :=
  fun x y h => by
    have : a - y ≤ a - x := by linarith
    change (⌈a - y⌉ : ℝ) ≤ ⌈a - x⌉
    exact_mod_cast Int.ceil_mono this

/-- `∫₀¹ ⌈a - t⌉ dt = a`. -/
theorem integral_ceil_sub (a : ℝ) : ∫ t in (0 : ℝ)..1, (⌈a - t⌉ : ℝ) = a := by
  set n : ℤ := ⌈a⌉
  set c : ℝ := a - n + 1
  have hn1 : (n : ℝ) - 1 < a := by have := Int.ceil_lt_add_one a; linarith
  have hn2 : a ≤ n := Int.le_ceil a
  have hc0 : 0 < c := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
    rw [ae_iff]; simp [measure_singleton]
  have h1 : ∫ t in (0 : ℝ)..c, (⌈a - t⌉ : ℝ) = ∫ t in (0 : ℝ)..c, (n : ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [hne] with t htc ht
    rw [uIoc_of_le hc0.le] at ht
    have hlt : t < c := lt_of_le_of_ne ht.2 htc
    have : ⌈a - t⌉ = n := by
      rw [Int.ceil_eq_iff]; constructor <;> linarith [ht.1]
    rw [this]
  have h2 : ∫ t in c..1, (⌈a - t⌉ : ℝ) = ∫ t in c..1, ((n : ℝ) - 1) := by
    refine integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hc1] at ht
    have : ⌈a - t⌉ = n - 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith [ht.1, ht.2]
    rw [this]; push_cast; ring
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => (⌈a - t⌉ : ℝ)) volume x y :=
    fun x y => (antitone_ceil_sub a).intervalIntegrable
  rw [← integral_add_adjacent_intervals (hi 0 c) (hi c 1), h1, h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, c]
  ring

variable {N m : ℕ}

/-- `∫₀¹ |⌈a - t⌉ - ⌈b - t⌉| dt = |a - b|`. -/
theorem integral_abs_ceil_sub_sub (a b : ℝ) :
    ∫ t in (0 : ℝ)..1, |(⌈a - t⌉ : ℝ) - ⌈b - t⌉| = |a - b| := by
  have hi : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => (⌈c - t⌉ : ℝ)) volume 0 1 :=
    fun c => (antitone_ceil_sub c).intervalIntegrable
  rcases le_total a b with hab | hab
  · have e : ∀ t, |(⌈a - t⌉ : ℝ) - ⌈b - t⌉| = (⌈b - t⌉ : ℝ) - ⌈a - t⌉ := fun t => by
      rw [abs_sub_comm, abs_of_nonneg]
      have : a - t ≤ b - t := by linarith
      exact sub_nonneg.2 (by exact_mod_cast Int.ceil_mono this)
    simp_rw [e]
    rw [intervalIntegral.integral_sub (hi b) (hi a), integral_ceil_sub, integral_ceil_sub,
      abs_of_nonpos (by linarith)]
    ring
  · have e : ∀ t, |(⌈a - t⌉ : ℝ) - ⌈b - t⌉| = (⌈a - t⌉ : ℝ) - ⌈b - t⌉ := fun t => by
      rw [abs_of_nonneg]
      have : b - t ≤ a - t := by linarith
      exact sub_nonneg.2 (by exact_mod_cast Int.ceil_mono this)
    simp_rw [e]
    rw [intervalIntegral.integral_sub (hi a) (hi b), integral_ceil_sub, integral_ceil_sub,
      abs_of_nonneg (by linarith)]

/-- Rounding up to the grid `hℤᴺ` after the diagonal shift `-t h`. -/
noncomputable def gridPt (h : ℝ) (x : Sp N) (t : ℝ) : Sp N := fun i => h * ⌈x i / h - t⌉

/-- The piecewise affine (Kuhn) interpolant on the grid `hℤᴺ`, written as an average over
diagonal shifts: `I_h f(x) = ∫₀¹ f(h ⌈x/h - t⌉) dt`. -/
noncomputable def pwInterp (h : ℝ) (f : Sp N → Tgt m) (x : Sp N) : Tgt m :=
  ∫ t in (0 : ℝ)..1, f (gridPt h x t)

/-- `t ↦ gridPt h x t` is measurable. -/
theorem measurable_gridPt (h : ℝ) (x : Sp N) : Measurable (gridPt h x) := by
  refine measurable_pi_lambda _ fun i => ?_
  change Measurable fun t : ℝ => h * (⌈x i / h - t⌉ : ℝ)
  exact measurable_const.mul (measurable_from_top.comp
    (Int.measurable_ceil.comp (measurable_const.sub measurable_id)))

/-- The grid point `gridPt h x t` is within `h` of `x` (sup norm) for `t ∈ [0,1]`. -/
theorem norm_gridPt_sub_le {h : ℝ} (hh : 0 < h) (x : Sp N) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖gridPt h x t - x‖ ≤ h := by
  refine (pi_norm_le_iff_of_nonneg hh.le).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  have h1 := Int.le_ceil (x i / h - t)
  have h2 := Int.ceil_lt_add_one (x i / h - t)
  have e : x i = h * (x i / h) := by field_simp
  simp only [gridPt, Pi.sub_apply]
  constructor <;> nlinarith

/-- `t ↦ f(gridPt h x t)` is integrable on `[0,1]` for `f` Lipschitz. -/
theorem intervalIntegrable_comp_gridPt {f : Sp N → Tgt m} {K : ℝ≥0} (hf : LipschitzWith K f)
    {h : ℝ} (hh : 0 < h) (x : Sp N) :
    IntervalIntegrable (fun t => f (gridPt h x t)) volume 0 1 := by
  refine (intervalIntegrable_const (c := ‖f x‖ + K * h)).mono_fun'
    (hf.continuous.measurable.comp (measurable_gridPt h x)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le zero_le_one] at ht
  have h1 := hf.norm_sub_le (gridPt h x t) x
  have h2 := norm_gridPt_sub_le hh x ht.1.le ht.2
  calc ‖f (gridPt h x t)‖ ≤ ‖f x‖ + ‖f (gridPt h x t) - f x‖ := by
        have := norm_sub_norm_le (f (gridPt h x t)) (f x); linarith
    _ ≤ ‖f x‖ + K * h := by gcongr; exact h1.trans (by gcongr)

/-- The interpolant of a `K`-Lipschitz function is `K N`-Lipschitz. -/
theorem lipschitzWith_pwInterp {f : Sp N → Tgt m} {K : ℝ≥0} (hf : LipschitzWith K f)
    {h : ℝ} (hh : 0 < h) : LipschitzWith (K * N) (pwInterp h f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hx := intervalIntegrable_comp_gridPt hf hh x
  have hy := intervalIntegrable_comp_gridPt hf hh y
  have habs : ∀ i, IntervalIntegrable
      (fun t : ℝ => |(⌈x i / h - t⌉ : ℝ) - ⌈y i / h - t⌉|) volume 0 1 := fun i =>
    (((antitone_ceil_sub _).intervalIntegrable).sub
      ((antitone_ceil_sub _).intervalIntegrable)).abs
  have hpt : ∀ t, ‖f (gridPt h x t) - f (gridPt h y t)‖ ≤
      K * ∑ i, h * |(⌈x i / h - t⌉ : ℝ) - ⌈y i / h - t⌉| := by
    intro t
    refine (hf.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ K.2)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)).2 fun i => ?_
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i))
    simp only [gridPt, Pi.sub_apply, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos hh,
      le_refl]
  calc ‖pwInterp h f x - pwInterp h f y‖
      = ‖∫ t in (0 : ℝ)..1, (f (gridPt h x t) - f (gridPt h y t))‖ := by
        rw [pwInterp, pwInterp, intervalIntegral.integral_sub hx hy]
    _ ≤ ∫ t in (0 : ℝ)..1, ‖f (gridPt h x t) - f (gridPt h y t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, K * ∑ i, h * |(⌈x i / h - t⌉ : ℝ) - ⌈y i / h - t⌉| := by
        refine intervalIntegral.integral_mono_on zero_le_one (hx.sub hy).norm ?_
          (fun t _ => hpt t)
        have hs : IntervalIntegrable
            (fun t : ℝ => ∑ i, h * |(⌈x i / h - t⌉ : ℝ) - ⌈y i / h - t⌉|) volume 0 1 := by
          have := IntervalIntegrable.sum Finset.univ fun i _ => (habs i).const_mul h
          simpa only [Finset.sum_fn] using this
        exact hs.const_mul _
    _ = K * ∑ i, |x i - y i| := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum fun i _ => (habs i).const_mul h]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_const_mul, integral_abs_ceil_sub_sub, ← sub_div, abs_div,
          abs_of_pos hh]
        field_simp
    _ ≤ K * (N * ‖x - y‖) := by
        gcongr
        calc ∑ i, |x i - y i| ≤ ∑ _i : Fin N, ‖x - y‖ := Finset.sum_le_sum fun i _ => by
              have := norm_le_pi_norm (x - y) i
              rwa [Real.norm_eq_abs, Pi.sub_apply] at this
          _ = N * ‖x - y‖ := by simp
    _ = ((K * N : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring

/-- `I_h f(x)` only depends on the values of `f` within `h` of `x`. -/
theorem pwInterp_eq_zero {f : Sp N → Tgt m} {h : ℝ} (hh : 0 < h) {x : Sp N}
    (hx : ∀ z, ‖z - x‖ ≤ h → f z = 0) : pwInterp h f x = 0 := by
  rw [pwInterp]
  refine (intervalIntegral.integral_congr fun t ht => ?_).trans intervalIntegral.integral_zero
  rw [uIcc_of_le zero_le_one] at ht
  exact hx _ (norm_gridPt_sub_le hh x ht.1 ht.2)

/-- Uniform error: `‖I_h f(x) - f(x)‖ ≤ K h` for `f` `K`-Lipschitz. -/
theorem norm_pwInterp_sub_le {f : Sp N → Tgt m} {K : ℝ≥0} (hf : LipschitzWith K f) {h : ℝ}
    (hh : 0 < h) (x : Sp N) : ‖pwInterp h f x - f x‖ ≤ K * h := by
  have hx := intervalIntegrable_comp_gridPt hf hh x
  calc ‖pwInterp h f x - f x‖ = ‖∫ t in (0 : ℝ)..1, (f (gridPt h x t) - f x)‖ := by
        rw [pwInterp, intervalIntegral.integral_sub hx intervalIntegrable_const,
          intervalIntegral.integral_const, sub_zero, one_smul]
    _ ≤ ∫ t in (0 : ℝ)..1, ‖f (gridPt h x t) - f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, (K * h : ℝ) := by
        refine intervalIntegral.integral_mono_on zero_le_one (hx.sub intervalIntegrable_const).norm
          intervalIntegrable_const (fun t ht => ?_)
        exact (hf.norm_sub_le _ _).trans (by gcongr; exact norm_gridPt_sub_le hh x ht.1 ht.2)
    _ = K * h := by simp

/-- For an antitone `g : Fin N → ℝ`, `{j | t < g j}` is the initial segment of length `J`. -/
theorem lt_antitone_iff_lt_card {g : Fin N → ℝ} (hg : Antitone g) (t : ℝ) (j : Fin N) :
    t < g j ↔ (j : ℕ) < (Finset.univ.filter fun j' => t < g j').card := by
  constructor
  · intro hj
    have hsub : Finset.Iic j ⊆ Finset.univ.filter fun j' => t < g j' := fun j' hj' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le hj (hg (Finset.mem_Iic.1 hj'))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hj
    by_contra hn
    have hsub : (Finset.univ.filter fun j' => t < g j') ⊆ Finset.Iio j := fun j' hj' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      rw [Finset.mem_Iio]
      by_contra hle
      exact hn (lt_of_lt_of_le hj' (hg (not_lt.1 hle)))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- Telescoping along an initial segment: `∑_{j < N} 1_{j < J} (F(j+1) - F j) = F J - F 0`. -/
theorem sum_fin_ite_lt_sub {E : Type*} [AddCommGroup E] (F : ℕ → E) {J : ℕ} (hJ : J ≤ N) :
    ∑ j : Fin N, (if (j : ℕ) < J then F (j + 1) - F j else 0) = F J - F 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < J then F (j + 1) - F j else 0) N,
    ← Finset.sum_filter]
  have e : (Finset.range N).filter (fun a => a < J) = Finset.range J := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [e, Finset.sum_range_sub]

/-- Fractional coordinates of `x` in the grid cell `h(k + [0,1]ᴺ)`. -/
noncomputable def kuhnFrac (h : ℝ) (k : Fin N → ℤ) (x : Sp N) (i : Fin N) : ℝ := x i / h - k i

/-- The open Kuhn simplex of the cell `h(k + [0,1]ᴺ)` attached to the permutation `σ`:
`1 > y_{σ 0} > y_{σ 1} > ⋯ > y_{σ (N-1)} > 0`, `y` the fractional coordinates. -/
def kuhnPiece (h : ℝ) (k : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) : Set (Sp N) :=
  {x | (∀ i, 0 < kuhnFrac h k x i ∧ kuhnFrac h k x i < 1) ∧
    StrictAnti fun j => kuhnFrac h k x (σ j)}

/-- The `j`-th vertex of the Kuhn simplex, `0 ≤ j ≤ N`: `h(k + 1_{σ{0,…,j-1}})` (for `j > N` the
formula gives the last vertex `h(k + 1)` again). -/
def kuhnVertex (h : ℝ) (k : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) (j : ℕ) : Sp N :=
  fun i => h * (k i + if ((σ.symm i : Fin N) : ℕ) < j then 1 else 0)

/-- On `kuhnPiece h k σ`, for `t ∈ ]0,1[` distinct from the fractional coordinates, the rounded
point is the `J`-th Kuhn vertex, `J = #{j | t < y_{σ j}}`. -/
theorem gridPt_eq_kuhnVertex {h : ℝ} {k : Fin N → ℤ} {σ : Equiv.Perm (Fin N)}
    {x : Sp N} (hx : x ∈ kuhnPiece h k σ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (htne : ∀ i, t ≠ kuhnFrac h k x i) :
    gridPt h x t = kuhnVertex h k σ
      (Finset.univ.filter fun j => t < kuhnFrac h k x (σ j)).card := by
  funext i
  have hg : Antitone fun j => kuhnFrac h k x (σ j) := hx.2.antitone
  have hiff := lt_antitone_iff_lt_card hg t (σ.symm i)
  simp only [Equiv.apply_symm_apply] at hiff
  simp only [gridPt, kuhnVertex]
  congr 1
  have e : x i / h - t = (kuhnFrac h k x i - t) + (k i : ℤ) := by
    simp only [kuhnFrac]; ring
  rw [e, Int.ceil_add_intCast]
  push_cast
  have hy := hx.1 i
  by_cases hti : t < kuhnFrac h k x i
  · rw [if_pos (hiff.1 hti)]
    have : ⌈kuhnFrac h k x i - t⌉ = 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; push_cast; ring
  · rw [if_neg (fun h' => hti (hiff.2 h'))]
    have hlt : kuhnFrac h k x i < t := lt_of_le_of_ne (not_lt.1 hti) (htne i).symm
    have : ⌈kuhnFrac h k x i - t⌉ = 0 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; push_cast; ring

/-- `∫₀¹ 1_{t < c} dt = c` for `c ∈ [0,1]`. -/
theorem integral_ite_lt {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ t in (0 : ℝ)..1, (if t < c then (1 : ℝ) else 0) = c := by
  have hm : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => if t < c then (1 : ℝ) else 0) volume a b :=
    fun a b => (show Antitone fun t : ℝ => if t < c then (1 : ℝ) else 0 from fun x y hxy => by
      change (if y < c then (1 : ℝ) else 0) ≤ if x < c then 1 else 0
      by_cases hy : y < c
      · rw [if_pos hy, if_pos (lt_of_le_of_lt hxy hy)]
      · rw [if_neg hy]; split_ifs <;> norm_num).intervalIntegrable
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
    rw [ae_iff]; simp [measure_singleton]
  have h1 : ∫ t in (0 : ℝ)..c, (if t < c then (1 : ℝ) else 0) = ∫ _ in (0 : ℝ)..c, (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with t htc ht
    rw [uIoc_of_le hc0] at ht
    rw [if_pos (lt_of_le_of_ne ht.2 htc)]
  have h2 : ∫ t in c..1, (if t < c then (1 : ℝ) else 0) = ∫ _ in c..1, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hc1] at ht
    rw [if_neg (not_lt.2 ht.1.le)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hm 0 c) (hm c 1), h1, h2]
  simp

/-- **Affine formula on a Kuhn simplex.** On `kuhnPiece h k σ`,
`I_h f(x) = f(v₀) + ∑_j y_{σ j} (f(v_{j+1}) - f(v_j))`, `v_j = kuhnVertex h k σ j`. -/
theorem pwInterp_eq_on_kuhnPiece {f : Sp N → Tgt m}
    {h : ℝ} {k : Fin N → ℤ} {σ : Equiv.Perm (Fin N)} {x : Sp N}
    (hx : x ∈ kuhnPiece h k σ) :
    pwInterp h f x = f (kuhnVertex h k σ 0) + ∑ j : Fin N, kuhnFrac h k x (σ j) •
      (f (kuhnVertex h k σ (j + 1)) - f (kuhnVertex h k σ j)) := by
  set F : ℕ → Tgt m := fun j => f (kuhnVertex h k σ j)
  set g : Fin N → ℝ := fun j => kuhnFrac h k x (σ j)
  have hg : Antitone g := hx.2.antitone
  have hfin : (Set.range (kuhnFrac h k x)).Finite := Set.finite_range _
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ Set.range (kuhnFrac h k x) := by
    rw [ae_iff]
    exact measure_mono_null (fun t ht => by simpa using ht) (hfin.measure_zero volume)
  have hne1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    rw [ae_iff]; simp [measure_singleton]
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 → f (gridPt h x t) =
      F 0 + ∑ j : Fin N, (if t < g j then (1 : ℝ) else 0) • (F (j + 1) - F j) := by
    filter_upwards [hae, hne1] with t htr ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    have htne : ∀ i, t ≠ kuhnFrac h k x i := fun i he => htr ⟨i, he.symm⟩
    have hJ : (Finset.univ.filter fun j => t < g j).card ≤ N :=
      (Finset.card_filter_le _ _).trans (by simp)
    rw [gridPt_eq_kuhnVertex hx ht.1 (lt_of_le_of_ne ht.2 ht1) htne]
    have hsum := sum_fin_ite_lt_sub F hJ
    have e : ∀ j : Fin N, (if t < g j then (1 : ℝ) else 0) • (F (j + 1) - F j) =
        if (j : ℕ) < (Finset.univ.filter fun j => t < g j).card then F (j + 1) - F j else 0 := by
      intro j
      have := lt_antitone_iff_lt_card hg t j
      by_cases hj : t < g j
      · rw [if_pos hj, if_pos (this.1 hj), one_smul]
      · rw [if_neg hj, if_neg (fun h' => hj (this.2 h')), zero_smul]
    simp_rw [e]
    rw [hsum]
    simp only [F, g]
    abel
  have hite : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => if t < c then (1 : ℝ) else 0) volume 0 1 :=
    fun c => (show Antitone fun t : ℝ => if t < c then (1 : ℝ) else 0 from fun x y hxy => by
      change (if y < c then (1 : ℝ) else 0) ≤ if x < c then 1 else 0
      by_cases hy : y < c
      · rw [if_pos hy, if_pos (lt_of_le_of_lt hxy hy)]
      · rw [if_neg hy]; split_ifs <;> norm_num).intervalIntegrable
  have hterm : ∀ j : Fin N, IntervalIntegrable
      (fun t : ℝ => (if t < g j then (1 : ℝ) else 0) • (F (j + 1) - F j)) volume 0 1 :=
    fun j => ⟨(hite (g j)).1.smul_const _, (hite (g j)).2.smul_const _⟩
  rw [pwInterp, intervalIntegral.integral_congr_ae hpt,
    intervalIntegral.integral_add intervalIntegrable_const
      (by simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ fun j _ => hterm j),
    intervalIntegral.integral_const, sub_zero, one_smul,
    intervalIntegral.integral_finsetSum fun j _ => hterm j]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_smul_const,
    integral_ite_lt (hx.1 (σ j)).1.le (hx.1 (σ j)).2.le]

/-- The constant gradient of `I_h f` on `kuhnPiece h k σ`:
`∑_j h⁻¹ e_{σ j}^* ⊗ (f(v_{j+1}) - f(v_j))`. -/
noncomputable def kuhnGrad (h : ℝ) (f : Sp N → Tgt m) (k : Fin N → ℤ)
    (σ : Equiv.Perm (Fin N)) : Mat m N :=
  ∑ j : Fin N, (h⁻¹ • (ContinuousLinearMap.proj (σ j) : Sp N →L[ℝ] ℝ)).smulRight
    (f (kuhnVertex h k σ (j + 1)) - f (kuhnVertex h k σ j))

/-- Kuhn simplices are open. -/
theorem isOpen_kuhnPiece (h : ℝ) (k : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    IsOpen (kuhnPiece h k σ) := by
  have hc : ∀ i, Continuous fun x : Sp N => kuhnFrac h k x i := fun i => by
    unfold kuhnFrac; fun_prop
  have e : kuhnPiece h k σ = (⋂ i, {x | 0 < kuhnFrac h k x i} ∩ {x | kuhnFrac h k x i < 1}) ∩
      ⋂ j, ⋂ j', {x | j < j' → kuhnFrac h k x (σ j') < kuhnFrac h k x (σ j)} := by
    ext x
    simp only [kuhnPiece, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rfl
  rw [e]
  refine (isOpen_iInter_of_finite fun i => (isOpen_lt continuous_const (hc i)).inter
    (isOpen_lt (hc i) continuous_const)).inter
    (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun j' => ?_)
  by_cases hjj : j < j'
  · simp only [hjj, true_implies]
    exact isOpen_lt (hc _) (hc _)
  · simp only [hjj, false_implies, Set.ofPred_true, isOpen_univ]

/-- `I_h f` has derivative `kuhnGrad h f k σ` at every point of `kuhnPiece h k σ`. -/
theorem hasFDerivAt_pwInterp_of_mem_kuhnPiece {f : Sp N → Tgt m} {h : ℝ}
    {k : Fin N → ℤ} {σ : Equiv.Perm (Fin N)} {x : Sp N} (hx : x ∈ kuhnPiece h k σ) :
    HasFDerivAt (pwInterp h f) (kuhnGrad h f k σ) x := by
  set A : Sp N → Tgt m := fun y => f (kuhnVertex h k σ 0) + ∑ j : Fin N,
    kuhnFrac h k y (σ j) • (f (kuhnVertex h k σ (j + 1)) - f (kuhnVertex h k σ j))
  set C : Tgt m := f (kuhnVertex h k σ 0) - ∑ j : Fin N, ((k (σ j) : ℤ) : ℝ) •
    (f (kuhnVertex h k σ (j + 1)) - f (kuhnVertex h k σ j))
  have hA : A = fun y => C + kuhnGrad h f k σ y := by
    funext y
    simp only [A, C, kuhnGrad, kuhnFrac, sum_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib, div_eq_inv_mul]
    abel
  have hderA : HasFDerivAt A (kuhnGrad h f k σ) x := by
    rw [hA]; exact (kuhnGrad h f k σ).hasFDerivAt.const_add C
  refine hderA.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_kuhnPiece h k σ).mem_nhds hx] with y hy
  exact pwInterp_eq_on_kuhnPiece hy

/-- For the sup norm on `Sp N`, `‖A‖ ≤ ∑ᵢ ‖A eᵢ‖`. -/
theorem opNorm_le_sum_single (A : Mat m N) :
    ‖A‖ ≤ ∑ i, ‖A (Pi.single i 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => norm_nonneg _)
    fun v => ?_
  have hv : v = ∑ i, v i • (Pi.single i 1 : Sp N) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  calc ‖A v‖ = ‖∑ i, v i • A (Pi.single i 1)‖ := by
        conv_lhs => rw [hv]
        simp [map_sum, map_smul]
    _ ≤ ∑ i, ‖v i • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, |v i| * ‖A (Pi.single i 1)‖ := by simp [norm_smul]
    _ ≤ ∑ i, ‖v‖ * ‖A (Pi.single i 1)‖ := Finset.sum_le_sum fun i _ => by
        gcongr; exact (Real.norm_eq_abs (v i)) ▸ norm_le_pi_norm v i
    _ = (∑ i, ‖A (Pi.single i 1)‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

/-- `kuhnGrad h f k σ e_{σ j} = h⁻¹ (f(v_{j+1}) - f(v_j))`. -/
theorem kuhnGrad_apply_single (h : ℝ) (f : Sp N → Tgt m) (k : Fin N → ℤ)
    (σ : Equiv.Perm (Fin N)) (j : Fin N) :
    kuhnGrad h f k σ (Pi.single (σ j) 1) =
      h⁻¹ • (f (kuhnVertex h k σ (j + 1)) - f (kuhnVertex h k σ j)) := by
  simp only [kuhnGrad, sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    rw [Pi.single_apply, if_neg (fun he => hj' (σ.injective he)), mul_zero, zero_smul]
  · simp

/-- Consecutive Kuhn vertices differ by `h e_{σ j}`. -/
theorem kuhnVertex_succ_sub (h : ℝ) (k : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) (j : Fin N) :
    kuhnVertex h k σ (j + 1) - kuhnVertex h k σ j = h • (Pi.single (σ j) 1 : Sp N) := by
  funext i
  simp only [kuhnVertex, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = σ j
  · subst hi
    simp only [Equiv.symm_apply_apply, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt,
      if_true, if_false, lt_self_iff_false]
    simp
    ring
  · have hne : ((σ.symm i : Fin N) : ℕ) ≠ j := fun he => hi (by
      rw [← Fin.ext_iff.mpr he]; simp)
    rw [if_neg hi]
    by_cases hlt : ((σ.symm i : Fin N) : ℕ) < j
    · rw [if_pos (by omega), if_pos hlt]; ring
    · rw [if_neg (by omega), if_neg hlt]; ring

/-- The Kuhn vertices are within `h` of every point of the simplex (sup norm). -/
theorem norm_kuhnVertex_sub_le {h : ℝ} (hh : 0 < h) {k : Fin N → ℤ} {σ : Equiv.Perm (Fin N)}
    {x : Sp N} (hx : x ∈ kuhnPiece h k σ) (j : ℕ) : ‖kuhnVertex h k σ j - x‖ ≤ h := by
  refine (pi_norm_le_iff_of_nonneg hh.le).2 fun i => ?_
  have h1 := (hx.1 i).1
  have h2 := (hx.1 i).2
  simp only [kuhnFrac] at h1 h2
  have e : x i = h * (x i / h) := by field_simp
  rw [Real.norm_eq_abs, abs_le]
  simp only [kuhnVertex, Pi.sub_apply]
  split_ifs <;> constructor <;> nlinarith

/-- **Gradient estimate on a Kuhn simplex.** If `‖∇f(z) - ∇f(x)‖ ≤ ε` for `‖z - x‖ ≤ h`, then
`‖∇(I_h f) - ∇f(x)‖ ≤ N ε` at `x ∈ kuhnPiece h k σ`. -/
theorem norm_kuhnGrad_sub_fderiv_le {f : Sp N → Tgt m} (hf : Differentiable ℝ f) {h ε : ℝ}
    (hh : 0 < h) {k : Fin N → ℤ} {σ : Equiv.Perm (Fin N)} {x : Sp N}
    (hx : x ∈ kuhnPiece h k σ)
    (hω : ∀ z, ‖z - x‖ ≤ h → ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε) :
    ‖kuhnGrad h f k σ - fderiv ℝ f x‖ ≤ N * ε := by
  refine (opNorm_le_sum_single _).trans ?_
  rw [← Equiv.sum_comp σ]
  have hterm : ∀ j : Fin N, ‖(kuhnGrad h f k σ - fderiv ℝ f x) (Pi.single (σ j) 1)‖ ≤ ε := by
    intro j
    set g : Sp N → Tgt m := fun z => f z - fderiv ℝ f x z
    have hgd : ∀ z, HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f x) z := fun z =>
      (hf z).hasFDerivAt.sub (fderiv ℝ f x).hasFDerivAt
    have hbound : ∀ z ∈ Metric.closedBall x h, ‖fderiv ℝ g z‖ ≤ ε := fun z hz => by
      rw [(hgd z).fderiv]
      exact hω z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)
    have hmem : ∀ i : ℕ, kuhnVertex h k σ i ∈ Metric.closedBall x h := fun i => by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact norm_kuhnVertex_sub_le hh hx i
    have hmv := (convex_closedBall x h).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hgd z).differentiableAt) hbound (hmem j) (hmem (j + 1))
    rw [kuhnVertex_succ_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at hmv
    have hsingle : ‖(Pi.single (σ j) 1 : Sp N)‖ = 1 := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
      · rw [Pi.single_apply]; split_ifs <;> simp
      · have := norm_le_pi_norm (Pi.single (σ j) 1 : Sp N) (σ j)
        simpa using this
    rw [hsingle, mul_one] at hmv
    have e : (kuhnGrad h f k σ - fderiv ℝ f x) (Pi.single (σ j) 1) =
        h⁻¹ • (g (kuhnVertex h k σ (j + 1)) - g (kuhnVertex h k σ j)) := by
      rw [sub_apply, kuhnGrad_apply_single]
      simp only [g]
      rw [show f (kuhnVertex h k σ (j + 1)) - fderiv ℝ f x (kuhnVertex h k σ (j + 1)) -
          (f (kuhnVertex h k σ j) - fderiv ℝ f x (kuhnVertex h k σ j)) =
          (f (kuhnVertex h k σ (j + 1)) - f (kuhnVertex h k σ j)) -
            fderiv ℝ f x (kuhnVertex h k σ (j + 1) - kuhnVertex h k σ j) by
        rw [map_sub]; abel]
      rw [kuhnVertex_succ_sub, map_smul, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh.ne',
        one_smul, smul_sub]
    rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
    calc h⁻¹ * ‖g (kuhnVertex h k σ (j + 1)) - g (kuhnVertex h k σ j)‖ ≤ h⁻¹ * (ε * h) := by
          gcongr
      _ = ε := by field_simp
  calc ∑ j, ‖(kuhnGrad h f k σ - fderiv ℝ f x) (Pi.single (σ j) 1)‖ ≤ ∑ _j : Fin N, ε :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = N * ε := by simp

/-- Level sets of a nonzero linear form are Lebesgue-null. -/
theorem volume_levelSet_eq_zero (L : Sp N →ₗ[ℝ] ℝ) (hL : L ≠ 0) (c : ℝ) :
    volume {x : Sp N | L x = c} = 0 := by
  by_cases hc : ∃ v, L v = c
  · obtain ⟨v, hv⟩ := hc
    have hker : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ker_eq_top.1 h)
    have e : {x : Sp N | L x = c} = (· + -v) ⁻¹' (LinearMap.ker L : Set (Sp N)) := by
      ext x; simp [sub_eq_zero, hv, ← sub_eq_add_neg]
    rw [e, measure_preimage_add_right]
    exact Measure.addHaar_submodule volume _ hker
  · simp only [not_exists] at hc
    have : {x : Sp N | L x = c} = ∅ := by ext x; simp [hc x]
    rw [this, measure_empty]

/-- The bad set where some fractional coordinate vanishes or two coincide. -/
def kuhnBad (h : ℝ) : Set (Sp N) :=
  (⋃ (i : Fin N) (z : ℤ), {x | x i = h * z}) ∪
    ⋃ (i : Fin N) (j : Fin N) (_ : i ≠ j) (z : ℤ), {x | x i - x j = h * z}

/-- The bad set is Lebesgue-null. -/
theorem volume_kuhnBad (h : ℝ) : volume (kuhnBad (N := N) h) = 0 := by
  refine measure_union_null (measure_iUnion_null fun i => measure_iUnion_null fun z => ?_)
    (measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij =>
      measure_iUnion_null fun z => ?_)
  · have hL : (LinearMap.proj i : Sp N →ₗ[ℝ] ℝ) ≠ 0 := fun h0 => by
      have := congrArg (fun L : Sp N →ₗ[ℝ] ℝ => L (Pi.single i 1)) h0
      simp at this
    exact volume_levelSet_eq_zero _ hL (h * z)
  · have hL : ((LinearMap.proj i : Sp N →ₗ[ℝ] ℝ) - LinearMap.proj j) ≠ 0 := fun h0 => by
      have := congrArg (fun L : Sp N →ₗ[ℝ] ℝ => L (Pi.single i 1)) h0
      change (Pi.single i (1 : ℝ) : Sp N) i - (Pi.single i (1 : ℝ) : Sp N) j = 0 at this
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at this
      norm_num at this
    exact volume_levelSet_eq_zero _ hL (h * z)

/-- Off the bad set, every point lies in a Kuhn simplex. -/
theorem exists_mem_kuhnPiece {h : ℝ} (hh : 0 < h) {x : Sp N} (hx : x ∉ kuhnBad h) :
    ∃ k σ, x ∈ kuhnPiece h k σ := by
  set k : Fin N → ℤ := fun i => ⌊x i / h⌋
  set y : Fin N → ℝ := fun i => kuhnFrac h k x i
  have hy0 : ∀ i, 0 < y i := by
    intro i
    have h1 : (⌊x i / h⌋ : ℝ) ≤ x i / h := Int.floor_le _
    refine lt_of_le_of_ne (by simp only [y, kuhnFrac, k]; linarith) fun he => hx ?_
    refine Or.inl (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨⌊x i / h⌋, ?_⟩⟩)
    simp only [y, kuhnFrac, k] at he
    change x i = h * ⌊x i / h⌋
    have : x i / h = ⌊x i / h⌋ := by linarith
    field_simp at this; linarith
  have hy1 : ∀ i, y i < 1 := fun i => by
    have := Int.lt_floor_add_one (x i / h)
    simp only [y, kuhnFrac, k]; linarith
  have hinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    refine hx (Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hne,
      mem_iUnion.2 ⟨⌊x i / h⌋ - ⌊x j / h⌋, ?_⟩⟩⟩⟩))
    simp only [y, kuhnFrac, k] at hij
    change x i - x j = h * ((⌊x i / h⌋ - ⌊x j / h⌋ : ℤ) : ℝ)
    push_cast
    have : x i / h - x j / h = ⌊x i / h⌋ - ⌊x j / h⌋ := by linarith
    field_simp at this; linarith
  refine ⟨k, Fin.revPerm.trans (Tuple.sort y), fun i => ⟨hy0 i, hy1 i⟩, ?_⟩
  have hmono : Monotone (y ∘ Tuple.sort y) := Tuple.monotone_sort y
  have hanti : Antitone fun j => y ((Fin.revPerm.trans (Tuple.sort y)) j) := fun a b hab => by
    simp only [Equiv.trans_apply]
    exact hmono (Fin.rev_le_rev.2 hab)
  exact hanti.strictAnti_of_injective (hinj.comp (Equiv.injective _))

/-- Distinct Kuhn simplices are disjoint. -/
theorem kuhnPiece_eq_of_mem {h : ℝ} {k k' : Fin N → ℤ}
    {σ σ' : Equiv.Perm (Fin N)} {x : Sp N} (hx : x ∈ kuhnPiece h k σ)
    (hx' : x ∈ kuhnPiece h k' σ') : k = k' ∧ σ = σ' := by
  have hk : ∀ k₀ : Fin N → ℤ, ∀ σ₀, x ∈ kuhnPiece h k₀ σ₀ → k₀ = fun i => ⌊x i / h⌋ := by
    intro k₀ σ₀ hx₀
    funext i
    have h1 := (hx₀.1 i).1
    have h2 := (hx₀.1 i).2
    simp only [kuhnFrac] at h1 h2
    exact (Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩).symm
  have hkk : k = k' := (hk k σ hx).trans (hk k' σ' hx').symm
  subst hkk
  refine ⟨rfl, ?_⟩
  set y : Fin N → ℝᵒᵈ := fun i => OrderDual.toDual (kuhnFrac h k x i)
  have h1 : Monotone (y ∘ σ) := fun a b hab => by
    simp only [Function.comp_apply, y, OrderDual.toDual_le_toDual]
    exact hx.2.antitone hab
  have h2 : Monotone (y ∘ σ') := fun a b hab => by
    simp only [Function.comp_apply, y, OrderDual.toDual_le_toDual]
    exact hx'.2.antitone hab
  have heq := Tuple.unique_monotone h1 h2
  have hinj : Function.Injective y := by
    intro i j hij
    have hσ : Function.Injective fun j => kuhnFrac h k x (σ j) := hx.2.injective
    have e1 : kuhnFrac h k x i = kuhnFrac h k x j := hij
    have := hσ (show kuhnFrac h k x (σ (σ.symm i)) = kuhnFrac h k x (σ (σ.symm j)) by simpa)
    simpa using this
  ext j
  exact congrArg Fin.val (hinj (congrFun heq j))

/-- Points of `U` on the boundary of a piece `kuhnPiece ∩ U` lie in the bad set. -/
theorem inter_frontier_kuhnPiece_subset {h : ℝ} (hh : 0 < h) {U : Set (Sp N)} (hUo : IsOpen U)
    (k : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    U ∩ frontier (kuhnPiece h k σ ∩ U) ⊆ kuhnBad h := by
  rintro x ⟨hxU, hxf⟩
  by_contra hbad
  obtain ⟨k', σ', hx'⟩ := exists_mem_kuhnPiece hh hbad
  have hopen : IsOpen (kuhnPiece h k σ ∩ U) := (isOpen_kuhnPiece h k σ).inter hUo
  obtain ⟨y, hy, hyP⟩ := mem_closure_iff.1 hxf.1 _ (isOpen_kuhnPiece h k' σ') hx'
  obtain ⟨hk, hσ⟩ := kuhnPiece_eq_of_mem hyP.1 hy
  subst hk; subst hσ
  exact hxf.2 (by rw [hopen.interior_eq]; exact ⟨hx', hxU⟩)

/-- **The interpolant is in `Aff₀(U)`**, for `U` bounded open and `f` Lipschitz vanishing within
`h` of `ℝᴺ \ U`. -/
theorem pwInterp_mem_Aff0 {U : Set (Sp N)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : Sp N → Tgt m} {K : ℝ≥0} (hf : LipschitzWith K f) {h : ℝ} (hh : 0 < h)
    (hzero : ∀ x ∉ U, ∀ z, ‖z - x‖ ≤ h → f z = 0) : pwInterp h f ∈ Aff0 U := by
  have hLip := lipschitzWith_pwInterp hf hh
  obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
  set M : ℤ := ⌈R / h⌉ + 1
  let ι := (Fin N → (Finset.Icc (-M) M : Set ℤ)) × Equiv.Perm (Fin N)
  let kOf : ι → Fin N → ℤ := fun a i => (a.1 i : ℤ)
  let V : ι → Set (Sp N) := fun a => kuhnPiece h (kOf a) a.2 ∩ U
  let ξ : ι → Mat m N := fun a => kuhnGrad h f (kOf a) a.2
  let e := Fintype.equivFin ι
  refine ⟨⟨_, hLip⟩, fun x hx => pwInterp_eq_zero hh (hzero x hx), ⟨_, hLip.lipschitzOnWith⟩,
    Fintype.card ι, fun i => V (e.symm i), fun i => ξ (e.symm i), fun i => ?_, fun i => ?_,
    fun i j hij => ?_, fun i => ?_, ?_, fun i y hy => ?_⟩
  · exact (isOpen_kuhnPiece _ _ _).inter hUo
  · exact inter_subset_right
  · refine Set.disjoint_left.2 fun y hy hy' => hij ?_
    obtain ⟨hk, hσ⟩ := kuhnPiece_eq_of_mem hy.1 hy'.1
    apply e.symm.injective
    refine Prod.ext (funext fun l => Subtype.ext (congrFun hk l)) hσ
  · exact measure_mono_null (inter_frontier_kuhnPiece_subset hh hUo _ _) (volume_kuhnBad h)
  · refine measure_mono_null (fun x ⟨hxU, hxV⟩ => ?_) (volume_kuhnBad h)
    by_contra hbad
    obtain ⟨k, σ, hx⟩ := exists_mem_kuhnPiece hh hbad
    have hk : ∀ l, k l ∈ (Finset.Icc (-M) M : Set ℤ) := by
      intro l
      have hkl : k l = ⌊x l / h⌋ := by
        have h1 := (hx.1 l).1
        have h2 := (hx.1 l).2
        simp only [kuhnFrac] at h1 h2
        exact (Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩).symm
      have hxR : |x l| ≤ R := by
        have := hR hxU
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact (Real.norm_eq_abs (x l) ▸ norm_le_pi_norm x l).trans this
      have hc := Int.le_ceil (R / h)
      rw [abs_le] at hxR
      simp only [Finset.coe_Icc, mem_Icc, hkl, M]
      constructor
      · rw [Int.le_floor]; push_cast
        rw [le_div_iff₀ hh]
        have : -R / h ≥ -(⌈R / h⌉ : ℝ) := by rw [neg_div]; linarith
        rw [ge_iff_le, le_div_iff₀ hh] at this
        nlinarith
      · rw [Int.floor_le_iff]; push_cast
        have : x l / h ≤ R / h := div_le_div_of_nonneg_right hxR.2 hh.le
        linarith
    apply hxV
    refine mem_iUnion.2 ⟨e (fun l => ⟨k l, hk l⟩, σ), ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨hx, hxU⟩
  · exact hasFDerivAt_pwInterp_of_mem_kuhnPiece hy.1

/-- **Piecewise affine approximation of `C¹` functions.** For `U` bounded open and `f` of class
`C¹` with compact support in `U`, for every `ε > 0` there is `φ ∈ Aff₀(U)` with
`‖φ - f‖_∞ ≤ ε` and `‖∇φ - ∇f‖ ≤ ε` a.e. (`φ = I_h f` for `h` small). -/
theorem exists_Aff0_approx_of_contDiff {U : Set (Sp N)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) (hfU : tsupport f ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ ∈ (Aff0 U : Set (Sp N → Tgt m)), (∀ x, ‖φ x - f x‖ ≤ ε) ∧
      ∀ᵐ x, ‖fderiv ℝ φ x - fderiv ℝ f x‖ ≤ ε := by
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfs one_ne_zero
  obtain ⟨δ, hδ, hδU⟩ := hfs.isCompact.exists_cthickening_subset_open hUo hfU
  have hUC : UniformContinuous (fderiv ℝ f) :=
    (hfs.fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)
  set ε' : ℝ := ε / (N + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.uniformContinuous_iff.1 hUC ε' hε'
  set h : ℝ := min (min δ (δ' / 2)) (ε / (C + 1))
  have hh : 0 < h := lt_min (lt_min hδ (by positivity)) (by positivity)
  have hhδ : h ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hhδ' : h < δ' := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _))
    (by linarith)
  have hhε : (C : ℝ) * h ≤ ε := by
    have h1 : h ≤ ε / (C + 1) := min_le_right _ _
    have h2 : (C : ℝ) * h ≤ (C + 1) * h := by nlinarith
    calc (C : ℝ) * h ≤ (C + 1) * h := h2
      _ ≤ (C + 1) * (ε / (C + 1)) := by gcongr
      _ = ε := by field_simp
  have hzero : ∀ x ∉ U, ∀ z, ‖z - x‖ ≤ h → f z = 0 := by
    intro x hx z hz
    by_contra hfz
    apply hx
    apply hδU
    refine Metric.mem_cthickening_of_dist_le x z δ _ (subset_tsupport f hfz) ?_
    rw [dist_eq_norm, norm_sub_rev]
    exact hz.trans hhδ
  refine ⟨pwInterp h f, pwInterp_mem_Aff0 hUo hUb hC hh hzero,
    fun x => (norm_pwInterp_sub_le hC hh x).trans hhε, ?_⟩
  have hae : ∀ᵐ x, x ∉ kuhnBad (N := N) h := by
    rw [ae_iff]; simpa using volume_kuhnBad (N := N) h
  filter_upwards [hae] with x hx
  obtain ⟨k, σ, hxP⟩ := exists_mem_kuhnPiece hh hx
  rw [(hasFDerivAt_pwInterp_of_mem_kuhnPiece hxP).fderiv]
  have hω : ∀ z, ‖z - x‖ ≤ h → ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε' := by
    intro z hz
    have := hδ'U (a := z) (b := x) (by rw [dist_eq_norm]; exact lt_of_le_of_lt hz hhδ')
    rw [dist_eq_norm] at this
    exact this.le
  calc ‖kuhnGrad h f k σ - fderiv ℝ f x‖ ≤ N * ε' :=
        norm_kuhnGrad_sub_fderiv_le (hf.differentiable one_ne_zero) hh hxP hω
    _ ≤ ε := by
        simp only [ε']
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

end Homogenization
