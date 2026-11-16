import Homogenization.Step4
import Homogenization.Subadditive
import Homogenization.Vitali
import Homogenization.Cutoff
import Homogenization.Radial
import Homogenization.Domains
import Homogenization.LowerBound

/-!
# Local Dirichlet problems for the upper bound of Proposition 2.1(ii)

The paper's local problem minimizes the oscillatory energy among functions with prescribed boundary
values. Writing competitors as `u + φ`, with `φ ∈ W^{1,p}_0(A)`, gives the equivalent integrand
`W(x/ε, ∇u + ∇φ)`. This module begins the upper-bound argument with that exact Sobolev class.

The local problem, its subadditivity, its growth-density domination, and the Vitali-envelope upper
bound are formalized. A `W1p` gradient has a measurable representative equal to it almost
everywhere; `mDirichletLimsup_congr_of_ae_on_open` and
`mDirichletLimsup_congr_eventually_cube_of_ae_on_open` transfer its Dirichlet values and
centered-cube density back to the weak gradient, with only eventual cube inclusion in `Ω`.
The annular growth majorant and finiteness of the cutoff trial energy are proved. The normalized
cell/annulus comparison now carries the coarse annular bound
`β (∫ G (∇u) + K volume(S))` through the `ε → 0` limit. At each fixed `s`, the radius-limit
comparison transfers this estimate to the Vitali cube density using the annular differentiation
limits, and `mDirichletLimsup_vitali_density_le_Hp_of_affine_remainder` performs the common-data
squeeze `s → 1`. The almost-everywhere assembly from the cited affine differentiability interface
is now provided for each fixed contraction `t`. The corollary
`mDirichletLimsup_vitaliEnv_le_Hp_of_cited` integrates that pointwise density bound to control the
same Vitali envelope by the contracted homogenized energy on every open subset. This is a bound
for the `t`-dependent Dirichlet problem; it does not identify its envelope with its density or
produce a recovery sequence for the uncontracted problem. The lemmas
`RUUSCWith.le_affine_radial` and `lintegral_le_radial_affine` now give a pointwise and integrated
radial majorant without measurability assumptions; `mDirichletLimsup_vitaliEnv_le_radialHp_of_cited`
applies it to the Vitali envelope for contractions above the RU-usc threshold. The required
RU-usc of `L` is available in applications such as `L = Ytloc W` from `Hypotheses.ruusc`. However,
these bounds concern a different contracted Dirichlet problem for each `t`; the recovery sequence
and final `GammaLimsup` assembly remain open. Finite gluing is now formalized for `W1p0` correctors
on disjoint open pieces: it gives the global `W1p` competitor, its a.e. piecewise gradients, and
the exact energy decomposition including the uncovered remainder. This finite result does not
yet provide a Vitali-family competitor or an ε/radius diagonal.
`finiteW1p0_lipschitz_cube_correction_poincare` proves on a finite union `U` of disjoint cubes
the estimate
`∫_U ‖Σ φᵢ‖^p ≤ m R^p ∫_U ‖Σ ∇φᵢ‖^p`, where every cube side length is at most `R`. Its pieces must
belong to `W1p0`, have globally Lipschitz representatives, and have pointwise derivatives equal
a.e. to their weak gradients. For Lipschitz pieces this equality is now derived by
`W1p0.lipschitz_fderiv_eq_grad_ae`, and
`finiteW1p0_lipschitz_cube_correction_poincare_of_lipschitz` removes the explicit equality
premise. It uses the project’s `poincare_cube`; neither it nor Mathlib’s compactly supported
`C¹` Sobolev inequality gives the estimate for arbitrary `W1p0` correctors. That extension needs a
density/approximation theorem with convergence of both the functions and weak gradients in `Lᵖ`.
To obtain Lᵖ convergence in a recovery
sequence, one still needs uniform bounds on the glued gradient energies while `R → 0`, together
with the Vitali cover, control of the uncovered remainder, and the ε/radius diagonal.
For the variable-gradient route, `W1p.ae_tendsto_lintegral_G_grad_cube_ratio` now derives the
centered-cube Lebesgue-point limit from `Measurable G` and the explicit finite `G`-energy
assumption, using the measurable gradient representative and its a.e. agreement with the weak
gradient. `W1p.ae_tendsto_lintegral_G_grad_annulus_ratio` supplies the annular-average limit used
by the fixed-`s` density bound.
`mDirichlet_le_rescaled_Ytp_of_const` and `mDirichletLimsup_le_Hp_of_const` prove the cell
comparison in the constant-background case. Proposition 2.1(ii) is not proved; the route now
being pursued is the scaled-background construction `scaledBackgroundCellCutoffCorrector`, which
applies the inner-cell
recollement to `t • u` itself. Its cell and affine slopes are both `t • ξ`; hence the annular
gradient is `φ • (t • ξ) + (1-φ) • (t • ∇u) - E_t` with
`E_t = t • E`, and no extra `(1-t) • ξ` term occurs. The weighted three-point growth estimate
and `ConvexENN.smul_unit_le` keep the field arguments contracted;
`ConvexENN.lintegral_smul_unit_lt_top` proves finite energy of the contracted field from finite
volume, finite `G ∘ D` energy, and `G 0 < ⊤`; measurability is not needed for this extended
integral bound. The lemmas
`scaledBackgroundCutoffError_ae_small_of_remainder` and
`HasGGrowth.scaledBackground_error_argument_ae_le_local_bound` show that the normalized error
lies in a prescribed local boundedness ball when the affine remainder is sufficiently small.
`HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_upper_of_error_bound` integrates
the resulting pointwise estimate as an extended-valued inequality, and
`HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_lt_top` proves finite transition
energy from finite `∫ G (∇u)`, finite `G 0`, `G (θ • ξ)`, error bound `M`, and finite annulus
volume. This bound does not require measurability of `G ∘ ∇u`; when applying it to a measurable
representative, the existing almost-everywhere congruence transfers the integral. The pointwise
density bound for the contracted field is available conditionally, and
`mDirichletLimsup_vitali_density_le_Hp_of_cited` assembles its affine-remainder, energy-average,
and Vitali-density inputs almost everywhere for each fixed `0 < t < 1`, using cited interface
(b). The radial majorant is formalized, but constructing a recovery sequence and assembling the
final `GammaLimsup` bound remain open.
Earlier outer-cell and uncontracted-slope constructions remain in the file for comparison and
have not been removed. Alongside the
unchanged outer-cell construction, an inner-supported variant is available: it extends the
rescaled cell competitor by zero to the outer cube. The lemma
`variableCellCutoffCorrector_grad_annulus_ae` proves that its weak gradient vanishes almost
everywhere on the annulus. The inner trial energy
is exactly the rescaled cell energy, and finite cell infima have approximate competitors without
attainment. The contracted-slope variant `contractedVariableCellCutoffCorrector` has the same
admissibility and annular cancellation, with interior gradient `t • ξ + ∇w_cell` and annular
gradient `φ • (t • ξ) + (1-φ) • ∇u - E`. `affineRemainder_contract_slope_bound` isolates the
extra affine error `abs(1-t) ‖ξ‖ ‖y-x‖`; `HasGGrowth.cutoff_blend_upper` controls the blend before
subtracting `E` without dilating its two `G` arguments. Convexly separating `E` with weight δ,
however, rigorously requires `G ((1-δ)⁻¹ • X)` as well as `G (-E/δ)`; a local bound near zero
controls only the latter when `E/δ` is small. The former is not controlled by the current
hypotheses, so this variant also does not yet prove a variable-gradient density estimate. A
separate pointwise growth estimate on the annulus now uses weights `1/3,1/3,1/3`; it controls
the cutoff-error term by local finiteness of `G` near zero but leaves
`G (3 * φ * ξ)` and `G (3 * (1-φ) * ∇u)` explicit. Finiteness of the first requires control
along the segment to `3ξ`; the current hypotheses do not control the second from `G (∇u)` alone,
so this older three-weight construction does not prove the needed density estimate. Applying Vitali
to a `W1p` gradient also
requires `Measurable G`
and the explicit assumption `∫_Ω G(∇u) < ∞`; the latter does not follow from `W1p` alone for
general `G`. A recovery sequence and the final limit assembly remain to be formalized.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- The local Dirichlet value for Proposition 2.1(ii), with background gradient `D`. For
`D = ∇u`, this is the infimum of `Iε(u + φ; A)` over zero-extended `W^{1,p}_0(A)` correctors.
The project's `W1p0` definition consists of pairs whose function vanishes outside the open set and
whose globally defined weak gradient, together with the function, belongs to `MemLp`. This is the
usual zero-boundary Sobolev class on the regular domains considered in the paper; that
identification is not formalized here. On an arbitrary irregular open set this class can be larger
than the closure of smooth compactly supported functions. Values on irregular opens serve only as
auxiliary set-function inputs to subadditivity and Vitali. -/
noncomputable def mDirichlet (p : ℝ≥0∞) (W : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ)
    (D : Sp N → Mat m N) (A : Set (Sp N)) : ℝ≥0∞ :=
  ⨅ φg ∈ (W1p0 p A : Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
    ∫⁻ y in A, W (ε⁻¹ • y) (D y + φg.2 y)

/-- A measurable representative of the weak gradient of a `W1p` function. The representative is
defined on all of space and agrees with the weak gradient almost everywhere on the domain. -/
noncomputable def W1p.measurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) : Sp N → Mat m N :=
  u.memLp_grad.aestronglyMeasurable.mk u.grad

/-- The chosen measurable representative of a Sobolev gradient is measurable on the ambient
space. -/
theorem W1p.measurableGrad_measurable {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) : Measurable u.measurableGrad :=
  u.memLp_grad.aestronglyMeasurable.measurable_mk

/-- A Sobolev gradient and its chosen measurable representative agree almost everywhere on the
domain. -/
theorem W1p.grad_ae_measurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) : u.grad =ᵐ[volume.restrict Ω] u.measurableGrad :=
  u.memLp_grad.aestronglyMeasurable.ae_eq_mk

/-- Replacing the background gradient by an almost-everywhere equal field does not change a local
Dirichlet value on an open set. The statement uses only equality of the integrands almost
everywhere; no measurability of `W` is required. -/
theorem mDirichlet_congr_of_ae_on_open {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    {ε : ℝ} {D E : Sp N → Mat m N} {A Ω : Set (Sp N)} (hAo : IsOpen A)
    (hΩo : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hDE : D =ᵐ[volume.restrict Ω] E) :
    mDirichlet p W ε D A = mDirichlet p W ε E A := by
  have hglobal : ∀ᵐ y ∂volume, y ∈ Ω → D y = E y :=
    (ae_restrict_iff' hΩo.measurableSet).1 hDE
  unfold mDirichlet
  apply iInf_congr
  intro φg
  apply iInf_congr
  intro hφ
  apply setLIntegral_congr_fun_ae hAo.measurableSet
  filter_upwards [hglobal] with y hy
  intro hyA
  exact congrArg (fun ξ : Mat m N => W (ε⁻¹ • y) (ξ + φg.2 y)) (hy (hAΩ hyA))

/-- The Sobolev Dirichlet value is subadditive on two disjoint open pieces covering the domain
almost everywhere. This is `Ytp_sub` applied to the translated spatial integrand
`(y, ζ) ↦ W(y/ε, D(y) + ζ)`; its proof chooses correctors up to an arbitrary ENNReal error and
glues them in `W^{1,p}_0` using `W1p0.add` and weak-gradient locality. -/
theorem mDirichlet_le_add {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {W : Sp N → Mat m N → ℝ≥0∞} {ε : ℝ} {D : Sp N → Mat m N}
    {A B C : Set (Sp N)} (hAo : IsOpen A) (_hAb : Bornology.IsBounded A)
    (hBo : IsOpen B) (hCo : IsOpen C) (hBA : B ⊆ A) (hCA : C ⊆ A)
    (hBC : Disjoint B C) (hcover : volume (A \ (B ∪ C)) = 0) :
    mDirichlet p W ε D A ≤ mDirichlet p W ε D B + mDirichlet p W ε D C := by
  let W' : Sp N → Mat m N → ℝ≥0∞ := fun y ξ => W (ε⁻¹ • y) (D y + ξ)
  have h := Ytp_sub (p := p) (W := W') (ξ := (0 : Mat m N))
    hAo _hAb hBo hCo hBA hCA hBC hcover
  simpa [mDirichlet, Ytp, W'] using h

/-- Testing with the zero corrector bounds the Dirichlet value by the unperturbed energy. This
is the basic domination estimate before the growth hypothesis supplies an integrable density. -/
theorem mDirichlet_le_unperturbed {p : ℝ≥0∞} (W : Sp N → Mat m N → ℝ≥0∞)
    (ε : ℝ) (D : Sp N → Mat m N) (A : Set (Sp N)) :
    mDirichlet p W ε D A ≤ ∫⁻ y in A, W (ε⁻¹ • y) (D y) := by
  let W' : Sp N → Mat m N → ℝ≥0∞ := fun y ξ => W (ε⁻¹ • y) (D y + ξ)
  have h := Ytp_le_lintegral p W' A (0 : Mat m N)
  simpa [mDirichlet, Ytp, W'] using h

/-- A measurable finite-gradient-energy field supplies an integrable growth majorant for the
Dirichlet value. The finite-volume assumption controls the constant part of `β (1 + G(D))`; the
finite integral assumption controls its `G` part. -/
theorem mDirichlet_le_growthDensity {p : ℝ≥0∞} (G : Mat m N → ℝ≥0∞)
    (W : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ) (D : Sp N → Mat m N) (A : Set (Sp N))
    {α β : ℝ≥0} (hGrowth : HasGGrowth G α β W)
    (hGDmeas : Measurable (fun y => G (D y))) (hAvol : volume A < ⊤)
    (hGint : ∫⁻ y in A, G (D y) < ⊤) :
    mDirichlet p W ε D A ≤ ∫⁻ y in A, (β : ℝ≥0∞) * (1 + G (D y)) ∧
      ∫⁻ y in A, (β : ℝ≥0∞) * (1 + G (D y)) < ⊤ := by
  have hGgrad : AEMeasurable (fun y => G (D y)) (volume.restrict A) :=
    hGDmeas.aemeasurable
  have hsum : AEMeasurable (fun y => (1 : ℝ≥0∞) + G (D y)) (volume.restrict A) :=
    aemeasurable_const.add hGgrad
  have hfinite : ∫⁻ y in A, (β : ℝ≥0∞) * (1 + G (D y)) < ⊤ := by
    calc
      ∫⁻ y in A, (β : ℝ≥0∞) * (1 + G (D y)) =
          (β : ℝ≥0∞) * (volume A + ∫⁻ y in A, G (D y)) := by
        rw [lintegral_const_mul'' _ hsum, lintegral_add_right' _ hGgrad,
          setLIntegral_const]
        simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top
        (ENNReal.add_lt_top.2 ⟨hAvol, hGint⟩)
  refine ⟨(mDirichlet_le_unperturbed (p := p) W ε D A).trans ?_, hfinite⟩
  exact lintegral_mono fun y => (hGrowth (ε⁻¹ • y) (D y)).2

/-- The upper envelope of the local Dirichlet values as `ε → 0⁺`. -/
noncomputable def mDirichletLimsup (p : ℝ≥0∞) (W : Sp N → Mat m N → ℝ≥0∞)
    (D : Sp N → Mat m N) (A : Set (Sp N)) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => mDirichlet p W ε D A) (𝓝[>] 0)

/-- Scalar multiplication of a Sobolev pair. The weak-gradient field scales by the same scalar;
this is the background used below for the contracted-function construction. -/
noncomputable def W1p.smul {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) (t : ℝ) : W1p N m p Ω where
  toFun := t • u.toFun
  grad := t • u.grad
  memLp := u.memLp.const_smul t
  memLp_grad := u.memLp_grad.const_smul t
  weak := by
    intro ψ hψ hcs hsub v
    have h := u.weak ψ hψ hcs hsub v
    calc
      ∫ y, fderiv ℝ ψ y v • (t • u.toFun y) =
          t • ∫ y, fderiv ℝ ψ y v • u.toFun y := by
            rw [← integral_smul]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp only [smul_smul, mul_comm]
      _ = t • -∫ y, ψ y • u.grad y v := by rw [h]
      _ = -∫ y, ψ y • (t • u.grad y) v := by
            rw [smul_neg, ← integral_smul]
            congr 1
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp only [smul_apply, smul_smul, mul_comm]

/-- Rescale a zero-boundary cell competitor on the dilated cube back to the physical cube. This
is the inverse direction to `W1p0.rescale` and preserves the global weak-gradient definition of
`W1p0`. -/
theorem W1p0.rescale_back_cube {p : ℝ≥0∞} {ε ρ : ℝ} (hε : 0 < ε) (x : Sp N)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 p (cube (ρ / ε) (ε⁻¹ • x))) :
    ((fun y => ε • v.1 (ε⁻¹ • y)), (fun y => v.2 (ε⁻¹ • y))) ∈
      W1p0 p (cube ρ x) := by
  have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
  have h := W1p0.rescale hv hεinv.ne'
  rw [preimage_smul_cube hεinv] at h
  have hrad : (ρ / ε) / ε⁻¹ = ρ := by field_simp [hε.ne']
  have hcenter : ε • ε⁻¹ • x = x := smul_inv_smul₀ hε.ne' x
  simpa [hrad, hcenter, inv_inv] using h

/-- A zero-extended `W1p0` pair remains admissible when its open support is enlarged. The
function, global weak gradient, and their `MemLp` witnesses are unchanged; only the vanishing
outside condition needs to be transported along the set inclusion. -/
theorem W1p0.mono_of_subset {p : ℝ≥0∞} {U V : Set (Sp N)} {v :
    (Sp N → Tgt m) × (Sp N → Mat m N)} (hUV : U ⊆ V)
    (hv : v ∈ W1p0 p U) : v ∈ W1p0 p V := by
  rcases hv with ⟨hzero, hfun, hgrad, hweak⟩
  exact ⟨fun y hyV => hzero y (fun hyU => hyV (hUV hyU)), hfun, hgrad, hweak⟩

/-! ### Finite gluing of local Sobolev correctors -/

/-- The pointwise sum of a finite family of zero-extended correctors. -/
def finiteCubeCorrection {n : ℕ} (v : Fin n →
    (Sp N → Tgt m) × (Sp N → Mat m N)) :
    (Sp N → Tgt m) × (Sp N → Mat m N) :=
  ∑ i, v i

/-- A finite sum of zero-extended Sobolev correctors supported in `Ω` is again in
`W^{1,p}_0(Ω)`. This is the admissibility part of finite gluing; disjointness is only needed for
the piecewise gradient and energy formulas below. -/
theorem W1p0.finite_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (Sp N)} {n : ℕ}
    {v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hn : 0 < n) (hv : ∀ i, v i ∈ W1p0 p Ω) :
    finiteCubeCorrection v ∈ W1p0 p Ω := by
  classical
  have hsum : ∀ s : Finset (Fin n), s.Nonempty → s.sum v ∈ W1p0 p Ω := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        rcases hs with ⟨i, hi⟩
        simp at hi
    | @insert i s his ih =>
        by_cases hne : s.Nonempty
        · rw [Finset.sum_insert his]
          exact W1p0.add (A := Ω) (B := Ω) (C := Ω)
            (subset_rfl : Ω ⊆ Ω) (subset_rfl : Ω ⊆ Ω) (hv i) (ih hne)
        · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          subst s
          simpa using hv i
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  simpa [finiteCubeCorrection] using hsum Finset.univ huniv

/-- On one cube, all the other gradients in a finite disjoint family vanish almost everywhere.
This uses distributional locality of the weak gradient, not pointwise differentiation of the
zero extensions. -/
theorem finiteCubeCorrectionGrad_ae_eq_on {p : ℝ≥0∞} [Fact (1 ≤ p)] {n : ℕ}
    {Q : Fin n → Set (Sp N)} {v : Fin n →
      (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hQo : ∀ i, IsOpen (Q i))
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hv : ∀ i, v i ∈ W1p0 p (Q i)) (i : Fin n) :
    (fun y => (finiteCubeCorrection v).2 y) =ᵐ[volume.restrict (Q i)] (v i).2 := by
  classical
  have hzero : ∀ j, j ≠ i →
      ∀ᵐ y ∂(volume.restrict (Q i)), (v j).2 y = 0 := by
    intro j hji
    have hfun : (v j).1 =ᵐ[volume.restrict (Q i)] 0 := by
      apply (ae_restrict_iff' (hQo i).measurableSet).2
      exact ae_of_all _ fun y hy => (hv j).1 y (fun hyj =>
        (Set.disjoint_left.mp (hQd hji)) hyj hy)
    have hglobal := HasWeakGrad.eq_zero_on_open (hQo i) hfun
      (hv j).2.2.1 (hv j).2.2.2
    exact (ae_restrict_iff' (hQo i).measurableSet).2 hglobal
  have hall : ∀ᵐ y ∂(volume.restrict (Q i)),
      ∀ j, j ≠ i → (v j).2 y = 0 := by
    apply ae_all_iff.2
    intro j
    by_cases hji : j = i
    · subst j
      exact ae_of_all _ fun y h => (h rfl).elim
    · exact (hzero j hji).mono fun y hy hne => hy
  filter_upwards [hall] with y hy
  simp only [finiteCubeCorrection, Prod.snd_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by
    intro j hj hji
    exact hy j hji)]

/-- Off the union of finitely many cubes, the correction gradient vanishes almost everywhere.
Each individual assertion follows from `W1p0.ae_grad_eq_zero_off`, using the null frontier of a
cube. -/
theorem finiteCubeCorrectionGrad_ae_eq_zero_off {p : ℝ≥0∞} [Fact (1 ≤ p)] {n : ℕ}
    {Q : Fin n → Set (Sp N)} {v : Fin n →
      (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hQo : ∀ i, IsOpen (Q i)) (hQf : ∀ i, volume (frontier (Q i)) = 0)
    (hv : ∀ i, v i ∈ W1p0 p (Q i)) :
    ∀ᵐ y, y ∉ ⋃ i, Q i → (finiteCubeCorrection v).2 y = 0 := by
  classical
  have hall : ∀ᵐ y, ∀ i, y ∉ Q i → (v i).2 y = 0 := by
    apply ae_all_iff.2
    intro i
    exact W1p0.ae_grad_eq_zero_off (hQo i) (hQf i) (hv i)
  filter_upwards [hall] with y hy hyU
  simp only [finiteCubeCorrection, Prod.snd_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact hy i (fun h => hyU (mem_iUnion.2 ⟨i, h⟩))

/-- Adding the finite glued correction to a Sobolev background gives an admissible `W1p` map.
The returned map records the sum formulas for its function and weak gradient. -/
theorem W1p.add_finiteCubeCorrection {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (Sp N)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : W1p N m p Ω) {n : ℕ}
    {Q : Fin n → Set (Sp N)} {v : Fin n →
      (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hQΩ : ∀ i, Q i ⊆ Ω) (hv : ∀ i, v i ∈ W1p0 p (Q i)) :
    ∃ ψ : W1p N m p Ω,
      ψ.toFun = u.toFun + (finiteCubeCorrection v).1 ∧
      ψ.grad = u.grad + (finiteCubeCorrection v).2 := by
  by_cases hn : n = 0
  · subst n
    exact ⟨u, by simp [finiteCubeCorrection], by simp [finiteCubeCorrection]⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let z := finiteCubeCorrection v
    have hzΩ : z ∈ W1p0 p Ω := W1p0.finite_sum hnpos
      (fun i => W1p0.mono_of_subset (hQΩ i) (hv i))
    have hzweak : HasWeakGrad Ω z.1 z.2 := by
      intro ψ hψ hcs hsub w
      exact hzΩ.2.2.2 ψ hψ hcs (hsub.trans (subset_univ Ω)) w
    let ψ : W1p N m p Ω :=
      { toFun := u.toFun + z.1
        grad := u.grad + z.2
        memLp := memLp_add' u.memLp (hzΩ.2.1.restrict Ω)
        memLp_grad := memLp_add' u.memLp_grad (hzΩ.2.2.1.restrict Ω)
        weak := HasWeakGrad.add hΩo hΩb u.memLp u.memLp_grad
          (hzΩ.2.1.restrict Ω) (hzΩ.2.2.1.restrict Ω) u.weak hzweak }
    exact ⟨ψ, rfl, rfl⟩

/-- The gradient of the finite glued perturbation has the expected local values almost everywhere:
inside `Q i` it is the gradient of the `i`th corrector, and outside all cubes it is zero. -/
theorem W1p.add_finiteCubeCorrection_grad_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (Sp N)}
    {n : ℕ} (u : W1p N m p Ω) {Q : Fin n → Set (Sp N)}
    {v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hQo : ∀ i, IsOpen (Q i))
    (hQf : ∀ i, volume (frontier (Q i)) = 0)
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hv : ∀ i, v i ∈ W1p0 p (Q i)) :
    (∀ i, ∀ᵐ y ∂(volume.restrict (Q i)),
      (u.grad y + (finiteCubeCorrection v).2 y) = u.grad y + (v i).2 y) ∧
    (∀ᵐ y, y ∉ ⋃ i, Q i →
      u.grad y + (finiteCubeCorrection v).2 y = u.grad y) := by
  refine ⟨?_, ?_⟩
  · intro i
    filter_upwards [finiteCubeCorrectionGrad_ae_eq_on hQo hQd hv i] with y hy
    rw [hy]
  · filter_upwards [finiteCubeCorrectionGrad_ae_eq_zero_off hQo hQf hv] with y hy
    intro hyU
    rw [hy hyU]
    simp

/-- Exact energy decomposition for a finite gluing. On each cube the other correctors have zero
weak gradient almost everywhere; on the uncovered part of `Ω` every corrector gradient vanishes.
The last integral is the energy of the unchanged background on the remainder. No covering
assumption is hidden: if the cubes do not cover `Ω` a.e., this remainder must be controlled. -/
theorem W1p.add_finiteCubeCorrection_energy_eq {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Set (Sp N)} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : W1p N m p Ω) {n : ℕ} {Q : Fin n → Set (Sp N)}
    {v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hQo : ∀ i, IsOpen (Q i)) (hQΩ : ∀ i, Q i ⊆ Ω)
    (hQf : ∀ i, volume (frontier (Q i)) = 0)
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hv : ∀ i, v i ∈ W1p0 p (Q i))
    (L : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ) :
    ∃ ψ : W1p N m p Ω,
      ψ.toFun = u.toFun + (finiteCubeCorrection v).1 ∧
      ψ.grad = u.grad + (finiteCubeCorrection v).2 ∧
      intFun L ε ψ =
        (∑ i, ∫⁻ y in Q i, L (ε⁻¹ • y) (u.grad y + (v i).2 y)) +
          ∫⁻ y in Ω \ (⋃ i, Q i), L (ε⁻¹ • y) (u.grad y) := by
  obtain ⟨ψ, hψfun, hψgrad⟩ :=
    W1p.add_finiteCubeCorrection hΩo hΩb u hQΩ hv
  have hgrad := W1p.add_finiteCubeCorrection_grad_ae u hQo hQf hQd hv
  let U : Set (Sp N) := ⋃ i, Q i
  let R : Set (Sp N) := Ω \ U
  have hUmeas : MeasurableSet U := (isOpen_iUnion hQo).measurableSet
  have hRmeas : MeasurableSet R := hΩo.measurableSet.diff hUmeas
  have hUΩ : U ⊆ Ω := iUnion_subset hQΩ
  have hdecomp : Ω = U ∪ R := by
    ext y
    constructor
    · intro hyΩ
      by_cases hyU : y ∈ U
      · exact Or.inl hyU
      · exact Or.inr ⟨hyΩ, hyU⟩
    · intro hy
      rcases hy with hyU | ⟨hyΩ, _⟩
      · exact hUΩ hyU
      · exact hyΩ
  have hdisj : Disjoint U R := by
    apply Set.disjoint_left.mpr
    intro y hyU hyR
    exact hyR.2 hyU
  have hlocal : ∀ i,
      ψ.grad =ᵐ[volume.restrict (Q i)]
        (fun y => u.grad y + (v i).2 y) := by
    intro i
    rw [hψgrad]
    exact hgrad.1 i
  have hrest' : (u.grad + (finiteCubeCorrection v).2) =ᵐ[volume.restrict R] u.grad := by
    apply (ae_restrict_iff' hRmeas).2
    filter_upwards [hgrad.2] with y hy hyR
    exact hy (fun hyU => hyR.2 hyU)
  have hrest : ψ.grad =ᵐ[volume.restrict R] u.grad := by
    simpa only [hψgrad] using hrest'
  have hlocalEnergy : ∀ i,
      (∫⁻ y in Q i, L (ε⁻¹ • y) (ψ.grad y)) =
        ∫⁻ y in Q i, L (ε⁻¹ • y) (u.grad y + (v i).2 y) := by
    intro i
    apply lintegral_congr_ae
    filter_upwards [hlocal i] with y hy
    rw [hy]
  have hrestEnergy :
      (∫⁻ y in R, L (ε⁻¹ • y) (ψ.grad y)) =
        ∫⁻ y in R, L (ε⁻¹ • y) (u.grad y) := by
    apply lintegral_congr_ae
    filter_upwards [hrest] with y hy
    rw [hy]
  have hpieces :
      (∫⁻ y in U, L (ε⁻¹ • y) (ψ.grad y)) =
        ∑ i, ∫⁻ y in Q i, L (ε⁻¹ • y) (ψ.grad y) := by
    exact lintegral_eq_sum_pieces_fintype hQo (fun i => subset_iUnion Q i)
      hQd (by simp) (fun y => L (ε⁻¹ • y) (ψ.grad y))
  refine ⟨ψ, hψfun, hψgrad, ?_⟩
  change (∫⁻ y in Ω, L (ε⁻¹ • y) (ψ.grad y)) = _
  calc
    (∫⁻ y in Ω, L (ε⁻¹ • y) (ψ.grad y)) =
        ∫⁻ y in U ∪ R, L (ε⁻¹ • y) (ψ.grad y) :=
      congrArg (fun A : Set (Sp N) => ∫⁻ y in A, L (ε⁻¹ • y) (ψ.grad y)) hdecomp
    _ = (∫⁻ y in U, L (ε⁻¹ • y) (ψ.grad y)) +
        ∫⁻ y in R, L (ε⁻¹ • y) (ψ.grad y) := lintegral_union hRmeas hdisj
    _ = (∑ i, ∫⁻ y in Q i, L (ε⁻¹ • y) (u.grad y + (v i).2 y)) +
        ∫⁻ y in R, L (ε⁻¹ • y) (u.grad y) := by
      rw [hpieces, hrestEnergy]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hlocalEnergy i

/-- Poincaré for a finite disjoint gluing of Lipschitz `W1p0` cube correctors, measured on the
union of their cubes. This is the global Lᵖ estimate used for finite recovery corrections. The
only Poincaré input is `poincare_cube`; the pointwise derivatives must agree a.e. with the weak
gradients in the `W1p0` pairs. -/
theorem finiteW1p0_lipschitz_cube_correction_poincare [NeZero N] {n : ℕ} {p R : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (ρ : Fin n → ℝ) (x : Fin n → Sp N)
    (hρR : ∀ i, ρ i ≤ R)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i)))
    (K : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (K i) (v i).1)
    (hgrad : ∀ i, (fun y => fderiv ℝ (v i).1 y) =ᵐ[volume] (v i).2)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j))) :
    let U : Set (Sp N) := ⋃ i, cube (ρ i) (x i)
    ∫⁻ y in U, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
      (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
        ∫⁻ y in U, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
  classical
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 (Fact.out : 1 ≤ ENNReal.ofReal p)
  let Q : Fin n → Set (Sp N) := fun i => cube (ρ i) (x i)
  let U : Set (Sp N) := ⋃ i, Q i
  have hQo : ∀ i, IsOpen (Q i) := fun i => isOpen_cube _ _
  have hpieces {F : Sp N → ℝ≥0∞} :
      ∫⁻ y in U, F y = ∑ i, ∫⁻ y in Q i, F y := by
    apply lintegral_eq_sum_pieces_fintype hQo (fun i => subset_iUnion Q i) hQd ?_ F
    simp [Q]
  have hfun_local : ∀ i y, y ∈ Q i → (finiteCubeCorrection v).1 y = (v i).1 y := by
    intro i y hy
    simp only [finiteCubeCorrection, Prod.fst_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · intro j hj hji
      have hyj : y ∉ Q j := fun hmem => (Set.disjoint_left.mp (hQd hji)) hmem hy
      exact (hv j).1 y hyj
  have hgrad_local := fun i =>
    finiteCubeCorrectionGrad_ae_eq_on hQo hQd hv i
  have hp0 : 0 < p := by linarith
  have hlocal_est : ∀ i,
      (∫⁻ y in Q i, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) ≤
        (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
    intro i
    have hfun : (∫⁻ y in Q i, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) =
        ∫⁻ y in Q i, ‖(v i).1 y‖ₑ ^ p := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hQo i).measurableSet] with y hy
      exact congrArg (fun z : Tgt m => ‖z‖ₑ ^ p) (hfun_local i y hy)
    have hgrad' : (∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p) =
        ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := by
      apply lintegral_congr_ae
      filter_upwards [hgrad_local i] with y hy
      exact congrArg (fun z : Mat m N => ‖z‖ₑ ^ p) hy
    rw [hfun, hgrad']
    have hφall : ∫⁻ y, ‖(v i).1 y‖ₑ ^ p =
        ∫⁻ y in Q i, ‖(v i).1 y‖ₑ ^ p := by
      rw [← lintegral_indicator (hQo i).measurableSet]
      apply lintegral_congr_ae
      filter_upwards [] with y
      by_cases hmem : y ∈ Q i
      · simp [hmem]
      · simpa [hmem, (hv i).1 y hmem] using
          (ENNReal.zero_rpow_of_pos hp0 : (0 : ℝ≥0∞) ^ p = 0)
    have hdergrad : ∫⁻ y, ‖fderiv ℝ (v i).1 y‖ₑ ^ p =
        ∫⁻ y, ‖(v i).2 y‖ₑ ^ p := by
      apply lintegral_congr_ae
      exact (hgrad i).mono fun y hy => by simp [hy]
    have hgradall : ∫⁻ y, ‖(v i).2 y‖ₑ ^ p =
        ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := by
      rw [← lintegral_indicator (hQo i).measurableSet]
      apply lintegral_congr_ae
      have hoff := W1p0.ae_grad_eq_zero_off (hQo i) (volume_frontier_cube _ _) (hv i)
      filter_upwards [hoff] with y hy
      by_cases hmem : y ∈ Q i
      · simp [hmem]
      · rw [hy hmem]
        rw [indicator_of_notMem hmem]
        simp only [enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero]
        exact ENNReal.zero_rpow_of_pos hp0
    have hP := poincare_cube hp (hLip i) (fun y hy => (hv i).1 y hy)
    rw [hφall, hdergrad, hgradall] at hP
    calc ∫⁻ y in Q i, ‖(v i).1 y‖ₑ ^ p ≤
          (m : ℝ≥0∞) * ENNReal.ofReal (ρ i) ^ p *
            ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := hP
      _ ≤ (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
            ∫⁻ y in Q i, ‖(v i).2 y‖ₑ ^ p := by
          gcongr
          exact hρR i
  change (∫⁻ y in U, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) ≤
    (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
      ∫⁻ y in U, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p
  rw [hpieces, hpieces]
  calc
    (∑ i, ∫⁻ y in Q i, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) ≤
        ∑ i, ((m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p) :=
      Finset.sum_le_sum fun i hi => hlocal_est i
    _ = (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          ∑ i, ∫⁻ y in Q i, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
      rw [Finset.mul_sum]

/-- On a cube, the weak gradient in a `W1p0` pair agrees almost everywhere with the pointwise
derivative whenever its function component is globally Lipschitz. The derivative is in `Lᵖ`
because the function vanishes off a bounded cube, so its derivative has compact support and is
bounded. Uniqueness then follows from `HasWeakGrad.eq_zero_on_open` on the whole space. -/
theorem W1p0.lipschitz_fderiv_eq_grad_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] {ρ : ℝ} {x : Sp N}
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 p (cube ρ x)) {K : ℝ≥0} (hLip : LipschitzWith K v.1) :
    (fun y => fderiv ℝ v.1 y) =ᵐ[volume] v.2 := by
  have hcs : HasCompactSupport v.1 :=
    HasCompactSupport.intro (isBounded_cube ρ x).isCompact_closure fun y hy =>
      hv.1 y (fun hyQ => hy (subset_closure hyQ))
  have hDfLp : MemLp (fderiv ℝ v.1) p volume :=
    (hcs.fderiv (𝕜 := ℝ)).memLp_of_bound
      (measurable_fderiv ℝ v.1).aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hLip)
  have hneg : HasWeakGrad univ (fun y => -v.1 y) (fun y => -(fderiv ℝ v.1 y)) := by
    intro ψ hψ hψc hψs w
    have h := LipschitzWith.hasWeakGrad hLip univ ψ hψ hψc hψs w
    calc
      (∫ y, fderiv ℝ ψ y w • -v.1 y) =
          -(∫ y, fderiv ℝ ψ y w • v.1 y) := by
            rw [show (fun y => fderiv ℝ ψ y w • -v.1 y) =
              fun y => -(fderiv ℝ ψ y w • v.1 y) by funext y; simp, integral_neg]
      _ = -(-∫ y, ψ y • fderiv ℝ v.1 y w) := congrArg Neg.neg h
      _ = -∫ y, ψ y • -(fderiv ℝ v.1 y) w := by
        simp [smul_neg, integral_neg]
  have hzero : HasWeakGrad univ (fun _ : Sp N => (0 : Tgt m))
      (fun y => v.2 y - fderiv ℝ v.1 y) := by
    have hsum := HasWeakGrad.add_univ hv.2.1 hv.2.2.1
      ((hv.2.1).neg) hDfLp.neg hv.2.2.2 hneg
    convert hsum using 1 <;> ext y <;> simp [sub_eq_add_neg]
  have hgradZero := HasWeakGrad.eq_zero_on_open (isOpen_univ : IsOpen (univ : Set (Sp N)))
    (show (fun _ : Sp N => (0 : Tgt m)) =ᵐ[volume.restrict (univ : Set (Sp N))] 0 from
      ae_of_all _ fun _ => rfl) (hv.2.2.1.sub hDfLp) hzero
  filter_upwards [hgradZero] with y hy
  exact (sub_eq_zero.mp (hy (Set.mem_univ y))).symm

/-- Finite-union cube Poincaré for disjoint `W1p0` correctors whose function components are
Lipschitz. The weak-gradient identification is derived by `W1p0.lipschitz_fderiv_eq_grad_ae`, so
callers do not need to supply it separately. This still requires Lipschitz representatives; it
does not yet cover arbitrary `W1p0` pairs. -/
theorem finiteW1p0_lipschitz_cube_correction_poincare_of_lipschitz [NeZero N]
    {n : ℕ} {p R : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (ρ : Fin n → ℝ)
    (x : Fin n → Sp N) (hρR : ∀ i, ρ i ≤ R)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i)))
    (K : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (K i) (v i).1)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j))) :
    let U : Set (Sp N) := ⋃ i, cube (ρ i) (x i)
    ∫⁻ y in U, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
      (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
        ∫⁻ y in U, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
  apply finiteW1p0_lipschitz_cube_correction_poincare ρ x hρR v hv K hLip
    (fun i => W1p0.lipschitz_fderiv_eq_grad_ae (hv i) (hLip i)) hQd

/-- For a finite family of `W1p0` cube correctors, the global extended `Lᵖ` integrals of the
correction and its weak gradient equal their integrals over the union of the cubes. The function
vanishes there pointwise off the union, and the gradient vanishes almost everywhere off it. -/
theorem finiteCubeCorrection_lintegral_eq_on_union {n : ℕ} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (ρ : Fin n → ℝ) (x : Fin n → Sp N)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i))) :
    (∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) =
        ∫⁻ y in (⋃ i, cube (ρ i) (x i)), ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ∧
      (∫⁻ y, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p) =
        ∫⁻ y in (⋃ i, cube (ρ i) (x i)), ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
  classical
  let Q : Fin n → Set (Sp N) := fun i => cube (ρ i) (x i)
  let U : Set (Sp N) := ⋃ i, Q i
  have hp0 : 0 < p := by
    have hp := ENNReal.one_le_ofReal.1 (Fact.out : 1 ≤ ENNReal.ofReal p)
    linarith
  have hUmeas : MeasurableSet U := (isOpen_iUnion fun i => isOpen_cube _ _).measurableSet
  have hfun_zero : ∀ y, y ∉ U → (finiteCubeCorrection v).1 y = 0 := by
    intro y hy
    simp only [finiteCubeCorrection, Prod.fst_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hv i).1 y (fun h => hy (mem_iUnion.2 ⟨i, by simpa [Q] using h⟩))
  have hgrad_zero := finiteCubeCorrectionGrad_ae_eq_zero_off
    (fun i => isOpen_cube _ _) (fun i => volume_frontier_cube _ _) hv
  have hfun_integral :
      (∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p) =
        ∫⁻ y in U, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p := by
    rw [← lintegral_indicator hUmeas]
    apply lintegral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, hfun_zero y hy, ENNReal.zero_rpow_of_pos hp0]
  have hgrad_integral :
      (∫⁻ y, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p) =
        ∫⁻ y in U, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
    rw [← lintegral_indicator hUmeas]
    apply lintegral_congr_ae
    filter_upwards [hgrad_zero] with y hy
    by_cases hmem : y ∈ U
    · simp [hmem]
    · rw [indicator_of_notMem hmem, hy hmem]
      rw [enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero]
      exact ENNReal.zero_rpow_of_pos hp0
  exact ⟨hfun_integral, hgrad_integral⟩

/-- Global finite-union Poincaré estimate for the Lipschitz pieces, assuming explicitly that each
pointwise derivative agrees almost everywhere with the given weak gradient. For correctors whose
function components are globally Lipschitz, use
`finiteW1p0_lipschitz_cube_correction_global_poincare_of_lipschitz`, which derives this equality
from `W1p0.lipschitz_fderiv_eq_grad_ae`. -/
theorem finiteW1p0_lipschitz_cube_correction_global_poincare [NeZero N] {n : ℕ}
    {p R : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (ρ : Fin n → ℝ) (x : Fin n → Sp N)
    (hρR : ∀ i, ρ i ≤ R)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i)))
    (K : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (K i) (v i).1)
    (hgrad : ∀ i, (fun y => fderiv ℝ (v i).1 y) =ᵐ[volume] (v i).2)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j))) :
    ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
      (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
        ∫⁻ y, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
  have hEq := finiteCubeCorrection_lintegral_eq_on_union ρ x v hv
  rw [hEq.1, hEq.2]
  exact finiteW1p0_lipschitz_cube_correction_poincare
    ρ x hρR v hv K hLip hgrad hQd

/-- Global finite-union Poincaré estimate for disjoint cube correctors in `W1p0` whose function
components are globally Lipschitz. The pointwise derivatives are identified with the given weak
gradients by `W1p0.lipschitz_fderiv_eq_grad_ae`, and the global integrals reduce to the cube union.
This does not extend the estimate to arbitrary `W1p0` pairs without an approximation theorem. -/
theorem finiteW1p0_lipschitz_cube_correction_global_poincare_of_lipschitz [NeZero N]
    {n : ℕ} {p R : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (ρ : Fin n → ℝ)
    (x : Fin n → Sp N) (hρR : ∀ i, ρ i ≤ R)
    (v : Fin n → (Sp N → Tgt m) × (Sp N → Mat m N))
    (hv : ∀ i, v i ∈ W1p0 (ENNReal.ofReal p) (cube (ρ i) (x i)))
    (K : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (K i) (v i).1)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j))) :
    ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p ≤
      (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
        ∫⁻ y, ‖(finiteCubeCorrection v).2 y‖ₑ ^ p := by
  exact finiteW1p0_lipschitz_cube_correction_global_poincare
    ρ x hρR v hv K hLip
    (fun i => W1p0.lipschitz_fderiv_eq_grad_ae (hv i) (hLip i)) hQd

/-- A cell competitor gives a physical-domain competitor with exactly the rescaled energy when
the background gradient is constant. This is the trial-function direction needed for an upper
bound on `mDirichlet`; `Ytp_rescale_le` supplies the opposite comparison. -/
theorem mDirichlet_le_rescaled_cell_competitor {p : ℝ≥0∞}
    (W : Sp N → Mat m N → ℝ≥0∞) {ε ρ : ℝ} (hε : 0 < ε) (x : Sp N)
    (ξ : Mat m N) {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 p (cube (ρ / ε) (ε⁻¹ • x))) :
    mDirichlet p W ε (fun _ => ξ) (cube ρ x) ≤
      ENNReal.ofReal (ε ^ N) * ∫⁻ y in cube (ρ / ε) (ε⁻¹ • x), W y (ξ + v.2 y) := by
  have hback := W1p0.rescale_back_cube hε x hv
  have hchange := setLIntegral_rescale_energy W hε x ξ
    (fun y => v.2 (ε⁻¹ • y)) (ρ := ρ)
  calc
    mDirichlet p W ε (fun _ => ξ) (cube ρ x) ≤
        ∫⁻ y in cube ρ x,
          W (ε⁻¹ • y) (ξ + v.2 (ε⁻¹ • y)) := by
            change (⨅ φg ∈ (W1p0 p (cube ρ x) :
              Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
              ∫⁻ y in cube ρ x, W (ε⁻¹ • y) (ξ + φg.2 y)) ≤ _
            exact iInf₂_le _ hback
    _ = ENNReal.ofReal (ε ^ N) *
        ∫⁻ y in cube (ρ / ε) (ε⁻¹ • x), W y (ξ + v.2 y) := by
          simpa only [inv_smul_smul₀ hε.ne'] using hchange

/-- For a constant background gradient, the local Dirichlet infimum is bounded above by the
rescaled Sobolev cell problem. The proof uses an actual rescaled cell competitor; it does not
assume attainment of either infimum. -/
theorem mDirichlet_le_rescaled_Ytp_of_const {p : ℝ≥0∞}
    (W : Sp N → Mat m N → ℝ≥0∞) {ε ρ : ℝ} (hε : 0 < ε) (x : Sp N)
    (ξ : Mat m N) :
    mDirichlet p W ε (fun _ => ξ) (cube ρ x) ≤
      ENNReal.ofReal (ε ^ N) * Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ := by
  have hc0 : ENNReal.ofReal (ε ^ N) ≠ 0 := by simp [hε, pow_pos]
  have hct : ENNReal.ofReal (ε ^ N) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [Ytp]
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  simp only [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf₂ (α := ℝ≥0∞) fun v hv => ?_
  exact mDirichlet_le_rescaled_cell_competitor W hε x ξ hv

/-- For a constant background gradient, the centered-cube density of the limsup Dirichlet value
is bounded by the homogenized Sobolev cell integrand. This is the flat-field case of the local
density comparison; it does not yet handle a variable weak gradient. -/
theorem mDirichletLimsup_le_Hp_of_const {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {G : Mat m N → ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞} {β : ℝ≥0}
    (hW : IsPeriodic W) (hGrowth : ∀ y ζ, W y ζ ≤ β * (1 + G ζ))
    {ξ : Mat m N} (hξ : G ξ ≠ ⊤) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    mDirichletLimsup p W (fun _ => ξ) (cube ρ x) / volume (cube ρ x) ≤ Hp p W ξ := by
  let F : Filter ℝ := 𝓝[>] 0
  let V : ℝ≥0∞ := volume (cube ρ x)
  have hV0 : V ≠ 0 := by
    change volume (cube ρ x) ≠ 0
    rw [volume_cube]
    exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr hρ).ne'
  have hVtop : V ≠ ⊤ := by
    change volume (cube ρ x) ≠ ⊤
    rw [volume_cube]
    exact ENNReal.pow_ne_top (ENNReal.ofReal_ne_top)
  have hlimsup :
      mDirichletLimsup p W (fun _ => ξ) (cube ρ x) ≤ V * Hp p W ξ := by
    have hpoint : ∀ᶠ ε in F,
        mDirichlet p W ε (fun _ => ξ) (cube ρ x) ≤ V *
          (Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ /
            volume (cube (ρ / ε) (ε⁻¹ • x))) := by
      filter_upwards [eventually_mem_nhdsWithin] with ε hεmem
      have hε : 0 < ε := by simpa using hεmem
      let Vcell : ℝ≥0∞ := volume (cube (ρ / ε) (ε⁻¹ • x))
      have hVcell0 : Vcell ≠ 0 := by
        change volume (cube (ρ / ε) (ε⁻¹ • x)) ≠ 0
        rw [volume_cube]
        exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (div_pos hρ hε)).ne'
      have hVcelltop : Vcell ≠ ⊤ := by
        change volume (cube (ρ / ε) (ε⁻¹ • x)) ≠ ⊤
        rw [volume_cube]
        exact ENNReal.pow_ne_top (ENNReal.ofReal_ne_top)
      have hc0 : ENNReal.ofReal (ε ^ N) ≠ 0 := by simp [hε, pow_pos]
      have hct : ENNReal.ofReal (ε ^ N) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hvol : V = ENNReal.ofReal (ε ^ N) * Vcell := by
        change volume (cube ρ x) = ENNReal.ofReal (ε ^ N) *
          volume (cube (ρ / ε) (ε⁻¹ • x))
        rw [volume_cube, volume_cube, ENNReal.ofReal_pow hε.le, ← mul_pow,
          ← ENNReal.ofReal_mul hε.le]
        congr 1
        field_simp [hε.ne']
      have hscale : ENNReal.ofReal (ε ^ N) *
          Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ = V *
            (Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ / Vcell) := by
        calc
          ENNReal.ofReal (ε ^ N) *
              Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ =
              ENNReal.ofReal (ε ^ N) *
                (Vcell * (Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ / Vcell)) := by
                  rw [ENNReal.mul_div_cancel hVcell0 hVcelltop]
          _ = (ENNReal.ofReal (ε ^ N) * Vcell) *
                (Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ / Vcell) := by ac_rfl
          _ = V * (Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ / Vcell) := by rw [← hvol]
      exact (mDirichlet_le_rescaled_Ytp_of_const W hε x ξ).trans_eq hscale
    let R : ℝ → ℝ≥0∞ := fun ε => V *
      (Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ /
        volume (cube (ρ / ε) (ε⁻¹ • x)))
    have hcell := Ytp_tendsto_Hp (p := p) (W := W) hW hGrowth hξ hρ x
    calc
      mDirichletLimsup p W (fun _ => ξ) (cube ρ x) ≤
          limsup R F :=
        limsup_le_limsup hpoint (by isBoundedDefault) (by isBoundedDefault)
      _ = V * Hp p W ξ := by
        have hscaled : Tendsto R F (𝓝 (V * Hp p W ξ)) :=
          ENNReal.Tendsto.const_mul (a := V) hcell (Or.inr hVtop)
        exact hscaled.limsup_eq
  change mDirichletLimsup p W (fun _ => ξ) (cube ρ x) / V ≤ Hp p W ξ
  calc
    mDirichletLimsup p W (fun _ => ξ) (cube ρ x) / V ≤ (V * Hp p W ξ) / V :=
      ENNReal.div_le_div_right hlimsup V
    _ = Hp p W ξ := by rw [mul_comm V, ENNReal.mul_div_cancel_right hV0 hVtop]

/-! ### A variable-background trial function at one cube -/

/-- The physical `W1p0` correction obtained by adding a rescaled cell corrector to the negative
cut-off correction of `u - ℓ`. Here `ℓ(y) = a + ξ (y - x)`. Its gradient is defined globally,
as required by this project's `W1p0` structure. -/
noncomputable def variableCellCutoffCorrector {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m)
    (ξ : Mat m N) (x : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ρ ε : ℝ) (v : (Sp N → Tgt m) × (Sp N → Mat m N)) :
    (Sp N → Tgt m) × (Sp N → Mat m N) :=
  (fun y => ε • v.1 (ε⁻¹ • y), fun y => v.2 (ε⁻¹ • y)) +
    (-1 : ℝ) •
      (fun y => cutoff hs ρ x y • (u.toFun y - affineMap a ξ x y),
       fun y => cutoff hs ρ x y • (u.grad y - ξ) +
         (fderiv ℝ (cutoff hs ρ x) y).smulRight
           (u.toFun y - affineMap a ξ x y))

/-- The inner-supported cutoff corrector with the affine reference slope contracted from `ξ` to
`t • ξ`. This is a separate wrapper around the existing construction; the original corrector and
its callers are unchanged. -/
noncomputable def contractedVariableCellCutoffCorrector {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N)
    (x : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (t ρ ε : ℝ) (v : (Sp N → Tgt m) × (Sp N → Mat m N)) :
    (Sp N → Tgt m) × (Sp N → Mat m N) :=
  variableCellCutoffCorrector u a (t • ξ) x hs ρ ε v

/-- Inner-cell correction for the background function `t • u`, so that both its weak gradient and
its affine reference are contracted by the same factor. -/
noncomputable def scaledBackgroundCellCutoffCorrector {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N)
    (x : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (t ρ ε : ℝ) (v : (Sp N → Tgt m) × (Sp N → Mat m N)) :
    (Sp N → Tgt m) × (Sp N → Mat m N) :=
  variableCellCutoffCorrector (W1p.smul u t) (t • a) (t • ξ) x hs ρ ε v

/-- Affine maps commute with the simultaneous scalar contraction of their value and slope. -/
theorem affineMap_smul_data (a : Tgt m) (ξ : Mat m N) (x y : Sp N) (t : ℝ) :
    affineMap (t • a) (t • ξ) x y = t • affineMap a ξ x y := by
  simp [affineMap]

/-- Every Sobolev cell competitor on the dilated cube produces an admissible physical correction.
The proof uses `W1p0.rescale_back_cube`, the product-rule cutoff in `Cutoff.lean`, scalar closure,
and addition in `W1p0`. No infimum is assumed to be attained. -/
theorem variableCellCutoffCorrector_mem_W1p0 {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p) (cube (ρ / ε) (ε⁻¹ • x))) :
    variableCellCutoffCorrector u a ξ x hs ρ ε v ∈
      W1p0 (ENNReal.ofReal p) (cube ρ x) := by
  have hcell := W1p0.rescale_back_cube hε x hv
  have hcut := cutoff_sub_affine_mem_W1p0 hΩopen hΩbounded u a ξ x hs hρ x hball
  have hcutNeg := W1p0.smul hcut (-1 : ℝ)
  have hsum := W1p0.add (A := cube ρ x) (B := cube ρ x) (C := cube ρ x)
    subset_rfl subset_rfl hcell hcutNeg
  simpa [variableCellCutoffCorrector] using hsum

/-- Variant of `variableCellCutoffCorrector_mem_W1p0` with the cell competitor supported only on
the inner cube. Rescaling gives a physical `W1p0` pair on `cube (s * ρ) x`; `mono_of_subset`
extends its zero-boundary membership to the outer cube before it is added to the cutoff
correction. -/
theorem variableCellCutoffCorrector_inner_mem_W1p0 {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    variableCellCutoffCorrector u a ξ x hs ρ ε v ∈
      W1p0 (ENNReal.ofReal p) (cube ρ x) := by
  have hcellInner := W1p0.rescale_back_cube hε x hv
  have hrad : s * ρ ≤ ρ := by nlinarith [hs.2, hρ]
  have hinner : cube (s * ρ) x ⊆ cube ρ x := SubaddCube.cube_subset_cube hrad x
  have hcell := W1p0.mono_of_subset hinner hcellInner
  have hcut := cutoff_sub_affine_mem_W1p0 hΩopen hΩbounded u a ξ x hs hρ x hball
  have hcutNeg := W1p0.smul hcut (-1 : ℝ)
  have hsum := W1p0.add (A := cube ρ x) (B := cube ρ x) (C := cube ρ x)
    subset_rfl subset_rfl hcell hcutNeg
  simpa [variableCellCutoffCorrector] using hsum

/-- The contracted-slope corrector is admissible whenever its cell test is supported on the
dilated inner cube. This reuses the zero-extension argument for the uncontracted wrapper. -/
theorem contractedVariableCellCutoffCorrector_inner_mem_W1p0 {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    contractedVariableCellCutoffCorrector u a ξ x hs t ρ ε v ∈
      W1p0 (ENNReal.ofReal p) (cube ρ x) := by
  simpa [contractedVariableCellCutoffCorrector] using
    (variableCellCutoffCorrector_inner_mem_W1p0 hΩopen hΩbounded u a (t • ξ) x hs
      hρ hε hball hv)

/-- Adding the variable background gradient to the correction gives the rescaled cell gradient
on the inner cube, where the cut-off is one and its derivative vanishes. -/
theorem variableCellCutoffCorrector_grad_inner {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ ε : ℝ} (hρ : 0 < ρ)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) {y : Sp N}
    (hy : y ∈ cube (s * ρ) x) :
    u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y =
      ξ + v.2 (ε⁻¹ • y) := by
  simp [variableCellCutoffCorrector, fderiv_cutoff_eq_zero hs hρ x hy,
    cutoff_eq_one hs hρ x hy, sub_eq_add_neg]
  abel

/-- The physical gradient in the inner cube for the contracted reference slope. -/
theorem contractedVariableCellCutoffCorrector_grad_inner {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) {ρ ε : ℝ} (hρ : 0 < ρ)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) {y : Sp N}
    (hy : y ∈ cube (s * ρ) x) :
    u.grad y + (contractedVariableCellCutoffCorrector u a ξ x hs t ρ ε v).2 y =
      t • ξ + v.2 (ε⁻¹ • y) := by
  simpa [contractedVariableCellCutoffCorrector] using
    (variableCellCutoffCorrector_grad_inner u a (t • ξ) x hs hρ v hy)

/-- The cell part of an inner-supported cutoff competitor has exactly the expected rescaled
energy on the interior cube. The physical centre becomes `ε⁻¹ • x`, and the factor is
`ε^N`; the identity is an extended-integral change of variables and needs no integrability
assumption. -/
theorem variableCellCutoff_inner_cell_energy_eq
    (L : Sp N → Mat m N → ℝ≥0∞) {s ρ ε : ℝ} (hε : 0 < ε) (x : Sp N)
    (ξ : Mat m N) (v : (Sp N → Tgt m) × (Sp N → Mat m N)) :
    ∫⁻ y in cube (s * ρ) x,
      L (ε⁻¹ • y) (ξ + v.2 (ε⁻¹ • y)) =
      ENNReal.ofReal (ε ^ N) *
        ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (ξ + v.2 z) := by
  have h := setLIntegral_rescale_energy L hε x ξ (fun y => v.2 (ε⁻¹ • y))
    (ρ := s * ρ)
  simpa only [inv_smul_smul₀ hε.ne'] using h

/-- The inner energy identity specialized to the contracted slope. The same physical-to-dilated
change of variables applies; no attainment of the cell infimum or finiteness of the integral is
needed. -/
theorem contractedVariableCellCutoff_inner_cell_energy_eq
    (L : Sp N → Mat m N → ℝ≥0∞) {s ρ ε : ℝ} (hε : 0 < ε) (x : Sp N)
    (t : ℝ) (ξ : Mat m N) (v : (Sp N → Tgt m) × (Sp N → Mat m N)) :
    ∫⁻ y in cube (s * ρ) x,
      L (ε⁻¹ • y) (t • ξ + v.2 (ε⁻¹ • y)) =
      ENNReal.ofReal (ε ^ N) *
        ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (t • ξ + v.2 z) := by
  exact variableCellCutoff_inner_cell_energy_eq L hε x (t • ξ) v

/-- For an admissible inner cell competitor, the energy of the glued trial function on the inner
physical cube equals its cell energy after rescaling. The cutoff vanishes from the gradient there,
and the boundary extension contributes no extra term. -/
theorem variableCellCutoff_inner_trial_energy_eq {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (u : W1p N m (ENNReal.ofReal p) Ω)
    (a : Tgt m) (ξ : Mat m N) (x : Sp N) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) :
    ∫⁻ y in cube (s * ρ) x,
      L (ε⁻¹ • y)
        (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) =
      ENNReal.ofReal (ε ^ N) *
        ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (ξ + v.2 z) := by
  calc
    ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) =
        ∫⁻ y in cube (s * ρ) x, L (ε⁻¹ • y) (ξ + v.2 (ε⁻¹ • y)) := by
          have hS := (isOpen_cube (s * ρ) x).measurableSet
          have hpoint : ∀ᵐ y ∂volume,
              y ∈ cube (s * ρ) x →
                L (ε⁻¹ • y)
                    (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) =
                  L (ε⁻¹ • y) (ξ + v.2 (ε⁻¹ • y)) := by
            apply ae_of_all
            intro y hy
            exact congrArg (fun ζ : Mat m N => L (ε⁻¹ • y) ζ)
              (variableCellCutoffCorrector_grad_inner u a ξ x hs hρ v hy)
          apply setLIntegral_congr_fun_ae hS
          exact hpoint
    _ = ENNReal.ofReal (ε ^ N) *
        ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (ξ + v.2 z) :=
          variableCellCutoff_inner_cell_energy_eq L hε x ξ v

/-- A finite cell infimum can be approximated by an admissible competitor even when it is not
attained. -/
theorem exists_W1p0_cell_competitor_lt {p : ℝ≥0∞}
    (L : Sp N → Mat m N → ℝ≥0∞) (U : Set (Sp N)) (ξ : Mat m N)
    (hfinite : Ytp p L U ξ < ⊤) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ v ∈ (W1p0 p U : Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
      (∫⁻ y in U, L y (ξ + v.2 y)) < Ytp p L U ξ + δ := by
  have hlt := ENNReal.lt_add_right hfinite.ne hδ.ne'
  simpa [Ytp, iInf_lt_iff, exists_prop] using hlt

/-- If the cell value is finite, its approximate minimizer gives an inner-supported physical
trial whose interior energy is within the rescaled tolerance. This is the precise cell-to-physical
comparison available without assuming a minimizer. -/
theorem exists_inner_trial_energy_lt_of_cell_finite {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (u : W1p N m (ENNReal.ofReal p) Ω)
    (a : Tgt m) (ξ : Mat m N) (x : Sp N) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hcell : Ytp (ENNReal.ofReal p) L
      (cube ((s * ρ) / ε) (ε⁻¹ • x)) ξ < ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ v ∈ (W1p0 (ENNReal.ofReal p)
        (cube ((s * ρ) / ε) (ε⁻¹ • x)) :
        Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
      ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) <
        ENNReal.ofReal (ε ^ N) *
          (Ytp (ENNReal.ofReal p) L
            (cube ((s * ρ) / ε) (ε⁻¹ • x)) ξ + δ) := by
  obtain ⟨v, hv, hnear⟩ := exists_W1p0_cell_competitor_lt L
    (cube ((s * ρ) / ε) (ε⁻¹ • x)) ξ hcell hδ
  refine ⟨v, hv, ?_⟩
  rw [variableCellCutoff_inner_trial_energy_eq L u a ξ x hs hρ hε v]
  exact ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.mpr (pow_pos hε N)).ne' ENNReal.ofReal_ne_top hnear

/-- An inner-supported cell test makes the variable-background Dirichlet infimum no larger than
the trial energy. This does not assume that the cell infimum is attained. -/
theorem mDirichlet_le_inner_variableCellCutoff_trial {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    mDirichlet (ENNReal.ofReal p) L ε u.grad (cube ρ x) ≤
      ∫⁻ y in cube ρ x, L (ε⁻¹ • y)
        (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) := by
  have hcorrector := variableCellCutoffCorrector_inner_mem_W1p0
    hΩopen hΩbounded u a ξ x hs hρ hε hball hv
  change (⨅ φg ∈ (W1p0 (ENNReal.ofReal p) (cube ρ x) :
      Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
      ∫⁻ y in cube ρ x, L (ε⁻¹ • y) (u.grad y + φg.2 y)) ≤ _
  exact iInf₂_le _ hcorrector

/-- Dirichlet comparison for the contracted-slope inner-supported trial. This is an actual
admissible competitor on the outer cube; its interior gradient is `t • ξ + ∇w_cell`. -/
theorem mDirichlet_le_contracted_inner_variableCellCutoff_trial {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    mDirichlet (ENNReal.ofReal p) L ε u.grad (cube ρ x) ≤
      ∫⁻ y in cube ρ x, L (ε⁻¹ • y)
        (u.grad y + (contractedVariableCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) := by
  simpa [contractedVariableCellCutoffCorrector] using
    (mDirichlet_le_inner_variableCellCutoff_trial L hΩopen hΩbounded u a (t • ξ) x
      hs hρ hε hball hv)

/-- Cell energy of the contracted trial on the inner physical cube, with the exact factor
`ε^N` and translated centre `ε⁻¹ • x`. -/
theorem contractedVariableCellCutoff_inner_trial_energy_eq {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (u : W1p N m (ENNReal.ofReal p) Ω)
    (a : Tgt m) (ξ : Mat m N) (x : Sp N) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) :
    ∫⁻ y in cube (s * ρ) x,
      L (ε⁻¹ • y)
        (u.grad y + (contractedVariableCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) =
      ENNReal.ofReal (ε ^ N) *
        ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (t • ξ + v.2 z) := by
  simpa [contractedVariableCellCutoffCorrector] using
    (variableCellCutoff_inner_trial_energy_eq L u a (t • ξ) x hs hρ hε v)

/-- The corrected gradient on the transition region. The two error terms are displayed explicitly;
their energy requires additional affine-approximation, growth, and RU-usc estimates. -/
theorem variableCellCutoffCorrector_grad_formula {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ρ ε : ℝ)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) (y : Sp N) :
    u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y =
      ξ + v.2 (ε⁻¹ • y) + (1 - cutoff hs ρ x y) • (u.grad y - ξ) -
        (fderiv ℝ (cutoff hs ρ x) y).smulRight
          (u.toFun y - affineMap a ξ x y) := by
  simp [variableCellCutoffCorrector]
  module

/-- For an inner-supported cell corrector, its rescaled weak gradient vanishes almost everywhere
on the transition annulus. It uses weak-gradient locality for `W1p0`, then restricts the
almost-everywhere conclusion to the measurable annulus; it is not a pointwise claim. -/
theorem variableCellCutoffCorrector_cell_grad_ae_zero_annulus {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {s ρ ε : ℝ} (hε : 0 < ε) (x : Sp N)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      v.2 (ε⁻¹ • y) = 0 := by
  have hcell := W1p0.rescale_back_cube hε x hv
  have hzero := W1p0.ae_grad_eq_zero_off (isOpen_cube (s * ρ) x)
    (volume_frontier_cube (s * ρ) x) hcell
  have hAnn : MeasurableSet (cube ρ x \ cube (s * ρ) x) :=
    (isOpen_cube ρ x).measurableSet.diff (isOpen_cube (s * ρ) x).measurableSet
  apply (ae_restrict_iff' hAnn).2
  filter_upwards [hzero] with y hy hyAnn
  exact hy hyAnn.2

/-- On the annulus, adding an inner-supported cell corrector to the cutoff correction has no
cell-gradient term almost everywhere. The right-hand side is the variable-background cutoff
gradient. -/
theorem variableCellCutoffCorrector_grad_annulus_ae {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y =
        cutoff hs ρ x y • ξ + (1 - cutoff hs ρ x y) • u.grad y -
          (fderiv ℝ (cutoff hs ρ x) y).smulRight
            (u.toFun y - affineMap a ξ x y) := by
  have hzero := variableCellCutoffCorrector_cell_grad_ae_zero_annulus hε x hv
  filter_upwards [hzero] with y hy
  rw [variableCellCutoffCorrector_grad_formula u a ξ x hs ρ ε v y, hy]
  module

/-- Contracting the affine slope leaves the cell-gradient cancellation on the annulus unchanged.
The conclusion remains an almost-everywhere identity. -/
theorem contractedVariableCellCutoffCorrector_grad_annulus_ae {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      u.grad y + (contractedVariableCellCutoffCorrector u a ξ x hs t ρ ε v).2 y =
        cutoff hs ρ x y • (t • ξ) +
          (1 - cutoff hs ρ x y) • u.grad y -
          (fderiv ℝ (cutoff hs ρ x) y).smulRight
            (u.toFun y - affineMap a (t • ξ) x y) := by
  simpa [contractedVariableCellCutoffCorrector] using
    (variableCellCutoffCorrector_grad_annulus_ae u a (t • ξ) x hs hε hv)

/-- Pointwise gradient formula for the contracted affine reference. -/
theorem contractedVariableCellCutoffCorrector_grad_formula {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t ρ ε : ℝ)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) (y : Sp N) :
    u.grad y + (contractedVariableCellCutoffCorrector u a ξ x hs t ρ ε v).2 y =
      t • ξ + v.2 (ε⁻¹ • y) + (1 - cutoff hs ρ x y) • (u.grad y - t • ξ) -
        (fderiv ℝ (cutoff hs ρ x) y).smulRight
          (u.toFun y - affineMap a (t • ξ) x y) := by
  simpa [contractedVariableCellCutoffCorrector] using
    (variableCellCutoffCorrector_grad_formula u a (t • ξ) x hs ρ ε v y)

/-- The scaled-background, inner-supported corrector is admissible on the outer cube. -/
theorem scaledBackgroundCellCutoffCorrector_mem_W1p0 {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v ∈
      W1p0 (ENNReal.ofReal p) (cube ρ x) := by
  exact variableCellCutoffCorrector_inner_mem_W1p0 hΩopen hΩbounded
    (W1p.smul u t) (t • a) (t • ξ) x hs hρ hε hball hv

/-- Interior gradient of the scaled-background trial: the cell corrector is built for the same
contracted slope as the background affine map. -/
theorem scaledBackgroundCellCutoffCorrector_grad_inner {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) {ρ ε : ℝ} (hρ : 0 < ρ)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) {y : Sp N}
    (hy : y ∈ cube (s * ρ) x) :
    t • u.grad y +
      (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y =
        t • ξ + v.2 (ε⁻¹ • y) := by
  simpa [scaledBackgroundCellCutoffCorrector, W1p.smul] using
    (variableCellCutoffCorrector_grad_inner (W1p.smul u t) (t • a) (t • ξ)
      x hs hρ v hy)

/-- Annular gradient formula for the scaled-background construction. Its cutoff error is formed
from `t • u - t • ℓ`, with no extra `(1-t) • ξ` displacement term. -/
theorem scaledBackgroundCellCutoffCorrector_grad_annulus_ae {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      t • u.grad y +
        (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y =
          cutoff hs ρ x y • (t • ξ) +
            (1 - cutoff hs ρ x y) • (t • u.grad y) -
            (fderiv ℝ (cutoff hs ρ x) y).smulRight
              (t • u.toFun y - affineMap (t • a) (t • ξ) x y) := by
  simpa [scaledBackgroundCellCutoffCorrector, W1p.smul] using
    (variableCellCutoffCorrector_grad_annulus_ae (W1p.smul u t) (t • a) (t • ξ)
      x hs hε hv)

/-- The transition error for the scaled-background construction. -/
noncomputable def scaledBackgroundCutoffError {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m)
    (ξ : Mat m N) (x : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (t ρ : ℝ) (y : Sp N) : Mat m N :=
  (fderiv ℝ (cutoff hs ρ x) y).smulRight
    (t • u.toFun y - affineMap (t • a) (t • ξ) x y)

/-- The scaled-background error is exactly `t` times the ordinary affine cut-off error. -/
theorem scaledBackgroundCutoffError_eq_smul {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t ρ : ℝ) (y : Sp N) :
    scaledBackgroundCutoffError u a ξ x hs t ρ y =
      t • ((fderiv ℝ (cutoff hs ρ x) y).smulRight
        (u.toFun y - affineMap a ξ x y)) := by
  simp only [scaledBackgroundCutoffError, affineMap_smul_data]
  rw [← smul_sub, smulRight_smul_right]

/-- The scaled-background competitor is admissible for the local Dirichlet problem with
background field `t • ∇u`. -/
theorem mDirichlet_le_scaledBackgroundCellCutoff_trial {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (u : W1p N m (ENNReal.ofReal p) Ω)
    (a : Tgt m) (ξ : Mat m N) (x : Sp N) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (t : ℝ) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    mDirichlet (ENNReal.ofReal p) L ε (fun y => t • u.grad y) (cube ρ x) ≤
      ∫⁻ y in cube ρ x, L (ε⁻¹ • y)
        (t • u.grad y + (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) := by
  change mDirichlet (ENNReal.ofReal p) L ε (t • u.grad) (cube ρ x) ≤ _
  simpa [scaledBackgroundCellCutoffCorrector, W1p.smul] using
    (mDirichlet_le_inner_variableCellCutoff_trial L hΩopen hΩbounded
      (W1p.smul u t) (t • a) (t • ξ) x hs hρ hε hball hv)


/-- Contracting the affine slope changes its value by exactly `(1-t) • ξ (y-x)`. This
isolates the additional approximation error rather than hiding it in the ordinary affine
remainder. -/
theorem affineMap_contract_slope_error (a : Tgt m) (ξ : Mat m N) (x y : Sp N) (t : ℝ) :
    affineMap a (t • ξ) x y = affineMap a ξ x y - (1 - t) • ξ (y - x) := by
  simp [affineMap]
  module

/-- Quantitative contracted-slope affine remainder. If the ordinary affine remainder is at most
`η ρ`, then the contracted reference adds precisely the geometric error
`abs(1-t) ‖ξ‖ ‖y-x‖`. A cube-specific estimate may substitute its bound on `‖y-x‖`. -/
theorem affineRemainder_contract_slope_bound
    {uval : Tgt m} (a : Tgt m) (ξ : Mat m N) (x y : Sp N) (t η ρ : ℝ)
    (hrem : ‖uval - affineMap a ξ x y‖ ≤ η * ρ) :
    ‖uval - affineMap a (t • ξ) x y‖ ≤
      η * ρ + |1 - t| * ‖ξ‖ * ‖y - x‖ := by
  rw [affineMap_contract_slope_error]
  have hid : uval - (affineMap a ξ x y - (1 - t) • ξ (y - x)) =
      (uval - affineMap a ξ x y) + (1 - t) • ξ (y - x) := by
    simp only [sub_eq_add_neg]
    module
  rw [hid]
  calc
    ‖(uval - affineMap a ξ x y) + (1 - t) • ξ (y - x)‖ ≤
        ‖uval - affineMap a ξ x y‖ + ‖(1 - t) • ξ (y - x)‖ := norm_add_le _ _
    _ ≤ η * ρ + |1 - t| * ‖ξ‖ * ‖y - x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        ‖uval - affineMap a ξ x y‖ + |1 - t| * ‖ξ (y - x)‖ ≤
            η * ρ + |1 - t| * (‖ξ‖ * ‖y - x‖) :=
          add_le_add hrem (mul_le_mul_of_nonneg_left (ξ.le_opNorm (y - x)) (abs_nonneg _))
        _ = η * ρ + |1 - t| * ‖ξ‖ * ‖y - x‖ := by ring

/-- Almost-everywhere version of the contracted affine-remainder estimate on a measurable set.
The displacement hypothesis exposes the geometric factor; for a cube of radius `ρ`, it is
bounded by a dimension-dependent constant times `ρ`. -/
theorem affineRemainder_contract_slope_ae_bound
    {q : ℝ≥0∞} {Ω : Set (Sp N)} {u : W1p N m q Ω}
    (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ η t C : ℝ} (hrem : ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ)
    (hdist : ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      ‖y - x‖ ≤ C * ρ) :
    ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      ‖u.toFun y - affineMap a (t • ξ) x y‖ ≤
        η * ρ + |1 - t| * ‖ξ‖ * (C * ρ) := by
  filter_upwards [hrem, hdist] with y hyrem hydist
  exact (affineRemainder_contract_slope_bound a ξ x y t η ρ hyrem).trans
    (by
      simpa [add_comm, mul_assoc] using
        add_le_add_right
          (mul_le_mul_of_nonneg_left hydist
            (mul_nonneg (abs_nonneg (1 - t)) (norm_nonneg ξ))) (η * ρ))

/-- The exact convex decomposition available for a cut-off gradient after subtracting its error.
Its second argument still contains the blended gradient; a local bound for `G (E/δ)` alone does
not control this value. -/
theorem ConvexENN.cutoff_sub_error_le {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (X E : Mat m N) :
    G (X - E) ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) * G X +
      (δ : ℝ≥0∞) * G (X - (δ : ℝ)⁻¹ • E) := by
  have hweights : (1 - δ : ℝ≥0) + δ + 0 = 1 := by
    apply NNReal.coe_injective
    simp [NNReal.coe_sub hδ1]
  have hdecomp : X - E =
      ((1 - δ : ℝ≥0) : ℝ) • X + (δ : ℝ) • (X - (δ : ℝ)⁻¹ • E) := by
    rw [NNReal.coe_sub hδ1]
    simp only [NNReal.coe_one]
    rw [smul_sub, smul_smul]
    have hmul : (δ : ℝ) * (δ : ℝ)⁻¹ = 1 := by
      exact mul_inv_cancel₀ (by exact_mod_cast hδ0.ne')
    simp [hmul]
    module
  have hj := hG.weighted_three_le (1 - δ) δ 0 hweights X (X - (δ : ℝ)⁻¹ • E) 0
  rw [hdecomp]
  simpa using hj

/-- The affine part of the annular gradient is a genuine convex blend of the two *unscaled*
gradients. The statement takes its `ℝ≥0` weight explicitly so it can be instantiated with
`Real.toNNReal (cutoff ...)` without changing either argument of `G`. -/
theorem ConvexENN.weighted_two_le {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (w : ℝ≥0) (hw : w ≤ 1) (X Y : Mat m N) :
    G ((w : ℝ) • X + ((1 - w : ℝ≥0) : ℝ) • Y) ≤
      (w : ℝ≥0∞) * G X + ((1 - w : ℝ≥0) : ℝ≥0∞) * G Y := by
  have hweights : w + (1 - w : ℝ≥0) + 0 = 1 := by
    apply NNReal.coe_injective
    simp [NNReal.coe_sub hw]
  have hj := hG.weighted_three_le w (1 - w) 0 hweights X Y 0
  simpa [NNReal.coe_sub hw] using hj

/-- A contracted gradient has finite `G`-value when zero is interior to the effective domain and
the original gradient lies in its closure. -/
theorem ConvexENN.finite_smul_of_mem_closure_dom {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h0 : (0 : Mat m N) ∈ interior (dom G))
    {ξ : Mat m N} (hξ : ξ ∈ closure (dom G)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : G (t • ξ) < ⊤ := by
  have hmem := ConvexENN.smul_mem_interior_dom hG h0 hξ ht0 ht1
  have hdom : t • ξ ∈ dom G := interior_subset hmem
  change G (t • ξ) < ⊤ at hdom
  exact hdom

/-- Applying growth to the convex blend on an annulus does not dilate either controlled
gradient: the two `G` arguments are exactly `t • ξ` and the variable field `g y`. -/
theorem HasGGrowth.cutoff_blend_upper {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGrowth : HasGGrowth G α β L) (y : Sp N) (φ t : ℝ)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (ξ : Mat m N)
    (g : Sp N → Mat m N) :
    L y (φ • (t • ξ) + (1 - φ) • g y) ≤
      (β : ℝ≥0∞) * (1 + (Real.toNNReal φ : ℝ≥0∞) * G (t • ξ) +
        ((1 - Real.toNNReal φ : ℝ≥0) : ℝ≥0∞) * G (g y)) := by
  let w : ℝ≥0 := Real.toNNReal φ
  have hw : w ≤ 1 := by
    change Real.toNNReal φ ≤ 1
    exact Real.toNNReal_le_one.mpr hφ1
  have hreal : (w : ℝ) = φ := Real.coe_toNNReal φ hφ0
  have hcomp : ((1 - w : ℝ≥0) : ℝ) = 1 - φ := by
    rw [NNReal.coe_sub hw, NNReal.coe_one, hreal]
  have hblend := hG.weighted_two_le w hw (t • ξ) (g y)
  rw [hreal, hcomp] at hblend
  have hblend' : G (φ • (t • ξ) + (1 - φ) • g y) ≤
      (Real.toNNReal φ : ℝ≥0∞) * G (t • ξ) +
        ((1 - Real.toNNReal φ : ℝ≥0) : ℝ≥0∞) * G (g y) := by
    simpa [w, Real.coe_toNNReal φ hφ0] using hblend
  have hsum : 1 + G (φ • (t • ξ) + (1 - φ) • g y) ≤
      1 + ((Real.toNNReal φ : ℝ≥0∞) * G (t • ξ) +
        ((1 - Real.toNNReal φ : ℝ≥0) : ℝ≥0∞) * G (g y)) :=
    by simpa [add_comm] using add_le_add_left hblend' 1
  calc
    L y (φ • (t • ξ) + (1 - φ) • g y) ≤
        (β : ℝ≥0∞) * (1 + G (φ • (t • ξ) + (1 - φ) • g y)) :=
      (hGrowth y _).2
    _ ≤ (β : ℝ≥0∞) *
        (1 + (Real.toNNReal φ : ℝ≥0∞) * G (t • ξ) +
          ((1 - Real.toNNReal φ : ℝ≥0) : ℝ≥0∞) * G (g y)) := by
      simpa [add_assoc] using
        (mul_le_mul_of_nonneg_left hsum (show (0 : ℝ≥0∞) ≤ β by positivity))

/-- Convexity controls a contracted field directly by the original energy and `G 0`; this is the
step that avoids asking for any bound on `G (c • ∇u)` with `c > 1`. -/
theorem ConvexENN.smul_unit_le {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (X : Mat m N) :
    G (θ • X) ≤ (Real.toNNReal θ : ℝ≥0∞) * G X +
      ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0 := by
  let w : ℝ≥0 := Real.toNNReal θ
  have hw : w ≤ 1 := by
    change Real.toNNReal θ ≤ 1
    exact Real.toNNReal_le_one.mpr hθ1
  have hreal : (w : ℝ) = θ := Real.coe_toNNReal θ hθ0
  have hblend := hG.weighted_two_le w hw X 0
  rw [hreal] at hblend
  have hcomp : ((1 - w : ℝ≥0) : ℝ) = 1 - θ := by
    rw [NNReal.coe_sub hw, NNReal.coe_one, hreal]
  rw [hcomp, smul_zero, add_zero] at hblend
  simpa [w, Real.coe_toNNReal θ hθ0] using hblend

/-- Convexity makes the contracted growth density integrable: if `D` is measurable and
`G ∘ D` has finite integral, then `G (θ • D)` also has finite integral for `0 ≤ θ ≤ 1`.
The estimate uses the explicit additional constant `G 0`; no growth of `G` beyond the unit
segment is assumed. -/
theorem ConvexENN.lintegral_smul_unit_lt_top {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) {A : Set (Sp N)} (hAvol : volume A < ⊤)
    (D : Sp N → Mat m N)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hG0 : G 0 < ⊤)
    (hGint : ∫⁻ y in A, G (D y) < ⊤) :
    ∫⁻ y in A, G (θ • D y) < ⊤ := by
  have hpoint : ∀ y, G (θ • D y) ≤ G (D y) + G 0 := by
    intro y
    calc
      G (θ • D y) ≤
          (Real.toNNReal θ : ℝ≥0∞) * G (D y) +
            ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0 :=
        hG.smul_unit_le hθ0 hθ1 (D y)
      _ ≤ G (D y) + G 0 := by
        have hc₁ : (Real.toNNReal θ : ℝ≥0∞) ≤ 1 :=
          ENNReal.coe_le_coe.mpr (Real.toNNReal_le_one.mpr hθ1)
        have hc₂ : ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) ≤ 1 := by
          apply ENNReal.coe_le_coe.mpr
          exact_mod_cast (tsub_le_self :
            (1 : ℝ≥0) - Real.toNNReal θ ≤ 1)
        calc
          (Real.toNNReal θ : ℝ≥0∞) * G (D y) +
              ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0 ≤
              1 * G (D y) + 1 * G 0 :=
            add_le_add (mul_le_mul_left hc₁ _) (mul_le_mul_left hc₂ _)
          _ = G (D y) + G 0 := by simp
  have hle : ∫⁻ y in A, G (θ • D y) ≤ ∫⁻ y in A, (G (D y) + G 0) :=
    lintegral_mono (fun y => hpoint y)
  calc
    ∫⁻ y in A, G (θ • D y) ≤ ∫⁻ y in A, (G (D y) + G 0) := hle
    _ = (∫⁻ y in A, G (D y)) + G 0 * volume A := by
      rw [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
    _ < ⊤ := ENNReal.add_lt_top.2
      ⟨hGint, ENNReal.mul_lt_top hG0 hAvol⟩

/-- Growth estimate on the annulus for the `t • u` background. The three arguments are contracted
ones, and the cut-off error is exactly divided by the remaining convex weight. -/
theorem HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_pointwise_upper
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x))) :
    let τ : ℝ := t / θ
    ∀ᵐ y ∂volume.restrict (cube ρ x \ cube (s * ρ) x),
      L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        (β : ℝ≥0∞) * (1 + (Real.toNNReal (τ * cutoff hs ρ x y) : ℝ≥0∞) *
          G (θ • ξ) +
          (Real.toNNReal (τ * (1 - cutoff hs ρ x y)) : ℝ≥0∞) *
            G (θ • u.grad y) +
          (Real.toNNReal (1 - τ) : ℝ≥0∞) *
            G ((-(1 - τ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y)) := by
  dsimp
  let τ : ℝ := t / θ
  have hθ0 : 0 < θ := lt_trans ht htθ
  have hτ0 : 0 < τ := by dsimp [τ]; exact div_pos ht hθ0
  have hτ1 : τ < 1 := by dsimp [τ]; exact (div_lt_one₀ hθ0).2 htθ
  have hgrad := scaledBackgroundCellCutoffCorrector_grad_annulus_ae
    u a ξ x hs t hε hv
  filter_upwards [hgrad] with y hy
  let φ : ℝ := cutoff hs ρ x y
  have hφ_def : φ = cutoff hs ρ x y := rfl
  let w₁ : ℝ≥0 := Real.toNNReal (τ * φ)
  let w₂ : ℝ≥0 := Real.toNNReal (τ * (1 - φ))
  let w₃ : ℝ≥0 := Real.toNNReal (1 - τ)
  have hφ0 : 0 ≤ φ := by dsimp [φ]; exact cutoff_nonneg hs ρ x y
  have hφ1 : φ ≤ 1 := by dsimp [φ]; exact cutoff_le_one hs ρ x y
  have hw₁ : 0 ≤ τ * φ := mul_nonneg hτ0.le hφ0
  have hw₂ : 0 ≤ τ * (1 - φ) := mul_nonneg hτ0.le (sub_nonneg.mpr hφ1)
  have hw₃ : 0 ≤ 1 - τ := sub_nonneg.mpr hτ1.le
  have habc : w₁ + w₂ + w₃ = 1 := by
    apply NNReal.coe_injective
    simp only [w₁, w₂, w₃, NNReal.coe_add, Real.coe_toNNReal _ hw₁,
      Real.coe_toNNReal _ hw₂, Real.coe_toNNReal _ hw₃, NNReal.coe_one]
    dsimp [τ]
    ring
  have hfirst : τ * φ * θ = t * φ := by
    dsimp [τ]
    field_simp [ne_of_gt hθ0]
  have hsecond : τ * (1 - φ) * θ = t * (1 - φ) := by
    dsimp [τ]
    field_simp [ne_of_gt hθ0]
  have hthird : (1 - τ) * (-(1 - τ)⁻¹) = -1 := by
    field_simp [ne_of_gt (sub_pos.mpr hτ1)]
  let e := scaledBackgroundCutoffError u a ξ x hs t ρ y
  have hdecomp :
      t • u.grad y + (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y =
        (w₁ : ℝ) • (θ • ξ) + (w₂ : ℝ) • (θ • u.grad y) +
          (w₃ : ℝ) • ((-(1 - τ)⁻¹) • e) := by
    rw [hy, ← hφ_def]
    simp only [w₁, w₂, w₃, Real.coe_toNNReal _ hw₁,
      Real.coe_toNNReal _ hw₂, Real.coe_toNNReal _ hw₃, e,
      scaledBackgroundCutoffError]
    simp only [smul_smul]
    rw [hfirst, hsecond, hthird]
    module
  rw [hdecomp]
  simpa [τ, w₁, w₂, w₃, φ, e] using
    (HasGGrowth.weighted_three_upper hG hGrowth (ε⁻¹ • y) w₁ w₂ w₃ habc
      (θ • ξ) (θ • u.grad y) ((-(1 - τ)⁻¹) • e))

/-- If `G` is convex, separating an error with weight `δ` costs a slightly expanded first
argument `X/(1-δ)` and the isolated term `-E/δ`. This is the valid normalized convexity identity;
the expansion of `X` is a real extra cost and is not controlled by local boundedness near zero. -/
theorem ConvexENN.cutoff_sub_error_le_scaled {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (X E : Mat m N) :
    G (X - E) ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) *
        G ((1 - (δ : ℝ))⁻¹ • X) +
      (δ : ℝ≥0∞) * G (-((δ : ℝ)⁻¹ • E)) := by
  have hweights : (1 - δ : ℝ≥0) + δ + 0 = 1 := by
    apply NNReal.coe_injective
    simp [NNReal.coe_sub (le_of_lt hδ1)]
  have hδr : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hfirst : ((1 - δ : ℝ≥0) : ℝ) ≠ 0 := by
    rw [NNReal.coe_sub (le_of_lt hδ1), NNReal.coe_one]
    linarith
  have hsecond : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ0.ne'
  have hdecomp : X - E =
      ((1 - δ : ℝ≥0) : ℝ) • ((1 - (δ : ℝ))⁻¹ • X) +
        (δ : ℝ) • (-((δ : ℝ)⁻¹ • E)) := by
    rw [NNReal.coe_sub (le_of_lt hδ1), NNReal.coe_one]
    simp only [smul_smul]
    have hc1 : (1 - (δ : ℝ)) * (1 - (δ : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.mpr (by linarith))
    have hc2 : (δ : ℝ) * (δ : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hδ0.ne')
    rw [hc1]
    simp only [one_smul, smul_neg, smul_smul, hc2]
    module
  have hj := hG.weighted_three_le (1 - δ) δ 0 hweights
    ((1 - (δ : ℝ))⁻¹ • X) (-((δ : ℝ)⁻¹ • E)) 0
  rw [hdecomp]
  simpa using hj

/-- A local bound for `G` controls the separated term `G (-E/δ)` only under the explicit
smallness condition `‖E‖ ≤ δ R`. This records the exact premise needed after the cut-off error
estimate. -/
theorem ConvexENN.scaled_error_le_local_bound {G : Mat m N → ℝ≥0∞}
    {R : ℝ} {M : ℝ≥0∞}
    (hball : ∀ ζ, ‖ζ‖ ≤ R → G ζ ≤ M) {δ : ℝ} (hδ : 0 < δ)
    {E : Mat m N} (hE : ‖E‖ ≤ δ * R) : G (-((δ : ℝ)⁻¹ • E)) ≤ M := by
  apply hball
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
  calc
    δ⁻¹ * ‖E‖ ≤ δ⁻¹ * (δ * R) := mul_le_mul_of_nonneg_left hE (le_of_lt (inv_pos.mpr hδ))
    _ = R := by field_simp [hδ.ne']

/-- For every finite cell infimum, a `W1p0` cell test can be chosen arbitrarily close and its
contracted-slope energy transported to the physical inner cube. The exact scale is `ε^N`; no
attainment is assumed. -/
theorem exists_contracted_inner_trial_energy_lt_of_cell_finite
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (L : Sp N → Mat m N → ℝ≥0∞) {s ρ ε : ℝ} (hε : 0 < ε) (x : Sp N)
    (t : ℝ) (ξ : Mat m N) (δ : ℝ≥0∞)
    (hcell : Ytp (ENNReal.ofReal p) L
      (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) < ⊤)
    (hδ : 0 < δ) :
    ∃ v ∈ W1p0 (ENNReal.ofReal p)
        (cube ((s * ρ) / ε) (ε⁻¹ • x)),
      ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y) (t • ξ + v.2 (ε⁻¹ • y)) <
        ENNReal.ofReal (ε ^ N) *
          (Ytp (ENNReal.ofReal p) L
            (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + δ) := by
  obtain ⟨v, hv, hnear⟩ := exists_W1p0_cell_competitor_lt L
    (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) hcell hδ
  refine ⟨v, hv, ?_⟩
  rw [contractedVariableCellCutoff_inner_cell_energy_eq L hε x t ξ v]
  exact ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.mpr (pow_pos hε N)).ne' ENNReal.ofReal_ne_top hnear

/-- The cutoff derivative term is small whenever the affine remainder is small at scale `ρ`.
This is stated almost everywhere because affine approximation for Sobolev representatives is an
essential-supremum estimate, not a pointwise estimate. -/
theorem affineCutoff_error_ae_small_of_remainder {p : ℝ}
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m)
    (ξ : Mat m N) (x : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρ C η : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hderiv : ∀ y, ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ) :
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖(fderiv ℝ (cutoff hs ρ x) y).smulRight
          (u.toFun y - affineMap a ξ x y)‖ ≤ C * η := by
  filter_upwards [hrem] with y hy
  rw [ContinuousLinearMap.norm_smulRight_apply]
  calc
    ‖fderiv ℝ (cutoff hs ρ x) y‖ * ‖u.toFun y - affineMap a ξ x y‖ ≤
        (C / ρ) * (η * ρ) := mul_le_mul (hderiv y) hy (norm_nonneg _) (div_nonneg hC hρ.le)
    _ = C * η := by field_simp [hρ.ne']

/-- The error in the scaled-background construction is small whenever the ordinary affine
remainder is small. The scaling contributes only the factor `|t|`; in particular it introduces
no term proportional to `(1-t) • ξ`. -/
theorem scaledBackgroundCutoffError_ae_small_of_remainder {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ C η t : ℝ} (hρ : 0 < ρ)
    (hC : 0 ≤ C)
    (hderiv : ∀ y, ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ) :
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖scaledBackgroundCutoffError u a ξ x hs t ρ y‖ ≤ |t| * (C * η) := by
  filter_upwards [affineCutoff_error_ae_small_of_remainder u a ξ x hs
    hρ hC hderiv hrem] with y hy
  rw [scaledBackgroundCutoffError_eq_smul]
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hy (abs_nonneg t)

/-- If the scaled cut-off error is at most the remaining convex weight times the local radius,
the third argument in the weighted growth estimate lies in the ball where `G` is bounded. The
bound `M` must come from one fixed closed ball about zero on which `G` is bounded. This is the
precise almost-everywhere estimate needed before integrating the annular growth bound. -/
theorem HasGGrowth.scaledBackground_error_argument_ae_le_local_bound
    {G : Mat m N → ℝ≥0∞} {R : ℝ} {M : ℝ≥0∞}
    (hR : 0 < R) (hGball : ∀ ζ, ‖ζ‖ ≤ R → G ζ ≤ M)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ)
    {C η : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hderiv : ∀ y, ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ)
    (hsmall : |t| * (C * η) ≤ (1 - t / θ) * R) :
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M := by
  have hτ : 0 < 1 - t / θ := by
    have hθ : 0 < θ := lt_trans ht htθ
    rw [sub_pos]
    exact (div_lt_one₀ hθ).2 htθ
  filter_upwards [scaledBackgroundCutoffError_ae_small_of_remainder u a ξ x hs
    hρ hC hderiv hrem] with y hy
  apply hGball
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hτ)]
  calc
    (1 - t / θ)⁻¹ * ‖scaledBackgroundCutoffError u a ξ x hs t ρ y‖ ≤
        (1 - t / θ)⁻¹ * (|t| * (C * η)) :=
          mul_le_mul_of_nonneg_left hy (le_of_lt (inv_pos.mpr hτ))
    _ ≤ (1 - t / θ)⁻¹ * ((1 - t / θ) * R) :=
          mul_le_mul_of_nonneg_left hsmall (le_of_lt (inv_pos.mpr hτ))
    _ = R := by field_simp [ne_of_gt hτ]

/-- If the affine remainder is `o(ρ)` a.e. on each fixed-`s` annulus, the normalized cut-off
error lies a.e. in one fixed ball for all sufficiently small radii. The bound `M` comes from the
fixed ball `closedBall 0 R`; only the radius threshold depends on `s` and the affine-remainder
modulus. -/
theorem HasGGrowth.scaledBackground_error_argument_eventually_le_local_bound
    {G : Mat m N → ℝ≥0∞} {R : ℝ} {M : ℝ≥0∞}
    (hR : 0 < R) (hGball : ∀ ζ, ‖ζ‖ ≤ R → G ζ ≤ M)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {t θ : ℝ}
    (ht : 0 < t) (htθ : t < θ) {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ ρ, 0 < ρ → ∀ y,
      ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
        G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M := by
  have hθ : 0 < θ := lt_trans ht htθ
  have hweight : 0 < 1 - t / θ := by
    rw [sub_pos]
    exact (div_lt_one₀ hθ).2 htθ
  let A : ℝ := |t| * C
  let B : ℝ := (1 - t / θ) * R
  have hA : 0 ≤ A := mul_nonneg (abs_nonneg t) hC
  have hB : 0 < B := mul_pos hweight hR
  let η : ℝ := B / (A + 1)
  have hη : 0 < η := div_pos hB (by positivity)
  have hsmall : |t| * (C * η) ≤ (1 - t / θ) * R := by
    have hmul : A * (B / (A + 1)) ≤ B := calc
      A * (B / (A + 1)) = A * B / (A + 1) := by ring
      _ ≤ B := (div_le_iff₀ (by positivity : 0 < A + 1)).2 (by
        nlinarith [mul_nonneg hA (le_of_lt hB)])
    dsimp [A, B, η] at hmul ⊢
    nlinarith [hmul]
  obtain ⟨ρ₀, hρ₀, hremρ⟩ := hrem η hη
  have hsmallRadius : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < ρ₀ :=
    (eventually_lt_nhds hρ₀).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmallRadius, eventually_mem_nhdsWithin] with ρ hρlt hρmem
  have hρ : 0 < ρ := by simpa using hρmem
  exact HasGGrowth.scaledBackground_error_argument_ae_le_local_bound hR hGball
    u a ξ x hs t θ ht htθ hρ hC (hderiv ρ hρ) (hremρ ρ hρ hρlt) hsmall

/-- After the local error argument is controlled, the annular growth estimate depends on the
variable field only through `G (∇u)`, with the original field contracted by `θ ≤ 1`. This is the
pointwise majorant suitable for integration under explicit measurability and integrability
hypotheses; those hypotheses are not inferred from `W1p` alone. -/
theorem HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_pointwise_upper_of_error_bound
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x)))
    {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M) :
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        (β : ℝ≥0∞) *
          (1 + (Real.toNNReal ((t / θ) * cutoff hs ρ x y) : ℝ≥0∞) * G (θ • ξ) +
            (Real.toNNReal ((t / θ) * (1 - cutoff hs ρ x y)) : ℝ≥0∞) *
              ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
                ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) +
            (Real.toNNReal (1 - t / θ) : ℝ≥0∞) * M) := by
  have hθ0 : 0 < θ := lt_trans ht htθ
  have hpoint := HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_pointwise_upper
    hG hGrowth u a ξ x hs t θ ht htθ hε hv
  filter_upwards [hpoint, herr] with y hy he
  calc
    L (ε⁻¹ • y)
        (t • u.grad y +
          (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        (β : ℝ≥0∞) *
          (1 + (Real.toNNReal ((t / θ) * cutoff hs ρ x y) : ℝ≥0∞) * G (θ • ξ) +
            (Real.toNNReal ((t / θ) * (1 - cutoff hs ρ x y)) : ℝ≥0∞) * G (θ • u.grad y) +
            (Real.toNNReal (1 - t / θ) : ℝ≥0∞) *
              G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y)) := hy
    _ ≤ (β : ℝ≥0∞) *
          (1 + (Real.toNNReal ((t / θ) * cutoff hs ρ x y) : ℝ≥0∞) * G (θ • ξ) +
            (Real.toNNReal ((t / θ) * (1 - cutoff hs ρ x y)) : ℝ≥0∞) *
              ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
                ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) +
            (Real.toNNReal (1 - t / θ) : ℝ≥0∞) * M) := by
      gcongr
      exact ConvexENN.smul_unit_le hG (le_of_lt hθ0) hθ1 (u.grad y)

/-- Integrating the scaled-background pointwise estimate gives an extended-valued transition
bound. The inequality itself needs no measurability or finiteness assumptions for the Lebesgue
lower integral; to conclude that its right-hand side is finite one must separately assume
measurability of `G` and finite `G (∇u)` energy on the annulus. -/
theorem HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_upper_of_error_bound
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x)))
    {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M) :
    ∫⁻ y in cube ρ x \ cube (s * ρ) x,
      L (ε⁻¹ • y)
        (t • u.grad y +
          (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
      ∫⁻ y in cube ρ x \ cube (s * ρ) x,
        (β : ℝ≥0∞) *
          (1 + (Real.toNNReal ((t / θ) * cutoff hs ρ x y) : ℝ≥0∞) * G (θ • ξ) +
            (Real.toNNReal ((t / θ) * (1 - cutoff hs ρ x y)) : ℝ≥0∞) *
              ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
                ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) +
            (Real.toNNReal (1 - t / θ) : ℝ≥0∞) * M) := by
  exact lintegral_mono_ae
    (HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_pointwise_upper_of_error_bound
      hG hGrowth u a ξ x hs t θ ht htθ hθ1 hε hv herr)

/-- The weighted transition estimate is bounded by one copy of the variable `G`-energy and a
constant independent of the radius and of the cutoff weights. This is the form needed before
using the annular Lebesgue-point limit. `M` must bound `G` on a fixed ball about zero and be chosen
independently of the radius. -/
theorem HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_coarse_ae
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x)))
    {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M) :
    let K : ℝ≥0∞ := 1 + G (θ • ξ) + G 0 + M
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      L (ε⁻¹ • y)
        (t • u.grad y +
          (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        (β : ℝ≥0∞) * (G (u.grad y) + K) := by
  let K : ℝ≥0∞ := 1 + G (θ • ξ) + G 0 + M
  have hpoint :=
    HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_pointwise_upper_of_error_bound
      hG hGrowth u a ξ x hs t θ ht htθ hθ1 hε hv herr
  have hθ0 : 0 < θ := lt_trans ht htθ
  have hτ0 : 0 < t / θ := div_pos ht hθ0
  have hτ1 : t / θ < 1 := (div_lt_one₀ hθ0).2 htθ
  have hK : K = 1 + G (θ • ξ) + G 0 + M := rfl
  filter_upwards [hpoint] with y hy
  let τ : ℝ := t / θ
  let φ : ℝ := cutoff hs ρ x y
  let w₁ : ℝ≥0∞ := Real.toNNReal (τ * φ)
  let w₂ : ℝ≥0∞ := Real.toNNReal (τ * (1 - φ))
  let w₃ : ℝ≥0∞ := Real.toNNReal (1 - τ)
  have hφ0 : 0 ≤ φ := by dsimp [φ]; exact cutoff_nonneg hs ρ x y
  have hφ1 : φ ≤ 1 := by dsimp [φ]; exact cutoff_le_one hs ρ x y
  have hw₁ : w₁ ≤ 1 := by
    apply ENNReal.coe_le_coe.mpr
    apply Real.toNNReal_le_one.mpr
    calc
      τ * φ ≤ τ * 1 := mul_le_mul_of_nonneg_left hφ1 hτ0.le
      _ ≤ 1 * 1 := by nlinarith [hτ1.le]
      _ = 1 := by ring
  have hw₂ : w₂ ≤ 1 := by
    apply ENNReal.coe_le_coe.mpr
    apply Real.toNNReal_le_one.mpr
    have hφ' : 0 ≤ 1 - φ := sub_nonneg.mpr hφ1
    have hφ'' : 1 - φ ≤ 1 := by linarith [hφ0]
    calc
      τ * (1 - φ) ≤ τ * 1 := mul_le_mul_of_nonneg_left hφ'' hτ0.le
      _ ≤ 1 * 1 := by nlinarith [hτ1.le]
      _ = 1 := by ring
  have hw₃ : w₃ ≤ 1 := by
    apply ENNReal.coe_le_coe.mpr
    apply Real.toNNReal_le_one.mpr
    dsimp [w₃, τ]
    have hnonneg : 0 ≤ t / θ := hτ0.le
    linarith
  have hcθ : (Real.toNNReal θ : ℝ≥0∞) ≤ 1 :=
    ENNReal.coe_le_coe.mpr (Real.toNNReal_le_one.mpr hθ1)
  have hc₀ : ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) ≤ 1 := by
    apply ENNReal.coe_le_coe.mpr
    exact_mod_cast (tsub_le_self : (1 : ℝ≥0) - Real.toNNReal θ ≤ 1)
  have hconv :
      (Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
          ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0 ≤ G (u.grad y) + G 0 := by
    calc
      _ ≤ 1 * G (u.grad y) + 1 * G 0 :=
        add_le_add (mul_le_mul_left hcθ _) (mul_le_mul_left hc₀ _)
      _ = G (u.grad y) + G 0 := by simp
  have hsum :
      1 + w₁ * G (θ • ξ) + w₂ *
          ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
            ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) + w₃ * M ≤
        G (u.grad y) + K := by
    rw [hK]
    have h₁ : w₁ * G (θ • ξ) ≤ G (θ • ξ) := by
      simpa using mul_le_mul_left hw₁ (G (θ • ξ))
    have h₂ : w₂ *
        ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
          ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) ≤ G (u.grad y) + G 0 := by
      calc
        _ ≤ 1 * ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
            ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) := mul_le_mul_left hw₂ _
        _ ≤ 1 * (G (u.grad y) + G 0) := by simpa using hconv
        _ = G (u.grad y) + G 0 := by simp
    have h₃ : w₃ * M ≤ M := by simpa using mul_le_mul_left hw₃ M
    calc
      _ ≤ 1 + G (θ • ξ) + (G (u.grad y) + G 0) + M := by
        exact add_le_add (add_le_add (add_le_add le_rfl h₁) h₂) h₃
      _ = G (u.grad y) + (1 + G (θ • ξ) + G 0 + M) := by ac_rfl
  calc
    L (ε⁻¹ • y)
        (t • u.grad y +
          (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        (β : ℝ≥0∞) * (1 + w₁ * G (θ • ξ) + w₂ *
          ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
            ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) + w₃ * M) := by
      simpa [τ, φ, w₁, w₂, w₃] using hy
    _ ≤ (β : ℝ≥0∞) * (G (u.grad y) + K) := mul_le_mul_right hsum (β : ℝ≥0∞)

/-- Integrating the coarse pointwise estimate bounds the transition by the original `G`-energy
plus a constant times the annulus volume. The error bound `M` must come from a fixed ball on which
`G` is bounded; for limits in the radius it must be chosen independently of that radius. -/
theorem HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_coarse_le
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x)))
    {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M) :
    let K : ℝ≥0∞ := 1 + G (θ • ξ) + G 0 + M
    ∫⁻ y in cube ρ x \ cube (s * ρ) x,
      L (ε⁻¹ • y)
        (t • u.grad y +
          (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
      (β : ℝ≥0∞) * ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) +
        K * volume (cube ρ x \ cube (s * ρ) x)) := by
  let K : ℝ≥0∞ := 1 + G (θ • ξ) + G 0 + M
  have hpoint := HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_coarse_ae
    hG hGrowth u a ξ x hs t θ ht htθ hθ1 hε hv herr
  calc
    _ ≤ ∫⁻ y in cube ρ x \ cube (s * ρ) x,
        (β : ℝ≥0∞) * (G (u.grad y) + K) := lintegral_mono_ae hpoint
    _ = (β : ℝ≥0∞) *
        ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) +
          K * volume (cube ρ x \ cube (s * ρ) x)) := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        lintegral_add_right' _ aemeasurable_const, setLIntegral_const]

/-- The transition energy is finite when the original growth energy and the fixed terms are
finite. The coefficients in the convex decomposition are at most one, so the integrated bound is
dominated by `β * (G (∇u) + 1 + G (θ • ξ) + G 0 + M)`. No measurability of `G ∘ u.grad` is
assumed: the finite extended integral is used directly, and the constant is added on the right. -/
theorem HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_lt_top
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x)))
    {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M)
    (hGxi : G (θ • ξ) < ⊤) (hG0 : G 0 < ⊤) (hM : M < ⊤)
    (hGint : ∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y) < ⊤)
    (hvol : volume (cube ρ x \ cube (s * ρ) x) < ⊤) :
    ∫⁻ y in cube ρ x \ cube (s * ρ) x,
      L (ε⁻¹ • y)
        (t • u.grad y +
          (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) < ⊤ := by
  let K : ℝ≥0∞ := 1 + G (θ • ξ) + G 0 + M
  have hK : K < ⊤ := by
    dsimp [K]
    have h₁ : 1 + G (θ • ξ) < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hGxi⟩
    have h₂ : G 0 + M < ⊤ := ENNReal.add_lt_top.2 ⟨hG0, hM⟩
    simpa [add_assoc] using (ENNReal.add_lt_top.2 ⟨h₁, h₂⟩)
  have hcoarse : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        (β : ℝ≥0∞) * (G (u.grad y) + K) := by
    have hpoint :=
      HasGGrowth.scaledBackgroundCellCutoff_inner_annulus_pointwise_upper_of_error_bound
      hG hGrowth u a ξ x hs t θ ht htθ hθ1 hε hv herr
    have hθ0 : 0 < θ := lt_trans ht htθ
    have hτ0 : 0 < t / θ := div_pos ht hθ0
    have hτ1 : t / θ < 1 := (div_lt_one₀ hθ0).2 htθ
    filter_upwards [hpoint] with y hy
    let τ : ℝ := t / θ
    let φ : ℝ := cutoff hs ρ x y
    let w₁ : ℝ≥0∞ := Real.toNNReal (τ * φ)
    let w₂ : ℝ≥0∞ := Real.toNNReal (τ * (1 - φ))
    let w₃ : ℝ≥0∞ := Real.toNNReal (1 - τ)
    have hφ0 : 0 ≤ φ := by dsimp [φ]; exact cutoff_nonneg hs ρ x y
    have hφ1 : φ ≤ 1 := by dsimp [φ]; exact cutoff_le_one hs ρ x y
    have hw₁ : w₁ ≤ 1 := by
      apply ENNReal.coe_le_coe.mpr
      apply Real.toNNReal_le_one.mpr
      calc
        τ * φ ≤ τ * 1 := mul_le_mul_of_nonneg_left hφ1 hτ0.le
        _ ≤ 1 * 1 := by simpa using hτ1.le
        _ = 1 := by ring
    have hw₂ : w₂ ≤ 1 := by
      apply ENNReal.coe_le_coe.mpr
      apply Real.toNNReal_le_one.mpr
      have hφ' : 0 ≤ 1 - φ := sub_nonneg.mpr hφ1
      have hφ'' : 1 - φ ≤ 1 := by linarith [hφ0]
      calc
        τ * (1 - φ) ≤ τ * 1 := mul_le_mul_of_nonneg_left hφ'' hτ0.le
        _ ≤ 1 * 1 := by simpa using hτ1.le
        _ = 1 := by ring
    have hw₃ : w₃ ≤ 1 := by
      apply ENNReal.coe_le_coe.mpr
      apply Real.toNNReal_le_one.mpr
      linarith [hτ0, hτ1]
    have hcθ : (Real.toNNReal θ : ℝ≥0∞) ≤ 1 :=
      ENNReal.coe_le_coe.mpr (Real.toNNReal_le_one.mpr hθ1)
    have hc₀ : ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) ≤ 1 := by
      apply ENNReal.coe_le_coe.mpr
      exact_mod_cast (tsub_le_self : (1 : ℝ≥0) - Real.toNNReal θ ≤ 1)
    have hconv : (Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
        ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0 ≤ G (u.grad y) + G 0 := by
      calc
        _ ≤ 1 * G (u.grad y) + 1 * G 0 :=
          add_le_add (mul_le_mul_left hcθ _) (mul_le_mul_left hc₀ _)
        _ = G (u.grad y) + G 0 := by simp
    have hsum : 1 + w₁ * G (θ • ξ) +
        w₂ * ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
          ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) + w₃ * M ≤
        G (u.grad y) + K := by
      dsimp [K]
      have h₁ : w₁ * G (θ • ξ) ≤ G (θ • ξ) := by
        simpa using mul_le_mul_left hw₁ (G (θ • ξ))
      have h₂ : w₂ * ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
          ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) ≤
          G (u.grad y) + G 0 := by
        calc
          _ ≤ 1 * ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
              ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) :=
            mul_le_mul_left hw₂ _
          _ ≤ 1 * (G (u.grad y) + G 0) := by simpa using hconv
          _ = G (u.grad y) + G 0 := by simp
      have h₃ : w₃ * M ≤ M := by simpa using mul_le_mul_left hw₃ M
      calc
        _ ≤ 1 + G (θ • ξ) + (G (u.grad y) + G 0) + M := by
          exact add_le_add (add_le_add (add_le_add le_rfl h₁) h₂) h₃
        _ = G (u.grad y) + (1 + G (θ • ξ) + G 0 + M) := by ac_rfl
    calc
      L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        (β : ℝ≥0∞) *
          (1 + w₁ * G (θ • ξ) +
            w₂ * ((Real.toNNReal θ : ℝ≥0∞) * G (u.grad y) +
              ((1 - Real.toNNReal θ : ℝ≥0) : ℝ≥0∞) * G 0) + w₃ * M) := by
        simpa [τ, φ, w₁, w₂, w₃] using hy
      _ ≤ (β : ℝ≥0∞) * (G (u.grad y) + K) :=
        mul_le_mul_right hsum (β : ℝ≥0∞)
  have hInt : ∫⁻ y in cube ρ x \ cube (s * ρ) x,
      (β : ℝ≥0∞) * (G (u.grad y) + K) < ⊤ := by
    calc
      ∫⁻ y in cube ρ x \ cube (s * ρ) x,
          (β : ℝ≥0∞) * (G (u.grad y) + K) =
          (β : ℝ≥0∞) *
            ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) +
              K * volume (cube ρ x \ cube (s * ρ) x)) := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top <| ENNReal.add_lt_top.2
        ⟨hGint, ENNReal.mul_lt_top hK hvol⟩
  exact (lt_of_le_of_lt (lintegral_mono_ae hcoarse) hInt)

/-- A finite cell value and a finite annular growth bound provide a finite-energy full-cube trial.
The cell infimum need not be attained: choose an inner test within additive unit error, then join
the inner and annular integrals across their measurable partition. -/
theorem HasGGrowth.exists_scaledBackgroundCellCutoff_trial_energy_lt_top
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hε : 0 < ε)
    (hcell : Ytp (ENNReal.ofReal p) L
      (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) < ⊤)
    {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M)
    (hGxi : G (θ • ξ) < ⊤) (hG0 : G 0 < ⊤) (hM : M < ⊤)
    (hGint : ∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y) < ⊤)
    (hvol : volume (cube ρ x \ cube (s * ρ) x) < ⊤) :
    ∃ v ∈ W1p0 (ENNReal.ofReal p)
        (cube ((s * ρ) / ε) (ε⁻¹ • x)),
      ∫⁻ y in cube ρ x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) < ⊤ := by
  obtain ⟨v, hv, hcellNear⟩ := exists_contracted_inner_trial_energy_lt_of_cell_finite
    L hε x t ξ 1 hcell (by norm_num)
  have hinnerCellEq :
      ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) =
      ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y) (t • ξ + v.2 (ε⁻¹ • y)) := by
    apply setLIntegral_congr_fun_ae (isOpen_cube (s * ρ) x).measurableSet
    filter_upwards [] with y hy
    exact congrArg (L (ε⁻¹ • y))
      (scaledBackgroundCellCutoffCorrector_grad_inner u a ξ x hs t hρ v hy)
  have hcellBound : ENNReal.ofReal (ε ^ N) *
        (Ytp (ENNReal.ofReal p) L
          (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + 1) < ⊤ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.add_lt_top.2 ⟨hcell, ENNReal.one_lt_top⟩
  have hinnerFinite :
      ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) < ⊤ := by
    rw [hinnerCellEq]
    exact lt_trans hcellNear hcellBound
  have houter : cube (s * ρ) x ⊆ cube ρ x :=
    SubaddCube.cube_subset_cube (le_of_lt (mul_lt_of_lt_one_left hρ hs.2)) x
  have hset : cube ρ x = cube (s * ρ) x ∪ (cube ρ x \ cube (s * ρ) x) := by
    ext y
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hy
      by_cases hi : y ∈ cube (s * ρ) x
      · exact Or.inl hi
      · exact Or.inr ⟨hy, hi⟩
    · rintro (hi | ⟨hy, _⟩)
      · exact houter hi
      · exact hy
  have hdisj : Disjoint (cube (s * ρ) x) (cube ρ x \ cube (s * ρ) x) :=
    disjoint_left.mpr fun y hy ⟨_, hny⟩ => hny hy
  have hset' : cube ρ x = (cube ρ x \ cube (s * ρ) x) ∪ cube (s * ρ) x := by
    ext y
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hy
      by_cases hi : y ∈ cube (s * ρ) x
      · exact Or.inr hi
      · exact Or.inl ⟨hy, hi⟩
    · rintro (⟨hy, _⟩ | hi)
      · exact hy
      · exact houter hi
  have htotalEq :
      ∫⁻ y in cube ρ x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) =
      (∫⁻ y in cube ρ x \ cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y)) +
      (∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y)) := by
    calc
      ∫⁻ y in cube ρ x,
          L (ε⁻¹ • y)
            (t • u.grad y +
              (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) =
          ∫⁻ y in (cube ρ x \ cube (s * ρ) x) ∪ cube (s * ρ) x,
            L (ε⁻¹ • y)
              (t • u.grad y +
                (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) := by
        exact congrArg (fun A : Set (Sp N) => ∫⁻ y in A,
          L (ε⁻¹ • y)
            (t • u.grad y +
              (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y)) hset'
      _ = _ :=
        lintegral_union (isOpen_cube (s * ρ) x).measurableSet hdisj.symm
  have houterFinite :
      ∫⁻ y in cube ρ x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) < ⊤ := by
    rw [htotalEq]
    exact ENNReal.add_lt_top.2
      ⟨HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_lt_top
          hG hGrowth u a ξ x hs t θ ht htθ hθ1 hε hv herr hGxi hG0 hM hGint hvol,
        hinnerFinite⟩
  exact ⟨v, hv, houterFinite⟩

/-- At fixed scale, the inner-supported corrector bounds the Dirichlet infimum by the cell value
up to an arbitrary cell tolerance, plus the coarse annular bound for its actual transition energy.
The constant `M` in the error control must come from a fixed ball on which `G` is bounded; in
applications it is chosen uniformly in the radius. The cell infimum is not assumed to be attained.
This form keeps the variable `G`-energy available for the radius limit. -/
theorem exists_scaledBackgroundCellCutoff_mDirichlet_le_cell_add_annulus
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (t θ : ℝ)
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hε : 0 < ε)
    (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    (hcell : Ytp (ENNReal.ofReal p) L
      (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) < ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ)
    {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M) :
    ∃ v : (Sp N → Tgt m) × (Sp N → Mat m N),
      v ∈ W1p0 (N := N) (m := m) (ENNReal.ofReal p)
        (cube ((s * ρ) / ε) (ε⁻¹ • x)) ∧
      mDirichlet (ENNReal.ofReal p) L ε (fun y => t • u.grad y) (cube ρ x) ≤
        ENNReal.ofReal (ε ^ N) *
          (Ytp (ENNReal.ofReal p) L
            (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + δ) +
        (β : ℝ≥0∞) *
          ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) +
            (1 + G (θ • ξ) + G 0 + M) *
              volume (cube ρ x \ cube (s * ρ) x)) := by
  obtain ⟨v, hv, hcellNear⟩ := exists_contracted_inner_trial_energy_lt_of_cell_finite
    L hε x t ξ δ hcell hδ
  have hinnerEq :
      ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) =
      ENNReal.ofReal (ε ^ N) *
        ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (t • ξ + v.2 z) := by
    calc
      ∫⁻ y in cube (s * ρ) x,
          L (ε⁻¹ • y)
            (t • u.grad y +
              (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) =
          ∫⁻ y in cube (s * ρ) x, L (ε⁻¹ • y) (t • ξ + v.2 (ε⁻¹ • y)) := by
            apply setLIntegral_congr_fun_ae (isOpen_cube (s * ρ) x).measurableSet
            filter_upwards [] with y hy
            exact congrArg (L (ε⁻¹ • y))
              (scaledBackgroundCellCutoffCorrector_grad_inner u a ξ x hs t hρ v hy)
      _ = ENNReal.ofReal (ε ^ N) *
          ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (t • ξ + v.2 z) :=
        contractedVariableCellCutoff_inner_cell_energy_eq L hε x t ξ v
  have hinnerLe :
      ∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) ≤
        ENNReal.ofReal (ε ^ N) *
          (Ytp (ENNReal.ofReal p) L
            (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + δ) := by
    calc
      _ = ENNReal.ofReal (ε ^ N) *
          ∫⁻ z in cube ((s * ρ) / ε) (ε⁻¹ • x), L z (t • ξ + v.2 z) := hinnerEq
      _ = ∫⁻ y in cube (s * ρ) x, L (ε⁻¹ • y) (t • ξ + v.2 (ε⁻¹ • y)) :=
        (contractedVariableCellCutoff_inner_cell_energy_eq L hε x t ξ v).symm
      _ ≤ _ := le_of_lt hcellNear
  have houter : cube (s * ρ) x ⊆ cube ρ x :=
    SubaddCube.cube_subset_cube (le_of_lt (mul_lt_of_lt_one_left hρ hs.2)) x
  have hset : cube ρ x = cube (s * ρ) x ∪ (cube ρ x \ cube (s * ρ) x) := by
    ext y
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hy
      by_cases hi : y ∈ cube (s * ρ) x
      · exact Or.inl hi
      · exact Or.inr ⟨hy, hi⟩
    · rintro (hi | ⟨hy, _⟩)
      · exact houter hi
      · exact hy
  have hdisj : Disjoint (cube (s * ρ) x) (cube ρ x \ cube (s * ρ) x) :=
    disjoint_left.mpr fun y hy ⟨_, hny⟩ => hny hy
  have hset' : cube ρ x = (cube ρ x \ cube (s * ρ) x) ∪ cube (s * ρ) x := by
    ext y
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hy
      by_cases hi : y ∈ cube (s * ρ) x
      · exact Or.inr hi
      · exact Or.inl ⟨hy, hi⟩
    · rintro (⟨hy, _⟩ | hi)
      · exact hy
      · exact houter hi
  have htotal :
      ∫⁻ y in cube ρ x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) =
      (∫⁻ y in cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y)) +
      (∫⁻ y in cube ρ x \ cube (s * ρ) x,
        L (ε⁻¹ • y)
          (t • u.grad y +
            (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y)) := by
    calc
      _ = ∫⁻ y in (cube ρ x \ cube (s * ρ) x) ∪ cube (s * ρ) x,
          L (ε⁻¹ • y)
            (t • u.grad y +
              (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) :=
        congrArg (fun A : Set (Sp N) => ∫⁻ y in A,
          L (ε⁻¹ • y)
            (t • u.grad y +
              (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y)) hset'
      _ = _ := lintegral_union (isOpen_cube (s * ρ) x).measurableSet hdisj.symm
      _ = _ := by ac_rfl
  refine ⟨v, hv, ?_⟩
  calc
    mDirichlet (ENNReal.ofReal p) L ε (fun y => t • u.grad y) (cube ρ x) ≤
        ∫⁻ y in cube ρ x,
          L (ε⁻¹ • y)
            (t • u.grad y +
              (scaledBackgroundCellCutoffCorrector u a ξ x hs t ρ ε v).2 y) :=
      mDirichlet_le_scaledBackgroundCellCutoff_trial L hΩopen hΩbounded u a ξ x hs t
        hρ hε hball hv
    _ = _ := htotal
    _ ≤ _ := add_le_add hinnerLe
      (HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_coarse_le
        hG hGrowth u a ξ x hs t θ ht htθ hθ1 hε hv herr)

/-- Normalize the fixed-scale cell/annulus comparison and pass `ε → 0⁺`. The inner cell term
converges using `Ytp_tendsto_Hp`; choosing a cell competitor within `1` leaves the vanishing
remainder `ε^N`. The transition energy is bounded by
`HasGGrowth.lintegral_scaledBackgroundCellCutoff_inner_annulus_coarse_le`; its constant `M` must
come from one fixed ball about zero on which `G` is bounded, independently of the radius. Dividing
by the outer cube volume exposes the exact physical inner-volume ratio, hence the factor `s^N`. -/
theorem mDirichletLimsup_le_scaledBackground_cell_add_annulus
    [NeZero N] {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {t θ : ℝ}
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ)
    (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    (hξ : G (t • ξ) < ⊤) {M : ℝ≥0∞}
    (herr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      G ((-(1 - t / θ)⁻¹) • scaledBackgroundCutoffError u a ξ x hs t ρ y) ≤ M) :
    mDirichletLimsup (ENNReal.ofReal p) L (fun y => t • u.grad y) (cube ρ x) /
        volume (cube ρ x) ≤
      ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) +
        (β : ℝ≥0∞) *
          ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) +
            (1 + G (θ • ξ) + G 0 + M) *
              volume (cube ρ x \ cube (s * ρ) x)) /
        volume (cube ρ x) := by
  let V : ℝ≥0∞ := volume (cube ρ x)
  let Vinner : ℝ≥0∞ := volume (cube (s * ρ) x)
  let ann : ℝ≥0∞ := (β : ℝ≥0∞) *
    ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) +
      (1 + G (θ • ξ) + G 0 + M) * volume (cube ρ x \ cube (s * ρ) x))
  have hVpos : V ≠ 0 := by
    change volume (cube ρ x) ≠ 0
    exact (volume_cube_pos hρ x).ne'
  have hVtop : V ≠ ⊤ := by
    change volume (cube ρ x) ≠ ⊤
    exact volume_cube_ne_top ρ x
  have hVinnerTop : Vinner ≠ ⊤ := by
    change volume (cube (s * ρ) x) ≠ ⊤
    exact volume_cube_ne_top (s * ρ) x
  have hinnerRatio : Vinner / V = ENNReal.ofReal (s ^ N) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.div_ne_top hVinnerTop hVpos) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (pow_nonneg hs.1.le N)]
    simpa [V, Vinner] using volume_cube_inner_ratio (N := N) hρ hs x
  have hρinner : 0 < s * ρ := mul_pos hs.1 hρ
  have hcoeffTop : (β : ℝ≥0∞) * (1 + G (t • ξ)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2
      ⟨ENNReal.one_lt_top, hξ⟩)
  have hcoeffEq : ((β : ℝ≥0∞) * (1 + G (t • ξ))).toNNReal =
      (β : ℝ≥0∞) * (1 + G (t • ξ)) := ENNReal.coe_toNNReal hcoeffTop.ne
  have hcellPoint : ∀ z, L z (t • ξ) ≤
      (((β : ℝ≥0∞) * (1 + G (t • ξ))).toNNReal : ℝ≥0∞) := by
    intro z
    rw [hcoeffEq]
    exact (hGrowth z (t • ξ)).2
  have hcellFinite (ε : ℝ) (hε : 0 < ε) :
      Ytp (ENNReal.ofReal p) L
        (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) < ⊤ := by
    have hbound := Ytp_bound_of_pointwise (p := ENNReal.ofReal p) hcellPoint
      (cube ((s * ρ) / ε) (ε⁻¹ • x))
    apply lt_of_le_of_lt hbound
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (lt_top_iff_ne_top.mpr
        (volume_cube_ne_top ((s * ρ) / ε) (ε⁻¹ • x)))
  have hpoint : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      mDirichlet (ENNReal.ofReal p) L ε (fun y => t • u.grad y) (cube ρ x) ≤
        ENNReal.ofReal (ε ^ N) *
          (Ytp (ENNReal.ofReal p) L
            (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + 1) + ann := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hεmem
    have hε : 0 < ε := by simpa using hεmem
    obtain ⟨v, hv, htrial⟩ := exists_scaledBackgroundCellCutoff_mDirichlet_le_cell_add_annulus
      hG hGrowth hΩopen hΩbounded u a ξ x hs t θ ht htθ hθ1 hρ hε hball
      (hcellFinite ε hε) (δ := 1) (by norm_num) herr
    dsimp [ann]
    exact htrial
  let cellRatio : ℝ → ℝ≥0∞ := fun ε =>
    Ytp (ENNReal.ofReal p) L (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) /
      volume (cube ((s * ρ) / ε) (ε⁻¹ • x))
  have hcellTendsto : Tendsto cellRatio (𝓝[>] (0 : ℝ))
      (𝓝 (Hp (ENNReal.ofReal p) L (t • ξ))) :=
    Ytp_tendsto_Hp hLper (fun z ζ => (hGrowth z ζ).2) hξ.ne hρinner x
  have hscaledCell : Tendsto
      (fun ε : ℝ => ENNReal.ofReal (ε ^ N) *
        Ytp (ENNReal.ofReal p) L
          (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Vinner * Hp (ENNReal.ofReal p) L (t • ξ))) := by
    have hbase := ENNReal.Tendsto.const_mul (a := Vinner) hcellTendsto (Or.inr hVinnerTop)
    apply hbase.congr'
    filter_upwards [eventually_mem_nhdsWithin] with ε hεmem
    have hε : 0 < ε := by simpa using hεmem
    have hVcell0 : volume (cube ((s * ρ) / ε) (ε⁻¹ • x)) ≠ 0 :=
      (volume_cube_pos (div_pos hρinner hε) _).ne'
    have hVcellTop : volume (cube ((s * ρ) / ε) (ε⁻¹ • x)) ≠ ⊤ :=
      volume_cube_ne_top _ _
    have hcancel : volume (cube ((s * ρ) / ε) (ε⁻¹ • x)) * cellRatio ε =
        Ytp (ENNReal.ofReal p) L (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) := by
      dsimp [cellRatio]
      exact ENNReal.mul_div_cancel hVcell0 hVcellTop
    have hscaleVolume : Vinner = ENNReal.ofReal (ε ^ N) *
        volume (cube ((s * ρ) / ε) (ε⁻¹ • x)) := by
      change volume (cube (s * ρ) x) = _
      rw [volume_cube, volume_cube, ENNReal.ofReal_pow hε.le, ← mul_pow,
        ← ENNReal.ofReal_mul hε.le]
      congr 1
      field_simp [hε.ne']
    calc
      Vinner * cellRatio ε = (ENNReal.ofReal (ε ^ N) *
          volume (cube ((s * ρ) / ε) (ε⁻¹ • x))) * cellRatio ε := by
            rw [← hscaleVolume]
      _ = ENNReal.ofReal (ε ^ N) *
          (volume (cube ((s * ρ) / ε) (ε⁻¹ • x)) * cellRatio ε) := by ac_rfl
      _ = ENNReal.ofReal (ε ^ N) *
          Ytp (ENNReal.ofReal p) L (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) := by
            rw [hcancel]
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hεpowReal : Tendsto (fun ε : ℝ => ε ^ N) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    simpa [zero_pow (Nat.ne_of_gt hN)] using hid.pow N
  have hεpow : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ N))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hεpowReal
  have hcellPlusError : Tendsto
      (fun ε : ℝ => ENNReal.ofReal (ε ^ N) *
        (Ytp (ENNReal.ofReal p) L
          (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (Vinner * Hp (ENNReal.ofReal p) L (t • ξ))) := by
    have hadd := hscaledCell.add hεpow
    have hsum : Tendsto
        (fun ε : ℝ => ENNReal.ofReal (ε ^ N) *
          (Ytp (ENNReal.ofReal p) L
            (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + 1))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Vinner * Hp (ENNReal.ofReal p) L (t • ξ) + 0)) := by
      apply hadd.congr'
      filter_upwards [] with ε
      rw [mul_add, mul_one]
    simpa using hsum
  have hR : Tendsto
      (fun ε : ℝ => ENNReal.ofReal (ε ^ N) *
        (Ytp (ENNReal.ofReal p) L
          (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + 1) + ann)
      (𝓝[>] (0 : ℝ)) (𝓝 (Vinner * Hp (ENNReal.ofReal p) L (t • ξ) + ann)) :=
    hcellPlusError.add_const ann
  have hlimsup :
      mDirichletLimsup (ENNReal.ofReal p) L (fun y => t • u.grad y) (cube ρ x) ≤
        Vinner * Hp (ENNReal.ofReal p) L (t • ξ) + ann := by
    calc
      _ ≤ limsup (fun ε : ℝ => ENNReal.ofReal (ε ^ N) *
          (Ytp (ENNReal.ofReal p) L
            (cube ((s * ρ) / ε) (ε⁻¹ • x)) (t • ξ) + 1) + ann) (𝓝[>] (0 : ℝ)) :=
            limsup_le_limsup hpoint (by isBoundedDefault) (by isBoundedDefault)
      _ = Vinner * Hp (ENNReal.ofReal p) L (t • ξ) + ann := hR.limsup_eq
  have hnormalized :
      mDirichletLimsup (ENNReal.ofReal p) L (fun y => t • u.grad y) (cube ρ x) / V ≤
        ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) + ann / V := by
    calc
      _ ≤ (Vinner * Hp (ENNReal.ofReal p) L (t • ξ) + ann) / V :=
        ENNReal.div_le_div_right hlimsup V
      _ = Vinner / V * Hp (ENNReal.ofReal p) L (t • ξ) + ann / V := by
        rw [ENNReal.add_div, ENNReal.mul_div_right_comm]
      _ = _ := by rw [hinnerRatio]
  simpa [V, ann] using hnormalized

/-- Under an explicit affine-differentiability modulus, the coarse cell/annulus comparison holds
for every sufficiently small outer radius. The fixed local bound `M` is supplied on one ball about
zero; the affine-remainder and open-domain arguments provide radius thresholds, which may depend
on the fixed `s`. This is the pointwise-in-radius estimate to which the Lebesgue limits can be
applied. -/
theorem mDirichletLimsup_cube_average_le_coarse_eventually
    [NeZero N] {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    (hx : x ∈ Ω) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {t θ : ℝ}
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1)
    (hξ : G (t • ξ) < ⊤) {R C : ℝ} {M : ℝ≥0∞}
    (hR : 0 < R) (hGball : ∀ ζ, ‖ζ‖ ≤ R → G ζ ≤ M) (hC : 0 ≤ C)
    (hderiv : ∀ ρ, 0 < ρ → ∀ y,
      ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      mDirichletLimsup (ENNReal.ofReal p) L (fun y => t • u.grad y) (cube ρ x) /
          volume (cube ρ x) ≤
        ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) +
          (β : ℝ≥0∞) *
            ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) +
              (1 + G (θ • ξ) + G 0 + M) *
                volume (cube ρ x \ cube (s * ρ) x)) /
            volume (cube ρ x) := by
  obtain ⟨r, hr, hballΩ⟩ := Metric.isOpen_iff.1 hΩopen x hx
  have hρsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  have hball : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), Metric.closedBall x (ρ / 2) ⊆ Ω := by
    filter_upwards [hρsmall] with ρ hρr y hy
    apply hballΩ
    rw [Metric.mem_ball]
    calc
      dist y x ≤ ρ / 2 := Metric.mem_closedBall.mp hy
      _ < r := by linarith
  have herror := HasGGrowth.scaledBackground_error_argument_eventually_le_local_bound
    hR hGball u a ξ x hs ht htθ hC hderiv hrem
  filter_upwards [hball, herror, eventually_mem_nhdsWithin] with ρ hballρ herrρ hρmem
  exact mDirichletLimsup_le_scaledBackground_cell_add_annulus hG hGrowth hLper
    hΩopen hΩbounded u a ξ x hs ht htθ hθ1
    (show 0 < ρ by simpa using hρmem) hballρ hξ herrρ

/-- A Vitali cube-density limit inherits the fixed-`s` coarse upper bound. The annular energy
limit is stated in the real form supplied by `W1p.ae_tendsto_lintegral_G_grad_annulus_ratio`;
`hvolAnn` is the exact volume ratio from `volume_cube_annulus_ratio`. This is a pointwise density
conclusion, separate from the integrated envelope inequality in `vitaliEnvelopeUpper`. -/
theorem mDirichletLimsup_vitali_density_le_of_coarse_bound
    {dS : ℝ≥0∞} {F I V A : ℝ → ℝ≥0∞} {HpVal g K : ℝ≥0∞}
    {β : ℝ≥0} {s : ℝ} {q : ℝ}
    (hq : q = (1 - s ^ N) * g.toReal) (hK : K < ⊤)
    (hdensity : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 dS))
    (hannulus : Tendsto (fun ρ : ℝ => (I ρ / V ρ).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 q))
    (hIfinite : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), I ρ < ⊤)
    (hVpos : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), V ρ ≠ 0)
    (hvolAnn : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      A ρ / V ρ = ENNReal.ofReal (1 - s ^ N))
    (hbound : F ≤ᶠ[𝓝[>] (0 : ℝ)] fun ρ =>
      ENNReal.ofReal (s ^ N) * HpVal +
        (β : ℝ≥0∞) * ((I ρ + K * A ρ) / V ρ)) :
    dS ≤ ENNReal.ofReal (s ^ N) * HpVal +
      (β : ℝ≥0∞) *
        (ENNReal.ofReal q + K * ENNReal.ofReal (1 - s ^ N)) := by
  have hQreal : Tendsto (fun ρ : ℝ => ENNReal.ofReal ((I ρ / V ρ).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal q)) :=
    (ENNReal.continuous_ofReal.tendsto q).comp hannulus
  have hQ : Tendsto (fun ρ : ℝ => I ρ / V ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal q)) := by
    apply hQreal.congr'
    filter_upwards [hIfinite, hVpos] with ρ hI hV
    exact ENNReal.ofReal_toReal (ENNReal.div_ne_top hI.ne hV)
  have hA : Tendsto (fun ρ : ℝ => A ρ / V ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (1 - s ^ N))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hvolAnn] with ρ hρ
    exact hρ.symm
  have hKA : Tendsto (fun ρ : ℝ => K * (A ρ / V ρ))
      (𝓝[>] (0 : ℝ)) (𝓝 (K * ENNReal.ofReal (1 - s ^ N))) :=
    ENNReal.Tendsto.const_mul (a := K) hA (Or.inr hK.ne)
  have hsum : Tendsto (fun ρ : ℝ => I ρ / V ρ + K * (A ρ / V ρ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal q + K * ENNReal.ofReal (1 - s ^ N))) := hQ.add hKA
  have hsumEq : (fun ρ : ℝ => (I ρ + K * A ρ) / V ρ) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ρ => I ρ / V ρ + K * (A ρ / V ρ) := by
    filter_upwards [] with ρ
    rw [ENNReal.add_div]
    congr 1
    calc
      (K * A ρ) / V ρ = (A ρ * K) / V ρ := by rw [mul_comm K]
      _ = A ρ / V ρ * K := ENNReal.mul_div_right_comm
      _ = K * (A ρ / V ρ) := by rw [mul_comm]
  have hcoarse : Tendsto
      (fun ρ : ℝ => ENNReal.ofReal (s ^ N) * HpVal +
        (β : ℝ≥0∞) * ((I ρ + K * A ρ) / V ρ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (s ^ N) * HpVal +
        (β : ℝ≥0∞) * (ENNReal.ofReal q + K * ENNReal.ofReal (1 - s ^ N)))) := by
    have hmul := ENNReal.Tendsto.const_mul (a := (β : ℝ≥0∞)) hsum
      (Or.inr ENNReal.coe_ne_top)
    have hadd := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => ENNReal.ofReal (s ^ N) * HpVal)
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (s ^ N) * HpVal))).add hmul
    exact hadd.congr' (by filter_upwards [hsumEq] with ρ hρ; rw [hρ])
  have hlimit := le_of_tendsto_of_tendsto hdensity hcoarse hbound
  simpa [hq] using hlimit

/-- Growth and convexity give an explicit transition estimate for the inner-supported corrector.
The weights are exactly `1/3,1/3,1/3`, applied to three times the affine part, the variable
gradient part, and the cutoff error. A local finite bound for `G` controls the third term when the
affine remainder is small. The remaining variable term is `G (3 * (1-φ) * ∇u)`; it is not
controlled by `G (∇u)` from convexity alone. -/
theorem HasGGrowth.variableCellCutoff_inner_annulus_pointwise_upper
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x)))
    {R C η : ℝ} {M : ℝ≥0∞} (_hR : 0 < R) (_hM : M < ⊤)
    (hGball : ∀ ζ, ‖ζ‖ ≤ R → G ζ ≤ M)
    (hC : 0 ≤ C) (hsmall : 3 * C * η ≤ R)
    (hρ : 0 < ρ) (hderiv : ∀ y, ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ) :
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      L (ε⁻¹ • y)
        (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) ≤
        (β : ℝ≥0∞) * (1 + (1 / 3 : ℝ≥0∞) * G
            (((3 : ℝ) * cutoff hs ρ x y) • ξ) +
          (1 / 3 : ℝ≥0∞) * G (((3 : ℝ) * (1 - cutoff hs ρ x y)) • u.grad y) +
          (1 / 3 : ℝ≥0∞) * M) := by
  have hgrad := variableCellCutoffCorrector_grad_annulus_ae u a ξ x hs hε hv
  have hErr : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖(fderiv ℝ (cutoff hs ρ x) y).smulRight
          (u.toFun y - affineMap a ξ x y)‖ ≤ R / 3 := by
    filter_upwards [affineCutoff_error_ae_small_of_remainder u a ξ x hs hρ hC
      hderiv hrem] with y hy
    exact hy.trans (by nlinarith [hsmall])
  filter_upwards [hgrad, hErr] with y hy hEy
  let e : Mat m N := (fderiv ℝ (cutoff hs ρ x) y).smulRight
    (u.toFun y - affineMap a ξ x y)
  have heG : G ((-3 : ℝ) • e) ≤ M := by
    apply hGball
    calc
      ‖(-3 : ℝ) • e‖ = 3 * ‖e‖ := by rw [norm_smul]; norm_num
      _ ≤ 3 * (R / 3) := by gcongr
      _ = R := by ring
  have hdecomp : u.grad y +
      (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y =
      ((1 / 3 : ℝ) • (((3 : ℝ) * cutoff hs ρ x y) • ξ)) +
        ((1 / 3 : ℝ) • (((3 : ℝ) * (1 - cutoff hs ρ x y)) • u.grad y)) +
        ((1 / 3 : ℝ) • ((-3 : ℝ) • e)) := by
    rw [hy]
    dsimp [e]
    module
  calc
    L (ε⁻¹ • y)
        (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) ≤
        (β : ℝ≥0∞) * (1 + (1 / 3 : ℝ≥0∞) * G
          (((3 : ℝ) * cutoff hs ρ x y) • ξ) +
          (1 / 3 : ℝ≥0∞) * G (((3 : ℝ) * (1 - cutoff hs ρ x y)) • u.grad y) +
          (1 / 3 : ℝ≥0∞) * G ((-3 : ℝ) • e)) := by
      rw [hdecomp]
      convert hGrowth.weighted_three_upper hG (ε⁻¹ • y) (1 / 3) (1 / 3) (1 / 3)
        (by norm_num)
        (((3 : ℝ) * cutoff hs ρ x y) • ξ)
        (((3 : ℝ) * (1 - cutoff hs ρ x y)) • u.grad y)
        ((-3 : ℝ) • e) using 1 <;> norm_num
    _ ≤ (β : ℝ≥0∞) * (1 + (1 / 3 : ℝ≥0∞) * G
          (((3 : ℝ) * cutoff hs ρ x y) • ξ) +
          (1 / 3 : ℝ≥0∞) * G (((3 : ℝ) * (1 - cutoff hs ρ x y)) • u.grad y) +
          (1 / 3 : ℝ≥0∞) * M) := by gcongr

/-- Integrating the preceding almost-everywhere annulus estimate gives an extended-integral
bound for the transition energy. It asserts no finiteness by itself: to obtain a finite energy
bound one still needs integrability of the displayed variable-gradient term (and measurability of
the relevant compositions). -/
theorem HasGGrowth.lintegral_variableCellCutoff_inner_annulus_upper
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s ρ ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p)
      (cube ((s * ρ) / ε) (ε⁻¹ • x)))
    {R C η : ℝ} {M : ℝ≥0∞} (_hR : 0 < R) (_hM : M < ⊤)
    (hGball : ∀ ζ, ‖ζ‖ ≤ R → G ζ ≤ M)
    (hC : 0 ≤ C) (hsmall : 3 * C * η ≤ R)
    (hρ : 0 < ρ) (hderiv : ∀ y, ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ) :
    ∫⁻ y in cube ρ x \ cube (s * ρ) x,
      L (ε⁻¹ • y)
        (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) ≤
      ∫⁻ y in cube ρ x \ cube (s * ρ) x,
        (β : ℝ≥0∞) * (1 + (1 / 3 : ℝ≥0∞) * G
            (((3 : ℝ) * cutoff hs ρ x y) • ξ) +
          (1 / 3 : ℝ≥0∞) * G (((3 : ℝ) * (1 - cutoff hs ρ x y)) • u.grad y) +
          (1 / 3 : ℝ≥0∞) * M) := by
  exact lintegral_mono_ae
    (HasGGrowth.variableCellCutoff_inner_annulus_pointwise_upper hG hGrowth u a ξ x hs hε
      hv _hR _hM hGball hC hsmall hρ hderiv hrem)

/-- Testing `mDirichlet` with the glued correction gives a concrete energy upper bound. This is
valid without a minimizer for the cell problem; it makes no claim yet that the transition energy
vanishes after normalization or in a small-cube limit. -/
theorem mDirichlet_le_variableCellCutoff_trial {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hball : Metric.closedBall x (ρ / 2) ⊆ Ω)
    {v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hv : v ∈ W1p0 (ENNReal.ofReal p) (cube (ρ / ε) (ε⁻¹ • x))) :
    mDirichlet (ENNReal.ofReal p) L ε u.grad (cube ρ x) ≤
      ∫⁻ y in cube ρ x, L (ε⁻¹ • y)
        (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) := by
  have hcorrector := variableCellCutoffCorrector_mem_W1p0
    hΩopen hΩbounded u a ξ x hs hρ hε hball hv
  change (⨅ φg ∈ (W1p0 (ENNReal.ofReal p) (cube ρ x) :
      Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
      ∫⁻ y in cube ρ x, L (ε⁻¹ • y) (u.grad y + φg.2 y)) ≤ _
  exact iInf₂_le _ hcorrector

/-- Integrated upper-growth estimate for the glued trial gradient. It is valid as an inequality
of extended integrals without assuming measurability or finiteness. Its right-hand side still
contains `G` of the full corrected gradient, displayed using
`variableCellCutoffCorrector_grad_formula`; deriving a bound for that term from the cell energy
and `∫ G(∇u)` is the unresolved transition-layer estimate. -/
theorem HasGGrowth.lintegral_variableCellCutoff_growth_bound
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hGrowth : HasGGrowth G α β L)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (ξ : Mat m N) (x : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ρ ε : ℝ)
    (v : (Sp N → Tgt m) × (Sp N → Mat m N)) (S : Set (Sp N)) :
    ∫⁻ y in S, L (ε⁻¹ • y)
        (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y) ≤
      ∫⁻ y in S, (β : ℝ≥0∞) *
        (1 + G (ξ + v.2 (ε⁻¹ • y) +
          (1 - cutoff hs ρ x y) • (u.grad y - ξ) -
          (fderiv ℝ (cutoff hs ρ x) y).smulRight
            (u.toFun y - affineMap a ξ x y))) := by
  apply lintegral_mono
  intro y
  simpa only [variableCellCutoffCorrector_grad_formula] using
    (hGrowth (ε⁻¹ • y)
      (u.grad y + (variableCellCutoffCorrector u a ξ x hs ρ ε v).2 y)).2

/-- The `ε → 0⁺` limsup Dirichlet value is unchanged when the background fields agree almost
everywhere on `Ω`, provided the open set on which the value is computed is contained in `Ω`. No
measurability assumption on the fields or on `W` is needed: the defining integrals agree pointwise
almost everywhere for every `ε` and every competitor. -/
theorem mDirichletLimsup_congr_of_ae_on_open {p : ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} {D E : Sp N → Mat m N}
    {A Ω : Set (Sp N)} (hAo : IsOpen A) (hΩo : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hDE : D =ᵐ[volume.restrict Ω] E) :
    mDirichletLimsup p W D A = mDirichletLimsup p W E A := by
  unfold mDirichletLimsup
  apply limsup_congr
  exact Eventually.of_forall fun ε => mDirichlet_congr_of_ae_on_open hAo hΩo hAΩ hDE

/-- If `x ∈ Ω` and `Ω` is open, the normalized limsup Dirichlet values for two fields that agree
almost everywhere on `Ω` are eventually equal on centered cubes as `ρ → 0⁺`. The cubes need only
be contained in `Ω` for sufficiently small radii. -/
theorem mDirichletLimsup_congr_eventually_cube_of_ae_on_open {p : ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} {D E : Sp N → Mat m N}
    {Ω : Set (Sp N)} (hΩo : IsOpen Ω) {x : Sp N} (hx : x ∈ Ω)
    (hDE : D =ᵐ[volume.restrict Ω] E) :
    (fun ρ => mDirichletLimsup p W D (cube ρ x) / volume (cube ρ x)) =ᶠ[𝓝[>] 0]
      (fun ρ => mDirichletLimsup p W E (cube ρ x) / volume (cube ρ x)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩo x hx
  have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with ρ hρ hs
  have hcube : cube ρ x ⊆ Ω := by
    exact (cube_subset_ball (by simpa using hρ) x).trans
      ((Metric.ball_subset_ball hs.le).trans hball)
  exact congrArg (fun z : ℝ≥0∞ => z / volume (cube ρ x))
    (mDirichletLimsup_congr_of_ae_on_open (isOpen_cube ρ x) hΩo hcube hDE)

/-- Applied to a `W1p` gradient and its measurable representative, the normalized limsup
Dirichlet densities agree eventually in radius for almost every center in the domain. -/
theorem W1p.mDirichletLimsup_grad_congr_ae {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) (hΩo : IsOpen Ω) (W : Sp N → Mat m N → ℝ≥0∞) :
    ∀ᵐ x ∂(volume.restrict Ω),
      (fun ρ => mDirichletLimsup p W u.grad (cube ρ x) / volume (cube ρ x)) =ᶠ[𝓝[>] 0]
        (fun ρ =>
          mDirichletLimsup p W u.measurableGrad (cube ρ x) / volume (cube ρ x)) := by
  filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
  exact mDirichletLimsup_congr_eventually_cube_of_ae_on_open hΩo hx
    u.grad_ae_measurableGrad

/-- The limsup Dirichlet set function has the same growth-density bound, since the estimate is
uniform in `ε`. -/
theorem mDirichletLimsup_le_growthDensity {p : ℝ≥0∞}
    (G : Mat m N → ℝ≥0∞) (W : Sp N → Mat m N → ℝ≥0∞) (D : Sp N → Mat m N)
    (A : Set (Sp N)) {α β : ℝ≥0} (hGrowth : HasGGrowth G α β W)
    (hGDmeas : Measurable (fun y => G (D y))) (hAvol : volume A < ⊤)
    (hGint : ∫⁻ y in A, G (D y) < ⊤) :
    mDirichletLimsup p W D A ≤ ∫⁻ y in A, (β : ℝ≥0∞) * (1 + G (D y)) ∧
      ∫⁻ y in A, (β : ℝ≥0∞) * (1 + G (D y)) < ⊤ := by
  obtain ⟨_, hfinite⟩ :=
    mDirichlet_le_growthDensity (p := p) G W 1 D A hGrowth hGDmeas hAvol hGint
  refine ⟨?_, hfinite⟩
  unfold mDirichletLimsup
  exact limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun ε =>
    (mDirichlet_le_growthDensity (p := p) G W ε D A hGrowth hGDmeas
      hAvol hGint).1)

/-- Subadditivity passes from each local Dirichlet problem to its `ε → 0⁺` limsup. -/
theorem mDirichletLimsup_le_add {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {W : Sp N → Mat m N → ℝ≥0∞} {D : Sp N → Mat m N}
    {A B C : Set (Sp N)} (hAo : IsOpen A) (hAb : Bornology.IsBounded A)
    (hBo : IsOpen B) (hCo : IsOpen C) (hBA : B ⊆ A) (hCA : C ⊆ A)
    (hBC : Disjoint B C) (hcover : volume (A \ (B ∪ C)) = 0) :
    mDirichletLimsup p W D A ≤ mDirichletLimsup p W D B + mDirichletLimsup p W D C := by
  unfold mDirichletLimsup
  calc
    limsup (fun ε => mDirichlet p W ε D A) (𝓝[>] 0) ≤
        limsup (fun ε => mDirichlet p W ε D B + mDirichlet p W ε D C) (𝓝[>] 0) :=
      limsup_le_limsup (Eventually.of_forall fun ε =>
        mDirichlet_le_add hAo hAb hBo hCo hBA hCA hBC hcover)
    _ ≤ limsup (fun ε => mDirichlet p W ε D B) (𝓝[>] 0) +
        limsup (fun ε => mDirichlet p W ε D C) (𝓝[>] 0) :=
      limsup_add_le_ennreal _ _

/-- With a measurable background field and finite `G`-energy, the already-proved
`vitaliEnvelopeUpper` applies to the limsup Dirichlet set function. This gives its Vitali density
and envelope upper bound; it does not yet construct the recovery sequence needed for
Proposition 2.1(ii). -/
theorem mDirichletLimsup_vitaliUpper [NeZero N] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Ω : Set (Sp N)) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (G : Mat m N → ℝ≥0∞) (W : Sp N → Mat m N → ℝ≥0∞) (D : Sp N → Mat m N)
    {α β : ℝ≥0} (hGrowth : HasGGrowth G α β W)
    (hGDmeas : Measurable (fun y => G (D y)))
    (hGint : ∫⁻ y in Ω, G (D y) < ⊤) :
    ∃ dS : Sp N → ℝ≥0∞,
      (∀ᵐ x ∂(volume.restrict Ω),
        Tendsto (fun ρ => mDirichletLimsup p W D (cube ρ x) / volume (cube ρ x))
          (𝓝[>] 0) (𝓝 (dS x))) ∧
      ∀ A, IsOpen A → A ⊆ Ω →
        vitaliEnv (mDirichletLimsup p W D) A ≤ ∫⁻ x in A, dS x := by
  let S : Set (Sp N) → ℝ≥0∞ := mDirichletLimsup p W D
  let g : Sp N → ℝ≥0∞ := fun x => (β : ℝ≥0∞) * (1 + G (D x))
  have hg : Measurable g := measurable_const.mul (measurable_const.add hGDmeas)
  have hΩvol : volume Ω < ⊤ := hΩbounded.measure_lt_top
  have hΩg : ∫⁻ x in Ω, g x < ⊤ := by
    exact (mDirichletLimsup_le_growthDensity (p := p) G W D Ω hGrowth hGDmeas
      hΩvol hGint).2
  have hdom : ∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x := by
    intro A hAo hAΩ
    have hAb := hΩbounded.subset hAΩ
    have hAvol : volume A < ⊤ := hAb.measure_lt_top
    have hGA : ∫⁻ y in A, G (D y) < ⊤ := by
      exact (lt_of_le_of_lt (lintegral_mono_set hAΩ) hGint)
    exact (mDirichletLimsup_le_growthDensity (p := p) G W D A hGrowth hGDmeas
      hAvol hGA).1
  have hsub : ∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω →
      Disjoint U V → U ∪ V ⊆ A → volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V := by
    intro A U V hAo _hUo _hVo hAΩ hUV hUnion hnull
    have hAb := hΩbounded.subset hAΩ
    exact mDirichletLimsup_le_add hAo hAb _hUo _hVo
      (fun y hy => hUnion (Or.inl hy)) (fun y hy => hUnion (Or.inr hy))
      hUV hnull
  obtain ⟨dS, hdS, henv⟩ := vitaliEnvelopeUpper Ω hΩopen hΩbounded S g hg hΩg hdom hsub
  exact ⟨dS, hdS, henv⟩

/-- Integrating `G` against the weak gradient or the chosen measurable representative gives the
same extended integral on the Sobolev domain. -/
theorem W1p.lintegral_G_grad_eq_measurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) (G : Mat m N → ℝ≥0∞) (hΩ : IsOpen Ω) :
    ∫⁻ y in Ω, G (u.grad y) = ∫⁻ y in Ω, G (u.measurableGrad y) := by
  apply setLIntegral_congr_fun_ae hΩ.measurableSet
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).1 u.grad_ae_measurableGrad]
    with y hy
  intro hyΩ
  exact congrArg G (hy hyΩ)

/-- The integral congruence also holds on any measurable subdomain `A ⊆ Ω`. It uses only the
almost-everywhere equality of the weak gradient and its chosen representative, not measurability
of `G`. -/
theorem W1p.lintegral_G_grad_eq_measurableGrad_on {p : ℝ≥0∞} {Ω A : Set (Sp N)}
    (u : W1p N m p Ω) (G : Mat m N → ℝ≥0∞) (hΩ : MeasurableSet Ω)
    (hA : MeasurableSet A) (hAΩ : A ⊆ Ω) :
    ∫⁻ y in A, G (u.grad y) = ∫⁻ y in A, G (u.measurableGrad y) := by
  apply setLIntegral_congr_fun_ae hA
  filter_upwards [(ae_restrict_iff' hΩ).1 u.grad_ae_measurableGrad] with y hy
  intro hyA
  exact congrArg G (hy (hAΩ hyA))

/-- Annular differentiation for a nonnegative density. If the normalized integral over centered
cubes tends to a finite value `q`, then for each fixed `s ∈ (0,1)` the normalized integral over
the annulus tends to `(1-s^N)q`. The measurability and local integrability needed to obtain the
cube-average hypothesis from the Lebesgue differentiation theorem are separate inputs in an
application; this lemma records the exact averaging implication. -/
theorem tendsto_lintegral_cube_annulus_ratio {g : Sp N → ℝ≥0∞} {q : ℝ≥0∞}
    {x : Sp N} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hfinite : ∫⁻ y, g y < ⊤)
    (hdensity : Tendsto
      (fun ρ : ℝ => (∫⁻ y in cube ρ x, g y) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 q)) (hq : q < ⊤) :
    Tendsto (fun ρ : ℝ =>
      ((∫⁻ y in cube ρ x \ cube (s * ρ) x, g y) /
        volume (cube ρ x)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 - s ^ N) * q.toReal)) := by
  let μ : Measure (Sp N) := volume.withDensity g
  have hμfinite : μ Set.univ < ⊤ := by
    change (volume.withDensity g) Set.univ < ⊤
    rw [withDensity_apply g MeasurableSet.univ]
    simpa using hfinite
  have hcube (ρ : ℝ) : μ (cube ρ x) = ∫⁻ y in cube ρ x, g y := by
    change (volume.withDensity g) (cube ρ x) = _
    rw [withDensity_apply g (isOpen_cube ρ x).measurableSet]
  have hratio : Tendsto
      (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    convert hdensity using 1
    funext ρ
    rw [hcube]
  have h := @tendsto_measure_cube_annulus_ratio N μ ⟨hμfinite⟩ s hs x q hq hratio
  have hannulus (ρ : ℝ) :
      μ (cube ρ x \ cube (s * ρ) x) =
        ∫⁻ y in cube ρ x \ cube (s * ρ) x, g y := by
    change (volume.withDensity g) (cube ρ x \ cube (s * ρ) x) = _
    rw [withDensity_apply g
      ((isOpen_cube ρ x).measurableSet.diff (isOpen_cube (s * ρ) x).measurableSet)]
  have heq : (fun ρ : ℝ =>
      (μ (cube ρ x \ cube (s * ρ) x) / volume (cube ρ x)).toReal) =
    fun ρ => ((∫⁻ y in cube ρ x \ cube (s * ρ) x, g y) /
      volume (cube ρ x)).toReal := by
    funext ρ
    rw [hannulus]
  exact h.congr' (Filter.Eventually.of_forall fun ρ => congrFun heq ρ)

/-- At an interior point with finite `G` energy, the annular averages of the weak-gradient energy
have the expected Lebesgue-point limit, provided the centered-cube averages converge to a finite
value. This integral implication itself does not require `Measurable G`; measurability is needed
separately when deriving the cube-average hypothesis by Lebesgue differentiation. -/
theorem W1p.tendsto_lintegral_G_grad_annulus_ratio {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) (G : Mat m N → ℝ≥0∞) (hΩo : IsOpen Ω)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤)
    {x : Sp N} (hx : x ∈ Ω) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {q : ℝ≥0∞} (hq : q < ⊤)
    (hdensity : Tendsto
      (fun ρ : ℝ => (∫⁻ y in cube ρ x, G (u.measurableGrad y)) /
        volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 q)) :
    Tendsto (fun ρ : ℝ =>
        ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) /
          volume (cube ρ x)).toReal)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 - s ^ N) * q.toReal)) := by
  let g : Sp N → ℝ≥0∞ := Ω.indicator (fun y => G (u.measurableGrad y))
  have hrepInt : ∫⁻ y in Ω, G (u.measurableGrad y) < ⊤ := by
    rw [← u.lintegral_G_grad_eq_measurableGrad G hΩo]
    exact hGint
  have hglobal : ∫⁻ y, g y < ⊤ := by
    rw [show g = Ω.indicator (fun y => G (u.measurableGrad y)) by rfl,
      lintegral_indicator hΩo.measurableSet]
    exact hrepInt
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩo x hx
  have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  have hcubeSub : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), cube ρ x ⊆ Ω := by
    filter_upwards [eventually_mem_nhdsWithin, hsmall] with ρ hρ hρr
    exact (cube_subset_ball (by simpa using hρ) x).trans
      ((Metric.ball_subset_ball hρr.le).trans hball)
  have hdensityExt : Tendsto
      (fun ρ : ℝ => (∫⁻ y in cube ρ x, g y) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    apply hdensity.congr'
    filter_upwards [hcubeSub] with ρ hsub
    congr 1
    apply setLIntegral_congr_fun_ae (isOpen_cube ρ x).measurableSet
    filter_upwards [] with y hy
    simp [g, Set.indicator_of_mem (hsub hy)]
  have hlim := tendsto_lintegral_cube_annulus_ratio hs hglobal hdensityExt hq
  have hAnnEq : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      ∫⁻ y in cube ρ x \ cube (s * ρ) x, g y =
        ∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y) := by
    filter_upwards [hcubeSub] with ρ hsub
    have hsubset : cube ρ x \ cube (s * ρ) x ⊆ Ω := fun y hy => hsub hy.1
    have hmeas : MeasurableSet (cube ρ x \ cube (s * ρ) x) :=
      (isOpen_cube ρ x).measurableSet.diff (isOpen_cube (s * ρ) x).measurableSet
    calc
      ∫⁻ y in cube ρ x \ cube (s * ρ) x, g y =
          ∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.measurableGrad y) := by
            apply setLIntegral_congr_fun_ae hmeas
            filter_upwards [] with y hy
            simp [g, Set.indicator_of_mem (hsubset hy)]
      _ = ∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y) :=
        (u.lintegral_G_grad_eq_measurableGrad_on G hΩo.measurableSet hmeas hsubset).symm
  apply hlim.congr'
  filter_upwards [hAnnEq] with ρ hρ
  rw [hρ]

/-- Almost every point of an open Sobolev domain is a Lebesgue point of the `G`-energy of its
weak gradient. The assumptions `Measurable G` and finite `G`-energy are explicit: the former makes
the measurable representative's composition measurable, while the latter gives local integrability.
The conclusion uses the equality a.e. between the weak gradient and `u.measurableGrad`; it does not
leave cube-average convergence as an input. -/
theorem W1p.ae_tendsto_lintegral_G_grad_cube_ratio [NeZero N] {p : ℝ≥0∞}
    {Ω : Set (Sp N)} (u : W1p N m p Ω) (G : Mat m N → ℝ≥0∞)
    (hΩo : IsOpen Ω) (hGmeas : Measurable G)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤) :
    ∀ᵐ x ∂(volume.restrict Ω),
      G (u.grad x) < ⊤ ∧
        Tendsto (fun ρ : ℝ =>
          (∫⁻ y in cube ρ x, G (u.measurableGrad y)) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (G (u.grad x))) := by
  have hrepMeas : Measurable (fun y => G (u.measurableGrad y)) :=
    hGmeas.comp u.measurableGrad_measurable
  have hgradEq : ∀ᵐ x ∂volume, x ∈ Ω → u.grad x = u.measurableGrad x :=
    (ae_restrict_iff' hΩo.measurableSet).1 u.grad_ae_measurableGrad
  let g : Sp N → ℝ≥0∞ := Ω.indicator (fun y => G (u.measurableGrad y))
  have hgMeas : Measurable g := hrepMeas.indicator hΩo.measurableSet
  have hgInt : ∫⁻ x, g x < ⊤ := by
    rw [show g = Ω.indicator (fun y => G (u.measurableGrad y)) by rfl,
      lintegral_indicator hΩo.measurableSet]
    rw [← u.lintegral_G_grad_eq_measurableGrad G hΩo]
    exact hGint
  let μ : Measure (Sp N) := volume.withDensity g
  have hμfinite : μ Set.univ < ⊤ := by
    change (volume.withDensity g) Set.univ < ⊤
    rw [withDensity_apply g MeasurableSet.univ]
    simpa using hgInt
  have hrn : μ.rnDeriv volume =ᵐ[volume] g :=
    Measure.rnDeriv_withDensity volume hgMeas
  have hfinite : ∀ᵐ x ∂volume, g x < ⊤ := ae_lt_top hgMeas hgInt.ne
  have hdiff := @ae_tendsto_measure_ratio_cube_rnDeriv N inferInstance μ ⟨hμfinite⟩
  apply (ae_restrict_iff' hΩo.measurableSet).2
  filter_upwards [hdiff, hrn, hfinite, hgradEq] with x hxDiff hxRN hxFinite hxGrad hxΩ
  have hxCubeSub : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), cube ρ x ⊆ Ω := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩo x hxΩ
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r :=
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, eventually_mem_nhdsWithin] with ρ hρr hρ
    exact (cube_subset_ball (by simpa using hρ) x).trans
      ((Metric.ball_subset_ball hρr.le).trans hball)
  have hmeasureDensity : Tendsto
      (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
    rw [← hxRN]
    exact hxDiff
  have hcubeAverage : Tendsto
      (fun ρ : ℝ => (∫⁻ y in cube ρ x, G (u.measurableGrad y)) /
        volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
    apply hmeasureDensity.congr'
    filter_upwards [hxCubeSub] with ρ hsub
    have hμcube : μ (cube ρ x) = ∫⁻ y in cube ρ x, g y := by
      change (volume.withDensity g) (cube ρ x) = _
      rw [withDensity_apply g (isOpen_cube ρ x).measurableSet]
    rw [hμcube]
    congr 1
    apply setLIntegral_congr_fun_ae (isOpen_cube ρ x).measurableSet
    filter_upwards [] with y hy
    simp [g, Set.indicator_of_mem (hsub hy)]
  have hxg : g x = G (u.grad x) := by
    simp [g, Set.indicator_of_mem hxΩ, hxGrad hxΩ]
  refine ⟨?_, ?_⟩
  · rw [← hxg]
    exact hxFinite
  · simpa [hxg] using hcubeAverage

/-- For fixed `s`, the affine-cutoff comparison gives a bound for the actual Vitali density of
the variable-gradient limsup functional. The affine remainder modulus is an explicit pointwise
input here (it can be obtained from the affine differentiability interface); it is not hidden in a
claim of uniform approximation. The fixed-ball majorant `M` does not depend on `s` or `ρ`, though
the derivative bound and radius threshold may depend on `s`. `hmean` is the centered-cube
Lebesgue differentiation limit for `G(∇u)`. -/
theorem mDirichletLimsup_vitali_density_le_coarse_of_affine_remainder
    [NeZero N] {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) {a : Tgt m} {ξ : Mat m N} {x : Sp N}
    (hx : x ∈ Ω) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {t θ : ℝ}
    (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1)
    (hξt : G (t • ξ) < ⊤) (hξθ : G (θ • ξ) < ⊤) (hG0 : G 0 < ⊤)
    {R C : ℝ} {M : ℝ≥0∞} (hR : 0 < R)
    (hGball : ∀ ζ, ‖ζ‖ ≤ R → G ζ ≤ M) (hM : M < ⊤) (hC : 0 ≤ C)
    (hderiv : ∀ ρ, 0 < ρ → ∀ y,
      ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (hrem : ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤)
    (hξ : G ξ < ⊤)
    (hmean : Tendsto (fun ρ : ℝ =>
      (∫⁻ y in cube ρ x, G (u.measurableGrad y)) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 (G ξ)))
    {dS : Sp N → ℝ≥0∞}
    (hdensity : Tendsto
      (fun ρ : ℝ => mDirichletLimsup (ENNReal.ofReal p) L (fun y => t • u.grad y) (cube ρ x) /
        volume (cube ρ x)) (𝓝[>] (0 : ℝ)) (𝓝 (dS x))) :
    dS x ≤ ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) +
      (β : ℝ≥0∞) *
        (ENNReal.ofReal ((1 - s ^ N) * (G ξ).toReal) +
          (1 + G (θ • ξ) + G 0 + M) * ENNReal.ofReal (1 - s ^ N)) := by
  let F : ℝ → ℝ≥0∞ := fun ρ =>
    mDirichletLimsup (ENNReal.ofReal p) L (fun y => t • u.grad y) (cube ρ x) / volume (cube ρ x)
  let I : ℝ → ℝ≥0∞ := fun ρ => ∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)
  let V : ℝ → ℝ≥0∞ := fun ρ => volume (cube ρ x)
  let A : ℝ → ℝ≥0∞ := fun ρ => volume (cube ρ x \ cube (s * ρ) x)
  let K : ℝ≥0∞ := 1 + G (θ • ξ) + G 0 + M
  have hK : K < ⊤ := by
    dsimp [K]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hξθ⟩, hG0⟩, hM⟩
  have hcubeEventually : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), cube ρ x ⊆ Ω := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩopen x hx
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with ρ hρ hrρ
    exact (cube_subset_ball (by simpa using hρ) x).trans
      ((Metric.ball_subset_ball hrρ.le).trans hball)
  have hIfinite : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), I ρ < ⊤ := by
    filter_upwards [hcubeEventually] with ρ hsub
    dsimp [I]
    exact (lt_of_le_of_lt (lintegral_mono_set (Set.sdiff_subset.trans hsub)) hGint)
  have hVpos : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), V ρ ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
    exact (volume_cube_pos (by simpa using hρ) x).ne'
  have hbound : F ≤ᶠ[𝓝[>] (0 : ℝ)] fun ρ =>
      ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) +
        (β : ℝ≥0∞) * ((I ρ + K * A ρ) / V ρ) := by
    have hcoarse := mDirichletLimsup_cube_average_le_coarse_eventually hG hGrowth hLper
      hΩopen hΩbounded u a ξ x hx hs ht htθ hθ1 hξt hR hGball hC hderiv hrem
    filter_upwards [hcoarse] with ρ hρ
    calc
      F ρ ≤ ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) +
          ((β : ℝ≥0∞) * (I ρ + K * A ρ)) / V ρ := by
            simpa [F, I, V, A, K] using hρ
      _ = ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) +
          (β : ℝ≥0∞) * ((I ρ + K * A ρ) / V ρ) := by
            congr 1
            rw [mul_div_assoc']
  have hvolAnn : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), A ρ / V ρ = ENNReal.ofReal (1 - s ^ N) := by
    filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
    have hρ' : 0 < ρ := by simpa using hρ
    have hA : A ρ < ⊤ := by
      dsimp [A]
      exact lt_of_le_of_lt (measure_mono sdiff_subset) (volume_cube_ne_top ρ x).lt_top
    have hV : V ρ ≠ 0 := by dsimp [V]; exact (volume_cube_pos hρ' x).ne'
    have hratio : (A ρ / V ρ).toReal = 1 - s ^ N := by
      simpa [A, V] using volume_cube_annulus_ratio (N := N) hρ' hs x
    rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top hA.ne hV), hratio]
  have hannulus := u.tendsto_lintegral_G_grad_annulus_ratio G hΩopen hGint hx hs hξ hmean
  have hresult := mDirichletLimsup_vitali_density_le_of_coarse_bound
    (dS := dS x) (F := F) (I := I) (V := V) (A := A)
    (HpVal := Hp (ENNReal.ofReal p) L (t • ξ)) (g := G ξ) (K := K)
    (β := β) (s := s) (q := (1 - s ^ N) * (G ξ).toReal) rfl hK hdensity hannulus
    hIfinite hVpos hvolAnn hbound
  simpa [K] using hresult

set_option maxHeartbeats 500000 in
-- This limit lemma combines the radius estimate, Vitali density, and ENNReal continuity; the
-- higher heartbeat budget avoids timing out while elaborating the nested filter limits.
/-- If the fixed-`s` estimate above is available for every `s` with the same point, Vitali
density, affine slope, and fixed-ball bound `M`, then the annular contribution vanishes as
`s → 1`. The derivative constants and affine-remainder moduli may depend on `s`; only their
eventual-in-radius conclusions are used separately at each fixed `s`. This gives the pointwise
density bound for the contracted background `t • u`. -/
theorem mDirichletLimsup_vitali_density_le_Hp_of_affine_remainder
    [NeZero N] {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) {a : Tgt m} {ξ : Mat m N} {x : Sp N}
    (hx : x ∈ Ω) {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ1 : θ ≤ 1)
    (hξ : G ξ < ⊤) (hG0 : G 0 < ⊤)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    (C : ℝ → ℝ)
    (hC : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ C s)
    (hderiv : ∀ s (hs : s ∈ Ioo (0 : ℝ) 1), ∀ ρ, 0 < ρ → ∀ y,
      ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C s / ρ)
    (hrem : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict
          (cube ρ x \ cube (s * ρ) x)),
          ‖u.toFun y - affineMap a ξ x y‖ ≤ η * ρ)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤)
    (hmean : Tendsto (fun ρ : ℝ =>
      (∫⁻ y in cube ρ x, G (u.measurableGrad y)) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 (G ξ)))
    {dS : Sp N → ℝ≥0∞}
    (hdensity : Tendsto
      (fun ρ : ℝ => mDirichletLimsup (ENNReal.ofReal p) L
        (u.smul t).measurableGrad (cube ρ x) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 (dS x)))
    (hgradRep : (fun ρ : ℝ => mDirichletLimsup (ENNReal.ofReal p) L
        (fun y => t • u.grad y) (cube ρ x) / volume (cube ρ x)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ρ => mDirichletLimsup (ENNReal.ofReal p) L
        (u.smul t).measurableGrad (cube ρ x) / volume (cube ρ x)) :
    dS x ≤ Hp (ENNReal.ofReal p) L (t • ξ) := by
  obtain ⟨R, M, hR, hM, hGball⟩ := hG.exists_finite_bound_closedBall_zero h0
  have hθ0 : 0 ≤ θ := le_of_lt (lt_trans ht htθ)
  have ht1 : t ≤ 1 := (lt_of_lt_of_le htθ hθ1).le
  have hscaled_finite (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : G (r • ξ) < ⊤ := by
    apply lt_of_le_of_lt (hG.smul_unit_le hr0 hr1 ξ)
    exact ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hξ,
        ENNReal.mul_lt_top ENNReal.coe_lt_top hG0⟩
  have hξt : G (t • ξ) < ⊤ := hscaled_finite t ht.le ht1
  have hξθ : G (θ • ξ) < ⊤ := hscaled_finite θ hθ0 hθ1
  have hHp : Hp (ENNReal.ofReal p) L (t • ξ) < ⊤ := by
    exact lt_of_le_of_lt (hGrowth.Hp_le (ENNReal.ofReal p) (t • ξ))
      (ENNReal.mul_lt_top ENNReal.coe_lt_top
        (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hξt⟩))
  have hK : 1 + G (θ • ξ) + G 0 + M < ⊤ := by
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hξθ⟩, hG0⟩, hM⟩
  let rhs : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (s ^ N) * Hp (ENNReal.ofReal p) L (t • ξ) +
      (β : ℝ≥0∞) *
        (ENNReal.ofReal ((1 - s ^ N) * (G ξ).toReal) +
          (1 + G (θ • ξ) + G 0 + M) * ENNReal.ofReal (1 - s ^ N))
  have hrhs : Tendsto rhs (𝓝[<] (1 : ℝ))
      (𝓝 (Hp (ENNReal.ofReal p) L (t • ξ))) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hpow : Tendsto (fun s : ℝ => s ^ N) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa using hid.pow N
    have hone : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ N))
        (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
      convert (ENNReal.continuous_ofReal.tendsto 1).comp hpow using 1 <;> aesop
    have hcell := ENNReal.Tendsto.const_mul (a := Hp (ENNReal.ofReal p) L (t • ξ))
      hone (Or.inr hHp.ne)
    have hsub : Tendsto (fun s : ℝ => 1 - s ^ N) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      convert tendsto_const_nhds.sub hpow using 1
      aesop
    have hlin : Tendsto (fun s : ℝ => (1 - s ^ N) * (G ξ).toReal)
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using hsub.mul_const (G ξ).toReal
    have herr1 : Tendsto
        (fun s : ℝ => ENNReal.ofReal ((1 - s ^ N) * (G ξ).toReal))
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      convert (ENNReal.continuous_ofReal.tendsto 0).comp hlin using 1 <;> aesop
    have hvol : Tendsto (fun s : ℝ => ENNReal.ofReal (1 - s ^ N))
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      convert (ENNReal.continuous_ofReal.tendsto 0).comp hsub using 1 <;> aesop
    have herr2 := ENNReal.Tendsto.const_mul
      (a := 1 + G (θ • ξ) + G 0 + M) hvol (Or.inr hK.ne)
    have herr := ENNReal.Tendsto.const_mul (a := (β : ℝ≥0∞)) (herr1.add herr2)
      (Or.inr ENNReal.coe_ne_top)
    have hsum := hcell.add herr
    simpa [rhs, mul_comm] using hsum
  have hnear : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo (0 : ℝ) 1 := by
    have hpos : ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hpos, self_mem_nhdsWithin] with s hs hbelow
    exact ⟨hs, hbelow⟩
  have hle : (fun _ : ℝ => dS x) ≤ᶠ[𝓝[<] (1 : ℝ)] rhs := by
    filter_upwards [hnear] with s hs
    have hdensityWeak : Tendsto
        (fun ρ : ℝ => mDirichletLimsup (ENNReal.ofReal p) L
          (fun y => t • u.grad y) (cube ρ x) / volume (cube ρ x))
        (𝓝[>] (0 : ℝ)) (𝓝 (dS x)) := Tendsto.congr' hgradRep.symm hdensity
    exact mDirichletLimsup_vitali_density_le_coarse_of_affine_remainder
      (a := a) (ξ := ξ) (x := x) hG hGrowth hLper hΩopen hΩbounded u hx hs ht htθ hθ1
      hξt hξθ hG0 hR hGball hM (C := C s) (hC s hs)
      (fun ρ hρ y => hderiv s hs ρ hρ y) (hrem s hs) hGint hξ hmean hdensityWeak
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hrhs hle

/-- The annular-average limit is available almost everywhere without assuming cube-average
convergence as an input. It follows from `ae_tendsto_lintegral_G_grad_cube_ratio` and the
annular differentiation lemma above. The annulus is measured with the weak gradient; equality with
the measurable representative is used only through a.e. congruence on cubes contained in `Ω`. -/
theorem W1p.ae_tendsto_lintegral_G_grad_annulus_ratio [NeZero N] {p : ℝ≥0∞}
    {Ω : Set (Sp N)} (u : W1p N m p Ω) (G : Mat m N → ℝ≥0∞)
    (hΩo : IsOpen Ω) (hGmeas : Measurable G)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ x ∂(volume.restrict Ω),
      G (u.grad x) < ⊤ ∧
        Tendsto (fun ρ : ℝ =>
          ((∫⁻ y in cube ρ x \ cube (s * ρ) x, G (u.grad y)) /
            volume (cube ρ x)).toReal)
          (𝓝[>] (0 : ℝ)) (𝓝 ((1 - s ^ N) * (G (u.grad x)).toReal)) := by
  have hcube := u.ae_tendsto_lintegral_G_grad_cube_ratio G hΩo hGmeas hGint
  apply (ae_restrict_iff' hΩo.measurableSet).2
  filter_upwards [(ae_restrict_iff' hΩo.measurableSet).1 hcube] with x hx
  intro hxΩ
  rcases hx hxΩ with ⟨hfinite, hdensity⟩
  exact ⟨hfinite, u.tendsto_lintegral_G_grad_annulus_ratio G hΩo hGint hxΩ
    hs hfinite hdensity⟩

/-- The Vitali-envelope estimate can be applied to the measurable representative of a Sobolev
gradient when `G` is measurable and the explicit finite `G`-energy assumption holds. Membership
in `W1p` alone does not imply that energy bound for a general `G`. The resulting set function uses
`u.measurableGrad`; `W1p.mDirichletLimsup_grad_congr_ae` identifies its centered-cube densities
eventually with those for the weak gradient at almost every center in `Ω`. -/
theorem mDirichletLimsup_vitaliUpper_of_W1p [NeZero N] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Ω : Set (Sp N)) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (G : Mat m N → ℝ≥0∞) (W : Sp N → Mat m N → ℝ≥0∞)
    (u : W1p N m p Ω) {α β : ℝ≥0} (hGrowth : HasGGrowth G α β W)
    (hGmeas : Measurable G)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤) :
    ∃ dS : Sp N → ℝ≥0∞,
      (∀ᵐ x ∂(volume.restrict Ω),
        Tendsto
          (fun ρ => mDirichletLimsup p W u.measurableGrad (cube ρ x) /
            volume (cube ρ x))
          (𝓝[>] 0) (𝓝 (dS x))) ∧
      ∀ A, IsOpen A → A ⊆ Ω →
        vitaliEnv (mDirichletLimsup p W u.measurableGrad) A ≤ ∫⁻ x in A, dS x := by
  have hGintRep : ∫⁻ y in Ω, G (u.measurableGrad y) < ⊤ := by
    rw [← u.lintegral_G_grad_eq_measurableGrad G hΩopen]
    exact hGint
  exact mDirichletLimsup_vitaliUpper Ω hΩopen hΩbounded G W u.measurableGrad
    hGrowth (hGmeas.comp u.measurableGrad_measurable) hGintRep

/-- Assemble the pointwise hypotheses of
`mDirichletLimsup_vitali_density_le_Hp_of_affine_remainder` almost everywhere from the cited
Sobolev differentiability interface and the existing Lebesgue/Vitali density results. The same
affine representative and slope supplied by (b), and the same Vitali density `dS`, are used for
every annulus parameter `s`; the squeeze in `s` is therefore performed by the pointwise theorem
before this a.e. assembly. The conclusion retains, for this very same `dS`, both its cube-density
limit and the integrated Vitali bound `vitaliEnv … A ≤ ∫⁻ x in A, dS x`. For fixed `0 < t < 1`,
the Vitali estimate is applied to `t • u`;
its finite `G`-energy follows from convexity, finite volume, `G 0 < ⊤`, and the explicit finite
energy assumption on `u`. The latter, as well as `Measurable G`, is not inferred from `W1p` alone.
This gives a density estimate for the contracted background only; no limit `t → 1` or recovery
sequence is asserted. -/
theorem mDirichletLimsup_vitali_density_le_Hp_of_cited [NeZero N]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (hDiff : CitedSobolevDiff N m p) (hp : (N : ℝ) < p)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hGmeas : Measurable G)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ dS : Sp N → ℝ≥0∞,
      (∀ᵐ x ∂(volume.restrict Ω),
        Tendsto
          (fun ρ => mDirichletLimsup (ENNReal.ofReal p) L
            (u.smul t).measurableGrad
            (cube ρ x) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (dS x))) ∧
      (∀ A, IsOpen A → A ⊆ Ω →
        vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L
          (u.smul t).measurableGrad) A ≤ ∫⁻ x in A, dS x) ∧
      ∀ᵐ x ∂(volume.restrict Ω),
        dS x ≤ Hp (ENNReal.ofReal p) L (t • u.grad x) := by
  have hG0 : G 0 < ⊤ := by
    have hdom : (0 : Mat m N) ∈ dom G := interior_subset h0
    exact hdom
  have htheta : t < (t + 1) / 2 := by linarith
  have htheta1 : (t + 1) / 2 ≤ 1 := by linarith
  let ut : W1p N m (ENNReal.ofReal p) Ω := u.smul t
  have ht0 : 0 ≤ t := le_of_lt ht
  have htle : t ≤ 1 := le_of_lt ht1
  have hGint_t : ∫⁻ y in Ω, G (ut.grad y) < ⊤ := by
    change ∫⁻ y in Ω, G (t • u.grad y) < ⊤
    exact hG.lintegral_smul_unit_lt_top (A := Ω) hΩbounded.measure_lt_top
      u.grad ht0 htle hG0 hGint
  obtain ⟨dS, hdensityRep, hEnvelope⟩ :=
    mDirichletLimsup_vitaliUpper_of_W1p Ω hΩopen hΩbounded G L ut hGrowth hGmeas hGint_t
  have hremAE := CitedSobolevDiff.affine_remainder_ae_small
    (N := N) (m := m) (p := p) hDiff hp Ω hΩopen u
  have hmeanAE := u.ae_tendsto_lintegral_G_grad_cube_ratio G hΩopen hGmeas hGint
  have hgradAE := ut.mDirichletLimsup_grad_congr_ae hΩopen L
  let C : ℝ → ℝ := fun s =>
    if hs : s ∈ Ioo (0 : ℝ) 1 then
      Classical.choose (exists_cutoff_fderiv_bound (N := N) hs)
    else 0
  have hC : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ C s := by
    intro s hs
    dsimp [C]
    rw [dif_pos hs]
    exact (Classical.choose_spec (exists_cutoff_fderiv_bound (N := N) hs)).1
  refine ⟨dS, hdensityRep, hEnvelope, ?_⟩
  filter_upwards [ae_restrict_mem hΩopen.measurableSet, hremAE, hmeanAE,
    hdensityRep, hgradAE] with x hxΩ hxrem hxmean hxdens hxgrad
  rcases hxrem with ⟨a, haff⟩
  rcases hxmean with ⟨hGxFinite, hmean⟩
  have hrem : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ η : ℝ, 0 < η →
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖u.toFun y - affineMap a (u.grad x) x y‖ ≤ η * ρ := by
    intro s hs η hη
    obtain ⟨ρ₀, hρ₀, hcube⟩ := haff η hη
    refine ⟨ρ₀, hρ₀, fun ρ hρ hρlt => ?_⟩
    exact ae_restrict_of_subset (U := cube ρ x)
      (V := cube ρ x \ cube (s * ρ) x) (hVU := fun y hy => hy.1)
      (hP := hcube ρ hρ hρlt)
  have hgradRep :
      (fun ρ : ℝ => mDirichletLimsup (ENNReal.ofReal p) L
        (fun y => t • u.grad y) (cube ρ x) / volume (cube ρ x)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ => mDirichletLimsup (ENNReal.ofReal p) L ut.measurableGrad
        (cube ρ x) / volume (cube ρ x)) := by
    filter_upwards [hxgrad] with ρ hρ
    have hfield : (t • u.grad) = (fun y => t • u.grad y) := by
      funext y
      rfl
    change mDirichletLimsup (ENNReal.ofReal p) L (t • u.grad)
      (cube ρ x) / volume (cube ρ x) = _ at hρ
    rw [hfield] at hρ
    exact hρ
  have hderiv : ∀ s (hs : s ∈ Ioo (0 : ℝ) 1), ∀ ρ, 0 < ρ → ∀ y,
      ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C s / ρ := by
    intro s hs ρ hρ y
    dsimp [C]
    rw [dif_pos hs]
    exact (Classical.choose_spec (exists_cutoff_fderiv_bound (N := N) hs)).2 ρ x y hρ
  exact mDirichletLimsup_vitali_density_le_Hp_of_affine_remainder
    hG hGrowth hLper hΩopen hΩbounded u (a := a) (ξ := u.grad x) (x := x) hxΩ
    ht htheta htheta1 hGxFinite hG0 h0
    C hC hderiv hrem hGint hmean (dS := dS) hxdens hgradRep

/-- For each fixed contraction `0 < t < 1`, the same Vitali density supplied by
`mDirichletLimsup_vitali_density_le_Hp_of_cited` bounds the Vitali envelope itself by the
contracted homogenized energy. The pointwise estimate `dS ≤ Hp (t • ∇u)` is integrated on each
open `A ⊆ Ω` and composed with the Vitali envelope estimate; no identification of the envelope
with its density is used. The witness `dS` may depend on `t`, so this result alone does not provide
a recovery sequence or a limit as `t → 1`. -/
theorem mDirichletLimsup_vitaliEnv_le_Hp_of_cited [NeZero N]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (hDiff : CitedSobolevDiff N m p) (hp : (N : ℝ) < p)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hGmeas : Measurable G)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ dS : Sp N → ℝ≥0∞,
      (∀ᵐ x ∂(volume.restrict Ω),
        Tendsto
          (fun ρ => mDirichletLimsup (ENNReal.ofReal p) L
            (u.smul t).measurableGrad (cube ρ x) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (dS x))) ∧
      (∀ A, IsOpen A → A ⊆ Ω →
        vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L
          (u.smul t).measurableGrad) A ≤ ∫⁻ x in A, dS x) ∧
      (∀ᵐ x ∂(volume.restrict Ω),
        dS x ≤ Hp (ENNReal.ofReal p) L (t • u.grad x)) ∧
      (∀ A, IsOpen A → A ⊆ Ω →
        vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L
          (u.smul t).measurableGrad) A ≤
          ∫⁻ x in A, Hp (ENNReal.ofReal p) L (t • u.grad x)) := by
  obtain ⟨dS, hDensity, hEnvelope, hPoint⟩ :=
    mDirichletLimsup_vitali_density_le_Hp_of_cited
      hG hGrowth hLper hΩopen hΩbounded u hDiff hp h0 hGmeas hGint ht ht1
  refine ⟨dS, hDensity, hEnvelope, hPoint, ?_⟩
  intro A hAopen hAΩ
  have hPointA : ∀ᵐ x ∂(volume.restrict A),
      dS x ≤ Hp (ENNReal.ofReal p) L (t • u.grad x) := by
    rw [ae_restrict_iff' hAopen.measurableSet]
    filter_upwards [(ae_restrict_iff' hΩopen.measurableSet).1 hPoint] with x hx hxA
    exact hx (hAΩ hxA)
  calc
    vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L
      (u.smul t).measurableGrad) A ≤ ∫⁻ x in A, dS x := hEnvelope A hAopen hAΩ
    _ ≤ ∫⁻ x in A, Hp (ENNReal.ofReal p) L (t • u.grad x) := lintegral_mono_ae hPointA

/-- Radial affine estimate for a ru-usc density. For each tolerance, all contractions above one
threshold satisfy `f(t ξ) ≤ (1+η) f̂(ξ) + η c`, where `f̂` is the radial envelope. The proof
compares `f(t ξ)` with `f(s ξ)` using the factor `t/s`, then lets `s → 1⁻`; it uses no
measurability. -/
theorem RUUSCWith.le_affine_radial {c : ℝ≥0} {f : Mat m N → ℝ≥0∞}
    (hruusc : RUUSCWith c (fun _ => f)) {η : ℝ≥0} (hη : 0 < η) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < 1 ∧
      ∀ t : ℝ, t₀ < t → t < 1 → ∀ ξ,
        f (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * Homogenization.radial f ξ +
          (η : ℝ≥0∞) * (c : ℝ≥0∞) := by
  have hnear := hruusc.le_affine hη
  obtain ⟨a, ha, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hnear
  let t₀ : ℝ := max a 0
  have ht₀ : t₀ < 1 := max_lt ha one_pos
  refine ⟨t₀, le_max_right a 0, ht₀, ?_⟩
  intro t htt ht1 ξ
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_right a 0) htt
  have hta : a < t := lt_of_le_of_lt (le_max_left a 0) htt
  have hrad := hruusc.tendsto_radial ξ
  have hcoef : (1 + (η : ℝ≥0∞)) ≠ ⊤ := by simp
  have hright : Tendsto
      (fun s : ℝ => (1 + (η : ℝ≥0∞)) * f (s • ξ) + (η : ℝ≥0∞) * c)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((1 + (η : ℝ≥0∞)) * Homogenization.radial f ξ +
        (η : ℝ≥0∞) * (c : ℝ≥0∞))) := by
    exact (ENNReal.Tendsto.const_mul (a := 1 + (η : ℝ≥0∞)) hrad (Or.inr hcoef)).add
      tendsto_const_nhds
  have hle : ∀ᶠ s in 𝓝[<] (1 : ℝ),
      f (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * f (s • ξ) +
        (η : ℝ≥0∞) * (c : ℝ≥0∞) := by
    have hmax : max t₀ t < 1 := max_lt ht₀ ht1
    filter_upwards [Ioo_mem_nhdsLT hmax] with s hs
    have hs0 : 0 < s := by
      have ht₀_nonneg : 0 ≤ t₀ := le_max_right a 0
      exact lt_of_le_of_lt ht₀_nonneg (lt_of_le_of_lt (le_max_left t₀ t) hs.1)
    have hts : t < s := lt_of_le_of_lt (le_max_right t₀ t) hs.1
    have htdiv : a < t / s := by
      calc a < t := hta
        _ < t / s := by
          rw [lt_div_iff₀ hs0]
          nlinarith [mul_lt_mul_of_pos_left hs.2 ht0]
    have hdivt : t / s < 1 := (div_lt_one hs0).2 hts
    have hest := hsub ⟨htdiv, hdivt⟩ 0 (s • ξ)
    rw [smul_smul, div_mul_cancel₀ t hs0.ne'] at hest
    exact hest
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hright hle

/-- Integrated radial affine estimate. It is obtained by monotonicity of the extended-valued
integral and the pointwise ru-usc estimate. No measurability assumption on `f`, `D`, or their
compositions is needed for this inequality of lower integrals. -/
theorem lintegral_le_radial_affine {c : ℝ≥0} {f : Mat m N → ℝ≥0∞}
    {η : ℝ≥0} {t : ℝ} {t₀ : ℝ}
    (hnear : ∀ t : ℝ, t₀ < t → t < 1 → ∀ ξ,
      f (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * Homogenization.radial f ξ +
        (η : ℝ≥0∞) * (c : ℝ≥0∞))
    (ht : t₀ < t) (ht1 : t < 1) (A : Set (Sp N)) (D : Sp N → Mat m N) :
    ∫⁻ x in A, f (t • D x) ≤
      (1 + (η : ℝ≥0∞)) * (∫⁻ x in A, Homogenization.radial f (D x)) +
        (η : ℝ≥0∞) * (c : ℝ≥0∞) * volume A := by
  calc
    ∫⁻ x in A, f (t • D x) ≤
        ∫⁻ x in A, ((1 + (η : ℝ≥0∞)) * Homogenization.radial f (D x) +
          (η : ℝ≥0∞) * (c : ℝ≥0∞)) :=
      lintegral_mono fun x => hnear t ht ht1 (D x)
    _ = (1 + (η : ℝ≥0∞)) * (∫⁻ x in A, Homogenization.radial f (D x)) +
        (η : ℝ≥0∞) * (c : ℝ≥0∞) * volume A := by
      rw [lintegral_add_right' _ aemeasurable_const,
        lintegral_const_mul' _ _ hane, setLIntegral_const]
where
  hane : (1 + (η : ℝ≥0∞)) ≠ ⊤ := by simp

/-- The fixed-contraction Vitali bound can be sharpened to a radial homogenized-density bound for
all contractions sufficiently close to one. `lsc_of_HW` transfers RU-usc of `L` to `Hp L`, and
`RUUSCWith.le_affine_radial` supplies a threshold, for the chosen tolerance, above which
`Hp(t ∇u) ≤ (1+η) radial(Hp)(∇u) + ηc`. The same density witness returned at each fixed `t`
still provides its cube-density limit and Vitali integral bound. This does not identify the
varying Vitali envelopes with `GammaLimsup` or construct a recovery family. No measurability of
`Hp` is needed for the integrated inequality. -/
theorem mDirichletLimsup_vitaliEnv_le_radialHp_of_cited [NeZero N]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    (hLruusc : RUUSC L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (hDiff : CitedSobolevDiff N m p) (hp : (N : ℝ) < p)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hGmeas : Measurable G)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤)
    {η : ℝ≥0} (hη : 0 < η) :
    ∃ c : ℝ≥0, 0 < c ∧ ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < 1 ∧
      ∀ t : ℝ, t₀ < t → t < 1 →
        ∃ dS : Sp N → ℝ≥0∞,
          (∀ᵐ x ∂(volume.restrict Ω),
            Tendsto
              (fun ρ => mDirichletLimsup (ENNReal.ofReal p) L
                (u.smul t).measurableGrad (cube ρ x) / volume (cube ρ x))
              (𝓝[>] (0 : ℝ)) (𝓝 (dS x))) ∧
          (∀ A, IsOpen A → A ⊆ Ω →
            vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L
              (u.smul t).measurableGrad) A ≤ ∫⁻ x in A, dS x) ∧
          (∀ᵐ x ∂(volume.restrict Ω),
            dS x ≤ Hp (ENNReal.ofReal p) L (t • u.grad x)) ∧
          (∀ A, IsOpen A → A ⊆ Ω →
            vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L
              (u.smul t).measurableGrad) A ≤
              (1 + (η : ℝ≥0∞)) *
                (∫⁻ x in A, radial (Hp (ENNReal.ofReal p) L) (u.grad x)) +
                (η : ℝ≥0∞) * c * volume A) := by
  obtain ⟨c, hc, hHpRuusc⟩ := (lsc_of_HW hLruusc).1
  obtain ⟨t₀, ht₀_nonneg, ht₀, hnear⟩ := hHpRuusc.le_affine_radial hη
  refine ⟨c, hc, t₀, ht₀_nonneg, ht₀, ?_⟩
  intro t htt ht1
  have htpos : 0 < t := lt_of_le_of_lt ht₀_nonneg htt
  obtain ⟨dS, hDensity, hEnvelope, hPoint, hPointwiseIntegral⟩ :=
    mDirichletLimsup_vitaliEnv_le_Hp_of_cited
      hG hGrowth hLper hΩopen hΩbounded u hDiff hp h0 hGmeas hGint htpos ht1
  refine ⟨dS, hDensity, hEnvelope, hPoint, ?_⟩
  intro A hAopen hAΩ
  have hInt := lintegral_le_radial_affine (c := c) (η := η) (t := t) (t₀ := t₀)
    (hnear := fun t' ht' ht'1 ξ => hnear t' ht' ht'1 ξ) htt ht1 A u.grad
  exact (hPointwiseIntegral A hAopen hAΩ).trans hInt

end Homogenization
