import Homogenization.Mollify
import Homogenization.Step4
import Homogenization.GammaConvergence
import Homogenization.Morrey

/-!
# Vitali truncations and remainder estimates for recovery sequences

This file formalizes near-optimal Vitali families, finite truncations suitable for the finite-cube
correction estimate, and small-measure/small-energy remainders. It does not construct correctors on
the truncated Vitali family, choose a diagonal in `ε` and the radius, connect the estimates to
`GammaLimsup`, or construct a recovery sequence; Proposition 2.1(ii) remains unproved.
-/

open MeasureTheory Filter Set Function TopologicalSpace
open scoped ENNReal Topology

namespace Homogenization

variable {N m : ℕ}

/-- If the Vitali infimum is finite, a family has cube energy within any positive tolerance of it.
The infimum need not be attained. This does not construct correctors on a finite truncation, control
any subsequent diagonal in `ε` and the radius, connect to `GammaLimsup`, or provide a recovery
sequence; Proposition 2.1(ii) remains unproved. -/
theorem vitaliDelta_exists_near_optimal
    (S : Set (Sp N) → ℝ≥0∞) {δ : ℝ} {A : Set (Sp N)}
    (hfinite : vitaliDelta S δ A ≠ ⊤) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ c ∈ VitaliFam δ A,
      ∑' i, S (cube (c i).1 (c i).2) ≤ vitaliDelta S δ A + η := by
  have hlt : vitaliDelta S δ A < vitaliDelta S δ A + η :=
    ENNReal.lt_add_right hfinite hη.ne'
  unfold vitaliDelta at hlt ⊢
  obtain ⟨c, hc⟩ := exists_lt_of_ciInf_lt hlt
  obtain ⟨hmem, hsum⟩ := (iInf_lt_iff).mp hc
  exact ⟨c, hmem, hsum.le⟩

/-- A finite truncation of a Vitali family is a disjoint family of cubes with closures in `A` and
with radii bounded by `δ`, in the form accepted by
`finite_cube_near_optimal_correction_lintegral_le`. The union is definitionally the first `n`
cubes used in `exists_finite_remainder_lt`. This does not construct correctors, take a diagonal,
connect to `GammaLimsup`, or construct a recovery sequence; Proposition 2.1(ii) remains unproved. -/
theorem VitaliFam.finite_truncation {δ : ℝ} {A : Set (Sp N)}
    {c : ℕ → ℝ × Sp N} (hc : c ∈ VitaliFam δ A) (n : ℕ) :
    let ρ : Fin n → ℝ := fun i => (c i.1).1
    let x : Fin n → Sp N := fun i => (c i.1).2
    (∀ i, 0 ≤ ρ i ∧ ρ i ≤ δ) ∧
    (∀ i, closure (cube (ρ i) (x i)) ⊆ A) ∧
    Pairwise (fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j))) ∧
    (⋃ i : Fin n, cube (ρ i) (x i)) ⊆ A := by
  dsimp only
  rcases hc with ⟨hρ, hclosure, hdisj, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hρ i.1).1, le_of_lt (hρ i.1).2⟩
  · intro i
    exact hclosure i.1
  · intro i j hij
    apply hdisj
    intro hEq
    exact hij (Fin.ext hEq)
  · intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    have hmem : y ∈ closure (cube (c i.1).1 (c i.1).2) := subset_closure hi
    exact hclosure i.1 hmem

/-- For a Vitali family whose covered set and energy are finite, some initial finite collection
leaves both small volume and small `f`-integral in the remainder. The proof only uses the given
finiteness of the integral, not measurability of `f`. This result does not construct correctors on
the truncated family, choose a diagonal in `ε` and the radius, connect to `GammaLimsup`, or provide
a recovery sequence; Proposition 2.1(ii) remains unproved. -/
theorem VitaliFam.exists_finite_remainder_lt
    {δ : ℝ} {A : Set (Sp N)} {c : ℕ → ℝ × Sp N} (hc : c ∈ VitaliFam δ A)
    (hA : MeasurableSet A) (hvol : volume A ≠ ⊤) (f : Sp N → ℝ≥0∞)
    (hf : ∫⁻ y in A, f y ≠ ⊤) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ n : ℕ,
      let R : Set (Sp N) := A \ ⋃ i : Fin n, cube (c i.1).1 (c i.1).2
      volume R < η ∧ ∫⁻ y in R, f y < η := by
  let Q : ℕ → Set (Sp N) := fun i => cube (c i).1 (c i).2
  let U : ℕ → Set (Sp N) := fun n => ⋃ i : Fin n, Q i
  let R : ℕ → Set (Sp N) := fun n => A \ U n
  have hQo : ∀ i, IsOpen (Q i) := fun i => isOpen_cube _ _
  have hUmeas : ∀ n, MeasurableSet (U n) := fun n =>
    MeasurableSet.iUnion fun i => (hQo i).measurableSet
  have hRmeas : ∀ n, MeasurableSet (R n) := fun n => hA.diff (hUmeas n)
  have hRsub : ∀ n, R n ⊆ A := fun _ => sdiff_subset
  have hUmono : Monotone U := by
    intro n k hnk y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨⟨i.1, Nat.lt_of_lt_of_le i.2 hnk⟩, hi⟩
  have hRanti : Antitone R := by
    intro n k hnk y hy
    exact ⟨hy.1, fun hyk => hy.2 (hUmono hnk hyk)⟩
  have hI : (⋂ n, R n) = A \ ⋃ i, Q i := by
    ext y
    simp only [Set.mem_iInter, Set.mem_sdiff]
    change (∀ n, y ∈ A ∧ y ∉ U n) ↔ y ∈ A ∧ y ∉ ⋃ i, Q i
    constructor
    · intro hy
      have hyA := (hy 0).1
      refine ⟨hyA, ?_⟩
      intro hnot
      rcases Set.mem_iUnion.mp hnot with ⟨i, hi⟩
      have hmem : y ∈ U (i + 1) := by
        exact Set.mem_iUnion.mpr ⟨⟨i, Nat.lt_succ_self _⟩, hi⟩
      exact (hy (i + 1)).2 hmem
    · rintro ⟨hyA, hyQ⟩ n
      refine ⟨hyA, ?_⟩
      intro hn
      rcases Set.mem_iUnion.mp hn with ⟨i, hi⟩
      apply hyQ
      exact Set.mem_iUnion.mpr ⟨(i : ℕ), hi⟩
  obtain ⟨hρ, hclosure, hdisj, hcover⟩ := hc
  have hnull : volume (A \ ⋃ i, Q i) = 0 := by simpa [Q] using hcover
  let ν : Measure (Sp N) := volume.withDensity f
  have hνA : ν A < ⊤ := by
    change (volume.withDensity f) A < ⊤
    rw [withDensity_apply f hA]
    exact hf.lt_top
  have hνnull : ν (A \ ⋃ i, Q i) = 0 := by
    change (volume.withDensity f) (A \ ⋃ i, Q i) = 0
    exact (withDensity_absolutelyContinuous volume f) hnull
  have hνI : ν (⋂ n, R n) = 0 := by rw [hI]; exact hνnull
  let μv : Measure (Sp N) := volume.restrict A
  have hvolLim : Tendsto (μv ∘ R) atTop (𝓝 (μv (⋂ n, R n))) := by
    apply tendsto_measure_iInter_atTop (fun n => (hRmeas n).nullMeasurableSet) hRanti
    refine ⟨0, ?_⟩
    apply ne_of_lt ?_
    have hle : μv (R 0) ≤ volume A := by
      calc
        μv (R 0) = volume (R 0 ∩ A) := by simp [μv, Measure.restrict_apply, hRmeas 0]
        _ ≤ volume A := measure_mono Set.inter_subset_right
    exact hle.trans_lt (lt_top_iff_ne_top.mpr hvol)
  have hνLim : Tendsto ((ν.restrict A) ∘ R) atTop (𝓝 ((ν.restrict A) (⋂ n, R n))) := by
    apply tendsto_measure_iInter_atTop (fun n => (hRmeas n).nullMeasurableSet) hRanti
    refine ⟨0, ?_⟩
    apply ne_of_lt ?_
    have hle : (ν.restrict A) (R 0) ≤ ν A := by
      calc
        (ν.restrict A) (R 0) = ν (R 0 ∩ A) := by simp [Measure.restrict_apply, hRmeas 0]
        _ ≤ ν A := measure_mono Set.inter_subset_right
    exact hle.trans_lt hνA
  have hvolLim0 : Tendsto (fun n => volume (R n)) atTop (𝓝 0) := by
    have hseq : (fun n => μv (R n)) = fun n => volume (R n) := by
      funext n
      change (volume.restrict A) (R n) = volume (R n)
      rw [Measure.restrict_apply (hRmeas n)]
      rw [Set.inter_eq_left.mpr (hRsub n)]
    have hlim0 : μv (⋂ n, R n) = 0 := by
      apply le_antisymm
      · calc
        μv (⋂ n, R n) ≤ volume (⋂ n, R n) := Measure.le_iff'.1 Measure.restrict_le_self _
        _ = 0 := by rw [hI]; exact hnull
      · exact bot_le
    change Tendsto (fun n => μv (R n)) atTop (𝓝 (μv (⋂ n, R n))) at hvolLim
    simpa only [hseq, hlim0] using hvolLim
  have hνLim0 : Tendsto (fun n => ∫⁻ y in R n, f y) atTop (𝓝 0) := by
    have hseq : (fun n => (ν.restrict A) (R n)) = fun n => ∫⁻ y in R n, f y := by
      funext n
      rw [Measure.restrict_apply (hRmeas n)]
      rw [Set.inter_eq_left.mpr (hRsub n)]
      rw [withDensity_apply f (hRmeas n)]
    have hlim0 : (ν.restrict A) (⋂ n, R n) = 0 := by
      apply le_antisymm
      · calc
        (ν.restrict A) (⋂ n, R n) ≤ ν (⋂ n, R n) := Measure.le_iff'.1 Measure.restrict_le_self _
        _ = 0 := hνI
      · exact bot_le
    change Tendsto (fun n => (ν.restrict A) (R n)) atTop
      (𝓝 ((ν.restrict A) (⋂ n, R n))) at hνLim
    simpa only [hseq, hlim0] using hνLim
  have hvolEventually : ∀ᶠ n in atTop, volume (R n) < η := by
    exact hvolLim0.eventually (Iio_mem_nhds hη)
  have hνEventually : ∀ᶠ n in atTop, ∫⁻ y in R n, f y < η := by
    exact hνLim0.eventually (Iio_mem_nhds hη)
  obtain ⟨n, hnvol, hnν⟩ := (hvolEventually.and hνEventually).exists
  refine ⟨n, ?_, ?_⟩
  · simpa [R, U, Q] using hnvol
  · simpa [R, U, Q] using hnν

/-- At a fixed `ε`, finitely many pairwise disjoint cubes provide a glued competitor whose energy is
bounded by the sum of the local `mDirichlet` values (with tolerance `δ` on each cube) and the
unchanged energy on the complement. Its distance from `u` has the stated coercivity/Poincaré
bound. This is only the finite-cube, fixed-`ε` assembly step: it proves no limit as `ε → 0`, no
diagonal in `ε` and the radius, no connection to `GammaLimsup`, and no passage `t → 1`; hence
Proposition 2.1(ii) remains unproved. -/
theorem W1p.exists_finiteCube_recovery_competitor [NeZero N]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    {n : ℕ} (ρ : Fin n → ℝ) (x : Fin n → Sp N) (R : ℝ)
    (hρR : ∀ i, ρ i ≤ R) (hQΩ : ∀ i, closure (cube (ρ i) (x i)) ⊆ Ω)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j)))
    (G : Mat m N → ℝ≥0∞) (α β c₀ : NNReal)
    (L : Sp N → Mat m N → ℝ≥0∞)
    (hGrowth : HasGGrowth G α β L) (hCoercive : IsCoercive p c₀ L)
    (hc₀ : 0 < c₀) (ε : ℝ)
    (hGmeas : Measurable (fun y => G (u.grad y)))
    (hGint : ∫⁻ y in ⋃ i, cube (ρ i) (x i), G (u.grad y) < ⊤)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ ψ : W1p N m (ENNReal.ofReal p) Ω,
      intFun L ε ψ ≤
          (∑ i, (mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)) + δ)) +
            ∫⁻ y in Ω \ ⋃ i, cube (ρ i) (x i), L (ε⁻¹ • y) (u.grad y) ∧
      ∫⁻ y in Ω, ‖ψ.toFun y - u.toFun y‖ₑ ^ p ≤
        (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ *
            ((∫⁻ y in ⋃ i, cube (ρ i) (x i),
              (β : ℝ≥0∞) * (1 + G (u.grad y))) + n * δ) +
            ∫⁻ y in ⋃ i, cube (ρ i) (x i), ‖u.grad y‖ₑ ^ p)) ∧
      edist ψ u ≤
        ((m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ *
            ((∫⁻ y in ⋃ i, cube (ρ i) (x i),
              (β : ℝ≥0∞) * (1 + G (u.grad y))) + n * δ) +
            ∫⁻ y in ⋃ i, cube (ρ i) (x i), ‖u.grad y‖ₑ ^ p))) ^ (1 / p) := by
  let U : Set (Sp N) := ⋃ i, cube (ρ i) (x i)
  let B : ℝ≥0∞ := (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
    (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ *
      ((∫⁻ y in U, (β : ℝ≥0∞) * (1 + G (u.grad y))) + n * δ) +
      ∫⁻ y in U, ‖u.grad y‖ₑ ^ p))
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 (Fact.out : 1 ≤ ENNReal.ofReal p)
  have hp0 : 0 < p := by linarith
  have hPt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hUΩ : U ⊆ Ω := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact hQΩ i (subset_closure hi)
  have hgradMeas : AEMeasurable u.grad (volume.restrict U) := by
    have hΩgrad := u.memLp_grad.aemeasurable
    apply hΩgrad.mono_ac
    exact Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set volume hUΩ)
  have hnormMeas : Measurable (fun ξ : Mat m N => ‖ξ‖ₑ ^ p) := by
    exact continuous_enorm.measurable.pow_const p
  have hD : AEMeasurable (fun y => ‖u.grad y‖ₑ ^ p) (volume.restrict U) :=
    hnormMeas.comp_aemeasurable hgradMeas
  obtain ⟨v, hv, henergy, hcorr⟩ := finite_cube_near_optimal_correction_lintegral_le
    ρ x hQd hρR G L hGrowth hCoercive hc₀ ε u.grad hGmeas hGint hδ hD
  have hQo : ∀ i, IsOpen (cube (ρ i) (x i)) := fun i => isOpen_cube _ _
  have hQΩ' : ∀ i, cube (ρ i) (x i) ⊆ Ω := fun i => (subset_closure.trans (hQΩ i))
  have hQf : ∀ i, volume (frontier (cube (ρ i) (x i))) = 0 :=
    fun i => volume_frontier_cube (ρ i) (x i)
  obtain ⟨ψ, hψfun, hψgrad, hEnergy⟩ :=
    W1p.add_finiteCubeCorrection_energy_eq hΩo hΩb u hQo hQΩ' hQf hQd hv L ε
  refine ⟨ψ, ?_, ?_, ?_⟩
  · have hlocal :
        (∑ i, ∫⁻ y in cube (ρ i) (x i),
          L (ε⁻¹ • y) (u.grad y + (v i).2 y)) ≤
          ∑ i, (mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)) + δ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact henergy i
    calc
      intFun L ε ψ =
          (∑ i, ∫⁻ y in cube (ρ i) (x i),
            L (ε⁻¹ • y) (u.grad y + (v i).2 y)) +
            ∫⁻ y in Ω \ U, L (ε⁻¹ • y) (u.grad y) := hEnergy
      _ ≤
          (∑ i, (mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)) + δ)) +
          ∫⁻ y in Ω \ U, L (ε⁻¹ • y) (u.grad y) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hlocal (∫⁻ y in Ω \ U, L (ε⁻¹ • y) (u.grad y))
  · calc
      ∫⁻ y in Ω, ‖ψ.toFun y - u.toFun y‖ₑ ^ p =
          ∫⁻ y in Ω, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p := by
            apply lintegral_congr
            intro y
            rw [hψfun]
            simp
      _ ≤ ∫⁻ y in Set.univ, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p :=
        lintegral_mono_set (μ := volume)
          (f := fun y : Sp N => ‖(finiteCubeCorrection v).1 y‖ₑ ^ p)
          (subset_univ Ω)
      _ = ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p := by simp
      _ ≤ B := by simpa [B, U] using hcorr
  · rw [W1p.edist_def,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 ENNReal.ofReal_ne_top, hPt]
    calc
      (∫⁻ y in Ω, ‖ψ.toFun y - u.toFun y‖ₑ ^ p) ^ (1 / p) ≤ B ^ (1 / p) := by
        apply ENNReal.rpow_le_rpow
        · calc
            ∫⁻ y in Ω, ‖ψ.toFun y - u.toFun y‖ₑ ^ p =
                ∫⁻ y in Ω, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p := by
                  apply lintegral_congr
                  intro y
                  rw [hψfun]
                  simp
            _ ≤ ∫⁻ y in Set.univ, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p :=
              lintegral_mono_set (μ := volume)
                (f := fun y : Sp N => ‖(finiteCubeCorrection v).1 y‖ₑ ^ p)
                (subset_univ Ω)
            _ = ∫⁻ y, ‖(finiteCubeCorrection v).1 y‖ₑ ^ p := by simp
            _ ≤ B := by simpa [B, U] using hcorr
        · positivity

/- The declarations below only choose a measurable representative of a Sobolev gradient. They do
not construct a Vitali-family correction, pass to a limit `t → 1`, or prove Proposition 2.1(ii). -/

/-- Replace the weak gradient field by its chosen measurable representative. This is only a
representative change: it does not connect to `vitaliEnv`, provide the Vitali-family correction,
pass to a limit `t → 1`, or prove Proposition 2.1(ii). -/
noncomputable def W1p.withMeasurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) : W1p N m p Ω where
  toFun := u.toFun
  grad := u.measurableGrad
  memLp := u.memLp
  memLp_grad := by
    refine ⟨u.memLp_grad.aestronglyMeasurable.congr u.grad_ae_measurableGrad, ?_⟩
    rw [← eLpNorm_congr_ae u.grad_ae_measurableGrad]
    exact u.memLp_grad.eLpNorm_lt_top
  weak := by
    intro ψ hψ hcompact hsupport v
    have hKΩ : tsupport ψ ⊆ Ω := hsupport
    have hKmeas : MeasurableSet (tsupport ψ) := hcompact.measurableSet
    have hgradK : u.grad =ᵐ[volume.restrict (tsupport ψ)] u.measurableGrad := by
      exact (ae_mono (Measure.restrict_mono_set volume hKΩ))
        u.grad_ae_measurableGrad
    have hgradGlobal : ∀ᵐ y ∂volume,
        ψ y • u.grad y v = ψ y • u.measurableGrad y v := by
      filter_upwards [(ae_restrict_iff' hKmeas).1 hgradK] with y hy
      by_cases hys : y ∈ tsupport ψ
      · exact congrArg (fun g : Mat m N => ψ y • g v) (hy hys)
      · simp [image_eq_zero_of_notMem_tsupport hys]
    calc
      ∫ y, fderiv ℝ ψ y v • u.toFun y = -∫ y, ψ y • u.grad y v :=
        u.weak ψ hψ hcompact hsupport v
      _ = -∫ y, ψ y • u.measurableGrad y v := by rw [integral_congr_ae hgradGlobal]

/-- The function component is unchanged by `withMeasurableGrad`. -/
theorem W1p.withMeasurableGrad_toFun {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) : u.withMeasurableGrad.toFun = u.toFun := rfl

/-- The gradient field of `withMeasurableGrad` is definitionally the measurable representative. -/
theorem W1p.withMeasurableGrad_grad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) : u.withMeasurableGrad.grad = u.measurableGrad := rfl

/-- The gradient of `withMeasurableGrad` is measurable on the ambient space. -/
theorem W1p.measurable_withMeasurableGrad_grad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (u : W1p N m p Ω) : Measurable u.withMeasurableGrad.grad := by
  simpa only [W1p.withMeasurableGrad_grad] using u.measurableGrad_measurable

/-- On a measurable domain, the energy is unchanged by replacing the weak gradient with its
measurable representative. -/
theorem W1p.intFun_withMeasurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ) (u : W1p N m p Ω)
    (hΩ : MeasurableSet Ω) :
    intFun L ε u.withMeasurableGrad = intFun L ε u := by
  unfold intFun
  apply setLIntegral_congr_fun_ae hΩ
  filter_upwards [(ae_restrict_iff' hΩ).1 u.grad_ae_measurableGrad] with y hy
  intro hyΩ
  exact congrArg (L (ε⁻¹ • y)) (hy hyΩ).symm

/-- The two representatives have zero `Lᵖ` pseudodistance when `p ≥ 1`. -/
theorem W1p.edist_withMeasurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    [Fact (1 ≤ p)] (u : W1p N m p Ω) :
    edist u.withMeasurableGrad u = 0 := by
  rw [W1p.edist_def]
  simp [W1p.withMeasurableGrad_toFun]

/-- The representative change is topologically invisible in the `Lᵖ` pseudometric topology. -/
theorem W1p.nhds_withMeasurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    [Fact (1 ≤ p)] (u : W1p N m p Ω) :
    𝓝 u.withMeasurableGrad = 𝓝 u := by
  apply Inseparable.nhds_eq
  exact uniformity_basis_edist.inseparable_iff_uniformity.mpr fun ε hε => by
    simp [u.edist_withMeasurableGrad, hε]

/-- Replacing `u` by its measurable-gradient representative leaves every `Γ`-limsup unchanged.
This representative preparation alone does not connect the Vitali envelope to `GammaLimsup`,
pass to `t → 1`, or prove Proposition 2.1(ii). -/
theorem GammaLimsup_withMeasurableGrad {p : ℝ≥0∞} {Ω : Set (Sp N)}
    [Fact (1 ≤ p)] (F : ℝ → W1p N m p Ω → ℝ≥0∞) (u : W1p N m p Ω) :
    GammaLimsup F u.withMeasurableGrad = GammaLimsup F u := by
  simp [GammaLimsup, W1p.nhds_withMeasurableGrad]

/-- For fixed cubes, choosing the finite-cube competitor at every `ε` gives a family with a uniform
`Lᵖ` distance bound and the expected limsup energy estimate. This does not choose a Vitali family,
take a diagonal in `ε` and the cube radii, connect the estimate to `GammaLimsup`, or pass `t → 1`;
Proposition 2.1(ii) remains unproved. -/
theorem W1p.exists_finiteCube_recovery_family [NeZero N]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    {n : ℕ} (ρ : Fin n → ℝ) (x : Fin n → Sp N) (R : ℝ)
    (hρR : ∀ i, ρ i ≤ R) (hQΩ : ∀ i, closure (cube (ρ i) (x i)) ⊆ Ω)
    (hQd : Pairwise fun i j => Disjoint (cube (ρ i) (x i)) (cube (ρ j) (x j)))
    (G : Mat m N → ℝ≥0∞) (α β c₀ : NNReal)
    (L : Sp N → Mat m N → ℝ≥0∞)
    (hGrowth : HasGGrowth G α β L) (hCoercive : IsCoercive p c₀ L)
    (hc₀ : 0 < c₀)
    (hGmeas : Measurable (fun y => G (u.grad y)))
    (hGint : ∫⁻ y in ⋃ i, cube (ρ i) (x i), G (u.grad y) < ⊤)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ v : ℝ → W1p N m (ENNReal.ofReal p) Ω,
      (∀ ε, edist (v ε) u ≤
        ((m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
          (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ *
            ((∫⁻ y in ⋃ i, cube (ρ i) (x i),
              (β : ℝ≥0∞) * (1 + G (u.grad y))) + n * δ) +
            ∫⁻ y in ⋃ i, cube (ρ i) (x i), ‖u.grad y‖ₑ ^ p))) ^ (1 / p)) ∧
      limsup (fun ε => intFun L ε (v ε)) (𝓝[>] 0) ≤
        (∑ i, mDirichletLimsup (ENNReal.ofReal p) L u.grad (cube (ρ i) (x i))) +
          n * δ +
          ∫⁻ y in Ω \ ⋃ i, cube (ρ i) (x i),
            (β : ℝ≥0∞) * (1 + G (u.grad y)) := by
  let U : Set (Sp N) := ⋃ i, cube (ρ i) (x i)
  let B : ℝ≥0∞ := (m : ℝ≥0∞) * ENNReal.ofReal R ^ p *
    (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ *
      ((∫⁻ y in U, (β : ℝ≥0∞) * (1 + G (u.grad y))) + n * δ) +
      ∫⁻ y in U, ‖u.grad y‖ₑ ^ p))
  have hchoose : ∀ ε : ℝ, ∃ ψ : W1p N m (ENNReal.ofReal p) Ω,
      intFun L ε ψ ≤
        (∑ i, (mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)) + δ)) +
          ∫⁻ y in Ω \ U, L (ε⁻¹ • y) (u.grad y) ∧ edist ψ u ≤ B ^ (1 / p) := by
    intro ε
    obtain ⟨ψ, hE, _, hdist⟩ := W1p.exists_finiteCube_recovery_competitor
      hΩo hΩb u ρ x R hρR hQΩ hQd G α β c₀ L hGrowth hCoercive hc₀ ε
      hGmeas (by simpa [U] using hGint) δ hδ
    exact ⟨ψ, hE, by simpa [B, U] using hdist⟩
  choose v hv using hchoose
  refine ⟨v, ?_, ?_⟩
  · intro ε
    exact (hv ε).2
  · let C : ℝ≥0∞ := n * δ +
      ∫⁻ y in Ω \ U, (β : ℝ≥0∞) * (1 + G (u.grad y))
    have hrem (ε : ℝ) :
        ∫⁻ y in Ω \ U, L (ε⁻¹ • y) (u.grad y) ≤
          ∫⁻ y in Ω \ U, (β : ℝ≥0∞) * (1 + G (u.grad y)) :=
      lintegral_mono fun y => (hGrowth (ε⁻¹ • y) (u.grad y)).2
    have hsum (ε : ℝ) :
        (∑ i, (mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)) + δ)) =
          (∑ i, mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i))) + n * δ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin]
      simp [nsmul_eq_mul]
    have henergy (ε : ℝ) : intFun L ε (v ε) ≤
        (∑ i, mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i))) + C := by
      calc
        intFun L ε (v ε) ≤
            (∑ i, (mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)) + δ)) +
              ∫⁻ y in Ω \ U, L (ε⁻¹ • y) (u.grad y) := (hv ε).1
        _ ≤ (∑ i, (mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)) + δ)) +
              ∫⁻ y in Ω \ U, (β : ℝ≥0∞) * (1 + G (u.grad y)) :=
                add_le_add le_rfl (hrem ε)
        _ = (∑ i, mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i))) + C := by
              rw [hsum]
              simp [C, add_assoc]
    calc
      limsup (fun ε => intFun L ε (v ε)) (𝓝[>] 0) ≤
          limsup (fun ε =>
            (∑ i, mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i))) + C)
              (𝓝[>] 0) :=
        limsup_le_limsup (Eventually.of_forall henergy)
      _ ≤ limsup (fun ε =>
            ∑ i, mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i)))
              (𝓝[>] 0) + C := by
        rw [limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)]
      _ ≤ (∑ i, limsup (fun ε =>
            mDirichlet (ENNReal.ofReal p) L ε u.grad (cube (ρ i) (x i))) (𝓝[>] 0)) + C := by
        exact add_le_add (limsup_finset_sum_le _ _) le_rfl
      _ = (∑ i, mDirichletLimsup (ENNReal.ofReal p) L u.grad (cube (ρ i) (x i))) + C := by
        simp only [mDirichletLimsup]
      _ = (∑ i, mDirichletLimsup (ENNReal.ofReal p) L u.grad (cube (ρ i) (x i))) +
          n * δ + ∫⁻ y in Ω \ U, (β : ℝ≥0∞) * (1 + G (u.grad y)) := by
        simp [C, add_assoc]
      _ = (∑ i, mDirichletLimsup (ENNReal.ofReal p) L u.grad (cube (ρ i) (x i))) +
          n * δ + ∫⁻ y in Ω \ ⋃ i, cube (ρ i) (x i),
            (β : ℝ≥0∞) * (1 + G (u.grad y)) := by rfl

/-- At a fixed radius `δ` and tolerance `η`, a near-optimal Vitali family is truncated and the
fixed-cube recovery family is applied: the family stays within `(C δ^p)^(1/p)` of `w`, with `C`
independent of `δ` and `η`, and its limsup energy is at most the Vitali envelope plus `η`.

The fixed-integrand Vitali recovery estimate does not pass to `t → 1`, bound its energy by
the radial homogenized energy, or prove the final form of Proposition 2.1(ii). -/
theorem W1p.exists_vitali_recovery_family [NeZero N]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (G : Mat m N → ℝ≥0∞) (α β c₀ : NNReal)
    (L : Sp N → Mat m N → ℝ≥0∞)
    (hGrowth : HasGGrowth G α β L) (hCoercive : IsCoercive p c₀ L)
    (hc₀ : 0 < c₀) (w : W1p N m (ENNReal.ofReal p) Ω)
    (hGmeas : Measurable (fun y => G (w.grad y)))
    (hGint : ∫⁻ y in Ω, G (w.grad y) < ⊤)
    (hfin : vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L w.grad) Ω ≠ ⊤)
    (δ : ℝ) (hδ : 0 < δ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ v : ℝ → W1p N m (ENNReal.ofReal p) Ω,
      (∀ ε, edist (v ε) w ≤
        (((m : ℝ≥0∞) * 2 ^ (p - 1) *
          ((c₀ : ℝ≥0∞)⁻¹ *
            ((∫⁻ y in Ω, (β : ℝ≥0∞) * (1 + G (w.grad y))) + 1) +
            ∫⁻ y in Ω, ‖w.grad y‖ₑ ^ p)) * ENNReal.ofReal δ ^ p) ^ (1 / p)) ∧
      limsup (fun ε => intFun L ε (v ε)) (𝓝[>] 0) ≤
        vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L w.grad) Ω + η := by
  let S : Set (Sp N) → ℝ≥0∞ := mDirichletLimsup (ENNReal.ofReal p) L w.grad
  let f : Sp N → ℝ≥0∞ := fun y => (β : ℝ≥0∞) * (1 + G (w.grad y))
  let C : ℝ≥0∞ := (m : ℝ≥0∞) * 2 ^ (p - 1) *
    ((c₀ : ℝ≥0∞)⁻¹ * ((∫⁻ y in Ω, f y) + 1) +
      ∫⁻ y in Ω, ‖w.grad y‖ₑ ^ p)
  have hδenv : vitaliDelta S δ Ω ≤ vitaliEnv S Ω :=
    le_iSup₂ (f := fun r (_ : 0 < r) => vitaliDelta S r Ω) δ hδ
  have hδfinite : vitaliDelta S δ Ω ≠ ⊤ := ne_top_of_le_ne_top hfin hδenv
  have hη3 : (0 : ℝ≥0∞) < η / 3 := ENNReal.div_pos hη.ne' (by norm_num)
  obtain ⟨c, hc, hcNear⟩ := vitaliDelta_exists_near_optimal S hδfinite hη3
  have hf : ∫⁻ y in Ω, f y ≠ ⊤ := by
    have h := mDirichletLimsup_le_growthDensity (p := ENNReal.ofReal p) G L w.grad Ω
      hGrowth hGmeas hΩb.measure_lt_top hGint
    exact ne_of_lt h.2
  obtain ⟨n, hnvol, hnrem⟩ := VitaliFam.exists_finite_remainder_lt hc
    hΩo.measurableSet hΩb.measure_lt_top.ne f hf hη3
  let ρ : Fin n → ℝ := fun i => (c i.1).1
  let x : Fin n → Sp N := fun i => (c i.1).2
  let U : Set (Sp N) := ⋃ i : Fin n, cube (ρ i) (x i)
  obtain ⟨hρ, hQΩ, hQd, hUΩ⟩ := VitaliFam.finite_truncation hc n
  let τ : ℝ≥0∞ := min (η / 3) 1 / ((n : ℝ≥0∞) + 1)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact ENNReal.div_pos (lt_min hη3 (by norm_num)).ne' (by simp)
  have hntau0 : n * τ ≤ min (η / 3) 1 := by
    dsimp [τ]
    calc
      (n : ℝ≥0∞) * (min (η / 3) 1 / ((n : ℝ≥0∞) + 1)) ≤
          ((n : ℝ≥0∞) + 1) * (min (η / 3) 1 / ((n : ℝ≥0∞) + 1)) := by
            gcongr
            simp
      _ ≤ min (η / 3) 1 := ENNReal.mul_div_le
  have hUenergy : ∫⁻ y in U, G (w.grad y) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (by simpa [U, ρ, x] using hUΩ)) hGint
  obtain ⟨v, hvDist, hvEnergy⟩ := W1p.exists_finiteCube_recovery_family
    hΩo hΩb w ρ x δ (fun i => (hρ i).2) hQΩ hQd G α β c₀ L hGrowth hCoercive hc₀ hGmeas
    (by simpa [U] using hUenergy) τ hτ
  refine ⟨v, ?_, ?_⟩
  · intro ε
    let B : ℝ≥0∞ := (m : ℝ≥0∞) * ENNReal.ofReal δ ^ p *
      (2 ^ (p - 1) * ((c₀ : ℝ≥0∞)⁻¹ * ((∫⁻ y in U, f y) + n * τ) +
        ∫⁻ y in U, ‖w.grad y‖ₑ ^ p))
    have hntau : n * τ ≤ min (η / 3) 1 := hntau0
    have hUintegral : ∫⁻ y in U, f y ≤ ∫⁻ y in Ω, f y :=
      lintegral_mono_set (by simpa [U, ρ, x] using hUΩ)
    have hinner :
        (c₀ : ℝ≥0∞)⁻¹ * ((∫⁻ y in U, f y) + n * τ) +
            ∫⁻ y in U, ‖w.grad y‖ₑ ^ p ≤
          (c₀ : ℝ≥0∞)⁻¹ * ((∫⁻ y in Ω, f y) + 1) +
            ∫⁻ y in Ω, ‖w.grad y‖ₑ ^ p := by
      apply add_le_add
      · gcongr
        exact le_trans hntau (min_le_right _ _)
      · exact lintegral_mono_set (by simpa [U, ρ, x] using hUΩ)
    have hbase : B ≤ C * ENNReal.ofReal δ ^ p := by
      dsimp [B, C]
      calc
        (↑m * ENNReal.ofReal δ ^ p *
            (2 ^ (p - 1) * ((↑c₀)⁻¹ * ((∫⁻ y in U, f y) + ↑n * τ) +
              ∫⁻ y in U, ‖w.grad y‖ₑ ^ p))) =
            (↑m * 2 ^ (p - 1) *
              ((↑c₀)⁻¹ * ((∫⁻ y in U, f y) + ↑n * τ) +
                ∫⁻ y in U, ‖w.grad y‖ₑ ^ p)) * ENNReal.ofReal δ ^ p := by ac_rfl
        _ ≤ (↑m * 2 ^ (p - 1) *
              ((↑c₀)⁻¹ * ((∫⁻ y in Ω, f y) + 1) +
                ∫⁻ y in Ω, ‖w.grad y‖ₑ ^ p)) * ENNReal.ofReal δ ^ p :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinner (by positivity)) (by positivity)
    exact (hvDist ε).trans (ENNReal.rpow_le_rpow hbase (by
      have hp : 0 < p := by
        have : 1 ≤ ENNReal.ofReal p := Fact.out
        exact ENNReal.ofReal_pos.mp (lt_of_lt_of_le (by norm_num) this)
      positivity))
  · have hnτ : n * τ ≤ η / 3 := le_trans hntau0 (min_le_left _ _)
    have hsum : (∑ i : Fin n, S (cube (ρ i) (x i))) ≤
        ∑' i : ℕ, S (cube (c i).1 (c i).2) := by
      change (∑ i : Fin n, S (cube (c i.1).1 (c i.1).2)) ≤ _
      rw [Fin.sum_univ_eq_sum_range (fun i => S (cube (c i).1 (c i).2)) n]
      exact ENNReal.sum_le_tsum (Finset.range n)
    have hrem : ∫⁻ y in Ω \ U, f y < η / 3 := by
      simpa [U, ρ, x, f] using hnrem
    have hvE : limsup (fun ε => intFun L ε (v ε)) (𝓝[>] 0) ≤
        (∑ i : Fin n, S (cube (ρ i) (x i))) + n * τ + ∫⁻ y in Ω \ U, f y := by
      simpa [S, U, ρ, x, f] using hvEnergy
    calc limsup (fun ε => intFun L ε (v ε)) (𝓝[>] 0)
        ≤ (∑ i : Fin n, S (cube (ρ i) (x i))) + n * τ + ∫⁻ y in Ω \ U, f y := hvE
      _ ≤ vitaliEnv S Ω + η := by
        have hnear : (∑ i : Fin n, S (cube (ρ i) (x i))) ≤ vitaliEnv S Ω + η / 3 := by
          calc _ ≤ ∑' i : ℕ, S (cube (c i).1 (c i).2) := hsum
            _ ≤ vitaliDelta S δ Ω + η / 3 := hcNear
            _ ≤ vitaliEnv S Ω + η / 3 := add_le_add hδenv le_rfl
        calc _ ≤ (vitaliEnv S Ω + η / 3) + η / 3 + η / 3 := by
              gcongr
          _ = vitaliEnv S Ω + η := by
              have ht : η / 3 + η / 3 + η / 3 = η := by
                calc
                  η / 3 + η / 3 + η / 3 = 3 * (η / 3) := by ring
                  _ = η :=
                    ENNReal.mul_div_cancel (a := 3) (b := η) (by norm_num) (by norm_num)
              simp [add_assoc, ht]

/-- This proves the fixed-integrand connection to `GammaLimsup`. It does not pass to `t → 1`,
bound the result by the radial homogenized energy, or prove the final form of Proposition 2.1(ii).
The explicit assumptions `Measurable G` and `∫_Ω G(∇u) < ⊤` remain in force. -/
theorem GammaLimsup_le_vitaliEnv_mDirichletLimsup [NeZero N]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (G : Mat m N → ℝ≥0∞) (α β c₀ : NNReal)
    (L : Sp N → Mat m N → ℝ≥0∞)
    (hGrowth : HasGGrowth G α β L) (hCoercive : IsCoercive p c₀ L)
    (hc₀ : 0 < c₀) (u : W1p N m (ENNReal.ofReal p) Ω)
    (hGm : Measurable G) (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤) :
    GammaLimsup (X := W1p N m (ENNReal.ofReal p) Ω) (intFun L) u ≤
      vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L u.measurableGrad) Ω := by
  by_cases htop : vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L u.measurableGrad) Ω = ⊤
  · simp [htop]
  · let w : W1p N m (ENNReal.ofReal p) Ω := u.withMeasurableGrad
    have hwmeas : Measurable (fun y => G (w.grad y)) := by
      exact hGm.comp (W1p.measurable_withMeasurableGrad_grad u)
    have hwint : ∫⁻ y in Ω, G (w.grad y) < ⊤ := by
      change ∫⁻ y in Ω, G (u.measurableGrad y) < ⊤
      rw [← W1p.lintegral_G_grad_eq_measurableGrad u G hΩo]
      exact hGint
    have hSfinite : vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L w.grad) Ω ≠ ⊤ := by
      simpa [w, W1p.withMeasurableGrad_grad] using htop
    let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    let η : ℕ → ℝ≥0∞ := fun k => ((k : ℝ≥0∞) + 1)⁻¹
    have hδpos : ∀ k, 0 < δ k := by intro k; positivity
    have hηpos : ∀ k, 0 < η k := by intro k; simp [η]
    choose v hv using fun k => W1p.exists_vitali_recovery_family
      hΩo hΩb G α β c₀ L hGrowth hCoercive hc₀ w hwmeas hwint hSfinite
      (δ k) (hδpos k) (η k) (hηpos k)
    let C : ℝ≥0∞ := (m : ℝ≥0∞) * 2 ^ (p - 1) *
      ((c₀ : ℝ≥0∞)⁻¹ *
        ((∫⁻ y in Ω, (β : ℝ≥0∞) * (1 + G (w.grad y))) + 1) +
        ∫⁻ y in Ω, ‖w.grad y‖ₑ ^ p)
    have hCtop : C < ⊤ := by
      have hF : ∫⁻ y in Ω, (β : ℝ≥0∞) * (1 + G (w.grad y)) < ⊤ := by
        exact (mDirichletLimsup_le_growthDensity (p := ENNReal.ofReal p) G L
          w.grad Ω hGrowth hwmeas hΩb.measure_lt_top hwint).2
      have hp1 : 1 ≤ p := by
        have hp0' : 0 ≤ p := le_of_lt (ENNReal.ofReal_pos.mp
          (lt_of_lt_of_le (by norm_num) (Fact.out : 1 ≤ ENNReal.ofReal p)))
        apply (ENNReal.ofReal_le_ofReal_iff hp0').mp
        simpa using (Fact.out : 1 ≤ ENNReal.ofReal p)
      have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp1
      have hpPow : (2 : ℝ≥0∞) ^ (p - 1) < ⊤ := by
        exact (ENNReal.rpow_ne_top_of_nonneg (by linarith : 0 ≤ p - 1)
          ENNReal.ofNat_ne_top).lt_top
      have hgrad : ∫⁻ y in Ω, ‖w.grad y‖ₑ ^ (ENNReal.ofReal p).toReal < ⊤ :=
        lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top
          w.memLp_grad.2
      have hgrad' : ∫⁻ y in Ω, ‖w.grad y‖ₑ ^ p < ⊤ := by
        simpa [ENNReal.toReal_ofReal (le_of_lt hp0)] using hgrad
      dsimp [C]
      apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top (by simp) hpPow
      · exact (ENNReal.add_lt_top).2 ⟨
          ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by exact_mod_cast hc₀))
            ((ENNReal.add_lt_top).2 ⟨hF, by simp⟩),
          hgrad'⟩
    let r : ℕ → ℝ≥0∞ := fun k =>
      (C * ENNReal.ofReal (δ k) ^ p) ^ (1 / p)
    have hδtend : Tendsto (fun k => ENNReal.ofReal (δ k)) atTop (𝓝 0) := by
      have hreal : Tendsto δ atTop (𝓝 0) := by
        simpa [δ] using (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0))
      have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
      simpa [Function.comp_def] using h
    have hp0 : 0 < p := by
      have hp1 : 1 ≤ p := by
        have hp0' : 0 ≤ p := le_of_lt (ENNReal.ofReal_pos.mp
          (lt_of_lt_of_le (by norm_num) (Fact.out : 1 ≤ ENNReal.ofReal p)))
        apply (ENNReal.ofReal_le_ofReal_iff hp0').mp
        simpa using (Fact.out : 1 ≤ ENNReal.ofReal p)
      linarith
    have hinnerTend : Tendsto (fun k => C * ENNReal.ofReal (δ k) ^ p) atTop (𝓝 0) := by
      have hpow := (ENNReal.continuous_rpow_const (y := p)).continuousAt.tendsto.comp hδtend
      have hpow' : Tendsto (fun k => ENNReal.ofReal (δ k) ^ p) atTop (𝓝 0) := by
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp0] using hpow
      simpa using ENNReal.Tendsto.const_mul hpow' (Or.inr (ne_of_lt hCtop))
    have hr : Tendsto r atTop (𝓝 0) := by
      have houter :=
        (ENNReal.continuous_rpow_const (y := 1 / p)).continuousAt.tendsto.comp hinnerTend
      have hz : (0 : ℝ≥0∞) ^ (1 / p) = 0 :=
        ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)
      rw [hz] at houter
      simpa [r, Function.comp_def] using houter
    let a : ℕ → ℝ≥0∞ := fun k =>
      vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L w.grad) Ω + η k
    have hηtend : Tendsto η atTop (𝓝 0) := by
      have h : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [η] using h
    have hatend : Tendsto a atTop
        (𝓝 (vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L w.grad) Ω)) := by
      simpa [a, add_zero] using tendsto_const_nhds.add hηtend
    have hdist : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), edist (v k ε) w ≤ r k := by
      intro k
      filter_upwards [Filter.Eventually.of_forall (hv k).1] with ε hε
      exact hε
    have henergy : ∀ k,
        limsup (fun ε => intFun L ε (v k ε)) (𝓝[>] 0) ≤ a k := by
      intro k
      simpa [a] using (hv k).2
    have hdiag := GammaLimsup_le_limsup_of_diagonal (intFun L) w v r a hr hdist henergy
    calc GammaLimsup (intFun L) u = GammaLimsup (intFun L) w := by
          symm
          exact GammaLimsup_withMeasurableGrad (intFun L) u
      _ ≤ limsup a atTop := hdiag
      _ = vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L w.grad) Ω := hatend.limsup_eq
      _ = vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L u.measurableGrad) Ω := by
          simp [w, W1p.withMeasurableGrad_grad]

/-- The radial Vitali-envelope bound with its RU-usc constant chosen uniformly before the
tolerance. For every positive tolerance, contractions sufficiently close to one satisfy the same
integrated estimate with that fixed constant. It only bounds the Vitali envelopes of the contracted
problems; by itself it gives no `GammaLimsup` bound and no recovery sequence. -/
theorem mDirichletLimsup_vitaliEnv_le_radialHp_of_cited_uniform [NeZero N]
    {G : Mat m N → ℝ≥0∞} {α β : NNReal}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L) (hLper : IsPeriodic L)
    (hLruusc : RUUSC L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (hDiff : CitedSobolevDiff N m p) (hp : (N : ℝ) < p)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hGmeas : Measurable G)
    (hGint : ∫⁻ y in Ω, G (u.grad y) < ⊤) :
    ∃ c : NNReal, 0 < c ∧ ∀ η : NNReal, 0 < η →
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < 1 ∧
        ∀ t : ℝ, t₀ < t → t < 1 → ∀ A, IsOpen A → A ⊆ Ω →
          vitaliEnv (mDirichletLimsup (ENNReal.ofReal p) L
            (u.smul t).measurableGrad) A ≤
            (1 + (η : ℝ≥0∞)) *
              (∫⁻ x in A, radial (Hp (ENNReal.ofReal p) L) (u.grad x)) +
              (η : ℝ≥0∞) * c * volume A := by
  obtain ⟨c, hc, hHpRuusc⟩ := (lsc_of_HW hLruusc).1
  refine ⟨c, hc, ?_⟩
  intro η hη
  obtain ⟨t₀, ht₀_nonneg, ht₀, hnear⟩ := hHpRuusc.le_affine_radial hη
  refine ⟨t₀, ht₀_nonneg, ht₀, ?_⟩
  intro t htt ht1 A hAopen hAΩ
  have htpos : 0 < t := lt_of_le_of_lt ht₀_nonneg htt
  obtain ⟨_, _, _, hBound⟩ := mDirichletLimsup_vitaliEnv_le_Hp_of_cited
    hG hGrowth hLper hΩopen hΩbounded u hDiff hp h0 hGmeas hGint htpos ht1
  have hInt := lintegral_le_radial_affine (c := c) (η := η) (t := t) (t₀ := t₀)
    (hnear := fun t' ht' ht'1 ξ => hnear t' ht' ht'1 ξ) htt ht1 A u.grad
  exact (hBound.2 A hAopen hAΩ).trans hInt

/-- This is the Γ-limsup upper bound of Proposition 2.1(ii), under the already agreed cited
interface (b), `Measurable G`, and the explicit finite-energy assumption
`∫_Ω G(∇u) < ⊤`. The latter two are removed in
`GammaLimsup_le_intHom_radialHp`. The lower bound (i) is unaffected. -/
theorem GammaLimsup_le_intHom_radialHp_of_cited [NeZero N]
    {G : Mat m N → ℝ≥0∞} {α β : NNReal}
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
    {c₀ : NNReal} (hCoercive : IsCoercive p c₀ L) (hc₀ : 0 < c₀) :
    GammaLimsup (X := W1p N m (ENNReal.ofReal p) Ω) (intFun L) u ≤
      intHom (radial (Hp (ENNReal.ofReal p) L)) u := by
  let I : ℝ≥0∞ := ∫⁻ x in Ω, radial (Hp (ENNReal.ofReal p) L) (u.grad x)
  by_cases hI : I = ⊤
  · simp [intHom, I, hI]
  have hG0 : G 0 < ⊤ := by
    have hmem : (0 : Mat m N) ∈ dom G := interior_subset h0
    simpa [dom] using hmem
  have hcontract : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∫⁻ y in Ω, G ((u.smul t).grad y) < ⊤ := by
    intro t ht0 ht1
    simpa [W1p.smul] using hG.lintegral_smul_unit_lt_top hΩbounded.measure_lt_top
      u.grad (le_of_lt ht0) ht1 hG0 hGint
  obtain ⟨c, hc, hηbounds⟩ := mDirichletLimsup_vitaliEnv_le_radialHp_of_cited_uniform
    hG hGrowth hLper hLruusc hΩopen hΩbounded u hDiff hp h0 hGmeas hGint
  have hVol : volume Ω < ⊤ := hΩbounded.measure_lt_top
  have hIlt : I < ⊤ := lt_of_le_of_ne le_top hI
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  let η : NNReal := (δ / (I + (c : ℝ≥0∞) * volume Ω + 1)).toNNReal
  have hηpos : 0 < η := by
    dsimp [η]
    have hden0 : 0 < I + (c : ℝ≥0∞) * volume Ω + 1 := by positivity
    have hdenTop : I + (c : ℝ≥0∞) * volume Ω + 1 ≠ ⊤ := by
      have hprod : (c : ℝ≥0∞) * volume Ω ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) hVol.ne
      have hsum : I + (c : ℝ≥0∞) * volume Ω ≠ ⊤ :=
        (ENNReal.add_ne_top).2 ⟨hIlt.ne, hprod⟩
      exact (ENNReal.add_ne_top).2 ⟨hsum, ENNReal.one_ne_top⟩
    have hratio : 0 < δ / (I + (c : ℝ≥0∞) * volume Ω + 1) :=
      ENNReal.div_pos (by exact_mod_cast hδ.ne') hdenTop
    exact ENNReal.toNNReal_pos hratio.ne' (ENNReal.div_ne_top (by simp) hden0.ne')
  obtain ⟨t₀, ht₀nonneg, ht₀lt, hnear⟩ := hηbounds η hηpos
  let t : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2)
  have htend : Tendsto t atTop (𝓝 1) := by
    have hinv : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
      have hnat : Tendsto (fun j : ℕ => ((j + 2 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
      convert tendsto_inv_atTop_zero.comp hnat using 1; norm_num [one_div, Function.comp_def]
    simpa [t] using tendsto_const_nhds.sub hinv
  have htmem : ∀ᶠ j in atTop, t₀ < t j ∧ t j < 1 := by
    have hn : ∀ᶠ j in atTop, |t j - 1| < 1 - t₀ :=
      htend.eventually (Metric.ball_mem_nhds _ (sub_pos.mpr ht₀lt))
    filter_upwards [hn] with j hj
    have habs : |t j - 1| < 1 - t₀ := by simpa [Real.dist_eq] using hj
    have habs' := abs_lt.mp habs
    constructor
    · dsimp [t]
      linarith
    · dsimp [t]
      have : 0 < 1 / ((j : ℝ) + 2) := by positivity
      linarith
  have hseq : Tendsto (fun j : ℕ => u.smul (t j)) atTop (𝓝 u) := by
    let ρ : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal |t j - 1| *
      eLpNorm u.toFun (ENNReal.ofReal p) (volume.restrict Ω)
    have hρ : Tendsto ρ atTop (𝓝 0) := by
      have hreal : Tendsto (fun j : ℕ => |t j - 1|) atTop (𝓝 0) := by
        have hminus : Tendsto (fun j : ℕ => t j - 1) atTop (𝓝 0) := by
          simpa using htend.sub_const 1
        simpa [Function.comp_def] using (continuous_abs.tendsto 0).comp hminus
      have hscalar : Tendsto (fun j : ℕ => ENNReal.ofReal |t j - 1|) atTop (𝓝 0) :=
        by simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hreal
      have hnorm : eLpNorm u.toFun (ENNReal.ofReal p) (volume.restrict Ω) ≠ ⊤ :=
        ne_of_lt u.memLp.eLpNorm_lt_top
      simpa only [ρ, Function.comp_def, zero_mul] using
        ((ENNReal.continuous_mul_const hnorm).tendsto 0).comp hscalar
    apply tendsto_of_edist_le tendsto_const_nhds hρ
    filter_upwards with j
    rw [W1p.edist_def]
    have hfun : (u.smul (t j)).toFun - u.toFun = (t j - 1) • u.toFun := by
      ext x k
      simp [W1p.smul]
      ring
    rw [hfun, eLpNorm_const_smul]
    simp [ρ, Real.enorm_eq_ofReal_abs]
  have hGamma := GammaLimsup_le_liminf (intFun L) hseq
  have henergy : ∀ᶠ j in atTop,
      GammaLimsup (intFun L) (u.smul (t j)) ≤
        (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω := by
    filter_upwards [htmem] with j hj
    have htpos : 0 < t j := lt_of_le_of_lt ht₀nonneg hj.1
    have hv := GammaLimsup_le_vitaliEnv_mDirichletLimsup hΩopen hΩbounded G α β c₀ L
      hGrowth hCoercive hc₀ (u.smul (t j)) hGmeas (hcontract (t j) htpos hj.2.le)
    have hrad := hnear (t j) hj.1 hj.2 Ω hΩopen (Set.Subset.rfl)
    simpa [I] using hv.trans hrad
  have hliminf : liminf (fun j : ℕ => GammaLimsup (intFun L) (u.smul (t j))) atTop ≤
      (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω :=
    liminf_le_of_frequently_le' (henergy.frequently)
  have hbound := hGamma.trans hliminf
  -- Let the tolerance tend to zero, using finiteness of the target integral and volume.
  have hηineq : (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω ≤ I + δ := by
    let D : ℝ≥0∞ := I + (c : ℝ≥0∞) * volume Ω + 1
    have hD0 : D ≠ 0 := by dsimp [D]; positivity
    have hDtop : D ≠ ⊤ := by
      dsimp [D]
      have hsum : I + (c : ℝ≥0∞) * volume Ω ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hIlt.ne,
          ENNReal.mul_ne_top (by simp) hVol.ne⟩
      exact ENNReal.add_ne_top.mpr ⟨hsum, ENNReal.one_ne_top⟩
    have hetaCoe : (η : ℝ≥0∞) = δ / D := by
      change ((δ / D).toNNReal : ℝ≥0∞) = δ / D
      exact ENNReal.coe_toNNReal (ENNReal.div_ne_top (by simp) hD0)
    rw [hetaCoe]
    have hsmall : I + (c : ℝ≥0∞) * volume Ω ≤ D := by
      dsimp [D]
      exact le_add_of_nonneg_right (by simp)
    have hmul : (δ / D) * (I + (c : ℝ≥0∞) * volume Ω) ≤ δ := by
      calc
        (δ / D) * (I + (c : ℝ≥0∞) * volume Ω) ≤ (δ / D) * D :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = δ := ENNReal.div_mul_cancel hD0 hDtop
    calc
      (1 + δ / D) * I + δ / D * c * volume Ω =
          I + (δ / D) * (I + (c : ℝ≥0∞) * volume Ω) := by ring
      _ ≤ I + δ := add_le_add_right hmul I
  exact (hbound.trans hηineq).trans (by simp [intHom, I])

/-- `G` restricted to the interior of its effective domain, `⊤` elsewhere. Auxiliary step to
remove `Measurable G` and `∫_Ω G(∇u) < ⊤` from the Γ-limsup bound;
that removal is not proved here. -/
noncomputable def intDomRestrict (G : Mat m N → ℝ≥0∞) : Mat m N → ℝ≥0∞ := by
  classical
  exact fun ξ => if ξ ∈ interior (dom G) then G ξ else ⊤

/-- On the interior of `dom G`, `intDomRestrict` agrees with `G`. -/
theorem intDomRestrict_of_mem {G : Mat m N → ℝ≥0∞} {ξ : Mat m N}
    (h : ξ ∈ interior (dom G)) : intDomRestrict G ξ = G ξ := by
  simp [intDomRestrict, h]

/-- Restricting to the interior of the effective domain can only increase `G`. -/
theorem le_intDomRestrict (G : Mat m N → ℝ≥0∞) (ξ : Mat m N) :
    G ξ ≤ intDomRestrict G ξ := by
  classical
  by_cases h : ξ ∈ interior (dom G)
  · simp [intDomRestrict, h]
  · simp [intDomRestrict, h]

/-- The effective domain of `intDomRestrict G` is the interior of `dom G`. -/
theorem dom_intDomRestrict (G : Mat m N → ℝ≥0∞) :
    dom (intDomRestrict G) = interior (dom G) := by
  classical
  ext ξ
  change intDomRestrict G ξ < ⊤ ↔ ξ ∈ interior (dom G)
  by_cases h : ξ ∈ interior (dom G)
  · have hfinite : G ξ < ⊤ := by simpa [dom] using interior_subset h
    simp [intDomRestrict, h, hfinite]
  · simp [intDomRestrict, h]

/-- Convexity is preserved by restricting `G` to `interior (dom G)` and setting the value to `⊤`.
This is an auxiliary step for removing the measurability and finite-energy assumptions; that
removal is not proved here. -/
theorem ConvexENN.intDomRestrict {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) :
    ConvexENN (Homogenization.intDomRestrict G) := by
  classical
  intro ξ ζ t ht
  by_cases ht0 : t = 0
  · subst t
    simp
  by_cases ht1 : t = 1
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne (by positivity) (Ne.symm ht0)
  have htlt : t < 1 := (lt_or_eq_of_le ht).resolve_right ht1
  have hcoeff : (1 : ℝ≥0∞) - (t : ℝ≥0∞) ≠ 0 := by
    have htltENN : (t : ℝ≥0∞) < 1 := by exact_mod_cast htlt
    exact ne_of_gt (tsub_pos_iff_lt.mpr htltENN)
  by_cases hξ : ξ ∈ interior (dom G)
  · by_cases hζ : ζ ∈ interior (dom G)
    · have hcombo : (t : ℝ) • ξ + (((1 : NNReal) - t : NNReal) : ℝ) • ζ ∈
          interior (dom G) := by
        have hI : Convex ℝ (interior (dom G)) := hG.convex_dom.interior
        refine hI hξ hζ (a := (t : ℝ))
          (b := (((1 : NNReal) - t : NNReal) : ℝ)) ?_ ?_ ?_
        · exact_mod_cast (show 0 ≤ t by positivity)
        · exact_mod_cast (show 0 ≤ ((1 : NNReal) - t : NNReal) by positivity)
        · exact_mod_cast (add_tsub_cancel_of_le ht)
      rw [intDomRestrict_of_mem hcombo, intDomRestrict_of_mem hξ,
        intDomRestrict_of_mem hζ]
      exact hG ξ ζ t ht
    · have hrhs : (t : ℝ≥0∞) * Homogenization.intDomRestrict G ξ +
          (1 - (t : ℝ≥0∞)) * Homogenization.intDomRestrict G ζ = ⊤ := by
        simp [Homogenization.intDomRestrict, hζ, hcoeff]
      calc
        _ ≤ ⊤ := le_top
        _ = (t : ℝ≥0∞) * Homogenization.intDomRestrict G ξ +
            (1 - (t : ℝ≥0∞)) * Homogenization.intDomRestrict G ζ := hrhs.symm
  · have hrhs : (t : ℝ≥0∞) * Homogenization.intDomRestrict G ξ +
        (1 - (t : ℝ≥0∞)) * Homogenization.intDomRestrict G ζ = ⊤ := by
      simp [Homogenization.intDomRestrict, hξ, ne_of_gt htpos]
    calc
      _ ≤ ⊤ := le_top
      _ = (t : ℝ≥0∞) * Homogenization.intDomRestrict G ξ +
          (1 - (t : ℝ≥0∞)) * Homogenization.intDomRestrict G ζ := hrhs.symm

/-- `intDomRestrict G` is measurable when `G` is convex. This auxiliary result does not itself
remove the measurability assumption from the Γ-limsup bound. -/
theorem ConvexENN.measurable_intDomRestrict {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) : Measurable (Homogenization.intDomRestrict G) := by
  classical
  have heq : Homogenization.intDomRestrict G =
      (interior (dom G)).piecewise G (fun _ => ⊤) := by
    funext ξ
    simp [Homogenization.intDomRestrict, Set.piecewise]
  rw [heq]
  exact hG.continuousOn_interior_dom.measurable_piecewise continuousOn_const
    isOpen_interior.measurableSet

/-- `intDomRestrict G` has growth bounds `(0, β)` whenever `G` has bounds `(α, β)`.
This result alone does not remove the assumptions from the Γ-limsup bound. -/
theorem HasGGrowth.intDomRestrict_zero {G : Mat m N → ℝ≥0∞} {α β : NNReal}
    {L : Sp N → Mat m N → ℝ≥0∞} (h : HasGGrowth G α β L) :
    HasGGrowth (Homogenization.intDomRestrict G) (0 : NNReal) β L := by
  intro x ξ
  refine ⟨by simp, ?_⟩
  calc
    L x ξ ≤ β * (1 + G ξ) := (h x ξ).2
    _ ≤ β * (1 + Homogenization.intDomRestrict G ξ) := by
      gcongr
      exact Homogenization.le_intDomRestrict G ξ

/-- If zero is interior to `dom G`, it remains interior to the effective domain after restriction.
This auxiliary fact alone does not remove the assumptions in the Γ-limsup bound. -/
theorem zero_mem_interior_dom_intDomRestrict {G : Mat m N → ℝ≥0∞}
    (h0 : (0 : Mat m N) ∈ interior (dom G)) :
    (0 : Mat m N) ∈ interior (dom (Homogenization.intDomRestrict G)) := by
  rw [Homogenization.dom_intDomRestrict, interior_interior]
  exact h0

section RemoveEnergyAssumptions

open scoped NNReal

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

set_option linter.style.haveILetI false in
/-- If a constant gradient lies outside the closure of the effective domain of a convex
integrand, every zero-boundary Sobolev perturbation has infinite integral. No measurability
assumption on the integrand is needed. -/
theorem ConvexENN.lintegral_W1p0_eq_top_of_not_mem_closure_dom
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G) {U : Set (Sp N)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUf : volume (frontier U) = 0) (hU0 : volume U ≠ 0)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : u ∈ W1p0 (ENNReal.ofReal p) U) {ζ : Mat m N}
    (hζ : ζ ∉ closure (dom G)) : ∫⁻ y in U, G (ζ + u.2 y) = ⊤ := by
  obtain ⟨f, c, hfζ, hfdom⟩ :=
    geometric_hahn_banach_point_closed hG.convex_dom.closure isClosed_closure hζ
  let μ := volume.restrict U
  let S : Set (Sp N) := {y | f (ζ + u.2 y) < c}
  have hSval : ∀ y ∈ S, G (ζ + u.2 y) = ⊤ := by
    intro y hy
    change f (ζ + u.2 y) < c at hy
    have hnot : ζ + u.2 y ∉ dom G := by
      intro hmem
      exact (not_lt_of_ge (le_of_lt (hfdom _ (subset_closure hmem)))) hy
    change ¬ G (ζ + u.2 y) < ⊤ at hnot
    exact top_unique (not_lt.mp hnot)
  have hpoint : ∀ y, S.indicator (fun _ : Sp N => (⊤ : ℝ≥0∞)) y ≤
      G (ζ + u.2 y) := by
    intro y
    by_cases hy : y ∈ S
    · simp [hy, hSval y hy]
    · simp [hy]
  have hμfinite : IsFiniteMeasure μ := by
    simpa [μ] using (isFiniteMeasure_restrict.2 hUb.measure_lt_top.ne)
  letI := hμfinite
  have hint : Integrable u.2 μ := (hu.2.2.1.restrict U).integrable hP.out
  have hS : NullMeasurableSet S μ := by
    apply nullMeasurableSet_lt
    · exact (f.continuous.measurable.comp_aemeasurable
        (aemeasurable_const.add hint.aemeasurable))
    · exact aemeasurable_const
  by_contra hne
  have hfinite : ∫⁻ y in U, G (ζ + u.2 y) ≠ ⊤ := hne
  have hzero : μ S = 0 := by
    by_contra hμ
    have hpos : 0 < μ S := lt_of_le_of_ne bot_le (Ne.symm hμ)
    have hlinf : ∫⁻ y, S.indicator (fun _ : Sp N => (⊤ : ℝ≥0∞)) y ∂μ = ⊤ := by
      rw [lintegral_indicator_const₀ hS]
      simp [hpos.ne']
    have : ⊤ ≤ ∫⁻ y in U, G (ζ + u.2 y) := by
      have hmono : (∫⁻ y, S.indicator (fun _ : Sp N => (⊤ : ℝ≥0∞)) y ∂μ) ≤
          ∫⁻ y, G (ζ + u.2 y) ∂μ := lintegral_mono hpoint
      change ⊤ ≤ ∫⁻ y, G (ζ + u.2 y) ∂μ
      calc
        ⊤ = ∫⁻ y, S.indicator (fun _ : Sp N => (⊤ : ℝ≥0∞)) y ∂μ := hlinf.symm
        _ ≤ ∫⁻ y, G (ζ + u.2 y) ∂μ := hmono
    exact hfinite (top_unique this)
  have hae : ∀ᵐ y ∂μ, c ≤ f (ζ + u.2 y) := by
    rw [ae_iff]
    have hset : {y | ¬ c ≤ f (ζ + u.2 y)} = S := by
      ext y
      simp only [Set.mem_ofPred_eq, S]
      constructor <;> intro h <;> linarith
    rw [hset, hzero]
  have hfun : (fun y => f (ζ + u.2 y)) = fun y => f ζ + f (u.2 y) := by
    funext y
    exact map_add f ζ (u.2 y)
  have hreal : (volume U).toReal * c ≤ ∫ y in U, f (ζ + u.2 y) := by
    have hcomp : Integrable (fun y => f (ζ + u.2 y)) μ := by
      rw [hfun]
      exact (integrable_const _).add (f.integrable_comp hint)
    have hae' : (fun _ : Sp N => c) ≤ᵐ[μ] fun y => f (ζ + u.2 y) :=
      hae.mono fun y hy => by simpa only [map_add] using hy
    change (volume U).toReal * c ≤ ∫ y, f (ζ + u.2 y) ∂μ
    calc
      (volume U).toReal * c = ∫ y, c ∂μ := by
        rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
        simp [Measure.real]
      _ ≤ ∫ y, f (ζ + u.2 y) ∂μ := integral_mono_ae (integrable_const c) hcomp hae'
  have hI : ∫ y in U, f (ζ + u.2 y) = (volume U).toReal * f ζ := by
    change (∫ y, f (ζ + u.2 y) ∂μ) = (volume U).toReal * f ζ
    calc
      (∫ y, f (ζ + u.2 y) ∂μ) = ∫ y, (f ζ + f (u.2 y)) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
          map_add f ζ (u.2 y))
      _ = (volume U).toReal * f ζ := by
        rw [integral_add (integrable_const (f ζ)) (f.integrable_comp hint),
          ContinuousLinearMap.integral_comp_comm f hint,
          W1p0.integral_grad_eq_zero hUo hUb hUf hu, map_zero, add_zero,
          integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
        simp [Measure.real]
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUb.measure_lt_top.ne
  rw [hI] at hreal
  exact (not_lt_of_ge hreal) (mul_lt_mul_of_pos_left hfζ hvol)

/-- Outside the closure of the effective domain, `Hp` is infinite when the lower growth
coefficient is positive. This is an intermediate step toward removing `Measurable G` and the
finite-energy assumption; the Γ-limsup bound without those assumptions is not proved here. -/
theorem HasGGrowth.Hp_eq_top_of_not_mem_closure_dom
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h : HasGGrowth G α β L) (hα : 0 < α)
    {ζ : Mat m N} (hζ : ζ ∉ closure (dom G)) : Hp (ENNReal.ofReal p) L ζ = ⊤ := by
  apply top_unique
  rw [Hp]
  refine le_iInf fun k => ?_
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hY : Ytp (ENNReal.ofReal p) L (cube ((k : ℝ) + 1) 0) ζ = ⊤ := by
    apply top_unique
    rw [Ytp]
    refine le_iInf₂ fun u hu => ?_
    have hA := hG.lintegral_W1p0_eq_top_of_not_mem_closure_dom
      (isOpen_cube _ _) (isBounded_cube _ _) (volume_frontier_cube _ _)
      (volume_cube_pos hk 0).ne' hu hζ
    calc
      ⊤ = (α : ℝ≥0∞) * ∫⁻ y in cube ((k : ℝ) + 1) 0, G (ζ + u.2 y) := by
        rw [hA]
        exact (ENNReal.mul_top (by exact_mod_cast hα.ne')).symm
      _ = ∫⁻ y in cube ((k : ℝ) + 1) 0, α * G (ζ + u.2 y) :=
        (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
      _ ≤ ∫⁻ y in cube ((k : ℝ) + 1) 0, L y (ζ + u.2 y) :=
        lintegral_mono fun y => (h y _).1
  rw [hY, ENNReal.top_div_of_ne_top (volume_cube_ne_top _ _)]

/-- A radial estimate for the interior-domain restriction, as an intermediate step toward
removing `Measurable G` and the finite-energy assumption. The Γ-limsup bound without those
assumptions is not proved here. -/
theorem HasGGrowth.mul_intDomRestrict_smul_le_radial_Hp
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h : HasGGrowth G α β L) (hα : 0 < α)
    (h0 : (0 : Mat m N) ∈ interior (dom G)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : Mat m N) :
    (α : ℝ≥0∞) * intDomRestrict G (s • ξ) ≤
      radial (Hp (ENNReal.ofReal p) L) ξ + (α : ℝ≥0∞) * G 0 := by
  by_cases hall : ∀ r ∈ Set.Ioo s 1, r • ξ ∈ interior (dom G)
  · have hsint : s • ξ ∈ interior (dom G) := by
      obtain ⟨r, hr⟩ := exists_between hs1
      have hrlo : s < r := hr.1
      have hrhi : r < 1 := hr.2
      have hrpos : 0 < r := hs0.trans hrlo
      let t : NNReal := ⟨s / r, by positivity⟩
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have ht1 : (t : ℝ) < 1 := by
        dsimp [t]
        exact (div_lt_one hrpos).2 hrlo
      have hξr := hall r ⟨hrlo, hrhi⟩
      have hξcl : r • ξ ∈ closure (dom G) := subset_closure (interior_subset hξr)
      have hmem := hG.smul_mem_interior_dom h0 hξcl ht0 ht1
      have htcoe : (t : ℝ) = s / r := by rfl
      have hscale : (t : ℝ) • (r • ξ) = s • ξ := by
        rw [smul_smul]
        rw [htcoe, div_mul_cancel₀ s hrpos.ne']
      rwa [hscale] at hmem
    rw [intDomRestrict_of_mem hsint]
    have hEventually : ∀ᶠ r in 𝓝[<] (1 : ℝ),
        (α : ℝ≥0∞) * G (s • ξ) - (α : ℝ≥0∞) * G 0 ≤
          Hp (ENNReal.ofReal p) L (r • ξ) := by
      filter_upwards [Ioo_mem_nhdsLT hs1] with r hr
      have hrpos : 0 < r := hs0.trans hr.1
      let ha : NNReal := ⟨s / r, by positivity⟩
      have ha0 : (ha : ℝ) ≤ 1 := by
        change s / r ≤ 1
        exact (div_le_one hrpos).2 hr.1.le
      have ha1 : (ha : ℝ) < 1 := by
        change s / r < 1
        exact (div_lt_one hrpos).2 hr.1
      have hmemr : r • ξ ∈ interior (dom G) := hall r hr
      have hcl0 : (0 : Mat m N) ∈ closure (dom G) := subset_closure (interior_subset h0)
      have hmems : s • ξ ∈ interior (dom G) := by
        have hsmul := hG.smul_mem_interior_dom h0
          (subset_closure (interior_subset hmemr)) (by positivity)
          ha1
        have hacoe : (ha : ℝ) = s / r := by rfl
        have hscale : (ha : ℝ) • (r • ξ) = s • ξ := by
          rw [smul_smul]
          rw [hacoe, div_mul_cancel₀ s hrpos.ne']
        rwa [hscale] at hsmul
      have hcombo : s • ξ = (ha : ℝ) • (r • ξ) +
          ((1 - ha : ℝ≥0) : ℝ) • (0 : Mat m N) := by
        simp only [smul_zero, add_zero]
        have hacoe : (ha : ℝ) = s / r := by rfl
        have hscale : (ha : ℝ) • (r • ξ) = s • ξ := by
          rw [smul_smul, hacoe, div_mul_cancel₀ s hrpos.ne']
        exact hscale.symm
      have hconv := hG (r • ξ) 0 ha ha0
      rw [← hcombo] at hconv
      have hpoint : (α : ℝ≥0∞) * G (s • ξ) ≤
          Hp (ENNReal.ofReal p) L (r • ξ) + (α : ℝ≥0∞) * G 0 := by
        calc
          (α : ℝ≥0∞) * G (s • ξ) ≤
              (α : ℝ≥0∞) * ((ha : ℝ≥0∞) * G (r • ξ) +
                (1 - ha : ℝ≥0) * G 0) := by gcongr
          _ = (ha : ℝ≥0∞) * ((α : ℝ≥0∞) * G (r • ξ)) +
                (1 - ha : ℝ≥0∞) * ((α : ℝ≥0∞) * G 0) := by
                  simp only [mul_add, ← mul_assoc]
                  rw [mul_comm (α : ℝ≥0∞) (ha : ℝ≥0∞)]
                  have ha0' : ha ≤ (1 : NNReal) := by exact_mod_cast ha0
                  have hcoeff : ((1 - ha : NNReal) : ℝ≥0∞) =
                      1 - (ha : ℝ≥0∞) := by simp
                  rw [hcoeff, mul_comm (α : ℝ≥0∞) (1 - (ha : ℝ≥0∞))]
          _ ≤ (α : ℝ≥0∞) * G (r • ξ) + (α : ℝ≥0∞) * G 0 := by
            apply add_le_add
            · calc
                (ha : ℝ≥0∞) * ((α : ℝ≥0∞) * G (r • ξ)) ≤
                    1 * ((α : ℝ≥0∞) * G (r • ξ)) := by
                      gcongr
                      exact_mod_cast ha0
                _ = (α : ℝ≥0∞) * G (r • ξ) := one_mul _
            · calc
                (1 - ha : ℝ≥0∞) * ((α : ℝ≥0∞) * G 0) ≤
                    1 * ((α : ℝ≥0∞) * G 0) := by
                      gcongr
                      exact_mod_cast (show (1 - ha : NNReal) ≤ 1 by exact tsub_le_self)
                _ = (α : ℝ≥0∞) * G 0 := one_mul _
          _ ≤ Hp (ENNReal.ofReal p) L (r • ξ) + (α : ℝ≥0∞) * G 0 :=
            calc
              _ = (α : ℝ≥0∞) * G 0 + (α : ℝ≥0∞) * G (r • ξ) := by ac_rfl
              _ ≤ (α : ℝ≥0∞) * G 0 + Hp (ENNReal.ofReal p) L (r • ξ) :=
                add_le_add_right (h.le_Hp (p := p) hG hmemr) _
              _ = _ := by ac_rfl
      exact tsub_le_iff_right.mpr hpoint
    have hlim := Filter.le_liminf_of_le (by isBoundedDefault) hEventually
    exact tsub_le_iff_right.mp hlim
  · push Not at hall
    obtain ⟨r₁, hr₁, hnot⟩ := hall
    have hEventually : ∀ᶠ r in 𝓝[<] (1 : ℝ),
        Hp (ENNReal.ofReal p) L (r • ξ) = ⊤ := by
      filter_upwards [Ioo_mem_nhdsLT hr₁.2] with r hr
      have hrpos : 0 < r := lt_trans (lt_trans hs0 hr₁.1) hr.1
      have hcl : r • ξ ∉ closure (dom G) := by
        intro hcl
        have hr10 : 0 < r₁ := lt_trans hs0 hr₁.1
        have ht0 : (0 : ℝ) ≤ r₁ / r := (div_pos hr10 hrpos).le
        have ht1 : r₁ / r < 1 := (div_lt_one hrpos).2 hr.1
        have hinterior := hG.smul_mem_interior_dom h0 hcl ht0 ht1
        have hscale : (r₁ / r) • (r • ξ) = r₁ • ξ := by
          rw [smul_smul, div_mul_cancel₀ r₁ hrpos.ne']
        exact hnot (hscale ▸ hinterior)
      exact h.Hp_eq_top_of_not_mem_closure_dom hG hα hcl
    have hrad : radial (Hp (ENNReal.ofReal p) L) ξ = ⊤ := by
      unfold radial
      rw [Filter.liminf_congr hEventually]
      simp
    rw [hrad]
    exact le_top

/-- The restricted energy of a contracted gradient is finite when its radial envelope is
integrable. This supplies the finite-energy hypothesis needed for the restricted integrand. -/
theorem HasGGrowth.lintegral_intDomRestrict_smul_lt_top
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h : HasGGrowth G α β L) (hα : 0 < α)
    (h0 : (0 : Mat m N) ∈ interior (dom G)) {Ω : Set (Sp N)} (hΩvol : volume Ω < ⊤)
    (D : Sp N → Mat m N)
    (hI : ∫⁻ x in Ω, radial (Hp (ENNReal.ofReal p) L) (D x) < ⊤)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∫⁻ x in Ω, intDomRestrict G (s • D x) < ⊤ := by
  have hG0 : G 0 < ⊤ := by
    have hmem : (0 : Mat m N) ∈ dom G := interior_subset h0
    simpa [dom] using hmem
  have hmul : (α : ℝ≥0∞) * (∫⁻ x in Ω, intDomRestrict G (s • D x)) < ⊤ := by
    calc
      (α : ℝ≥0∞) * (∫⁻ x in Ω, intDomRestrict G (s • D x)) =
          ∫⁻ x in Ω, (α : ℝ≥0∞) * intDomRestrict G (s • D x) :=
        (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
      _ ≤ ∫⁻ x in Ω, (radial (Hp (ENNReal.ofReal p) L) (D x) +
          (α : ℝ≥0∞) * G 0) := by
        apply lintegral_mono
        intro x
        exact h.mul_intDomRestrict_smul_le_radial_Hp hG hα h0 hs0 hs1 (D x)
      _ = (∫⁻ x in Ω, radial (Hp (ENNReal.ofReal p) L) (D x)) +
          (α : ℝ≥0∞) * G 0 * volume Ω := by
        rw [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
      _ < ⊤ := by
        apply ENNReal.add_lt_top.mpr
        constructor
        · exact hI
        · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hG0) hΩvol
  by_contra hnot
  have htop : ∫⁻ x in Ω, intDomRestrict G (s • D x) = ⊤ := top_unique (not_lt.mp hnot)
  rw [htop] at hmul
  have hαne : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
  simp [ENNReal.mul_top hαne] at hmul

/-- A local affine bound for `f` near scale one also bounds its radial envelope at every
intermediate scale. -/
theorem radial_smul_le_affine_of_near {c : ℝ≥0} {f : Mat m N → ℝ≥0∞} {η : ℝ≥0}
    {t₀ : ℝ}
    (hnear : ∀ t : ℝ, t₀ < t → t < 1 → ∀ ξ,
      f (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * radial f ξ + (η : ℝ≥0∞) * (c : ℝ≥0∞))
    (ht₀ : 0 ≤ t₀) {t : ℝ} (ht : t₀ < t) (ht1 : t < 1) (ξ : Mat m N) :
    radial f (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * radial f ξ +
      (η : ℝ≥0∞) * (c : ℝ≥0∞) := by
  have htpos : 0 < t := lt_of_le_of_lt ht₀ ht
  have hEventually : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      f (r • t • ξ) ≤ (1 + (η : ℝ≥0∞)) * radial f ξ +
        (η : ℝ≥0∞) * (c : ℝ≥0∞) := by
    filter_upwards [Ioo_mem_nhdsLT (show t₀ / t < 1 by exact (div_lt_one htpos).2 ht)]
      with r hr
    have hrt : t₀ < r * t := (div_lt_iff₀ htpos).mp hr.1
    have hrt1 : r * t < 1 := by
      calc
        r * t < 1 * t := mul_lt_mul_of_pos_right hr.2 htpos
        _ = t := one_mul _
        _ < 1 := ht1
    simpa only [smul_smul, mul_comm r t] using hnear (r * t) hrt hrt1 ξ
  unfold radial
  exact liminf_le_of_frequently_le' hEventually.frequently

/-- **Γ-limsup upper bound of Proposition 2.1(ii)**, without cited hypothesis, without
`Measurable G` and without `∫_Ω G(∇u) < ⊤`: under the hypotheses of `CitedAHM14` used here
(including `0 < α`, coercivity, ru-usc, periodicity). The cited interface (b) is supplied
by `citedSobolevDiff_holds` (`Morrey.lean`). The lower bound (i) is not concerned.
The proof applies `GammaLimsup_le_intHom_radialHp_of_cited` to `s • u` with
`intDomRestrict G` and `α = 0`, then takes `s → 1`. -/
theorem GammaLimsup_le_intHom_radialHp [NeZero N]
    {G : Mat m N → ℝ≥0∞} {α β : NNReal} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hGrowth : HasGGrowth G α β L) (hα : 0 < α)
    (hLper : IsPeriodic L) (hLruusc : RUUSC L) {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (hp : (N : ℝ) < p)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    {c₀ : NNReal} (hCoercive : IsCoercive p c₀ L) (hc₀ : 0 < c₀) :
    GammaLimsup (X := W1p N m (ENNReal.ofReal p) Ω) (intFun L) u ≤
      intHom (radial (Hp (ENNReal.ofReal p) L)) u := by
  have hDiff : CitedSobolevDiff N m p := citedSobolevDiff_holds p
  let I : ℝ≥0∞ := ∫⁻ x in Ω, radial (Hp (ENNReal.ofReal p) L) (u.grad x)
  by_cases hI : I = ⊤
  · simp [intHom, I, hI]
  obtain ⟨c, hc, hHpRuusc⟩ := (lsc_of_HW hLruusc).1
  have hVol : volume Ω < ⊤ := hΩbounded.measure_lt_top
  have hIlt : I < ⊤ := lt_of_le_of_ne le_top hI
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  let η : NNReal := (δ / (I + (c : ℝ≥0∞) * volume Ω + 1)).toNNReal
  have hηpos : 0 < η := by
    dsimp [η]
    have hden0 : 0 < I + (c : ℝ≥0∞) * volume Ω + 1 := by positivity
    have hdenTop : I + (c : ℝ≥0∞) * volume Ω + 1 ≠ ⊤ := by
      have hprod : (c : ℝ≥0∞) * volume Ω ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) hVol.ne
      have hsum : I + (c : ℝ≥0∞) * volume Ω ≠ ⊤ :=
        (ENNReal.add_ne_top).2 ⟨hIlt.ne, hprod⟩
      exact (ENNReal.add_ne_top).2 ⟨hsum, ENNReal.one_ne_top⟩
    have hratio : 0 < δ / (I + (c : ℝ≥0∞) * volume Ω + 1) :=
      ENNReal.div_pos (by exact_mod_cast hδ.ne') hdenTop
    exact ENNReal.toNNReal_pos hratio.ne' (ENNReal.div_ne_top (by simp) hden0.ne')
  obtain ⟨t₀, ht₀nonneg, ht₀lt, hnear⟩ := hHpRuusc.le_affine_radial hηpos
  let t : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2)
  have htend : Tendsto t atTop (𝓝 1) := by
    have hinv : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
      have hnat : Tendsto (fun j : ℕ => ((j + 2 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
      convert tendsto_inv_atTop_zero.comp hnat using 1
      norm_num [one_div, Function.comp_def]
    simpa [t] using tendsto_const_nhds.sub hinv
  have htmem : ∀ᶠ j in atTop, t₀ < t j ∧ t j < 1 := by
    have hn : ∀ᶠ j in atTop, |t j - 1| < 1 - t₀ :=
      htend.eventually (Metric.ball_mem_nhds _ (sub_pos.mpr ht₀lt))
    filter_upwards [hn] with j hj
    have habs : |t j - 1| < 1 - t₀ := by simpa [Real.dist_eq] using hj
    have habs' := abs_lt.mp habs
    constructor
    · dsimp [t]
      linarith
    · dsimp [t]
      have : 0 < 1 / ((j : ℝ) + 2) := by positivity
      linarith
  have hseq : Tendsto (fun j : ℕ => u.smul (t j)) atTop (𝓝 u) := by
    let ρ : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal |t j - 1| *
      eLpNorm u.toFun (ENNReal.ofReal p) (volume.restrict Ω)
    have hρ : Tendsto ρ atTop (𝓝 0) := by
      have hreal : Tendsto (fun j : ℕ => |t j - 1|) atTop (𝓝 0) := by
        have hminus : Tendsto (fun j : ℕ => t j - 1) atTop (𝓝 0) := by
          simpa using htend.sub_const 1
        simpa [Function.comp_def] using (continuous_abs.tendsto 0).comp hminus
      have hscalar : Tendsto (fun j : ℕ => ENNReal.ofReal |t j - 1|) atTop (𝓝 0) :=
        by simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hreal
      have hnorm : eLpNorm u.toFun (ENNReal.ofReal p) (volume.restrict Ω) ≠ ⊤ :=
        ne_of_lt u.memLp.eLpNorm_lt_top
      simpa only [ρ, Function.comp_def, zero_mul] using
        ((ENNReal.continuous_mul_const hnorm).tendsto 0).comp hscalar
    apply tendsto_of_edist_le tendsto_const_nhds hρ
    filter_upwards with j
    rw [W1p.edist_def]
    have hfun : (u.smul (t j)).toFun - u.toFun = (t j - 1) • u.toFun := by
      ext x k
      simp [W1p.smul]
      ring
    rw [hfun, eLpNorm_const_smul]
    simp [ρ, Real.enorm_eq_ofReal_abs]
  have hGamma := GammaLimsup_le_liminf (intFun L) hseq
  have henergy : ∀ᶠ j in atTop,
      GammaLimsup (intFun L) (u.smul (t j)) ≤
        (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω := by
    filter_upwards [htmem] with j hj
    have htpos : 0 < t j := lt_of_le_of_lt ht₀nonneg hj.1
    have hint : ∫⁻ y in Ω,
        intDomRestrict G ((u.smul (t j)).grad y) < ⊤ := by
      simpa [W1p.smul] using hGrowth.lintegral_intDomRestrict_smul_lt_top
        hG hα h0 hΩbounded.measure_lt_top u.grad hIlt htpos hj.2
    have hv := GammaLimsup_le_intHom_radialHp_of_cited
      (G := intDomRestrict G) (α := 0) hG.intDomRestrict
      hGrowth.intDomRestrict_zero hLper hLruusc hΩopen hΩbounded
      (u.smul (t j)) hDiff hp
      (zero_mem_interior_dom_intDomRestrict h0)
      hG.measurable_intDomRestrict hint hCoercive hc₀
    have hrad : intHom (radial (Hp (ENNReal.ofReal p) L)) (u.smul (t j)) ≤
        (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω := by
      simp only [intHom, W1p.smul]
      calc
        ∫⁻ x in Ω, radial (Hp (ENNReal.ofReal p) L) (t j • u.grad x) ≤
            ∫⁻ x in Ω, ((1 + (η : ℝ≥0∞)) *
              radial (Hp (ENNReal.ofReal p) L) (u.grad x) +
                (η : ℝ≥0∞) * (c : ℝ≥0∞)) :=
          lintegral_mono fun x => radial_smul_le_affine_of_near
            (f := Hp (ENNReal.ofReal p) L) hnear ht₀nonneg hj.1 hj.2 (u.grad x)
        _ = (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω := by
          rw [lintegral_add_right' _ aemeasurable_const,
            lintegral_const_mul' _ _ (by simp), setLIntegral_const]
    exact hv.trans hrad
  have hliminf : liminf (fun j : ℕ => GammaLimsup (intFun L) (u.smul (t j))) atTop ≤
      (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω :=
    liminf_le_of_frequently_le' (henergy.frequently)
  have hbound := hGamma.trans hliminf
  have hηineq : (1 + (η : ℝ≥0∞)) * I + (η : ℝ≥0∞) * c * volume Ω ≤ I + δ := by
    let D : ℝ≥0∞ := I + (c : ℝ≥0∞) * volume Ω + 1
    have hD0 : D ≠ 0 := by dsimp [D]; positivity
    have hDtop : D ≠ ⊤ := by
      dsimp [D]
      have hsum : I + (c : ℝ≥0∞) * volume Ω ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hIlt.ne, ENNReal.mul_ne_top (by simp) hVol.ne⟩
      exact ENNReal.add_ne_top.mpr ⟨hsum, ENNReal.one_ne_top⟩
    have hetaCoe : (η : ℝ≥0∞) = δ / D := by
      change ((δ / D).toNNReal : ℝ≥0∞) = δ / D
      exact ENNReal.coe_toNNReal (ENNReal.div_ne_top (by simp) hD0)
    rw [hetaCoe]
    have hsmall : I + (c : ℝ≥0∞) * volume Ω ≤ D := by
      dsimp [D]
      exact le_add_of_nonneg_right (by simp)
    have hmul : (δ / D) * (I + (c : ℝ≥0∞) * volume Ω) ≤ δ := by
      calc
        (δ / D) * (I + (c : ℝ≥0∞) * volume Ω) ≤ (δ / D) * D :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = δ := ENNReal.div_mul_cancel hD0 hDtop
    calc
      (1 + δ / D) * I + δ / D * c * volume Ω =
          I + (δ / D) * (I + (c : ℝ≥0∞) * volume Ω) := by ring
      _ ≤ I + δ := add_le_add_right hmul I
  exact (hbound.trans hηineq).trans (by simp [intHom, I])

end RemoveEnergyAssumptions

end Homogenization
