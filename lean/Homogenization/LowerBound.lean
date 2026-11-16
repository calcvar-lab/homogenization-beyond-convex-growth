import Homogenization.Domains
import Mathlib.Analysis.Real.Cardinality

/-!
# The lower bound of [oah-jpm-zorgati14]: formalization under cited hypotheses

This file formalizes Proposition `main result` (i) of [oah-jpm-zorgati14] (Proposition 2.1(i))
under the
three explicit interfaces below. The interfaces are hypotheses, not results proved in this file
or hidden axioms. The local theorem is `localLowerBound_of_cited`; its specialization to `O = Ω`
gives the whole-domain lower bound.

## The statement

The article's target is the local functional `I⁻(u;O)`, for every open `O ⊆ Ω`, not just its
special case `O = Ω`. `Iminus` below is the Γ-liminf of the restricted energies on `O`, using the
strong `Lᵖ(Ω)` topology for the approximating family, exactly as in the article's definition.
**The target is the local statement** `LocalLowerBoundStatement` (Proposition 2.1(i)): for every
open `O ⊆ Ω`, `∫_O \widehat{ℋ_p L}(∇u) ≤ I⁻(u;O)`. The whole-domain `LowerBoundStatement` (the
Γ-liminf half of `CitedAHM14`, used by the main theorem) follows by taking `O = Ω`
(`LocalLowerBoundStatement.lowerBound`; `Iminus L Ω u` is `GammaLiminf (intFun L) u` by
definition).

## The three classical hypotheses (Option A)

* (a) `CitedSobolevCompact`: for `p > N` and `Ω` bounded Lipschitz, a sequence `uₙ → u` in
  `Lᵖ(Ω)` with bounded `∫_Ω |∇uₙ|ᵖ`
  - (a1) converges uniformly: `‖uₙ - u‖_{L^∞(Ω)} → 0` (Morrey + Rellich–Kondrachov + Ascoli;
    the whole sequence converges because the `Lᵖ` limit is unique);
  - (a2) keeps closed convex gradient constraints: if `∇uₙ ∈ K` a.e. for a closed convex `K`,
    then `∇u ∈ K` a.e. (weak compactness of `W^{1,p}`, `p > 1`, and Mazur's lemma).
  The paper uses (a2) with `K = cl(dom G)`, to get `∇u(x) ∈ cl(dom G)` a.e. (first line of §5).
* (b) `CitedSobolevDiff`: for `p > N`, `u ∈ W^{1,p}(Ω)` is differentiable a.e. in the
  `L^∞`-on-cubes sense: for a.e. `x ∈ Ω` there is `a` with
  `ρ⁻¹ ‖u - (a + ∇u(x)(· - x))‖_{L^∞(Q_ρ(x))} → 0` (Calderón; eq. `difflowerbound`).
* (c) `CitedMeasureLimit`: weak-* compactness of bounded sequences of measures `gₙ dx` on a
  bounded open `O`, together with the two Alexandrov (portmanteau) inequalities: for a
  subsequence and a finite measure `μ` carried by `O`, `μ(U) ≤ liminf ∫_U g_{φ n}` for open
  `U ⊆ O` and `limsup ∫_K g_{φ n} ≤ μ(K)` for compact `K ⊆ O`.
  Lebesgue decomposition `μ = μ.singularPart volume + volume.withDensity (μ.rnDeriv volume)` and
  differentiation of finite measures are **not** cited: Mathlib provides
  `Measure.HaveLebesgueDecomposition`, its `SFinite` instance
  `Measure.haveLebesgueDecomposition_of_sigmaFinite`, and
  `VitaliFamily.ae_tendsto_rnDeriv` (modules `MeasureTheory.Measure.Decomposition.Lebesgue` and
  `MeasureTheory.Covering.Differentiation`).

The theorem is
`localLowerBound_of_cited : CitedSobolevCompact N m p → CitedSobolevDiff N m p →
  CitedMeasureLimit N → LocalLowerBoundStatement N m p`,
from which `LocalLowerBoundStatement.lowerBound` gives `LowerBoundStatement N m p`.

## Proof structure (following §5 of the paper, local form)

Fix an open `O ⊆ Ω` (bounded, since `Ω` is), `u ∈ W^{1,p}(Ω)`, and write
`I_ε(v;O) = intFunOn L ε O v`, so that `I⁻(u;O) = Iminus L O u`.

0. **Reduction to a sequence** (`le_GammaLiminf_of_seq` applied to `F ε v = I_ε(v;O)`): it
   suffices to prove `∫_O \widehat{ℋ_p L}(∇u) ≤ ℓ` whenever `I_{εₙ}(uₙ;O) → ℓ < ∞` with
   `εₙ > 0`, `εₙ → 0`, `uₙ → u` in `Lᵖ(Ω)`. Dropping finitely many terms, `I_{εₙ}(uₙ;O) ≤ E < ∞`.
   Then:
   - `IsCoercive.sequence_grad_integral_bound`: `sup_n ∫_O |∇uₙ|ᵖ < ∞`;
   - `HasGGrowth.ae_mem_domOn_sequence`: `∇uₙ ∈ dom G` a.e. on `O`;
   - the energy is controlled only on `O`, so (a) is applied on **cubes** `Q` with
     `closure Q ⊆ O`, through `CitedSobolevCompact.restrict` with `HasLipschitzBoundary.cube`
     (`Basic.lean`) and `isBounded_cube` (`Jensen.lean`): on each such `Q`,
     (a1) `‖uₙ - u‖_{L^∞(Q)} → 0` and (a2) with `K = cl(dom G)` (closed and convex by
     `ConvexENN.convex_dom`) `∇u ∈ cl(dom G)` a.e. on `Q`. A countable family of such cubes covers
     `O`, which gives `∇u ∈ cl(dom G)` a.e. on `O`: this is
     `CitedSobolevCompact.gradient_mem_closure_domOn` (proved).
1. **Localization** (Step 1). `CitedMeasureLimit.extract_energy` on `O` gives a subsequence and a
   finite measure `μ` carried by `O`, with `μ(O) ≤ liminf I_{εₙ}(uₙ;O) = ℓ`. Let
   `f = μ.rnDeriv volume`; `rnDeriv_lintegral_le_measure` gives `∫_O f ≤ μ(O) ≤ ℓ`, so it suffices
   to prove `f(x₀) ≥ \widehat{ℋ_p L}(∇u(x₀))` for a.e. `x₀ ∈ O` (`lintegral_mono_ae`, no
   measurability of the left integrand needed). The good points `x₀ ∈ O` satisfy:
   `f(x₀) < ∞`; `μ(Q_ρ(x₀))/|Q_ρ| → f(x₀)` and `μₛ(Q_ρ(x₀))/|Q_ρ| → 0` as `ρ → 0⁺`
   (`VitaliFamily.ae_tendsto_rnDeriv` for `vfam N`, `singularPart_ratio_tendsto_zero_vitali`, then
   conversion to centered cubes); (b) holds at `x₀` (applied to `u` on `Ω`); `∇u(x₀) ∈ cl(dom G)`.
   For `ρ` small, `closure Q_ρ(x₀) ⊆ O`, and `μ(∂Q_ρ(x₀)) = 0` except for countably many `ρ`, so
   that `μ(Q_ρ(x₀)) = lim_n ∫_{Q_ρ(x₀)} gₙ` (both Alexandrov inequalities).
2. **ru-usc reduction.** Fix `η > 0` and take the threshold `t₀ < 1` from
   `RUUSC.radial_interval_le_affine`. Choose `t ∈ (t₀,1)`; this gives the inner estimate
   `L(y,tξ) ≤ (1+η)L(y,ξ)+ηc` directly at `t`. Then choose `θ ∈ (t,1)` for the separate
   annulus estimate. The estimate at `t` is not inferred from the estimate at `θ`.
3. **Cut-off** (Step 2). With `φ = cutoff hs ρ x₀` and `ℓ = u(x₀) + ∇u(x₀)(· - x₀)`:
   `vₙ = ℓ + φ(uₙ - ℓ)`, `t vₙ - t ℓ ∈ W^{1,p}_0(Q_ρ(x₀))` (`cutoff_sub_affine_mem_W1p0`, with
   `W1p0.smul`). On `Q_{sρ}`, `∇vₙ = ∇uₙ` (`fderiv_cutoff_eq_zero`). On the ring `S_ρ`,
   `t∇vₙ = τ(φ θ∇uₙ + (1-φ) θ∇u(x₀)) + (1-τ) Φₙ` with `τ = t/θ`,
   `Φₙ = t/(1-τ) Dφ smulRight (uₙ - ℓ)`. The pointwise decomposition is proved as
   `affineCutoff_scaled_annulus_decomp_ae`, and the three-term pointwise bound follows from
   `HasGGrowth.weighted_three_upper` in `HasGGrowth.affineCutoff_scaled_annulus_upper`. The a.e.
   estimate making `Φₙ` small from
   `exists_cutoff_fderiv_bound`, differentiability (b), and uniform convergence (a1) is proved
   below, including the restriction of both cited estimates to a fixed cube. The a.e. bound for
   `G(Φₙ)` and the fixed-scale integrated annulus estimate are also proved below. The limiting
   normalized measure of the ring is controlled by `tendsto_measure_cube_annulus_ratio`, with the
   exact factor `1-sᴺ`. The extraction and the boundary-layer estimate now have separate interfaces:
   `affineCutoff_extract_data_of_cited` fixes the subsequence, measure, density, slope from (b),
   admissible radii, and effective-domain constraint before any of `s,t,η` is chosen.
   `affineCutoff_boundary_layer_of_cited` consumes these fixed data. For each fixed `t,η`, it
   chooses `θ` once before `s`; on one full-measure set, the same slope, admissible radii, and
   finite bound `M₀` serve every `s ∈ (0,1)`. The bound from
   `affineCutoff_remainder_ae_uniform_bound_all_s` is passed into the normalized limsup estimate,
   so its coefficient uses this same `M₀`; only the radius and index thresholds depend on `s`.
   `RUUSCWith c L` keeps `c` independent of `η`; the estimate at `θ` controls the annulus, while
   the separate estimate at `t` is now consumed in the cell comparison. These estimates use
   finiteness of `G` on a small closed ball around zero
   (`ConvexENN.continuousOn_interior_dom`, compactness), coercivity, and ru-usc.
4. **Subadditive limit** (Step 3). The exact rescaled competitor inequality, including the
   center `x₀/ε` and the normalization by both cube volumes, is `affineCutoff_rescaled_cell_lower`.
   `Ytp_cell_ratio_tendsto_Hp_subsequence` instantiates `Ytp_tendsto_Hp` along the extracted
   subsequence, under its precise assumptions of periodicity, upper `G`-growth,
   `G(t∇u(x₀)) < ∞`, and `εₙ → 0⁺`. The fixed-scale combination with ru-usc on the inner cube and
   the cut-off energy on the annulus is `affineCutoff_cell_le_inner_ruusc_and_annulus`.
   These are fixed-parameter inequalities. The extraction data are passed explicitly to
   `affineCutoff_boundary_layer_of_cited`; its shared finite remainder bound controls the
   normalized layer limsup independently of `s`, and it now also supplies eventual finiteness of
   the cut-off annulus integrals from the uniform integrated estimate. The real fixed-radius
   raccord is formalized by `affineCutoff_cell_ratio_le_of_limsup_annulus`: it applies the
   `toReal` cell/cube/annulus comparison and `le_of_tendsto_add_limsup` with an eventual inequality.
   Its inputs are the fixed-radius limsup bound for the cut-off annulus and the RU-usc estimate at
   `t`; the latter is obtained separately from its radial threshold, not inferred from the estimate
   at `θ`. The fixed-radius lemma itself derives finiteness of `Hp(t • A)` and of every cell ratio
   from `A ∈ closure (dom G)`, convexity, `0 ∈ interior (dom G)`, and upper `G`-growth. The scalar
   tools `ae_nat_forall`, `tendsto_ruusc_density_error`, and
   `radial_Hp_le_of_ruusc_sequence_bounds` are used in the completed parameter-limit argument.
   The concrete
   step that feeds the fixed-radius annulus limsup into the cell comparison and passes the result
   along the common admissible radii is now `affineCutoff_boundary_layer_of_cited`:
   it invokes `affineCutoff_cell_ratio_le_of_limsup_annulus` for each sufficiently small radius,
   using the same subsequence for the functions and scales and the separate ru-usc estimate at
   `t`. It obtains a real bound on `Hp(t • ∇u(x₀))` by the density term, the inner constant, and
   the normalized annulus terms; the limit in the admissible radii is computed explicitly.
   The data `θ`, `M₀`, the slope, the point, and the radii are common for every `s`. The
   `s → 1` squeeze and the countable `t → 1, η → 0` assembly are proved in
   `hp_toReal_le_ruusc_bound_of_uniform_s`,
   `RUUSCWith.exists_tolerance_and_radial_sequences`, and
   `affineCutoff_pointwise_density_of_cited`; `localLowerBound_sequence_of_cited` integrates the
   pointwise inequality, and `localLowerBound_of_cited` performs the sequence reduction.

## Auxiliary lemmas available (all proved)

* Local functionals: `intFunOn`, `Iminus`, `Iminus_le_liminf_of_tendsto`, `W1p.restrict`,
  `W1p.restrict_lipschitz`, `W1p.tendsto_restrict` (below);
* Step 0: `exists_sequence_tendsto_liminf`, `le_GammaLiminf_of_seq`;
  `HasGGrowth.G_finite_of_L_finite` (`Domains.lean`), `HasGGrowth.ae_mem_dom`,
  `HasGGrowth.ae_mem_domOn`, `HasGGrowth.ae_mem_domOn_sequence`; `IsCoercive.enorm_rpow_le`,
  `IsCoercive.grad_integral_bound`, `IsCoercive.sequence_grad_integral_bound`;
  `CitedSobolevCompact.restrict`, `CitedSobolevCompact.gradient_mem_closure_domOn` (below:
  `∇u ∈ cl(dom G)` a.e. on `O`, via a countable cover of `O` by cubes with closure in `O`);
  `HasLipschitzBoundary.cube` (`Basic.lean`), `isBounded_cube` (`Jensen.lean`);
* Step 1: `CitedMeasureLimit.extract_energy`, `rnDeriv_lintegral_le_measure`,
  `singularPart_rnDeriv_ae_zero`, `singularPart_ratio_tendsto_zero_vitali`,
  `tendsto_measure_ratio_cube_of_closedBall`, `ae_tendsto_measure_ratio_cube_rnDeriv`,
  `singularPart_ratio_tendsto_zero_cube`, `countable_positive_cube_frontier_measure`,
  `tendsto_cube_energy_of_portmanteau` (below);
* Step 3: `ConvexENN.exists_finite_bound_closedBall_zero` (`Domains.lean`),
  `HasGGrowth.weighted_three_upper` (`Jensen.lean`), `Cutoff.lean`; the affine cut-off is
  admissible in `W1p0`; its weak-gradient identities, the a.e. three-term decomposition on the
  annulus, and the pointwise growth bound `HasGGrowth.affineCutoff_scaled_annulus_upper` are
  proved below. `CitedSobolevDiff.affine_remainder_ae_small_of_tendsto` converts the normalized
  `eLpNorm` limit in (b) to an a.e. affine error on small cubes;
  `CitedSobolevCompact.restrict_ae_error` converts (a1) on a fixed Lipschitz set `U` to an a.e.
  error on each fixed subcube, and its cube and annulus variants state the scale quantifiers
  needed by the cut-off. `affineCutoff_remainder_ae_small_of_cited` constructs such a fixed cube
  with closure in `O`, applies `HasLipschitzBoundary.cube` and the annulus restriction, and joins
  that estimate to the annular form of (b), with the exact slope `u.grad x₀`. These estimates feed
   `affineCutoff_remainder_ae_small`, the finite a.e. bound for `G(Φₙ)`, and the fixed-scale
   integrated annulus estimate. The normalized measure term is controlled by
   `tendsto_measure_cube_annulus_ratio`; for fixed `t,η`, the assembly with the fixed-scale
   energy and ru-usc bounds is proved for every `s` using one `θ`, one full-measure set, and one
   common remainder bound by `affineCutoff_boundary_layer_of_cited`.
* Step 4: `affineCutoff_rescaled_cell_lower`,
  `Ytp_cell_ratio_tendsto_Hp_subsequence`, and
  `affineCutoff_cell_le_inner_ruusc_and_annulus` (fixed-scale rescaling, subadditive convergence,
  and interior/annulus split); the limsup assembly, finiteness and `toReal` conversions, and the
  limits `n → ∞`, admissible `ρ → 0` are proved in `affineCutoff_boundary_layer_of_cited`.
  The `s → 1` squeeze is `hp_toReal_le_ruusc_bound_of_uniform_s`; the countable radial/tolerance
  limit and `lsc_of_HW` are used by `affineCutoff_pointwise_density_of_cited`.

## Formalization status

The complete local lower-bound implication is proved by `localLowerBound_of_cited`; its
whole-domain specialization follows from `LocalLowerBoundStatement.lowerBound`. This is a
conditional formalization: (a) `CitedSobolevCompact`, (b) `CitedSobolevDiff`, and (c)
`CitedMeasureLimit` are explicit theorem parameters. Step 0's constraint `∇u ∈ cl(dom G)` almost
everywhere on `O` is proved by `CitedSobolevCompact.gradient_mem_closure_domOn`. Step 1 is
assembled by `CitedMeasureLimit.extract_energy_step1`, which gives
`∫_O μ.rnDeriv volume ≤ μ(O) ≤ ℓ`, finite RN density, centered-cube differentiation, admissible
null-boundary radii, convergence of extracted cube energies, and the gradient constraint. The
singular part is controlled by its density at almost every point; no local vanishing is assumed.

The cutoff decomposition, a.e. remainder estimates, weighted growth bound, integrated annulus
bound, and its normalized boundary-layer limit are proved by the auxiliary results listed above.
`affineCutoff_boundary_layer_of_cited` combines those estimates with the cell comparison and
subadditive limit, using common extraction data and radii for all `s`. The `s → 1` squeeze is
`hp_toReal_le_ruusc_bound_of_uniform_s`. `RUUSCWith.exists_tolerance_and_radial_sequences`
chooses `ηⱼ → 0` and `tⱼ → 1⁻` with one fixed RU-usc constant; `ae_nat_forall` intersects their
good sets, and `radial_Hp_le_of_ruusc_sequence_bounds` applies `lsc_of_HW` to prove the pointwise
density inequality. `localLowerBound_sequence_of_cited` integrates it and uses the Step 1 mass
bound. `localLowerBound_of_sequence_of_cited` shifts past any finite initial segment of infinite
energies, and `localLowerBound_of_cited` completes the Γ-liminf sequence reduction.

The result is stated with the cited analytic interfaces (a)–(c) as explicit hypotheses; they are
proved downstream (`citedSobolevCompact_holds`, `citedSobolevDiff_holds`,
`citedMeasureLimit_holds`) and discharged in `localLowerBound` (`AHM14.lean`).
The statement also retains the article's assumptions that `Ω` is
nonempty and has Lipschitz boundary; `hΩne` and `hΩlip` occur in the proposition interface but are
not used by this local lower-bound proof.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

/-- A sequence realizing the lower limit along positive parameters. This is the first reduction
used when proving the Γ-liminf inequality; it does not assert anything about the energies or the
corresponding Sobolev functions. -/
theorem exists_sequence_tendsto_liminf (f : ℝ → ℝ≥0∞) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] (0 : ℝ)) ∧
      Tendsto (fun n => f (ε n)) atTop (𝓝 (liminf f (𝓝[>] (0 : ℝ)))) := by
  obtain ⟨ε, hvalue, hε⟩ :=
    exists_seq_tendsto_liminf (f := 𝓝[>] (0 : ℝ)) (u := f)
  exact ⟨ε, hε, by simpa [Function.comp_def] using hvalue⟩

/-- The absolutely continuous part in the Lebesgue decomposition of a finite measure is dominated
on every measurable set by the full measure. This is the measure-theoretic first reduction in the
lower-bound proof. -/
theorem rnDeriv_lintegral_le_measure {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    {A : Set (Sp N)} (hA : MeasurableSet A) :
    ∫⁻ x in A, μ.rnDeriv volume x ≤ μ A := by
  have hdecomp := (Measure.haveLebesgueDecomposition_spec μ (volume : Measure (Sp N))).2.2
  have hmeasure : μ A = μ.singularPart volume A + volume.withDensity (μ.rnDeriv volume) A := by
    calc μ A = (μ.singularPart volume + volume.withDensity (μ.rnDeriv volume)) A :=
          congrArg (fun ν : Measure (Sp N) => ν A) hdecomp
      _ = μ.singularPart volume A + volume.withDensity (μ.rnDeriv volume) A :=
          Measure.add_apply _ _ _
  calc ∫⁻ x in A, μ.rnDeriv volume x
      = volume.withDensity (μ.rnDeriv volume) A :=
        (MeasureTheory.withDensity_apply _ hA).symm
    _ ≤ μ.singularPart volume A + volume.withDensity (μ.rnDeriv volume) A :=
        le_add_of_nonneg_left (show 0 ≤ μ.singularPart volume A from zero_le)
    _ = μ A := hmeasure.symm

/-- The singular part has zero Radon--Nikodym derivative almost everywhere. This is the density
statement used for the boundary layer; it does not assert that the singular measure vanishes on a
neighborhood of almost every point. -/
theorem singularPart_rnDeriv_ae_zero {μ : Measure (Sp N)} [IsFiniteMeasure μ] :
    (μ.singularPart volume).rnDeriv volume =ᵐ[volume] 0 := by
  exact (MeasureTheory.Measure.mutuallySingular_singularPart μ volume).rnDeriv_ae_eq_zero

/-- Differentiation of the singular part along the project's cubic Vitali family. In particular,
the singular mass in a small cube is `o(|Q|)` at almost every point, even if its support is dense.
The conversion from this filter statement to centered cubes is provided by
`singularPart_ratio_tendsto_zero_cube` below. -/
theorem singularPart_ratio_tendsto_zero_vitali [NeZero N] {μ : Measure (Sp N)}
    [IsFiniteMeasure μ] :
    ∀ᵐ x ∂volume,
      Tendsto (fun A : Set (Sp N) => μ.singularPart volume A / volume A)
        ((vfam N).filterAt x) (𝓝 0) := by
  have hdiff := (vfam N).ae_tendsto_rnDeriv (μ.singularPart volume)
  filter_upwards [hdiff, singularPart_rnDeriv_ae_zero (μ := μ)] with x hx hz
  simpa [hz] using hx

/-- For a finite measure, only countably many positive side lengths have a centered cube whose
boundary has positive measure. The boundaries are pairwise disjoint: by `cube_eq_ball`, they lie
on spheres of the distinct radii `ρ / 2`. -/
theorem countable_positive_cube_frontier_measure [NeZero N] {μ : Measure (Sp N)}
    [IsFiniteMeasure μ] (x : Sp N) :
    {ρ : ℝ | 0 < ρ ∧ 0 < μ (frontier (cube ρ x))}.Countable := by
  let A : ℝ → Set (Sp N) := fun ρ => if 0 < ρ then frontier (cube ρ x) else ∅
  have hmeas : ∀ ρ, MeasurableSet (A ρ) := by
    intro ρ
    by_cases hρ : 0 < ρ <;> simp [A, hρ, isClosed_frontier.measurableSet]
  have hdisj : Pairwise (Disjoint on A) := by
    intro ρ₁ ρ₂ hne
    by_cases hρ₁ : 0 < ρ₁ <;> by_cases hρ₂ : 0 < ρ₂
    · have hfront₁ : frontier (cube ρ₁ x) = Metric.sphere x (ρ₁ / 2) := by
        rw [cube_eq_ball hρ₁, frontier_ball x (by positivity)]
      have hfront₂ : frontier (cube ρ₂ x) = Metric.sphere x (ρ₂ / 2) := by
        rw [cube_eq_ball hρ₂, frontier_ball x (by positivity)]
      rw [Function.onFun]
      apply Set.disjoint_left.2
      intro y hy₁ hy₂
      have hy₁' : y ∈ Metric.sphere x (ρ₁ / 2) := by simpa [A, hρ₁, hfront₁] using hy₁
      have hy₂' : y ∈ Metric.sphere x (ρ₂ / 2) := by simpa [A, hρ₂, hfront₂] using hy₂
      have hdist₁ := Metric.mem_sphere.mp hy₁'
      have hdist₂ := Metric.mem_sphere.mp hy₂'
      apply hne
      linarith
    · simp [Function.onFun, A, hρ₂]
    · simp [Function.onFun, A, hρ₁]
    · simp [Function.onFun, A, hρ₁, hρ₂]
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := μ) hmeas hdisj
  apply hcount.mono
  intro ρ hρ
  change 0 < ρ ∧ 0 < μ (frontier (cube ρ x)) at hρ
  simpa [A, hρ.1] using hρ.2

/-- Convert differentiation along centered closed balls to differentiation on open cubes. The
inner closed ball has side length `ρ * (1 - ρ / 2)`, so its volume relative to the outer ball
tends to one; this squeeze avoids assuming that `μ` gives zero mass to every cube boundary. -/
theorem tendsto_measure_ratio_cube_of_closedBall [NeZero N] {μ : Measure (Sp N)}
    {x : Sp N} {c : ℝ≥0∞}
    (hclosed : Tendsto (fun ρ : ℝ =>
      μ (Metric.closedBall x (ρ / 2)) / volume (Metric.closedBall x (ρ / 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  let d : ℝ → ℝ := fun ρ => ρ * (1 - ρ / 2)
  have hd : Tendsto d (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < 1 := by
      exact (tendsto_id'.2 (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).eventually
        (Iio_mem_nhds (by norm_num))
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous fun ρ : ℝ => ρ * (1 - ρ / 2) := by fun_prop
      simpa [d] using (hcont.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin, hsmall] with ρ hρ hρsmall
      have hρ' : 0 < ρ := by simpa using hρ
      dsimp [d]
      exact mul_pos hρ' (by linarith)
  have hratio_inner : Tendsto (fun ρ : ℝ =>
      μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (d ρ / 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 c) := hclosed.comp hd
  have hfactor : Tendsto (fun ρ : ℝ => ENNReal.ofReal ((1 - ρ / 2) ^ N))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hreal : Tendsto (fun ρ : ℝ => (1 - ρ / 2) ^ N)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 - (0 : ℝ) / 2) ^ N)) := by
      have hcont : Continuous fun ρ : ℝ => (1 - ρ / 2) ^ N := by fun_prop
      exact (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hreal' : Tendsto (fun ρ : ℝ => (1 - ρ / 2) ^ N)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by simpa using hreal
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 1).comp hreal'
  have hlower : Tendsto (fun ρ : ℝ =>
      (μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (d ρ / 2))) *
        ENNReal.ofReal ((1 - ρ / 2) ^ N)) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    simpa using ENNReal.Tendsto.mul hratio_inner (Or.inr ENNReal.one_ne_top)
      hfactor (Or.inl one_ne_zero)
  have hupper : Tendsto (fun ρ : ℝ =>
      μ (Metric.closedBall x (ρ / 2)) / volume (Metric.closedBall x (ρ / 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 c) := hclosed
  have hcompare : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (d ρ / 2))) *
          ENNReal.ofReal ((1 - ρ / 2) ^ N) ≤
        μ (cube ρ x) / volume (cube ρ x) ∧
      μ (cube ρ x) / volume (cube ρ x) ≤
        μ (Metric.closedBall x (ρ / 2)) / volume (Metric.closedBall x (ρ / 2)) := by
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < 1 := by
      exact (tendsto_id'.2 (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).eventually
        (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hsmall] with ρ hρ hρsmall
    have hρ' : 0 < ρ := hρ
    have hρ2 : 0 < ρ / 2 := by linarith
    have hρsmall2 : ρ / 2 < 1 := by linarith
    have hdpos : 0 < d ρ := by dsimp [d]; positivity
    have hdlt : d ρ < ρ := by dsimp [d]; nlinarith
    have hinner : Metric.closedBall x (d ρ / 2) ⊆ Metric.ball x (ρ / 2) := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      exact hy.trans_lt (by linarith)
    have houter : Metric.ball x (ρ / 2) ⊆ Metric.closedBall x (ρ / 2) :=
      Metric.ball_subset_closedBall
    have hvolInner : volume (Metric.closedBall x (d ρ / 2)) =
        ENNReal.ofReal (d ρ ^ N) := by
      rw [Real.volume_pi_closedBall _ (by exact (div_nonneg hdpos.le (by norm_num))),
        Fintype.card_fin]
      congr 1
      congr 1
      ring
    have hvolOuter : volume (Metric.closedBall x (ρ / 2)) =
        ENNReal.ofReal (ρ ^ N) := by
      rw [Real.volume_pi_closedBall _ hρ2.le, Fintype.card_fin]
      congr 1
      congr 1
      ring
    have hvolBall : volume (Metric.ball x (ρ / 2)) =
        volume (Metric.closedBall x (ρ / 2)) := by
      exact measure_congr (ball_ae_eq_closedBall x (ρ / 2))
    have hq : volume (Metric.closedBall x (d ρ / 2)) /
        volume (Metric.closedBall x (ρ / 2)) = ENNReal.ofReal ((1 - ρ / 2) ^ N) := by
      rw [hvolInner, hvolOuter]
      rw [← ENNReal.ofReal_div_of_pos (pow_pos hρ' N)]
      congr 1
      rw [show d ρ = ρ * (1 - ρ / 2) by rfl, mul_pow]
      field_simp [ne_of_gt hρ']
    have hvolIn0 : volume (Metric.closedBall x (d ρ / 2)) ≠ 0 := by
      rw [hvolInner]
      exact (ENNReal.ofReal_pos.2 (pow_pos hdpos N)).ne'
    have hvolInTop : volume (Metric.closedBall x (d ρ / 2)) ≠ ∞ := by
      rw [hvolInner]
      exact ENNReal.ofReal_ne_top
    have hmul :
        (μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (d ρ / 2))) *
            (volume (Metric.closedBall x (d ρ / 2)) /
              volume (Metric.closedBall x (ρ / 2))) =
          μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (ρ / 2)) := by
      calc
        (μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (d ρ / 2))) *
            (volume (Metric.closedBall x (d ρ / 2)) /
              volume (Metric.closedBall x (ρ / 2))) =
          ((μ (Metric.closedBall x (d ρ / 2)) /
            volume (Metric.closedBall x (d ρ / 2))) * volume (Metric.closedBall x (d ρ / 2))) /
              volume (Metric.closedBall x (ρ / 2)) := by rw [← mul_div_assoc]
        _ = μ (Metric.closedBall x (d ρ / 2)) /
            volume (Metric.closedBall x (ρ / 2)) := by
          rw [ENNReal.div_mul_cancel hvolIn0 hvolInTop]
    constructor
    · rw [cube_eq_ball hρ', hvolBall]
      calc
        (μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (d ρ / 2))) *
            ENNReal.ofReal ((1 - ρ / 2) ^ N) =
          μ (Metric.closedBall x (d ρ / 2)) / volume (Metric.closedBall x (ρ / 2)) := by
            rw [← hq]
            exact hmul
        _ ≤ μ (Metric.ball x (ρ / 2)) / volume (Metric.closedBall x (ρ / 2)) :=
          ENNReal.div_le_div_right (measure_mono hinner) _
    · rw [cube_eq_ball hρ, hvolBall]
      exact ENNReal.div_le_div_right (measure_mono houter) _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hcompare.mono fun _ h => h.1) (hcompare.mono fun _ h => h.2)

/-- Lebesgue differentiation for the measure of centered open cubes. The `ρ / 2` radius in
`cube_eq_ball` is essential: the Vitali family is parametrized by closed balls, and the transfer
uses the same half-radius before the open/closed squeeze. -/
theorem ae_tendsto_measure_ratio_cube_rnDeriv [NeZero N] {μ : Measure (Sp N)}
    [IsFiniteMeasure μ] :
    ∀ᵐ x ∂volume,
      Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
        (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) := by
  have hdiff := (vfam N).ae_tendsto_rnDeriv μ
  filter_upwards [hdiff] with x hx
  have hmem : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      x ∈ Metric.closedBall ((fun _ : ℝ => x) ρ) (1 * (ρ / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ' : 0 < ρ := by simpa using hρ
    exact Metric.mem_closedBall_self (by positivity)
  have hclosed := hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
    (fun _ : ℝ => x) (fun ρ => ρ / 2) tendsto_half_nhdsGT hmem)
  change Tendsto (fun ρ : ℝ =>
    μ (Metric.closedBall x (ρ / 2)) / volume (Metric.closedBall x (ρ / 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) at hclosed
  apply tendsto_measure_ratio_cube_of_closedBall
  exact hclosed

/-- The singular part has zero density along centered open cubes almost everywhere. This follows
from the measure differentiation theorem and the general open-cube transfer above, not from
vanishing of the singular measure on a neighborhood. -/
theorem singularPart_ratio_tendsto_zero_cube [NeZero N] {μ : Measure (Sp N)}
    [IsFiniteMeasure μ] :
    ∀ᵐ x ∂volume,
      Tendsto (fun ρ : ℝ => μ.singularPart volume (cube ρ x) / volume (cube ρ x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsingular := singularPart_ratio_tendsto_zero_vitali (μ := μ)
  filter_upwards [hsingular] with x hx
  have hmem : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      x ∈ Metric.closedBall ((fun _ : ℝ => x) ρ) (1 * (ρ / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ' : 0 < ρ := by simpa using hρ
    exact Metric.mem_closedBall_self (by positivity)
  have hclosed := hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
    (fun _ : ℝ => x) (fun ρ => ρ / 2) tendsto_half_nhdsGT hmem)
  change Tendsto (fun ρ : ℝ =>
    μ.singularPart volume (Metric.closedBall x (ρ / 2)) /
      volume (Metric.closedBall x (ρ / 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) at hclosed
  exact tendsto_measure_ratio_cube_of_closedBall hclosed

/-- The two Alexandrov inequalities from `CitedMeasureLimit` give actual convergence of the
energy on a centered cube whenever its boundary has zero `μ`-measure. The energies `E A n` depend
on the set `A` (in applications `E A n = ∫_A gₙ`, e.g. `intFunOn L (ε (φ n)) A (u (φ n))` from
`CitedMeasureLimit.extract_energy`), and `hmono` is the monotonicity `E Q n ≤ E (closure Q) n`
(`lintegral_mono_set` in applications). The open inequality is applied to the cube, the compact
inequality to its closure, and the boundary-null hypothesis identifies their limiting measures. -/
theorem tendsto_cube_energy_of_portmanteau [NeZero N] {μ : Measure (Sp N)}
    (O : Set (Sp N)) {x : Sp N} {ρ : ℝ}
    (hclosure : closure (cube ρ x) ⊆ O) (hboundary : μ (frontier (cube ρ x)) = 0)
    {E : Set (Sp N) → ℕ → ℝ≥0∞}
    (hopen : ∀ U : Set (Sp N), IsOpen U → U ⊆ O →
      μ U ≤ liminf (E U) atTop)
    (hcompact : ∀ K : Set (Sp N), IsCompact K → K ⊆ O →
      limsup (E K) atTop ≤ μ K)
    (hmono : ∀ n, E (cube ρ x) n ≤ E (closure (cube ρ x)) n) :
    Tendsto (E (cube ρ x)) atTop (𝓝 (μ (cube ρ x))) := by
  have hfrontier : closure (cube ρ x) \ cube ρ x = frontier (cube ρ x) :=
    (isOpen_cube ρ x).frontier_eq.symm
  have hmeasure : μ (closure (cube ρ x)) = μ (cube ρ x) :=
    (measure_eq_measure_of_null_sdiff (s := cube ρ x) (t := closure (cube ρ x))
      subset_closure (by rw [hfrontier, hboundary])).symm
  have hlow : μ (cube ρ x) ≤ liminf (E (cube ρ x)) atTop :=
    hopen _ (isOpen_cube ρ x) (subset_closure.trans hclosure)
  have hhigh : limsup (E (cube ρ x)) atTop ≤ μ (cube ρ x) := by
    calc
      limsup (E (cube ρ x)) atTop ≤ limsup (E (closure (cube ρ x))) atTop :=
        limsup_le_limsup (Eventually.of_forall hmono)
      _ ≤ μ (closure (cube ρ x)) :=
        hcompact _ (isBounded_cube ρ x).isCompact_closure hclosure
      _ = μ (cube ρ x) := hmeasure
  exact tendsto_of_le_liminf_of_limsup_le hlow hhigh

/-- Every nonempty real interval contains a point outside a prescribed countable set. -/
private theorem exists_mem_Ioo_not_mem_countable {C : Set ℝ} (hC : C.Countable)
    {a b : ℝ} (hab : a < b) : ∃ r ∈ Ioo a b, r ∉ C := by
  have hIoo : ¬ (Ioo a b).Countable := by
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real hab,
      not_le]
    exact Cardinal.aleph0_lt_continuum
  by_contra h
  have hsub : Ioo a b ⊆ C := by
    intro r hr
    by_contra hnot
    exact h ⟨r, hr, hnot⟩
  exact hIoo (hC.mono hsub)

/-- For a finite measure and an open set, choose arbitrarily small positive side lengths whose
centered cube has null-measure boundary and whose closure stays in the open set. The radii can be
chosen strictly decreasing to zero; no vanishing of the singular part on a neighborhood is used. -/
theorem exists_good_cube_radii [NeZero N] {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    (O : Set (Sp N)) (hO : IsOpen O) {x : Sp N} (hx : x ∈ O) :
    ∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
        μ (frontier (cube (ρ k) x)) = 0 := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO x hx
  have hbad := countable_positive_cube_frontier_measure (μ := μ) x
  let pick (b : ℝ) (hb : 0 < b) : {q : ℝ // 0 < q ∧ q < b ∧
      q ∉ {s : ℝ | 0 < s ∧ 0 < μ (frontier (cube s x))}} := by
    let hq := exists_mem_Ioo_not_mem_countable hbad hb
    let q := Classical.choose hq
    have hqspec := Classical.choose_spec hq
    exact ⟨q, ⟨hqspec.1.1, hqspec.1.2, hqspec.2⟩⟩
  let seq : ℕ → {q : ℝ // 0 < q} := Nat.rec
    (let q := pick r hr
     ⟨q.1, q.2.1⟩)
    (fun k prev =>
      let b := min (prev.1 / 2) (r / (k + 2 : ℕ))
      let hb : 0 < b := lt_min (by linarith [prev.2]) (by positivity)
      let q := pick b hb
      ⟨q.1, q.2.1⟩)
  let ρ : ℕ → ℝ := fun k => (seq k).1
  have hprops : ∀ k, ρ k < r / (k + 1 : ℕ) ∧
      ρ k ∉ {s : ℝ | 0 < s ∧ 0 < μ (frontier (cube s x))} := by
    intro k
    induction k with
    | zero =>
        dsimp [ρ, seq]
        have hq := (pick r hr).2
        exact ⟨by simpa using hq.2.1, hq.2.2⟩
    | succ k ih =>
        dsimp [ρ, seq]
        have hq := (pick (min ((seq k).1 / 2) (r / (k + 2 : ℕ)))
          (lt_min (by linarith [(seq k).2]) (by positivity))).2
        constructor
        · calc
            (pick (min ((seq k).1 / 2) (r / (k + 2 : ℕ)))
              (lt_min (by linarith [(seq k).2]) (by positivity))).1
                < min ((seq k).1 / 2) (r / (k + 2 : ℕ)) := hq.2.1
            _ ≤ r / (k + 2 : ℕ) := min_le_right _ _
        · exact hq.2.2
  refine ⟨ρ, ?_, ?_, ?_⟩
  · have hstep : ∀ k, ρ (k + 1) < ρ k := fun k => by
      dsimp [ρ, seq]
      have hq := (pick (min ((seq k).1 / 2) (r / (k + 2 : ℕ)))
        (lt_min (by linarith [(seq k).2]) (by positivity))).2.2.1
      calc
        _ < min ((seq k).1 / 2) (r / (k + 2 : ℕ)) := hq
        _ ≤ (seq k).1 / 2 := min_le_left _ _
        _ < (seq k).1 := by linarith [(seq k).2]
    exact strictAnti_nat_of_succ_lt hstep
  · have hupper : Tendsto (fun k : ℕ => r / (k + 1 : ℕ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_comm] using
        (tendsto_const_nhds (x := r)).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := 0)) hupper
      (Eventually.of_forall fun k => (seq k).2.le)
      (Eventually.of_forall fun k => (hprops k).1.le)
  · intro k
    have hρpos : 0 < ρ k := (seq k).2
    refine ⟨hρpos, ?_, ?_⟩
    · rw [cube_closure_pi_Icc hρpos x]
      intro y hy
      have hnorm : ‖y - x‖ ≤ ρ k / 2 := by
        rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ρ k / 2)]
        intro i
        rw [Real.norm_eq_abs, abs_le]
        have hi := hy i (by simp)
        rw [Set.mem_Icc] at hi
        change -(ρ k / 2) ≤ (y - x) i ∧ (y - x) i ≤ ρ k / 2
        simpa only [Pi.sub_apply] using (show
          -(ρ k / 2) ≤ y i - x i ∧ y i - x i ≤ ρ k / 2 by
            constructor <;> linarith)
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hrho : ρ k / 2 < r := by
        have := (hprops k).1
        have hrpos : 0 < r := hr
        have hk : (1 : ℕ) ≤ k + 1 := by omega
        have hden : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast hk
        have hfrac : r / (k + 1 : ℕ) ≤ r := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))]
          nlinarith
        linarith
      exact hnorm.trans_lt hrho
    · have hnot := (hprops k).2
      have hnotpos : ¬ 0 < μ (frontier (cube (ρ k) x)) := by
        intro hm
        exact hnot ⟨hρpos, hm⟩
      exact le_antisymm (not_lt.mp hnotpos) zero_le

/-- Assemble the first localization step for a finite energy-limit measure. The density is finite
and has its centered-cube differentiation limit almost everywhere. At every point of `O` with
these properties, the selected cubes have null boundary and their energies converge by the two
portmanteau inequalities. In an application, `hopen` and `hcompact` are exactly the two fields
returned by `CitedMeasureLimit.extract_energy`. -/
theorem ae_exists_good_cubes_energy_converges [NeZero N]
    {μ : Measure (Sp N)} [IsFiniteMeasure μ] {O : Set (Sp N)} (hO : IsOpen O)
    {E : Set (Sp N) → ℕ → ℝ≥0∞}
    (hopen : ∀ U : Set (Sp N), IsOpen U → U ⊆ O →
      μ U ≤ liminf (E U) atTop)
    (hcompact : ∀ K : Set (Sp N), IsCompact K → K ⊆ O →
      limsup (E K) atTop ≤ μ K)
    (hmono : ∀ (x : Sp N) (ρ : ℝ) n,
      E (cube ρ x) n ≤ E (closure (cube ρ x)) n) :
    ∀ᵐ x ∂volume, x ∈ O →
      μ.rnDeriv volume x < ⊤ ∧
      Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
        (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) ∧
      ∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
        ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
          μ (frontier (cube (ρ k) x)) = 0 ∧
          Tendsto (E (cube (ρ k) x)) atTop (𝓝 (μ (cube (ρ k) x))) := by
  have hfinite : ∀ᵐ x ∂volume, μ.rnDeriv volume x < ⊤ :=
    ae_lt_top (Measure.measurable_rnDeriv μ volume)
      (Measure.lintegral_rnDeriv_lt_top μ volume).ne
  have hdensity := ae_tendsto_measure_ratio_cube_rnDeriv (μ := μ)
  filter_upwards [hfinite, hdensity] with x hfinite hdensity hxO
  obtain ⟨ρ, hanti, hρzero, hρ⟩ := exists_good_cube_radii (μ := μ) O hO hxO
  refine ⟨hfinite, hdensity, ρ, hanti, hρzero, ?_⟩
  intro k
  obtain ⟨hρpos, hclosure, hboundary⟩ := hρ k
  refine ⟨hρpos, hclosure, hboundary, ?_⟩
  exact tendsto_cube_energy_of_portmanteau O hclosure hboundary hopen hcompact
    (fun n => hmono x (ρ k) n)

/-- **Reduction of the Γ-liminf to sequences.** If `Φ ≤ ℓ` whenever `F_{εₙ}(vₙ) → ℓ < ∞` along
some sequence of positive `εₙ → 0` and `vₙ → u`, then `Φ ≤ Γ-liminf_{ε→0} F_ε(u)`. -/
theorem le_GammaLiminf_of_seq {X : Type*} [TopologicalSpace X] (F : ℝ → X → ℝ≥0∞) (u : X)
    (Φ : ℝ≥0∞)
    (h : ∀ (ε : ℕ → ℝ) (v : ℕ → X) (ℓ : ℝ≥0∞), (∀ n, 0 < ε n) →
      Tendsto ε atTop (𝓝[>] 0) → Tendsto v atTop (𝓝 u) → ℓ < ⊤ →
      Tendsto (fun n => F (ε n) (v n)) atTop (𝓝 ℓ) → Φ ≤ ℓ) :
    Φ ≤ GammaLiminf F u := by
  refine le_iInf₂ fun w hw => ?_
  set ℓ := liminf (fun ε => F ε (w ε)) (𝓝[>] (0 : ℝ))
  rcases eq_top_or_lt_top ℓ with hℓ | hℓ
  · rw [hℓ]; exact le_top
  obtain ⟨x, hx, hxℓ⟩ := exists_sequence_tendsto_liminf fun ε => F ε (w ε)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hx.eventually self_mem_nhdsWithin)
  have hshift : Tendsto (fun n => n + n₀) atTop atTop := tendsto_add_atTop_nat n₀
  exact h (fun n => x (n + n₀)) (fun n => w (x (n + n₀))) ℓ
    (fun n => hn₀ _ (Nat.le_add_left _ _)) (hx.comp hshift) ((hw.comp hx).comp hshift)
    hℓ (hxℓ.comp hshift)

/-- Finite energy forces the gradient into `dom G` almost everywhere. -/
theorem HasGGrowth.ae_mem_dom {m : ℕ} {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hL : HasGGrowth G α β L) (hα : 0 < α)
    (hLm : Measurable (uncurry L)) {p : ℝ≥0∞} {Ω : Set (Sp N)} (ε : ℝ) (u : W1p N m p Ω)
    (h : intFun L ε u ≠ ⊤) : ∀ᵐ x ∂(volume.restrict Ω), u.grad x ∈ dom G := by
  have hmeas : AEMeasurable (fun x => L (ε⁻¹ • x) (u.grad x)) (volume.restrict Ω) :=
    hLm.comp_aemeasurable
      ((measurable_const_smul ε⁻¹).aemeasurable.prodMk u.memLp_grad.1.aemeasurable)
  filter_upwards [ae_lt_top' hmeas h] with x hx
  exact hL.G_finite_of_L_finite hα hx

/-- The energy on an open subset `O` for a Sobolev function defined on the ambient domain `Ω`.
This is the setwise functional `I_ε(u;O)` from the article. -/
noncomputable def intFunOn {p : ℝ≥0∞} {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ) (O : Set (Sp N))
    (u : W1p N m p Ω) : ℝ≥0∞ :=
  ∫⁻ x in O, L (ε⁻¹ • x) (u.grad x)

/-- The local Γ-liminf `I⁻(u;O)` as defined in §2 of the article: the infimum over all families
converging to `u` in the ambient `Lᵖ(Ω)` topology of the liminf of their energies on `O`. -/
noncomputable def Iminus {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (O : Set (Sp N)) (u : W1p N m p Ω) : ℝ≥0∞ :=
  GammaLiminf (fun ε v => intFunOn L ε O v) u

/-- Every convergent family is an admissible competitor in the defining infimum of `Iminus`. -/
theorem Iminus_le_liminf_of_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (Sp N)}
    (L : Sp N → Mat m N → ℝ≥0∞) (O : Set (Sp N)) (u : W1p N m p Ω)
    (v : ℝ → W1p N m p Ω) (hv : Tendsto v (𝓝[>] 0) (𝓝 u)) :
    Iminus L O u ≤ liminf (fun ε => intFunOn L ε O (v ε)) (𝓝[>] 0) :=
  iInf₂_le v hv

/-- Restriction of a Sobolev function to a smaller open set. The weak-gradient identity restricts
because every test function supported in `U` is also supported in `Ω`. -/
def W1p.restrict {p : ℝ≥0∞} {Ω U : Set (Sp N)} (u : W1p N m p Ω) (hU : U ⊆ Ω) :
    W1p N m p U where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memLp.mono_measure (Measure.restrict_mono hU le_rfl)
  memLp_grad := u.memLp_grad.mono_measure (Measure.restrict_mono hU le_rfl)
  weak := by
    intro ψ hψ hcs hsupport v
    exact u.weak ψ hψ hcs (hsupport.trans hU) v

/-- Restriction is nonexpansive for the strong `Lᵖ` topology used on `W1p`. This allows (a1) and
(a2) to be applied on an interior cube when only the energy on `O` is bounded. -/
theorem W1p.restrict_lipschitz {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω U : Set (Sp N)}
    (hU : U ⊆ Ω) :
    LipschitzWith 1 (fun u : W1p N m p Ω => u.restrict hU) := by
  intro u v
  rw [edist_def, edist_def]
  exact (MeasureTheory.eLpNorm_mono_measure (u.toFun - v.toFun)
    (Measure.restrict_mono hU le_rfl)).trans_eq (by simp)

/-- Strong `Lᵖ` convergence on the ambient domain passes to every subset. -/
theorem W1p.tendsto_restrict {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω U : Set (Sp N)}
    (hU : U ⊆ Ω) {u : ℕ → W1p N m p Ω} {v : W1p N m p Ω}
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => (u n).restrict hU) atTop (𝓝 (v.restrict hU)) := by
  exact ((W1p.restrict_lipschitz (m := m) hU).continuous.tendsto _).comp hu

/-- Local version of `ae_mem_dom`: finite energy on `O` forces the gradient into the effective
domain on `O`. This is the form required for the local statement `I⁻(u;O)`. -/
theorem HasGGrowth.ae_mem_domOn {m : ℕ} {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hL : HasGGrowth G α β L) (hα : 0 < α)
    (hLm : Measurable (uncurry L)) {p : ℝ≥0∞} {Ω O : Set (Sp N)}
    (hOΩ : O ⊆ Ω) (ε : ℝ) (u : W1p N m p Ω)
    (hfinite : intFunOn L ε O u < ⊤) :
    ∀ᵐ x ∂(volume.restrict O), u.grad x ∈ dom G := by
  let uO := u.restrict hOΩ
  have hmeas : AEMeasurable (fun x => L (ε⁻¹ • x) (u.grad x)) (volume.restrict O) :=
    hLm.comp_aemeasurable
      ((measurable_const_smul ε⁻¹).aemeasurable.prodMk uO.memLp_grad.1.aemeasurable)
  filter_upwards [ae_lt_top' hmeas hfinite.ne] with x hx
  exact hL.G_finite_of_L_finite hα hx

/-- Pointwise form of the coercivity estimate, in the `ENNReal` power convention used by the
compactness interface (a). -/
theorem IsCoercive.enorm_rpow_le {p : ℝ} {c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hL : IsCoercive p c₀ L) (hp : 0 ≤ p) (hc₀ : 0 < c₀)
    (x : Sp N) (ξ : Mat m N) :
    ‖ξ‖ₑ ^ p ≤ (c₀ : ℝ≥0∞)⁻¹ * L x ξ := by
  have hc₀0 : (c₀ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc₀.ne'
  have hc₀top : (c₀ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hnorm : ‖ξ‖ₑ ^ p = ENNReal.ofReal (‖ξ‖ ^ p) := by
    simp [enorm_eq_nnnorm, ← ENNReal.ofReal_rpow_of_nonneg,
      norm_nonneg, hp]
  have hscale : ENNReal.ofReal (‖ξ‖ ^ p) =
      (c₀ : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((c₀ : ℝ) * ‖ξ‖ ^ p) := by
    calc
      ENNReal.ofReal (‖ξ‖ ^ p) =
          (c₀ : ℝ≥0∞)⁻¹ * ((c₀ : ℝ≥0∞) * ENNReal.ofReal (‖ξ‖ ^ p)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc₀0 hc₀top, one_mul]
      _ = (c₀ : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((c₀ : ℝ) * ‖ξ‖ ^ p) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg c₀), ENNReal.ofReal_coe_nnreal]
  calc
    ‖ξ‖ₑ ^ p = ENNReal.ofReal (‖ξ‖ ^ p) := hnorm
    _ = (c₀ : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((c₀ : ℝ) * ‖ξ‖ ^ p) := hscale
    _ ≤ (c₀ : ℝ≥0∞)⁻¹ * L x ξ := by
      calc
        _ = ENNReal.ofReal ((c₀ : ℝ) * ‖ξ‖ ^ p) * (c₀ : ℝ≥0∞)⁻¹ := mul_comm _ _
        _ ≤ L x ξ * (c₀ : ℝ≥0∞)⁻¹ := mul_le_mul_left (hL x ξ) _
        _ = (c₀ : ℝ≥0∞)⁻¹ * L x ξ := mul_comm _ _

/-- Coercivity bounds the local `p`-energy of the gradients by the local energy, with no
assumption on attainment of any infimum. The explicit `AEMeasurable` input is the composed
integrand needed by `setLIntegral_mono_ae`; in applications it follows from measurability of `L`
and the `MemLp` gradient of `u`. -/
theorem IsCoercive.grad_integral_bound {p : ℝ} {c₀ : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hL : IsCoercive p c₀ L)
    (hp : 0 ≤ p) (hc₀ : 0 < c₀) {Ω O : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (ε : ℝ)
    (henergy : AEMeasurable (fun x => L (ε⁻¹ • x) (u.grad x)) (volume.restrict O)) :
    ∫⁻ x in O, ‖u.grad x‖ₑ ^ p ≤
      (c₀ : ℝ≥0∞)⁻¹ * ∫⁻ x in O, L (ε⁻¹ • x) (u.grad x) := by
  have hscaled : AEMeasurable (fun x => (c₀ : ℝ≥0∞)⁻¹ * L (ε⁻¹ • x) (u.grad x))
      (volume.restrict O) := henergy.const_mul _
  calc
    ∫⁻ x in O, ‖u.grad x‖ₑ ^ p ≤
        ∫⁻ x in O, (c₀ : ℝ≥0∞)⁻¹ * L (ε⁻¹ • x) (u.grad x) := by
      refine setLIntegral_mono_ae hscaled ?_
      filter_upwards with x hxO
      exact hL.enorm_rpow_le hp hc₀ (ε⁻¹ • x) (u.grad x)
    _ = (c₀ : ℝ≥0∞)⁻¹ * ∫⁻ x in O, L (ε⁻¹ • x) (u.grad x) := by
      rw [MeasureTheory.lintegral_const_mul'' _ henergy]

/-- A uniform local energy bound gives a uniform `Lᵖ` bound for the gradients on the same open
set. This packages the coercivity step in the lower-bound sequence reduction. -/
theorem IsCoercive.sequence_grad_integral_bound {p : ℝ} {c₀ : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hL : IsCoercive p c₀ L)
    (hp : 0 ≤ p) (hc₀ : 0 < c₀) {Ω O : Set (Sp N)} (hOΩ : O ⊆ Ω)
    (hLm : Measurable (uncurry L)) (ε : ℕ → ℝ)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) {E : ℝ≥0∞} (hE : E < ⊤)
    (henergy : ∀ n, intFunOn L (ε n) O (u n) ≤ E) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, ∫⁻ x in O, ‖(u n).grad x‖ₑ ^ p ≤ C := by
  have hc₀' : 0 < (c₀ : ℝ≥0∞) := ENNReal.coe_pos.mpr hc₀
  refine ⟨(c₀ : ℝ≥0∞)⁻¹ * E,
    ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hc₀') hE, ?_⟩
  intro n
  have hmeas : AEMeasurable (fun x => L ((ε n)⁻¹ • x) ((u n).grad x))
      (volume.restrict O) := by
    let un := (u n).restrict hOΩ
    exact hLm.comp_aemeasurable
      ((measurable_const_smul (ε n)⁻¹).aemeasurable.prodMk un.memLp_grad.1.aemeasurable)
  exact (IsCoercive.grad_integral_bound hL hp hc₀ (u n) (ε n) hmeas).trans
    (mul_le_mul_of_nonneg_left (henergy n) bot_le)

/-- Under the same finite energy bound, every member of the sequence has gradient in the effective
domain almost everywhere on `O`. -/
theorem HasGGrowth.ae_mem_domOn_sequence {m : ℕ} {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hL : HasGGrowth G α β L) (hα : 0 < α)
    (hLm : Measurable (uncurry L)) {p : ℝ} {Ω O : Set (Sp N)} (hOΩ : O ⊆ Ω)
    (ε : ℕ → ℝ) (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) {E : ℝ≥0∞}
    (hE : E < ⊤) (henergy : ∀ n, intFunOn L (ε n) O (u n) ≤ E) :
    ∀ n, ∀ᵐ x ∂(volume.restrict O), (u n).grad x ∈ dom G := by
  intro n
  exact HasGGrowth.ae_mem_domOn hL hα hLm hOΩ (ε n) (u n) (henergy n |>.trans_lt hE)


section Statements

variable (N m : ℕ) [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- **(a)** Compactness in `W^{1,p}`, `p > N`, on a bounded Lipschitz domain (Morrey,
Rellich–Kondrachov, Ascoli, weak compactness and Mazur's lemma). Proved downstream:
`citedSobolevCompact_holds` (`SobolevCompactUniform.lean`). -/
def CitedSobolevCompact : Prop :=
  (N : ℝ) < p → ∀ Ω : Set (Sp N), IsOpen Ω → Bornology.IsBounded Ω → HasLipschitzBoundary Ω →
    ∀ (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) (v : W1p N m (ENNReal.ofReal p) Ω),
      Tendsto u atTop (𝓝 v) →
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, ∫⁻ x in Ω, ‖(u n).grad x‖ₑ ^ p ≤ C) →
      -- (a1) uniform convergence
      Tendsto (fun n => eLpNorm (fun x => (u n).toFun x - v.toFun x) ⊤ (volume.restrict Ω))
        atTop (𝓝 0) ∧
      -- (a2) closed convex gradient constraints pass to the limit
      ∀ K : Set (Mat m N), IsClosed K → Convex ℝ K →
        (∀ n, ∀ᵐ x ∂(volume.restrict Ω), (u n).grad x ∈ K) →
        ∀ᵐ x ∂(volume.restrict Ω), v.grad x ∈ K

/-- Apply the cited compactness statement on an interior Lipschitz set `U`, after restricting
ambient functions to `U`. This is the precise local form needed when the energies are controlled
only on the open set `O`. -/
theorem CitedSobolevCompact.restrict {N m : ℕ} {p : ℝ}
    [NeZero N] [Fact (1 ≤ ENNReal.ofReal p)] (hcompact : CitedSobolevCompact N m p)
    (hp : (N : ℝ) < p) {Ω U : Set (Sp N)} (hUΩ : U ⊆ Ω)
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hUlipschitz : HasLipschitzBoundary U)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) (v : W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto u atTop (𝓝 v))
    (hgrad : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, ∫⁻ x in U, ‖(u n).grad x‖ₑ ^ p ≤ C) :
    Tendsto (fun n => eLpNorm (((u n).restrict hUΩ).toFun - (v.restrict hUΩ).toFun) ⊤
      (volume.restrict U)) atTop (𝓝 0) ∧
    ∀ K : Set (Mat m N), IsClosed K → Convex ℝ K →
      (∀ n, ∀ᵐ x ∂(volume.restrict U), (u n).grad x ∈ K) →
      ∀ᵐ x ∂(volume.restrict U), v.grad x ∈ K := by
  have hgrad' : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n,
      ∫⁻ x in U, ‖((u n).restrict hUΩ).grad x‖ₑ ^ p ≤ C := by
    simpa [W1p.restrict] using hgrad
  obtain ⟨huniform, hclosed⟩ := hcompact hp U hUopen hUbounded hUlipschitz
    (fun n => (u n).restrict hUΩ) (v.restrict hUΩ)
    (W1p.tendsto_restrict hUΩ hu) hgrad'
  exact ⟨huniform, by simpa [W1p.restrict] using hclosed⟩

omit [NeZero N] in
theorem ae_norm_le_of_eLpNorm_top_le {μ : Measure (Sp N)}
    {f : Sp N → Tgt m} {B : ℝ} (hB : 0 ≤ B)
    (hbound : eLpNorm f ⊤ μ ≤ ENNReal.ofReal B) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ B := by
  have hess : eLpNormEssSup f μ ≤ ENNReal.ofReal B := by
    simpa only [eLpNorm_exponent_top] using hbound
  filter_upwards [MeasureTheory.enorm_ae_le_eLpNormEssSup f μ] with x hx
  have hx' : ‖f x‖ₑ ≤ ‖(B : ℝ)‖ₑ := by
    rw [Real.enorm_eq_ofReal hB]
    exact hx.trans hess
  simpa [Real.norm_eq_abs, abs_of_nonneg hB] using enorm_le_iff_norm_le.mp hx'

omit [NeZero N] in
/-- An a.e. statement on a measurable set remains valid a.e. on each of its subsets. -/
theorem ae_restrict_of_subset {U V : Set (Sp N)} (hVU : V ⊆ U)
    {P : Sp N → Prop} (hP : ∀ᵐ x ∂(volume.restrict U), P x) :
    ∀ᵐ x ∂(volume.restrict V), P x := by
  exact MeasureTheory.ae_mono (Measure.restrict_mono hVU le_rfl) hP

/-- Convert the (a1) essential-supremum convergence on a fixed Lipschitz set `U` to an a.e.
uniform error bound on any measurable subset `V ⊆ U`. The index threshold may depend on the
fixed scale `ρ` and on `η`. -/
theorem CitedSobolevCompact.restrict_ae_error
    {N m : ℕ} {p : ℝ} [NeZero N] [Fact (1 ≤ ENNReal.ofReal p)]
    (hcompact : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    {Ω U V : Set (Sp N)} (hUΩ : U ⊆ Ω)
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hUlipschitz : HasLipschitzBoundary U) (hVU : V ⊆ U)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) (v : W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto u atTop (𝓝 v))
    (hgrad : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, ∫⁻ x in U, ‖(u n).grad x‖ₑ ^ p ≤ C)
    {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ᵐ y ∂(volume.restrict V), ‖(u n).toFun y - v.toFun y‖ ≤ η * ρ := by
  have huniform := (hcompact.restrict hp hUΩ hUopen hUbounded hUlipschitz
    u v hu hgrad).1
  have hthreshold : 0 < ENNReal.ofReal (η * ρ) :=
    ENNReal.ofReal_pos.mpr (mul_pos hη hρ)
  obtain ⟨n₀, hn₀⟩ := ENNReal.tendsto_atTop_zero.mp huniform
    (ENNReal.ofReal (η * ρ)) hthreshold
  refine ⟨n₀, fun n hn => ?_⟩
  apply ae_norm_le_of_eLpNorm_top_le (N := N) (m := m)
    (mul_nonneg hη.le hρ.le)
  exact (MeasureTheory.eLpNorm_mono_measure
    (fun y => (u n).toFun y - v.toFun y)
    (Measure.restrict_mono hVU le_rfl)).trans (hn₀ n hn)

/-- On all cubes small enough to lie in a fixed Lipschitz set `U`, (a1) gives the sequence
error bound required by the cut-off argument, with a threshold `n₀` for each fixed cube. -/
theorem CitedSobolevCompact.restrict_ae_error_small_cubes
    {N m : ℕ} {p : ℝ} [NeZero N] [Fact (1 ≤ ENNReal.ofReal p)]
    (hcompact : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    {Ω U : Set (Sp N)} (hUΩ : U ⊆ Ω)
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hUlipschitz : HasLipschitzBoundary U)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) (v : W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto u atTop (𝓝 v))
    (hgrad : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, ∫⁻ x in U, ‖(u n).grad x‖ₑ ^ p ≤ C)
    {x₀ : Sp N} {ρU : ℝ}
    (hcube : ∀ ρ : ℝ, 0 < ρ → ρ < ρU → cube ρ x₀ ⊆ U) :
    ∀ ρ : ℝ, 0 < ρ → ρ < ρU → ∀ η : ℝ, 0 < η →
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀)),
          ‖(u n).toFun y - v.toFun y‖ ≤ η * ρ := by
  intro ρ hρ hρlt η hη
  exact hcompact.restrict_ae_error hp hUΩ hUopen hUbounded hUlipschitz
    (hcube ρ hρ hρlt) u v hu hgrad hρ hη

omit [NeZero N] in
/-- The fixed-set (a1) estimate also holds on the cut-off annulus, by restriction from the full
cube. The scale threshold is precisely the one ensuring `Qρ(x₀) ⊆ U`. -/
theorem CitedSobolevCompact.restrict_ae_error_small_annuli
    {N m : ℕ} {p : ℝ} [NeZero N] [Fact (1 ≤ ENNReal.ofReal p)]
    (hcompact : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    {Ω U : Set (Sp N)} (hUΩ : U ⊆ Ω)
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hUlipschitz : HasLipschitzBoundary U)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) (v : W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto u atTop (𝓝 v))
    (hgrad : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, ∫⁻ x in U, ‖(u n).grad x‖ₑ ^ p ≤ C)
    {x₀ : Sp N} {s ρU : ℝ} (hρU : 0 < ρU)
    (hcube : ∀ ρ : ℝ, 0 < ρ → ρ < ρU → cube ρ x₀ ⊆ U) :
    ∀ η : ℝ, 0 < η → ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          ‖(u n).toFun y - v.toFun y‖ ≤ η * ρ := by
  intro η hη
  refine ⟨ρU, hρU, ?_⟩
  intro ρ hρ hρlt
  obtain ⟨n₀, hcubeAE⟩ := hcompact.restrict_ae_error_small_cubes hp hUΩ
    hUopen hUbounded hUlipschitz u v hu hgrad hcube ρ hρ hρlt η hη
  refine ⟨n₀, fun n hn => ?_⟩
  exact ae_restrict_of_subset (U := cube ρ x₀)
    (V := cube ρ x₀ \ cube (s * ρ) x₀)
    (hVU := fun y hy => hy.1) (hP := hcubeAE n hn)

/-- If (a2) applies on every bounded Lipschitz subdomain and the approximating gradients lie in
`dom G` almost everywhere on `O`, then the limit gradient lies in `closure (dom G)` almost
everywhere on `O`. The proof uses a countable subcover by cubes whose closures are contained in
`O`; the exceptional null sets are combined using countability. -/
theorem CitedSobolevCompact.gradient_mem_closure_domOn {N m : ℕ} [NeZero N]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hcompact : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    {Ω O : Set (Sp N)} (hOopen : IsOpen O) (hOΩ : O ⊆ Ω)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) (v : W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto u atTop (𝓝 v))
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (hgrad : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, ∫⁻ x in O, ‖(u n).grad x‖ₑ ^ p ≤ C)
    (hdom : ∀ n, ∀ᵐ x ∂(volume.restrict O), (u n).grad x ∈ dom G) :
    ∀ᵐ x ∂(volume.restrict O), v.grad x ∈ closure (dom G) := by
  classical
  -- Choose an open metric ball `B(x, r x) ⊆ O` around each point, then the cube of side `r x`
  -- (half-side `r x / 2`) centered at `x`.
  let r : O → ℝ := fun x => Classical.choose (Metric.isOpen_iff.1 hOopen x.1 x.2)
  have hr : ∀ x : O, 0 < r x := fun x => (Classical.choose_spec
    (Metric.isOpen_iff.1 hOopen x.1 x.2)).1
  have hball : ∀ x : O, Metric.ball (x : Sp N) (r x) ⊆ O := fun x => (Classical.choose_spec
    (Metric.isOpen_iff.1 hOopen x.1 x.2)).2
  let Q : O → Set O := fun x => {y | (y : Sp N) ∈ cube (r x) (x : Sp N)}
  have hQnhds : ∀ x : O, Q x ∈ 𝓝 x := by
    intro x
    have hopen : IsOpen (Q x) := (isOpen_cube (r x) (x : Sp N)).preimage continuous_subtype_val
    have hxQ : x ∈ Q x := by
      change (x : Sp N) ∈ cube (r x) (x : Sp N)
      simp [cube, hr x]
    exact hopen.mem_nhds hxQ
  obtain ⟨S, hScount, hcover⟩ := countable_cover_nhds hQnhds
  let radius : (x : S) → ℝ := fun x => r x.1
  have hclosure : ∀ x : S, closure (cube (radius x) (x : Sp N)) ⊆ O := by
    intro x y hy
    have hρ : 0 < radius x := hr x.1
    rw [cube_closure_pi_Icc hρ (x : Sp N)] at hy
    have hnorm : ‖y - (x : Sp N)‖ ≤ radius x / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ radius x / 2)]
      intro i
      rw [Real.norm_eq_abs]
      have hi := hy i (by simp)
      rw [Set.mem_Icc] at hi
      rw [abs_le]
      constructor
      · change -(radius x / 2) ≤ y i - (x : Sp N) i
        linarith
      · change y i - (x : Sp N) i ≤ radius x / 2
        linarith
    apply hball x.1
    rw [Metric.mem_ball, dist_eq_norm]
    have : radius x / 2 < radius x := by linarith [hρ]
    exact hnorm.trans_lt this
  have hsubset : ∀ x : S, cube (radius x) (x : Sp N) ⊆ O := fun x y hy =>
    hclosure x (subset_closure hy)
  have : Countable S := hScount.to_subtype
  let K : Set (Mat m N) := closure (dom G)
  have hKclosed : IsClosed K := isClosed_closure
  have hKconvex : Convex ℝ K := hG.convex_dom.closure
  have hlocal : ∀ x : S,
      ∀ᵐ y ∂(volume.restrict (cube (radius x) (x : Sp N))),
        v.grad y ∈ K := by
    intro x
    let U := cube (radius x) (x : Sp N)
    have hUΩ : U ⊆ Ω := (hsubset x).trans hOΩ
    have hUopen : IsOpen U := isOpen_cube _ _
    have hUbounded : Bornology.IsBounded U := isBounded_cube _ _
    have hUlipschitz : HasLipschitzBoundary U := HasLipschitzBoundary.cube _ _
    have hgradU : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n,
        ∫⁻ y in U, ‖(u n).grad y‖ₑ ^ p ≤ C := by
      obtain ⟨C, hCtop, hC⟩ := hgrad
      refine ⟨C, hCtop, fun n => ?_⟩
      exact (lintegral_mono_set (hsubset x)).trans (hC n)
    have hdomU : ∀ n, ∀ᵐ y ∂(volume.restrict U), (u n).grad y ∈ K := by
      intro n
      have hglobal : ∀ᵐ y ∂volume, y ∈ O → (u n).grad y ∈ dom G :=
        (ae_restrict_iff' hOopen.measurableSet).1 (hdom n)
      have hglobalU : ∀ᵐ y ∂volume, y ∈ U → (u n).grad y ∈ K := by
        filter_upwards [hglobal] with y hy hyU
        exact subset_closure (hy ((hsubset x) hyU))
      exact (ae_restrict_iff' hUopen.measurableSet).2 hglobalU
    have hresult := hcompact.restrict hp hUΩ hUopen hUbounded hUlipschitz
      u v hu hgradU
    exact hresult.2 K hKclosed hKconvex hdomU
  have hglobal : ∀ᵐ y ∂volume, ∀ x : S,
      y ∈ cube (radius x) (x : Sp N) → v.grad y ∈ K := by
    rw [ae_all_iff]
    intro x
    have hUopen : IsOpen (cube (radius x) (x : Sp N)) := isOpen_cube _ _
    exact (ae_restrict_iff' hUopen.measurableSet).1 (hlocal x)
  rw [ae_restrict_iff' hOopen.measurableSet]
  filter_upwards [hglobal] with y hy hyO
  have hmem : (⟨y, hyO⟩ : O) ∈ ⋃ x ∈ S, Q x := by
    rw [hcover]
    simp
  rcases mem_iUnion.1 hmem with ⟨x, hx⟩
  rcases mem_iUnion.1 hx with ⟨hxS, hxQ⟩
  exact hy ⟨x, hxS⟩ hxQ

/-- **(b)** A.e. differentiability of `W^{1,p}` functions, `p > N`, in the `L^∞`-on-cubes sense
(eq. `difflowerbound` of the paper). Proved downstream: `citedSobolevDiff_holds` (`Morrey.lean`). -/
def CitedSobolevDiff : Prop :=
  (N : ℝ) < p → ∀ Ω : Set (Sp N), IsOpen Ω → ∀ u : W1p N m (ENNReal.ofReal p) Ω,
    ∀ᵐ x ∂(volume.restrict Ω), ∃ a : Tgt m,
      Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
          eLpNorm (fun y => u.toFun y - affineMap a (u.grad x) x y) ⊤
            (volume.restrict (cube ρ x)))
        (𝓝[>] 0) (𝓝 0)

omit [NeZero N] in
/-- The normalized `eLpNorm` differentiability limit in `CitedSobolevDiff` yields an `o(ρ)`
a.e. affine error on all sufficiently small centered cubes. -/
theorem CitedSobolevDiff.affine_remainder_ae_small_of_tendsto
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    {u : W1p N m (ENNReal.ofReal p) Ω} {x₀ : Sp N} {a₀ : Tgt m}
    (hlim : Tendsto
      (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
        eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x₀) x₀ y) ⊤
          (volume.restrict (cube ρ x₀)))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀)),
          ‖u.toFun y - affineMap a₀ (u.grad x₀) x₀ y‖ ≤ η * ρ := by
  intro η hη
  have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal ρ⁻¹ *
        eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x₀) x₀ y) ⊤
          (volume.restrict (cube ρ x₀)) ≤ ENNReal.ofReal η :=
    (ENNReal.tendsto_nhds_zero.mp hlim (ENNReal.ofReal η)
      (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hsmall)
  refine ⟨r, hr, fun ρ hρ hρr => ?_⟩
  have hratio := hnear (by simpa [Real.dist_eq, abs_of_pos hρ] using hρr) hρ
  let a : ℝ≥0∞ := ENNReal.ofReal ρ⁻¹
  let E : ℝ≥0∞ := eLpNorm
    (fun y => u.toFun y - affineMap a₀ (u.grad x₀) x₀ y) ⊤
    (volume.restrict (cube ρ x₀))
  have hae : a * E ≤ ENNReal.ofReal η := by simpa [a, E] using hratio
  have hmul : a * ENNReal.ofReal (η * ρ) = ENNReal.ofReal η := by
    dsimp [a]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le)]
    congr 1
    field_simp [ne_of_gt hρ]
  have hE : E ≤ ENNReal.ofReal (η * ρ) := by
    have hae' : a * E ≤ a * ENNReal.ofReal (η * ρ) := by
      calc
        a * E ≤ ENNReal.ofReal η := hae
        _ = a * ENNReal.ofReal (η * ρ) := hmul.symm
    exact (ENNReal.mul_le_mul_iff_right
      (by
        dsimp [a]
        exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hρ)))
      (by
        dsimp [a]
        exact ENNReal.ofReal_ne_top)).mp hae'
  exact ae_norm_le_of_eLpNorm_top_le (N := N) (m := m)
    (mul_nonneg hη.le hρ.le) hE

omit [NeZero N] in
/-- Apply the preceding conversion pointwise to the differentiability interface (b). -/
theorem CitedSobolevDiff.affine_remainder_ae_small
    (hDiff : CitedSobolevDiff N m p) (hp : (N : ℝ) < p)
    (Ω : Set (Sp N)) (hΩopen : IsOpen Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∃ a₀ : Tgt m,
      ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
          ∀ᵐ y ∂(volume.restrict (cube ρ x)),
            ‖u.toFun y - affineMap a₀ (u.grad x) x y‖ ≤ η * ρ := by
  filter_upwards [hDiff hp Ω hΩopen u] with x hx
  rcases hx with ⟨a₀, hlim⟩
  exact ⟨a₀, CitedSobolevDiff.affine_remainder_ae_small_of_tendsto
    (N := N) (m := m) hlim⟩

omit [NeZero N] in
/-- Restrict the affine approximation estimate from `Qρ(x₀)` to the cut-off annulus contained
in that cube. -/
theorem CitedSobolevDiff.affine_remainder_ae_small_on_annulus
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    {u : W1p N m (ENNReal.ofReal p) Ω} {x₀ : Sp N} {a₀ : Tgt m} {s : ℝ}
    (hlim : Tendsto
      (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
        eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x₀) x₀ y) ⊤
          (volume.restrict (cube ρ x₀)))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          ‖u.toFun y - affineMap a₀ (u.grad x₀) x₀ y‖ ≤ η * ρ := by
  intro η hη
  obtain ⟨ρ₀, hρ₀, hcube⟩ :=
    CitedSobolevDiff.affine_remainder_ae_small_of_tendsto (N := N) (m := m) hlim η hη
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρlt => ?_⟩
  exact ae_restrict_of_subset (U := cube ρ x₀)
    (V := cube ρ x₀ \ cube (s * ρ) x₀)
    (hVU := fun y hy => hy.1) (hP := hcube ρ hρ hρlt)

/-- **(c)** Weak-* compactness of bounded sequences of measures `gₙ dx` on a bounded open set,
with the two Alexandrov (portmanteau) inequalities. Proved downstream: `citedMeasureLimit_holds`
(`MeasureLimit.lean`). -/
def CitedMeasureLimit : Prop :=
  ∀ O : Set (Sp N), IsOpen O → Bornology.IsBounded O →
    ∀ g : ℕ → Sp N → ℝ≥0∞, (∀ n, AEMeasurable (g n) (volume.restrict O)) →
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, ∫⁻ x in O, g n x ≤ C) →
      ∃ (φ : ℕ → ℕ) (μ : Measure (Sp N)), StrictMono φ ∧ IsFiniteMeasure μ ∧ μ Oᶜ = 0 ∧
        (∀ U : Set (Sp N), IsOpen U → U ⊆ O →
          μ U ≤ liminf (fun n => ∫⁻ x in U, g (φ n) x) atTop) ∧
        (∀ K : Set (Sp N), IsCompact K → K ⊆ O →
          limsup (fun n => ∫⁻ x in K, g (φ n) x) atTop ≤ μ K)

/-- Apply the cited compactness/portmanteau interface to the local energy measures. Measurability
uses the restriction of each Sobolev function to `O`; the finite uniform energy bound is the only
measure compactness input. -/
theorem CitedMeasureLimit.extract_energy {N m : ℕ} {p : ℝ}
    [NeZero N] [Fact (1 ≤ ENNReal.ofReal p)]
    (hlimit : CitedMeasureLimit N) {Ω O : Set (Sp N)}
    (hOΩ : O ⊆ Ω) (hOopen : IsOpen O) (hObounded : Bornology.IsBounded O)
    {L : Sp N → Mat m N → ℝ≥0∞} (hLm : Measurable (uncurry L))
    (ε : ℕ → ℝ) (u : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hbound : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, intFunOn L (ε n) O (u n) ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ μ : Measure (Sp N), StrictMono φ ∧ IsFiniteMeasure μ ∧ μ Oᶜ = 0 ∧
      (∀ U : Set (Sp N), IsOpen U → U ⊆ O →
        μ U ≤ liminf (fun n => intFunOn L (ε (φ n)) U (u (φ n))) atTop) ∧
      (∀ K : Set (Sp N), IsCompact K → K ⊆ O →
        limsup (fun n => intFunOn L (ε (φ n)) K (u (φ n))) atTop ≤ μ K) := by
  rcases hbound with ⟨C, hCtop, hC⟩
  have hmeas (n : ℕ) :
      AEMeasurable (fun x => L ((ε n)⁻¹ • x) ((u n).grad x)) (volume.restrict O) := by
    let un := (u n).restrict hOΩ
    exact hLm.comp_aemeasurable
      ((measurable_const_smul (ε n)⁻¹).aemeasurable.prodMk un.memLp_grad.1.aemeasurable)
  obtain ⟨φ, μ, hφ, hμfinite, hμO, hopen, hcompact⟩ :=
    hlimit O hOopen hObounded (fun n x => L ((ε n)⁻¹ • x) ((u n).grad x)) hmeas
      ⟨C, hCtop, fun n => by simpa [intFunOn] using hC n⟩
  refine ⟨φ, μ, hφ, hμfinite, hμO, ?_, ?_⟩
  · intro U hUopen hUO
    simpa [intFunOn] using hopen U hUopen hUO
  · intro K hKcompact hKO
    simpa [intFunOn] using hcompact K hKcompact hKO

/-- The localization data returned by `CitedMeasureLimit.extract_energy`, together with the
almost-everywhere good-point and cube-energy convergence conclusions needed at the start of Step 1.
The monotonicity required by the portmanteau lemma is proved here directly from monotonicity of
the set integral. -/
theorem CitedMeasureLimit.extract_energy_localize_cubes {N m : ℕ} [NeZero N]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hlimit : CitedMeasureLimit N)
    {Ω O : Set (Sp N)} (hOΩ : O ⊆ Ω) (hOopen : IsOpen O)
    (hObounded : Bornology.IsBounded O) {L : Sp N → Mat m N → ℝ≥0∞}
    (hLm : Measurable (uncurry L)) (ε : ℕ → ℝ)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hbound : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, intFunOn L (ε n) O (u n) ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ μ : Measure (Sp N), StrictMono φ ∧ IsFiniteMeasure μ ∧ μ Oᶜ = 0 ∧
      (∀ U : Set (Sp N), IsOpen U → U ⊆ O →
        μ U ≤ liminf (fun n => intFunOn L (ε (φ n)) U (u (φ n))) atTop) ∧
      (∀ K : Set (Sp N), IsCompact K → K ⊆ O →
        limsup (fun n => intFunOn L (ε (φ n)) K (u (φ n))) atTop ≤ μ K) ∧
      (∀ᵐ x ∂volume, x ∈ O →
        μ.rnDeriv volume x < ⊤ ∧
        Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) ∧
        ∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
          ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
            μ (frontier (cube (ρ k) x)) = 0 ∧
            Tendsto (fun n => intFunOn L (ε (φ n)) (cube (ρ k) x) (u (φ n)))
              atTop (𝓝 (μ (cube (ρ k) x)))) := by
  obtain ⟨φ, μ, hφ, hμfinite, hμO, hopen, hcompact⟩ :=
    hlimit.extract_energy hOΩ hOopen hObounded hLm ε u hbound
  have hassembled := ae_exists_good_cubes_energy_converges (μ := μ) hOopen
    (E := fun A n => intFunOn L (ε (φ n)) A (u (φ n))) hopen hcompact ?_
  · exact ⟨φ, μ, hφ, hμfinite, hμO, hopen, hcompact, hassembled⟩
  · intro x ρ n
    change (∫⁻ y in cube ρ x, L ((ε (φ n))⁻¹ • y) ((u (φ n)).grad y)) ≤
      ∫⁻ y in closure (cube ρ x), L ((ε (φ n))⁻¹ • y) ((u (φ n)).grad y)
    exact lintegral_mono_set subset_closure

/-- Finish Step 1 of the local lower-bound proof for a sequence whose energies converge to a finite
value. The first inequality is the RN-density estimate on the measurable open set `O`; the second
uses the *open-set* portmanteau inequality and the fact that a convergent sequence has liminf equal
to its limit. The almost-everywhere conclusion combines the previously proved cube localization
with (a2), applied to the extracted subsequence. -/
theorem CitedMeasureLimit.extract_energy_step1 {N m : ℕ} [NeZero N]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hlimit : CitedMeasureLimit N)
    (hcompactSob : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    {Ω O : Set (Sp N)} (hOΩ : O ⊆ Ω) (hOopen : IsOpen O)
    (hObounded : Bornology.IsBounded O) {G : Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) {L : Sp N → Mat m N → ℝ≥0∞}
    (hLm : Measurable (uncurry L)) (ε : ℕ → ℝ)
    (u : ℕ → W1p N m (ENNReal.ofReal p) Ω) (v : W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto u atTop (𝓝 v))
    (hbound : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, intFunOn L (ε n) O (u n) ≤ C)
    (hgrad : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, ∫⁻ x in O, ‖(u n).grad x‖ₑ ^ p ≤ C)
    (hdom : ∀ n, ∀ᵐ x ∂(volume.restrict O), (u n).grad x ∈ dom G)
    (ell : ℝ≥0∞) (_hell : ell < ⊤)
    (henergy : Tendsto (fun n => intFunOn L (ε n) O (u n)) atTop (𝓝 ell)) :
    ∃ φ : ℕ → ℕ, ∃ μ : Measure (Sp N), StrictMono φ ∧ IsFiniteMeasure μ ∧ μ Oᶜ = 0 ∧
      (∀ U : Set (Sp N), IsOpen U → U ⊆ O →
        μ U ≤ liminf (fun n => intFunOn L (ε (φ n)) U (u (φ n))) atTop) ∧
      (∀ K : Set (Sp N), IsCompact K → K ⊆ O →
        limsup (fun n => intFunOn L (ε (φ n)) K (u (φ n))) atTop ≤ μ K) ∧
      (∫⁻ x in O, μ.rnDeriv volume x ≤ μ O ∧ μ O ≤ ell) ∧
      (∀ᵐ x ∂(volume.restrict O),
        μ.rnDeriv volume x < ⊤ ∧
        Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) ∧
        (∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
          ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
            μ (frontier (cube (ρ k) x)) = 0 ∧
            Tendsto (fun n => intFunOn L (ε (φ n)) (cube (ρ k) x) (u (φ n)))
              atTop (𝓝 (μ (cube (ρ k) x)))) ∧
        v.grad x ∈ closure (dom G)) := by
  obtain ⟨φ, μ, hφ, hμfinite, hμO, hopen, hportcompact, hgood⟩ :=
    hlimit.extract_energy_localize_cubes hOΩ hOopen hObounded hLm ε u hbound
  have henergyφ : Tendsto (fun n => intFunOn L (ε (φ n)) O (u (φ n)))
      atTop (𝓝 ell) := henergy.comp hφ.tendsto_atTop
  have hmass_le : ∫⁻ x in O, μ.rnDeriv volume x ≤ μ O :=
    rnDeriv_lintegral_le_measure hOopen.measurableSet
  have hO_le : μ O ≤ ell := by
    calc
      μ O ≤ liminf (fun n => intFunOn L (ε (φ n)) O (u (φ n))) atTop :=
        hopen O hOopen subset_rfl
      _ = ell := henergyφ.liminf_eq
  obtain ⟨Cgrad, hCgrad_top, hCgrad⟩ := hgrad
  have hgradφ : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ n, ∫⁻ x in O, ‖(u (φ n)).grad x‖ₑ ^ p ≤ C :=
    ⟨Cgrad, hCgrad_top, fun n => hCgrad (φ n)⟩
  have hgrad_limit := hcompactSob.gradient_mem_closure_domOn hp hOopen hOΩ
    (fun n => u (φ n)) v (hu.comp hφ.tendsto_atTop) hG hgradφ
    (fun n => hdom (φ n))
  have hgood_restrict : ∀ᵐ x ∂(volume.restrict O),
      μ.rnDeriv volume x < ⊤ ∧
        Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) ∧
        ∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
          ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
            μ (frontier (cube (ρ k) x)) = 0 ∧
            Tendsto (fun n => intFunOn L (ε (φ n)) (cube (ρ k) x) (u (φ n)))
              atTop (𝓝 (μ (cube (ρ k) x))) := by
    apply (ae_restrict_iff' hOopen.measurableSet).2
    exact hgood
  refine ⟨φ, μ, hφ, hμfinite, hμO, hopen, hportcompact, ⟨hmass_le, hO_le⟩, ?_⟩
  filter_upwards [hgood_restrict, hgrad_limit] with x hx hgradx
  exact ⟨hx.1, hx.2.1, hx.2.2, hgradx⟩

/-! ### The affine cut-off used in Step 2 of the local lower bound -/

/-- The cut-off replacement of an affine map by a Sobolev function. -/
noncomputable def affineCutoffValue {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m)
    (A : Mat m N) (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ρ : ℝ) (x y : Sp N) : Tgt m :=
  affineMap a A x₀ y + cutoff hs ρ x y • (u.toFun y - affineMap a A x₀ y)

/-- The weak-gradient formula associated with `affineCutoffValue`. -/
noncomputable def affineCutoffGrad {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m)
    (A : Mat m N) (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ρ : ℝ) (x y : Sp N) : Mat m N :=
  A + cutoff hs ρ x y • (u.grad y - A) +
    (fderiv ℝ (cutoff hs ρ x) y).smulRight (u.toFun y - affineMap a A x₀ y)

omit [NeZero N] in
/-- The zero-boundary perturbation `t(v - ℓ)` is admissible on the outer cube. This is precisely
`W1p0.smul` applied to `cutoff_sub_affine_mem_W1p0`; no regularity of the cut-off competitor
beyond that existing lemma is needed. -/
theorem affineCutoff_smul_mem_W1p0 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N) (x₀ : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N)
    (hball : Metric.closedBall x (ρ / 2) ⊆ Ω) (t : ℝ) :
    ((fun y => t • (affineCutoffValue (N := N) (m := m) u a A x₀ hs ρ x y -
        affineMap a A x₀ y)),
      (fun y => t • (affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x y - A))) ∈
        W1p0 (ENNReal.ofReal p) (cube ρ x) := by
  have hcut := cutoff_sub_affine_mem_W1p0 hΩopen hΩbounded u a A x₀ hs hρ x hball
  have hscaled := W1p0.smul hcut t
  convert hscaled using 1
  all_goals ext y
  all_goals simp [affineCutoffValue, affineCutoffGrad, sub_eq_add_neg]
  all_goals module

omit [NeZero N] in
/-- The cut-off competitor gives a normalized lower bound by the rescaled cell problem. The
reference slope is `t • A`; the zero-boundary correction has weak gradient
`t • (∇v - A)`, so after adding the slope the cell integrand is exactly `t • ∇v`. -/
theorem affineCutoff_rescaled_cell_lower
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hball : Metric.closedBall x₀ (ρ / 2) ⊆ Ω) (t : ℝ) :
    Ytp (ENNReal.ofReal p) L (cube (ρ / ε) (ε⁻¹ • x₀)) (t • A) /
        volume (cube (ρ / ε) (ε⁻¹ • x₀)) ≤
      (∫⁻ y in cube ρ x₀, L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y)) /
        volume (cube ρ x₀) := by
  let w : (Sp N → Tgt m) × (Sp N → Mat m N) :=
    (fun y => t • (affineCutoffValue (N := N) (m := m) u a A x₀ hs ρ x₀ y -
      affineMap a A x₀ y),
     fun y => t • (affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y - A))
  have hw : w ∈ W1p0 (ENNReal.ofReal p) (cube ρ x₀) :=
    affineCutoff_smul_mem_W1p0 (N := N) (m := m)
      hΩopen hΩbounded u a A x₀ hs hρ x₀ hball t
  have hcell := Ytp_rescale_le L hε x₀ (t • A) hw
  have hfactor : volume (cube ρ x₀) =
      ENNReal.ofReal (ε ^ N) * volume (cube (ρ / ε) (ε⁻¹ • x₀)) := by
    rw [volume_cube, volume_cube,
      show ENNReal.ofReal ρ = ENNReal.ofReal ε * ENNReal.ofReal (ρ / ε) by
        rw [← ENNReal.ofReal_mul hε.le, mul_div_cancel₀ _ hε.ne'],
      mul_pow, ← ENNReal.ofReal_pow hε.le]
  have hcoef0 : ENNReal.ofReal (ε ^ N) ≠ 0 := by simp [hε, pow_pos]
  have hratio :
      (ENNReal.ofReal (ε ^ N) *
        Ytp (ENNReal.ofReal p) L (cube (ρ / ε) (ε⁻¹ • x₀)) (t • A)) /
          volume (cube ρ x₀) =
      Ytp (ENNReal.ofReal p) L (cube (ρ / ε) (ε⁻¹ • x₀)) (t • A) /
        volume (cube (ρ / ε) (ε⁻¹ • x₀)) := by
    rw [hfactor]
    exact ENNReal.mul_div_mul_left _ _ hcoef0 ENNReal.ofReal_ne_top
  have hnormalized := ENNReal.div_le_div_right hcell (volume (cube ρ x₀))
  rw [hratio] at hnormalized
  have hgradarg : ∀ y,
      (t • A) + w.2 y =
        t • affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y := by
    intro y
    dsimp [w]
    module
  simpa [w, hgradarg] using hnormalized

omit [NeZero N] in
/-- `Ytp_tendsto_Hp` remains valid along the extracted subsequence. The only scale hypothesis is
the convergence of the original positive-parameter sequence to zero; strict monotonicity of the
subsequence is not otherwise needed here. -/
theorem Ytp_cell_ratio_tendsto_Hp_subsequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {L : Sp N → Mat m N → ℝ≥0∞}
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} (hperiodic : IsPeriodic L)
    (hgrowth : HasGGrowth G α β L) {ξ : Mat m N} (hξ : G ξ < ⊤)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) (ε : ℕ → ℝ) (φ : ℕ → ℕ)
    (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n =>
      Ytp p L (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x)) ξ /
        volume (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x)))
      atTop (𝓝 (Hp p L ξ)) := by
  have hcell := Ytp_tendsto_Hp (N := N) (m := m) (p := p) hperiodic
    (fun y ζ => (hgrowth y ζ).2) (ne_of_lt hξ) hρ x
  exact hcell.comp (hε.comp hφ)

omit [NeZero N] in
/-- The affine cut-off expression is a genuine Sobolev function on the ambient bounded open set,
and its weak gradient is exactly `affineCutoffGrad`. The proof adds the affine map to the
zero-extended `W1p0` product-rule pair supplied by `cutoff_sub_affine_mem_W1p0`. -/
theorem affineCutoff_mem_W1p {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N) (x₀ : Sp N)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N)
    (hball : Metric.closedBall x (ρ / 2) ⊆ Ω) :
    ∃ v : W1p N m (ENNReal.ofReal p) Ω,
      (∀ y, v.toFun y = affineCutoffValue (N := N) (m := m) u a A x₀ hs ρ x y) ∧
      (∀ y, v.grad y = affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x y) := by
  have hcut := cutoff_sub_affine_mem_W1p0 hΩopen hΩbounded u a A x₀ hs hρ x hball
  rcases hcut with ⟨hzero, hcutLp, hcutGradLp, hcutWeak⟩
  have hcutWeakΩ : HasWeakGrad Ω
      (fun y => cutoff hs ρ x y • (u.toFun y - affineMap a A x₀ y))
      (fun y => cutoff hs ρ x y • (u.grad y - A) +
        (fderiv ℝ (cutoff hs ρ x) y).smulRight (u.toFun y - affineMap a A x₀ y)) := by
    intro ψ hψ hcs hsupport w
    exact hcutWeak ψ hψ hcs (hsupport.trans (subset_univ Ω)) w
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.2 hΩbounded.measure_lt_top.ne
  refine ⟨{
    toFun := affineMap a A x₀ + fun y => cutoff hs ρ x y • (u.toFun y - affineMap a A x₀ y)
    grad := (fun _ => A) + fun y => cutoff hs ρ x y • (u.grad y - A) +
      (fderiv ℝ (cutoff hs ρ x) y).smulRight (u.toFun y - affineMap a A x₀ y)
    memLp := memLp_add' (memLp_affineMap hΩbounded a A x₀ (ENNReal.ofReal p))
      (hcutLp.restrict Ω)
    memLp_grad := memLp_add' (memLp_const A) (hcutGradLp.restrict Ω)
    weak := HasWeakGrad.add hΩopen hΩbounded
      (memLp_affineMap hΩbounded a A x₀ (ENNReal.ofReal p)) (memLp_const A)
      (hcutLp.restrict Ω) (hcutGradLp.restrict Ω)
      (hasWeakGrad_affineMap Ω a A x₀) hcutWeakΩ }, ?_, ?_⟩
  · intro y
    rfl
  · intro y
    simp [affineCutoffGrad]
    module

omit [NeZero N] in
/-- Pointwise product-rule identity for the gradient expression. -/
theorem affineCutoffGrad_eq_expanded {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ρ : ℝ) (x y : Sp N) :
    affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x y =
      cutoff hs ρ x y • u.grad y + (1 - cutoff hs ρ x y) • A +
        (fderiv ℝ (cutoff hs ρ x) y).smulRight
          (u.toFun y - affineMap a A x₀ y) := by
  simp [affineCutoffGrad]
  module

omit [NeZero N] in
/-- On the inner cube the cut-off is constant one, so the weak-gradient formula reduces
pointwise to the original gradient. -/
theorem affineCutoffGrad_eq_inner {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ)
    (x y : Sp N) (hy : y ∈ cube (s * ρ) x) :
    affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x y = u.grad y := by
  rw [affineCutoffGrad_eq_expanded (N := N) (m := m) u a A x₀ hs ρ x y]
  rw [cutoff_eq_one hs hρ x hy, fderiv_cutoff_eq_zero hs hρ x hy]
  simp

omit [NeZero N] in
/-- On the open annulus between the two cubes, the full product-rule expression remains active.
This records the exact gradient to which the three-term growth estimate is applied. -/
theorem affineCutoffGrad_eq_annulus {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ρ : ℝ) (x y : Sp N)
    (_hy : y ∈ cube ρ x \ cube (s * ρ) x) :
    affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x y =
      cutoff hs ρ x y • u.grad y + (1 - cutoff hs ρ x y) • A +
        (fderiv ℝ (cutoff hs ρ x) y).smulRight
          (u.toFun y - affineMap a A x₀ y) :=
  affineCutoffGrad_eq_expanded (N := N) (m := m) u a A x₀ hs ρ x y

omit [NeZero N] in
/-- On the cut-off annulus, scaling the weak gradient by `t` gives the three-term convex
decomposition used in the local lower-bound argument. Here `τ = t / θ` and the third term is
`Φ = t / (1 - τ) • (Dφ smulRight (u - ℓ))`. The formula is pointwise for the chosen Sobolev
representatives, hence also holds almost everywhere. -/
theorem affineCutoff_scaled_annulus_decomp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (_hρ : 0 < ρ)
    (x y : Sp N) (hy : y ∈ cube ρ x \ cube (s * ρ) x)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (_hθ : θ < 1) :
    t • affineCutoffGrad (N := N) (m := m) u a₀ A x₀ hs ρ x y =
      (t / θ * cutoff hs ρ x y) • (θ • u.grad y) +
        (t / θ * (1 - cutoff hs ρ x y)) • (θ • A) +
          (1 - t / θ) • ((t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x) y).smulRight
              (u.toFun y - affineMap a₀ A x₀ y))) := by
  have hθpos : 0 < θ := lt_trans ht htθ
  have hτpos : 0 < t / θ := div_pos ht hθpos
  have hτlt : t / θ < 1 := (div_lt_one₀ hθpos).2 htθ
  have hφ0 := cutoff_nonneg hs ρ x y
  have hφ1 := cutoff_le_one hs ρ x y
  have hfirst : t / θ * cutoff hs ρ x y * θ = t * cutoff hs ρ x y := by
    field_simp [ne_of_gt hθpos]
  have hsecond : t / θ * (1 - cutoff hs ρ x y) * θ =
      t * (1 - cutoff hs ρ x y) := by
    field_simp [ne_of_gt hθpos]
  have hthird : (1 - t / θ) * (t / (1 - t / θ)) = t := by
    have hθmt : 0 < θ - t := sub_pos.mpr htθ
    field_simp [ne_of_gt hθpos, ne_of_gt hθmt]
  rw [affineCutoffGrad_eq_annulus (N := N) (m := m) u a₀ A x₀ hs ρ x y hy]
  simp only [smul_smul]
  rw [hfirst, hsecond, hthird]
  module

omit [NeZero N] in
/-- Almost-everywhere form of `affineCutoff_scaled_annulus_decomp`, with respect to Lebesgue
measure restricted to the annulus. The pointwise representative identity is stronger. -/
theorem affineCutoff_scaled_annulus_decomp_ae {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Sp N) {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1) :
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      t • affineCutoffGrad (N := N) (m := m) u a₀ A x₀ hs ρ x y =
        (t / θ * cutoff hs ρ x y) • (θ • u.grad y) +
          (t / θ * (1 - cutoff hs ρ x y)) • (θ • A) +
            (1 - t / θ) • ((t / (1 - t / θ)) •
              ((fderiv ℝ (cutoff hs ρ x) y).smulRight
                (u.toFun y - affineMap a₀ A x₀ y))) := by
  filter_upwards [ae_restrict_mem
    ((isOpen_cube ρ x).measurableSet.diff (isOpen_cube (s * ρ) x).measurableSet)] with y hy
  exact affineCutoff_scaled_annulus_decomp (N := N) (m := m) u a₀ A x₀ hs hρ x y hy
    ht htθ hθ

omit [NeZero N] in
/-- Pointwise application of `HasGGrowth.weighted_three_upper` to the scaled cut-off gradient
on the annulus. The remainder `Φ` is left uncontrolled here; this lemma makes no estimate on it. -/
theorem HasGGrowth.affineCutoff_scaled_annulus_upper
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hgrowth : HasGGrowth G α β L)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (_hρ : 0 < ρ)
    (x y : Sp N) (hy : y ∈ cube ρ x \ cube (s * ρ) x)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (_hθ : θ < 1) :
    let τ : ℝ := t / θ
    let φ : ℝ := cutoff hs ρ x y
    let w₁ : ℝ≥0 := Real.toNNReal (τ * φ)
    let w₂ : ℝ≥0 := Real.toNNReal (τ * (1 - φ))
    let w₃ : ℝ≥0 := Real.toNNReal (1 - τ)
    L y (t • affineCutoffGrad (N := N) (m := m) u a₀ A x₀ hs ρ x y) ≤
      (β : ℝ≥0∞) * (1 + (w₁ : ℝ≥0∞) * G (θ • u.grad y) +
        (w₂ : ℝ≥0∞) * G (θ • A) + (w₃ : ℝ≥0∞) *
          G ((t / (1 - τ)) •
            ((fderiv ℝ (cutoff hs ρ x) y).smulRight
              (u.toFun y - affineMap a₀ A x₀ y)))) := by
  dsimp
  let τ : ℝ := t / θ
  let φ : ℝ := cutoff hs ρ x y
  let w₁ : ℝ≥0 := Real.toNNReal (τ * φ)
  let w₂ : ℝ≥0 := Real.toNNReal (τ * (1 - φ))
  let w₃ : ℝ≥0 := Real.toNNReal (1 - τ)
  have hθpos : 0 < θ := lt_trans ht htθ
  have hτpos : 0 < τ := by dsimp [τ]; exact div_pos ht hθpos
  have hτlt : τ < 1 := by dsimp [τ]; exact (div_lt_one₀ hθpos).2 htθ
  have hφ0 : 0 ≤ φ := by dsimp [φ]; exact cutoff_nonneg hs ρ x y
  have hφ1 : φ ≤ 1 := by dsimp [φ]; exact cutoff_le_one hs ρ x y
  have hw₁ : 0 ≤ τ * φ := mul_nonneg hτpos.le hφ0
  have hw₂ : 0 ≤ τ * (1 - φ) := mul_nonneg hτpos.le (sub_nonneg.mpr hφ1)
  have hw₃ : 0 ≤ 1 - τ := sub_nonneg.mpr hτlt.le
  have habc : w₁ + w₂ + w₃ = 1 := by
    apply NNReal.coe_injective
    simp only [w₁, w₂, w₃, NNReal.coe_add, Real.coe_toNNReal _ hw₁,
      Real.coe_toNNReal _ hw₂, Real.coe_toNNReal _ hw₃, NNReal.coe_one]
    dsimp [τ, φ]
    ring
  have hfirst : τ * φ * θ = t * φ := by
    dsimp [τ]
    field_simp [ne_of_gt hθpos]
  have hsecond : τ * (1 - φ) * θ = t * (1 - φ) := by
    dsimp [τ]
    field_simp [ne_of_gt hθpos]
  have hthird : (1 - τ) * (t / (1 - τ)) = t := by
    field_simp [ne_of_gt (sub_pos.mpr hτlt)]
  let err : Mat m N :=
    (fderiv ℝ (cutoff hs ρ x) y).smulRight (u.toFun y - affineMap a₀ A x₀ y)
  have hdecomp : t • affineCutoffGrad (N := N) (m := m) u a₀ A x₀ hs ρ x y =
      (w₁ : ℝ) • (θ • u.grad y) + (w₂ : ℝ) • (θ • A) +
        (w₃ : ℝ) • ((t / (1 - τ)) • err) := by
    rw [affineCutoffGrad_eq_annulus (N := N) (m := m) u a₀ A x₀ hs ρ x y hy]
    simp only [w₁, w₂, w₃, Real.coe_toNNReal _ hw₁, Real.coe_toNNReal _ hw₂,
      Real.coe_toNNReal _ hw₃, smul_smul]
    rw [hfirst, hsecond, hthird]
    module
  rw [hdecomp]
  exact HasGGrowth.weighted_three_upper hG hgrowth y w₁ w₂ w₃ habc
    (θ • u.grad y) (θ • A)
    ((t / (1 - τ)) •
      ((fderiv ℝ (cutoff hs ρ x) y).smulRight
        (u.toFun y - affineMap a₀ A x₀ y)))

omit [NeZero N] in
/-- Quantitative pointwise estimate for the cut-off remainder, from a bound on the affine error.
The conclusion is a.e. because the Sobolev representatives and the `L∞` hypotheses (a1), (b)
only control values outside null sets. -/
theorem affineCutoff_remainder_ae_bound {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (uₙ : W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m)
    (A : Mat m N) (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) {t θ : ℝ}
    (ht : 0 < t) (htθ : t < θ) (_hθ : θ < 1) {C R : ℝ}
    (hC : 0 ≤ C) (_hR : 0 ≤ R)
    (hderiv : ∀ y, ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (herror : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖uₙ.toFun y - affineMap a₀ A x₀ y‖ ≤ R) :
    ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖(t / (1 - t / θ)) •
        ((fderiv ℝ (cutoff hs ρ x) y).smulRight
          (uₙ.toFun y - affineMap a₀ A x₀ y))‖ ≤
            (t / (1 - t / θ)) * (C / ρ) * R := by
  have hden : 0 < 1 - t / θ := sub_pos.mpr ((div_lt_one₀ (lt_trans ht htθ)).2 htθ)
  have hK : 0 < t / (1 - t / θ) := div_pos ht hden
  filter_upwards [herror] with y hy
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hK,
    ContinuousLinearMap.norm_smulRight_apply]
  calc
    t / (1 - t / θ) *
        (‖fderiv ℝ (cutoff hs ρ x) y‖ *
          ‖uₙ.toFun y - affineMap a₀ A x₀ y‖)
      ≤ t / (1 - t / θ) * (C / ρ * R) := by
          gcongr
          exact hderiv y
    _ = (t / (1 - t / θ)) * (C / ρ) * R := by ring

/-! The next lemma assembles the error estimates from (a1) and (b). These assumptions state their
almost-everywhere consequences on the annulus; this is the strongest conclusion justified for
arbitrary Sobolev representatives. -/
omit [NeZero N] in
theorem affineCutoff_remainder_ae_small {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {Ω : Set (Sp N)} (u : W1p N m (ENNReal.ofReal p) Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (x : Sp N)
    (hcenter : x = x₀)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (_hθ : θ < 1)
    (hdiff : ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖u.toFun y - affineMap a₀ A x₀ y‖ ≤ η * ρ)
    (ha1 : ∀ η : ℝ, 0 < η → ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖(uₙ n).toFun y - u.toFun y‖ ≤ η * ρ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖(t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x) y).smulRight
              ((uₙ n).toFun y - affineMap a₀ A x₀ y))‖ ≤ δ := by
  subst x
  obtain ⟨C, hC, hderiv⟩ := exists_cutoff_fderiv_bound hs
  have hden : 0 < 1 - t / θ := sub_pos.mpr ((div_lt_one₀ (lt_trans ht htθ)).2 htθ)
  have hK : 0 < t / (1 - t / θ) := div_pos ht hden
  let q : ℝ := δ / (4 * (t / (1 - t / θ)) * (C + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨ρd, hρd, hdiffρ⟩ := hdiff q hq
  obtain ⟨ρa, hρa, ha1q⟩ := ha1 q hq
  refine ⟨min ρd ρa, lt_min hρd hρa, fun ρ hρ hρlt => ?_⟩
  have ⟨hρdlt, hρalt⟩ := lt_min_iff.mp hρlt
  obtain ⟨n₀, ha1n⟩ := ha1q ρ hρ hρalt
  refine ⟨n₀, fun n hn => ?_⟩
  have herror : ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
      ‖(uₙ n).toFun y - affineMap a₀ A x₀ y‖ ≤ 2 * (q * ρ) := by
    filter_upwards [ha1n n hn, hdiffρ ρ hρ hρdlt] with y hseq hdif
    calc
      ‖(uₙ n).toFun y - affineMap a₀ A x₀ y‖
          = ‖((uₙ n).toFun y - u.toFun y) +
              (u.toFun y - affineMap a₀ A x₀ y)‖ := by congr 1; abel
      _ ≤ ‖(uₙ n).toFun y - u.toFun y‖ +
            ‖u.toFun y - affineMap a₀ A x₀ y‖ := norm_add_le _ _
      _ ≤ q * ρ + q * ρ := add_le_add hseq hdif
      _ = 2 * (q * ρ) := by ring
  have hR : 0 ≤ 2 * (q * ρ) := by positivity
  have hsmall : (t / (1 - t / θ)) * ((C + 1) / ρ) * (2 * (q * ρ)) ≤ δ := by
    calc
      (t / (1 - t / θ)) * ((C + 1) / ρ) * (2 * (q * ρ))
          = 2 * (t / (1 - t / θ)) * (C + 1) * q := by
              field_simp [ne_of_gt hρ]
      _ = δ / 2 := by
            dsimp [q]
            field_simp [ne_of_gt hK, ne_of_gt (show 0 < C + 1 by linarith)]
            ring
      _ ≤ δ := by linarith
  filter_upwards [affineCutoff_remainder_ae_bound (N := N) (m := m)
    (uₙ n) a₀ A x₀ hs hρ x₀ ht htθ _hθ (C := C + 1) (R := 2 * (q * ρ))
    (by linarith) hR
    (fun y => by
      have h := hderiv ρ x₀ y hρ
      calc
        ‖fderiv ℝ (cutoff hs ρ x₀) y‖ ≤ C / ρ := h
        _ ≤ (C + 1) / ρ := by
          have : 0 ≤ 1 / ρ := by positivity
          rw [add_div]
          linarith) herror] with y hy
  exact hy.trans hsmall

/-- At a point satisfying the differentiability conclusion (b), the a.e. affine error from (b)
and the a.e. sequence error from (a1) can be supplied on the same shrinking cut-off annuli.
The fixed Lipschitz cube used for (a1) is chosen with closure inside `O`; the conclusion remains
almost everywhere, as required by the essential-supremum hypotheses. -/
theorem affineCutoff_remainder_ae_small_of_cited
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω O : Set (Sp N)}
    (hcompact : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    (hOopen : IsOpen O) (hOΩ : O ⊆ Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto uₙ atTop (𝓝 u))
    (hgradO : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n,
      ∫⁻ y in O, ‖(uₙ n).grad y‖ₑ ^ p ≤ C)
    {x₀ : Sp N} (hx₀ : x₀ ∈ O) (a₀ : Tgt m)
    (hDiffPoint : Tendsto
      (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
        eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x₀) x₀ y) ⊤
          (volume.restrict (cube ρ x₀)))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    (∀ η' : ℝ, 0 < η' → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          ‖u.toFun y - affineMap a₀ (u.grad x₀) x₀ y‖ ≤ η' * ρ) ∧
    (∀ η' : ℝ, 0 < η' → ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          ‖(uₙ n).toFun y - u.toFun y‖ ≤ η' * ρ) ∧
    (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          ‖(t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              ((uₙ n).toFun y - affineMap a₀ (u.grad x₀) x₀ y))‖ ≤ δ) := by
  classical
  let R : ℝ := Classical.choose (Metric.isOpen_iff.1 hOopen x₀ hx₀)
  have hR : 0 < R := (Classical.choose_spec
    (Metric.isOpen_iff.1 hOopen x₀ hx₀)).1
  have hball : Metric.ball x₀ R ⊆ O := (Classical.choose_spec
    (Metric.isOpen_iff.1 hOopen x₀ hx₀)).2
  have hclosure : closure (cube R x₀) ⊆ O := by
    intro y hy
    rw [cube_closure_pi_Icc hR x₀] at hy
    have hnorm : ‖y - x₀‖ ≤ R / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ R / 2)]
      intro i
      rw [Real.norm_eq_abs]
      have hi := hy i (by simp)
      rw [Set.mem_Icc] at hi
      rw [abs_le]
      constructor
      · change -(R / 2) ≤ y i - x₀ i
        linarith
      · change y i - x₀ i ≤ R / 2
        linarith
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hhalf : R / 2 < R := by linarith
    exact hnorm.trans_lt hhalf
  have hUO : cube R x₀ ⊆ O := fun y hy => hclosure (subset_closure hy)
  have hUΩ : cube R x₀ ⊆ Ω := hUO.trans hOΩ
  have hUopen : IsOpen (cube R x₀) := isOpen_cube _ _
  have hUbounded : Bornology.IsBounded (cube R x₀) := isBounded_cube _ _
  have hUlipschitz : HasLipschitzBoundary (cube R x₀) := HasLipschitzBoundary.cube _ _
  have hcube : ∀ ρ : ℝ, 0 < ρ → ρ < R → cube ρ x₀ ⊆ cube R x₀ := by
    intro ρ hρ hρR y hy
    rw [cube_eq_ball hρ] at hy
    rw [cube_eq_ball hR]
    exact Metric.ball_subset_ball (by linarith) hy
  have hgradU : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n,
      ∫⁻ y in cube R x₀, ‖(uₙ n).grad y‖ₑ ^ p ≤ C := by
    obtain ⟨C, hCtop, hC⟩ := hgradO
    exact ⟨C, hCtop, fun n => (lintegral_mono_set hUO).trans (hC n)⟩
  have ha1 := hcompact.restrict_ae_error_small_annuli hp hUΩ hUopen hUbounded
    hUlipschitz uₙ u hu hgradU (x₀ := x₀) (s := s) hR hcube
  have hdiff := CitedSobolevDiff.affine_remainder_ae_small_on_annulus
    (N := N) (m := m) hDiffPoint (s := s)
  refine ⟨hdiff, ha1, ?_⟩
  exact affineCutoff_remainder_ae_small (N := N) (m := m)
    u uₙ a₀ (u.grad x₀) x₀ hs x₀ rfl ht htθ hθ hdiff ha1 δ hδ

omit [NeZero N] in
/-- If the remainder is a.e. in the finite ball around zero provided by convexity, then `G` has
a finite uniform a.e. bound on the annulus. -/
theorem ConvexENN.affineCutoff_remainder_ae_le_finite
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (uₙ : W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Sp N) {t θ : ℝ}
    (ht : 0 < t) (htθ : t < θ) (_hθ : θ < 1)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hderiv : ∀ y, ‖fderiv ℝ (cutoff hs ρ x) y‖ ≤ C / ρ)
    (herror : ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
      ‖uₙ.toFun y - affineMap a₀ A x₀ y‖ ≤ R)
    (hsmall : (t / (1 - t / θ)) * (C / ρ) * R ≤
      Classical.choose (hG.exists_finite_bound_closedBall_zero h0)) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧
      ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
        G ((t / (1 - t / θ)) •
          ((fderiv ℝ (cutoff hs ρ x) y).smulRight
            (uₙ.toFun y - affineMap a₀ A x₀ y))) ≤ M := by
  let hexists := hG.exists_finite_bound_closedBall_zero h0
  let R₀ := Classical.choose hexists
  have hR₀spec := Classical.choose_spec hexists
  let M := Classical.choose hR₀spec
  have hspec := Classical.choose_spec hR₀spec
  have hball := hspec.2.2
  refine ⟨M, hspec.2.1, ?_⟩
  filter_upwards [affineCutoff_remainder_ae_bound (N := N) (m := m)
    uₙ a₀ A x₀ hs hρ x ht htθ _hθ
    hC hR hderiv herror] with y hy
  exact hball _ (hy.trans hsmall)

omit [NeZero N] in
/-- Under the a.e. error estimates from (a1) and (b), `G(Φₙ)` has a finite uniform bound for
sufficiently small cubes and all sufficiently large sequence indices. -/
theorem ConvexENN.affineCutoff_remainder_ae_uniform_bound
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (x : Sp N)
    (hcenter : x = x₀)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    (hdiff : ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖u.toFun y - affineMap a₀ A x₀ y‖ ≤ η * ρ)
    (ha1 : ∀ η : ℝ, 0 < η → ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          ‖(uₙ n).toFun y - u.toFun y‖ ≤ η * ρ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x \ cube (s * ρ) x)),
          G ((t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x) y).smulRight
              ((uₙ n).toFun y - affineMap a₀ A x₀ y))) ≤ M := by
  obtain ⟨r, M, hr, hM, hball⟩ := hG.exists_finite_bound_closedBall_zero h0
  obtain ⟨ρ₀, hρ₀, hsmall⟩ := affineCutoff_remainder_ae_small (N := N) (m := m)
    u uₙ a₀ A x₀ hs x hcenter ht htθ hθ hdiff ha1 r hr
  refine ⟨M, hM, ρ₀, hρ₀, fun ρ hρ hρlt => ?_⟩
  obtain ⟨n₀, hbound⟩ := hsmall ρ hρ hρlt
  refine ⟨n₀, fun n hn => ?_⟩
  filter_upwards [hbound n hn] with y hy
  exact hball _ hy

omit [NeZero N] in
/-- The finite bound for `G(Φₙ)` can be chosen independently of the annulus parameter `s`.
Only the small-radius and large-index thresholds depend on `s`; this is the uniformity needed
before sending `s → 1` in the boundary-layer estimate. -/
theorem ConvexENN.affineCutoff_remainder_ae_uniform_bound_all_s
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    (hdiff : ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
          ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
            ‖u.toFun y - affineMap a₀ A x₀ y‖ ≤ η * ρ)
    (ha1 : ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∃ n₀ : ℕ, ∀ n, n ≥ n₀ →
          ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
            ‖(uₙ n).toFun y - u.toFun y‖ ≤ η * ρ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧
      ∀ (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1),
        ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
          ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∃ n₀ : ℕ, ∀ n, n ≥ n₀ →
            ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
              G ((t / (1 - t / θ)) •
                ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
                  ((uₙ n).toFun y - affineMap a₀ A x₀ y))) ≤ M := by
  obtain ⟨r, M, hr, hM, hball⟩ := hG.exists_finite_bound_closedBall_zero h0
  refine ⟨M, hM, fun s hs => ?_⟩
  obtain ⟨ρ₀, hρ₀, hsmall⟩ := affineCutoff_remainder_ae_small (N := N) (m := m)
    u uₙ a₀ A x₀ ⟨hs.1, hs.2⟩ x₀ rfl ht htθ hθ
    (hdiff s hs) (ha1 s hs) r hr
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρlt => ?_⟩
  obtain ⟨n₀, hbound⟩ := hsmall ρ hρ hρlt
  refine ⟨n₀, fun n hn => ?_⟩
  filter_upwards [hbound n hn] with y hy
  exact hball _ hy

omit [NeZero N] in
/-- Integrate the pointwise three-term growth estimate on one fixed annulus. The `G`-term of the
sequence is a.e. measurable because its scaled gradient lies in `interior (dom G)`; the energy
integrand itself is also a.e. measurable by composing `L` with the Sobolev cut-off gradient. All
integrals are ENNReal integrals, so the conclusion remains meaningful when an energy is infinite. -/
theorem HasGGrowth.affineCutoff_scaled_annulus_lintegral_bound
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hgrowth : HasGGrowth G α β L)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hLm : Measurable (uncurry L))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (uₙ : W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall x₀ (ρ / 2) ⊆ Ω)
    {t θ ε : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    (M : ℝ≥0∞)
    (hM : ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
      G ((t / (1 - t / θ)) •
        ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
          (uₙ.toFun y - affineMap a₀ A x₀ y))) ≤ M)
    (hdom : ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
      uₙ.grad y ∈ dom G) :
    AEMeasurable (fun y => L (ε⁻¹ • y)
      (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y))
        (volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)) ∧
    ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
      L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y) ≤
      (β : ℝ≥0∞) *
        (((1 + M + G (θ • A)) *
            volume (cube ρ x₀ \ cube (s * ρ) x₀)) +
          ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, G (θ • uₙ.grad y)) := by
  classical
  let S : Set (Sp N) := cube ρ x₀ \ cube (s * ρ) x₀
  have hSΩ : S ⊆ Ω := by
    intro y hy
    change y ∈ cube ρ x₀ \ cube (s * ρ) x₀ at hy
    rw [cube_eq_ball hρ] at hy
    exact hball (Metric.ball_subset_closedBall hy.1)
  obtain ⟨vcut, _, hvgrad⟩ := affineCutoff_mem_W1p (N := N) (m := m)
    hΩopen hΩbounded
    uₙ a₀ A x₀ hs hρ x₀ hball
  have hcutgrad : AEMeasurable
      (fun y => t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y)
      (volume.restrict S) := by
    have hgrad := (vcut.restrict hSΩ).memLp_grad.1.aemeasurable
    have hscaled := (measurable_const_smul t).comp_aemeasurable hgrad
    exact hscaled.congr (Filter.Eventually.of_forall fun y =>
      congrArg (fun z : Mat m N => t • z) (hvgrad y))
  have henergy : AEMeasurable (fun y => L (ε⁻¹ • y)
      (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y))
      (volume.restrict S) := by
    exact hLm.comp_aemeasurable
      ((measurable_const_smul ε⁻¹).aemeasurable.prodMk hcutgrad)
  have hgrad : AEMeasurable (fun y => θ • uₙ.grad y) (volume.restrict S) := by
    have hgrad₀ := (uₙ.restrict hSΩ).memLp_grad.1.aemeasurable
    exact (measurable_const_smul θ).comp_aemeasurable hgrad₀
  let Gext : Mat m N → ℝ≥0∞ := (interior (dom G)).piecewise G (fun _ => 0)
  have hGext : Measurable Gext := by
    exact hG.continuousOn_interior_dom.measurable_piecewise continuousOn_const
      isOpen_interior.measurableSet
  have hGgrad : AEMeasurable (fun y => G (θ • uₙ.grad y)) (volume.restrict S) := by
    have hmeas := hGext.comp_aemeasurable hgrad
    have hinside : ∀ᵐ y ∂(volume.restrict S), θ • uₙ.grad y ∈ interior (dom G) := by
      filter_upwards [hdom] with y hy
      exact hG.smul_mem_interior_dom h0 (subset_closure hy)
        (le_of_lt (lt_trans ht htθ)) hθ
    apply hmeas.congr
    filter_upwards [hinside] with y hy
    simp [Gext, hy]
  have hGrowthε : HasGGrowth G α β (fun y ξ => L (ε⁻¹ • y) ξ) := by
    intro y ξ
    exact hgrowth (ε⁻¹ • y) ξ
  have hpoint : ∀ᵐ y ∂(volume.restrict S),
      L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y) ≤
          (β : ℝ≥0∞) *
            (1 + G (θ • uₙ.grad y) + G (θ • A) + M) := by
    filter_upwards [ae_restrict_mem
      ((isOpen_cube ρ x₀).measurableSet.diff (isOpen_cube (s * ρ) x₀).measurableSet),
      hM, hdom] with y hyS hMy hy
    have hupper := HasGGrowth.affineCutoff_scaled_annulus_upper
      (N := N) (m := m) hG hGrowthε uₙ a₀ A x₀ hs hρ x₀ y hyS ht htθ hθ
    let τ : ℝ := t / θ
    let φ : ℝ := cutoff hs ρ x₀ y
    let w₁ : ℝ≥0 := Real.toNNReal (τ * φ)
    let w₂ : ℝ≥0 := Real.toNNReal (τ * (1 - φ))
    let w₃ : ℝ≥0 := Real.toNNReal (1 - τ)
    have hθpos : 0 < θ := lt_trans ht htθ
    have hτpos : 0 < τ := by dsimp [τ]; exact div_pos ht hθpos
    have hτlt : τ < 1 := by dsimp [τ]; exact (div_lt_one₀ hθpos).2 htθ
    have hφ0 : 0 ≤ φ := by dsimp [φ]; exact cutoff_nonneg hs ρ x₀ y
    have hφ1 : φ ≤ 1 := by dsimp [φ]; exact cutoff_le_one hs ρ x₀ y
    have hw₁r : 0 ≤ τ * φ := mul_nonneg hτpos.le hφ0
    have hw₂r : 0 ≤ τ * (1 - φ) := mul_nonneg hτpos.le (sub_nonneg.mpr hφ1)
    have hw₃r : 0 ≤ 1 - τ := sub_nonneg.mpr hτlt.le
    have habc : w₁ + w₂ + w₃ = 1 := by
      apply NNReal.coe_injective
      simp only [w₁, w₂, w₃, NNReal.coe_add, Real.coe_toNNReal _ hw₁r,
        Real.coe_toNNReal _ hw₂r, Real.coe_toNNReal _ hw₃r, NNReal.coe_one]
      dsimp [τ, φ]
      ring
    change L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y) ≤
      (β : ℝ≥0∞) *
        (1 + (w₁ : ℝ≥0∞) * G (θ • uₙ.grad y) +
          (w₂ : ℝ≥0∞) * G (θ • A) + (w₃ : ℝ≥0∞) *
            G ((t / (1 - τ)) •
              ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
                (uₙ.toFun y - affineMap a₀ A x₀ y)))) at hupper
    have hw₁ : (w₁ : ℝ≥0∞) ≤ 1 := by
      have hw : w₁ ≤ 1 := by
        rw [← habc]
        calc w₁ ≤ w₁ + w₂ := le_add_of_nonneg_right w₂.2
          _ ≤ w₁ + w₂ + w₃ := le_add_of_nonneg_right w₃.2
      exact_mod_cast hw
    have hw₂ : (w₂ : ℝ≥0∞) ≤ 1 := by
      have hw : w₂ ≤ 1 := by
        rw [← habc]
        calc w₂ ≤ w₁ + w₂ := le_add_of_nonneg_left w₁.2
          _ ≤ w₁ + w₂ + w₃ := le_add_of_nonneg_right w₃.2
      exact_mod_cast hw
    have hw₃ : (w₃ : ℝ≥0∞) ≤ 1 := by
      have hw : w₃ ≤ 1 := by
        rw [← habc]
        exact le_add_of_nonneg_left (add_nonneg w₁.2 w₂.2)
      exact_mod_cast hw
    have hsum : 1 + (w₁ : ℝ≥0∞) * G (θ • uₙ.grad y) +
        (w₂ : ℝ≥0∞) * G (θ • A) + (w₃ : ℝ≥0∞) *
          G ((t / (1 - τ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              (uₙ.toFun y - affineMap a₀ A x₀ y))) ≤
        1 + G (θ • uₙ.grad y) + G (θ • A) + M := by
      have hterm₁ : (w₁ : ℝ≥0∞) * G (θ • uₙ.grad y) ≤ G (θ • uₙ.grad y) := by
        calc
          (w₁ : ℝ≥0∞) * G (θ • uₙ.grad y) ≤ 1 * G (θ • uₙ.grad y) :=
            mul_le_mul_of_nonneg_right hw₁ bot_le
          _ = G (θ • uₙ.grad y) := one_mul _
      have hterm₂ : (w₂ : ℝ≥0∞) * G (θ • A) ≤ G (θ • A) := by
        calc
          (w₂ : ℝ≥0∞) * G (θ • A) ≤ 1 * G (θ • A) :=
            mul_le_mul_of_nonneg_right hw₂ bot_le
          _ = G (θ • A) := one_mul _
      have hterm₃ : (w₃ : ℝ≥0∞) *
          G ((t / (1 - τ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              (uₙ.toFun y - affineMap a₀ A x₀ y))) ≤
          G ((t / (1 - τ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              (uₙ.toFun y - affineMap a₀ A x₀ y))) := by
        calc
          (w₃ : ℝ≥0∞) *
              G ((t / (1 - τ)) •
                ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
                  (uₙ.toFun y - affineMap a₀ A x₀ y))) ≤
              1 * G ((t / (1 - τ)) •
                ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
                  (uₙ.toFun y - affineMap a₀ A x₀ y))) :=
            mul_le_mul_of_nonneg_right hw₃ bot_le
          _ = G ((t / (1 - τ)) •
              ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
                (uₙ.toFun y - affineMap a₀ A x₀ y))) := one_mul _
      calc
        _ ≤ 1 + G (θ • uₙ.grad y) + G (θ • A) +
            G ((t / (1 - τ)) •
              ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
                (uₙ.toFun y - affineMap a₀ A x₀ y))) := by
              gcongr
        _ ≤ 1 + G (θ • uₙ.grad y) + G (θ • A) + M := by
          gcongr
    calc
      L (ε⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y) ≤
          (β : ℝ≥0∞) *
            (1 + (w₁ : ℝ≥0∞) * G (θ • uₙ.grad y) +
              (w₂ : ℝ≥0∞) * G (θ • A) + (w₃ : ℝ≥0∞) *
                G ((t / (1 - τ)) •
                  ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
                    (uₙ.toFun y - affineMap a₀ A x₀ y)))) := hupper
      _ ≤ (β : ℝ≥0∞) *
          (1 + G (θ • uₙ.grad y) + G (θ • A) + M) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
  refine ⟨by simpa [S] using henergy, ?_⟩
  have hpoint' : ∀ᵐ y ∂(volume.restrict S),
      L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y) ≤
          (β : ℝ≥0∞) *
            ((1 + M + G (θ • A)) + G (θ • uₙ.grad y)) := by
    filter_upwards [hpoint] with y hy
    convert hy using 1; ring
  calc
    ∫⁻ y in S, L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) uₙ a₀ A x₀ hs ρ x₀ y)
      ≤ ∫⁻ y in S, (β : ℝ≥0∞) *
          ((1 + M + G (θ • A)) + G (θ • uₙ.grad y)) := lintegral_mono_ae hpoint'
    _ = (β : ℝ≥0∞) *
          (((1 + M + G (θ • A)) * volume S) +
            ∫⁻ y in S, G (θ • uₙ.grad y)) := by
      let c : ℝ≥0∞ := 1 + M + G (θ • A)
      have hcmeas : AEMeasurable (fun y => c + G (θ • uₙ.grad y))
          (volume.restrict S) := aemeasurable_const.add hGgrad
      calc
        ∫⁻ y in S, (β : ℝ≥0∞) * (c + G (θ • uₙ.grad y)) =
            (β : ℝ≥0∞) * ∫⁻ y in S, c + G (θ • uₙ.grad y) :=
          lintegral_const_mul'' _ hcmeas
        _ = (β : ℝ≥0∞) *
            ((c * volume S) + ∫⁻ y in S, G (θ • uₙ.grad y)) := by
          rw [lintegral_add_right' _ hGgrad, setLIntegral_const]
        _ = (β : ℝ≥0∞) *
            (((1 + M + G (θ • A)) * volume S) +
              ∫⁻ y in S, G (θ • uₙ.grad y)) := by simp [c]

omit [NeZero N] in
/-- The fixed-scale annulus estimate, uniformly for all sufficiently small outer radii and all
sufficiently large sequence indices. The bound `M` and the two thresholds are supplied by
`ConvexENN.affineCutoff_remainder_ae_uniform_bound`; this theorem only integrates the resulting
pointwise growth estimate. -/
theorem ConvexENN.affineCutoff_integrated_annulus_bound
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hgrowth : HasGGrowth G α β L) (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hLm : Measurable (uncurry L))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρmax : ℝ} (hρmax : 0 < ρmax)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Metric.closedBall x₀ (ρ / 2) ⊆ Ω)
    (hdom : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → ∀ n,
      ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
        (uₙ n).grad y ∈ dom G)
    {t θ ε : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    (hdiff : ∀ η : ℝ, 0 < η → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          ‖u.toFun y - affineMap a₀ A x₀ y‖ ≤ η * ρ)
    (ha1 : ∀ η : ℝ, 0 < η → ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          ‖(uₙ n).toFun y - u.toFun y‖ ≤ η * ρ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        AEMeasurable (fun y => L (ε⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs ρ x₀ y))
          (volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀) ) ∧
        ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
          L (ε⁻¹ • y)
            (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs ρ x₀ y) ≤
          (β : ℝ≥0∞) *
            (((1 + M + G (θ • A)) *
                volume (cube ρ x₀ \ cube (s * ρ) x₀)) +
              ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, G (θ • (uₙ n).grad y)) := by
  obtain ⟨M, hMtop, ρrem, hρrem, hM⟩ :=
    hG.affineCutoff_remainder_ae_uniform_bound (N := N) (m := m)
      h0 u uₙ a₀ A x₀ hs x₀ rfl
      ht htθ hθ hdiff ha1
  refine ⟨M, hMtop, min ρmax ρrem, lt_min hρmax hρrem, ?_⟩
  intro ρ hρ hρsmall
  have hρmax' : ρ < ρmax := (lt_min_iff.mp hρsmall).1
  have hρrem' : ρ < ρrem := (lt_min_iff.mp hρsmall).2
  obtain ⟨n₀, hMρ⟩ := hM ρ hρ hρrem'
  refine ⟨n₀, fun n hn => ?_⟩
  have hfixed := HasGGrowth.affineCutoff_scaled_annulus_lintegral_bound
    (N := N) (m := m) (ε := ε) hG hgrowth h0 hLm hΩopen hΩbounded (uₙ n) a₀ A x₀ hs
    hρ (hball ρ hρ hρmax') ht htθ hθ M (hMρ n hn) (hdom ρ hρ hρmax' n)
  exact hfixed

omit [NeZero N] in
/-- Uniform-in-`ε` version of `affineCutoff_integrated_annulus_bound`, with an externally
supplied finite remainder bound `M`. Its radius and index thresholds come from that bound and are
chosen before `ε`; only the integrand estimate is specialized to each oscillation scale. -/
theorem ConvexENN.affineCutoff_integrated_annulus_bound_uniform_eps
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hgrowth : HasGGrowth G α β L) (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hLm : Measurable (uncurry L))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρmax : ℝ} (hρmax : 0 < ρmax)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Metric.closedBall x₀ (ρ / 2) ⊆ Ω)
    (hdom : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → ∀ n,
      ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
        (uₙ n).grad y ∈ dom G)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    {M : ℝ≥0∞}
    (hM : ∃ ρrem : ℝ, 0 < ρrem ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρrem → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          G ((t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              ((uₙ n).toFun y - affineMap a₀ A x₀ y))) ≤ M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ ρmax ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ε : ℝ,
        AEMeasurable (fun y => L (ε⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs ρ x₀ y))
          (volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)) ∧
        ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
          L (ε⁻¹ • y)
            (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs ρ x₀ y) ≤
          (β : ℝ≥0∞) *
            (((1 + M + G (θ • A)) *
                volume (cube ρ x₀ \ cube (s * ρ) x₀)) +
              ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, G (θ • (uₙ n).grad y)) := by
  obtain ⟨ρrem, hρrem, hM⟩ := hM
  refine ⟨min ρmax ρrem, lt_min hρmax hρrem, min_le_left _ _, ?_⟩
  intro ρ hρ hρsmall
  have hρmax' : ρ < ρmax := (lt_min_iff.mp hρsmall).1
  have hρrem' : ρ < ρrem := (lt_min_iff.mp hρsmall).2
  obtain ⟨n₀, hMρ⟩ := hM ρ hρ hρrem'
  refine ⟨n₀, ?_⟩
  intro n hn ε
  have hfixed := HasGGrowth.affineCutoff_scaled_annulus_lintegral_bound
    (N := N) (m := m) (ε := ε) hG hgrowth h0 hLm hΩopen hΩbounded (uₙ n) a₀ A x₀ hs
    hρ (hball ρ hρ hρmax') ht htθ hθ M (hMρ n hn) (hdom ρ hρ hρmax' n)
  exact hfixed

/-! ### Splitting the energy between the inner cube and the boundary layer -/

omit [NeZero N] in
/-- Exact additivity of a nonnegative integral over an outer cube, its centered inner cube, and
the set-theoretic remainder. The inner cube is open, so its boundary is part of the remainder;
no null-boundary assumption is involved. -/
theorem lintegral_cube_eq_inner_add_annulus {ρ s : ℝ} (hρ : 0 < ρ)
    (hs : s ∈ Ioo (0 : ℝ) 1) (x₀ : Sp N) (F : Sp N → ℝ≥0∞) :
    ∫⁻ y in cube ρ x₀, F y =
      (∫⁻ y in cube (s * ρ) x₀, F y) +
        ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, F y := by
  have hsρ : 0 ≤ s * ρ := mul_nonneg hs.1.le hρ.le
  have hinner : cube (s * ρ) x₀ ⊆ cube ρ x₀ := by
    intro y hy
    simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
    intro i
    obtain ⟨hlo, hhi⟩ := hy i
    constructor <;> nlinarith [hs.2]
  have hset : cube ρ x₀ = cube (s * ρ) x₀ ∪
      (cube ρ x₀ \ cube (s * ρ) x₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hy
      by_cases hi : y ∈ cube (s * ρ) x₀
      · exact Or.inl hi
      · exact Or.inr ⟨hy, hi⟩
    · rintro (hy | ⟨hy, _⟩)
      · exact hinner hy
      · exact hy
  have hdisj : Disjoint (cube (s * ρ) x₀)
      (cube ρ x₀ \ cube (s * ρ) x₀) := disjoint_sdiff_right
  have hmeasure : volume.restrict (cube ρ x₀) =
      volume.restrict (cube (s * ρ) x₀) +
        volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀) :=
    (congrArg (fun S : Set (Sp N) => volume.restrict S) hset).trans
      (Measure.restrict_union hdisj
        ((isOpen_cube ρ x₀).measurableSet.diff (isOpen_cube (s * ρ) x₀).measurableSet))
  calc
    ∫⁻ y in cube ρ x₀, F y = ∫⁻ y, F y ∂volume.restrict (cube ρ x₀) := rfl
    _ = ∫⁻ y, F y ∂(volume.restrict (cube (s * ρ) x₀) +
        volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)) := by rw [hmeasure]
    _ = (∫⁻ y in cube (s * ρ) x₀, F y) +
        ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, F y :=
      MeasureTheory.lintegral_add_measure F _ _

omit [NeZero N] in
/-- Split the cell lower bound into the ru-usc controlled interior and the cut-off annulus. This
fixed-scale inequality is the input for the successive `n` and radius limits. -/
theorem affineCutoff_cell_le_inner_ruusc_and_annulus
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hball : Metric.closedBall x₀ (ρ / 2) ⊆ Ω) (t : ℝ)
    {η c : ℝ≥0}
    (hru : ∀ z ξ, L z (t • ξ) ≤
      (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c) :
    Ytp (ENNReal.ofReal p) L (cube (ρ / ε) (ε⁻¹ • x₀)) (t • A) /
        volume (cube (ρ / ε) (ε⁻¹ • x₀)) ≤
      (((1 + (η : ℝ≥0∞)) *
          (∫⁻ y in cube ρ x₀, L (ε⁻¹ • y) (u.grad y))) +
        (η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀) +
        ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
          L (ε⁻¹ • y)
            (t • affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y)) /
        volume (cube ρ x₀) := by
  let Fcut : Sp N → ℝ≥0∞ := fun y =>
    L (ε⁻¹ • y) (t • affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y)
  let Fraw : Sp N → ℝ≥0∞ := fun y => L (ε⁻¹ • y) (u.grad y)
  have hcell := affineCutoff_rescaled_cell_lower (N := N) (m := m) (L := L)
    hΩopen hΩbounded u a A x₀ hs hρ hε hball t
  have hinner :
      (∫⁻ y in cube (s * ρ) x₀, Fcut y) ≤
        (1 + (η : ℝ≥0∞)) * (∫⁻ y in cube ρ x₀, Fraw y) +
          (η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀) := by
    have hpoint : ∀ᵐ y ∂(volume.restrict (cube (s * ρ) x₀)), L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y) ≤
          (1 + (η : ℝ≥0∞)) * L (ε⁻¹ • y) (u.grad y) +
            (η : ℝ≥0∞) * c := by
      filter_upwards [ae_restrict_mem
        (isOpen_cube (s * ρ) x₀).measurableSet] with y hy
      rw [affineCutoffGrad_eq_inner (N := N) (m := m)
        u a A x₀ hs hρ x₀ y hy]
      exact hru (ε⁻¹ • y) (u.grad y)
    have hmono :
        (∫⁻ y in cube (s * ρ) x₀, Fcut y) ≤
          ∫⁻ y in cube (s * ρ) x₀,
            ((1 + (η : ℝ≥0∞)) * Fraw y + (η : ℝ≥0∞) * c) := by
      exact lintegral_mono_ae hpoint
    have hrewrite :
        (∫⁻ y in cube (s * ρ) x₀,
          (1 + (η : ℝ≥0∞)) * Fraw y + (η : ℝ≥0∞) * c) =
          (1 + (η : ℝ≥0∞)) *
            (∫⁻ y in cube (s * ρ) x₀, Fraw y) +
            (η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀) := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_const_mul' _ _ (by simp : (1 + (η : ℝ≥0∞)) ≠ ⊤),
        setLIntegral_const]
    have hrawmono :
        (∫⁻ y in cube (s * ρ) x₀, Fraw y) ≤
          ∫⁻ y in cube ρ x₀, Fraw y :=
      lintegral_mono_set (by
        intro y hy
        simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
        intro i
        obtain ⟨hlo, hhi⟩ := hy i
        constructor <;> nlinarith [hs.2])
    calc
      (∫⁻ y in cube (s * ρ) x₀, Fcut y) ≤
          ∫⁻ y in cube (s * ρ) x₀,
            ((1 + (η : ℝ≥0∞)) * Fraw y + (η : ℝ≥0∞) * c) := hmono
      _ = (1 + (η : ℝ≥0∞)) *
            (∫⁻ y in cube (s * ρ) x₀, Fraw y) +
            (η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀) := hrewrite
      _ ≤ (1 + (η : ℝ≥0∞)) *
            (∫⁻ y in cube ρ x₀, Fraw y) +
            (η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀) := by
        gcongr
  have hsplit := lintegral_cube_eq_inner_add_annulus (N := N) hρ hs x₀ Fcut
  have htotal :
      (∫⁻ y in cube ρ x₀, Fcut y) ≤
        (1 + (η : ℝ≥0∞)) * (∫⁻ y in cube ρ x₀, Fraw y) +
          (η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀) +
          ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, Fcut y := by
    rw [hsplit]
    have h' := add_le_add_left hinner
      (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, Fcut y)
    simpa [add_assoc] using h'
  have hdiv := ENNReal.div_le_div_right htotal (volume (cube ρ x₀))
  exact hcell.trans (by simpa [Fcut, Fraw, add_assoc] using hdiv)

omit [NeZero N] in
/-- Convert the fixed-scale cell comparison to real-valued terms without assuming any infinite
quantity is finite implicitly. This is the conversion needed before applying the real limsup
lemmas to the cell, inner-cube, and annulus energies. -/
theorem toReal_div_le_sum_three_of_ENNReal
    {X a b c v w : ℝ≥0∞} (hv : 0 < v) (ha : a < ⊤) (hb : b < ⊤) (hc : c < ⊤)
    (hX : X / w ≤ ((a + b) + c) / v) :
    (X / w).toReal ≤ a.toReal / v.toReal + b.toReal / v.toReal + c.toReal / v.toReal := by
  have hnum : (a + b) + c < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ha, hb⟩, hc⟩
  have hden : v ≠ 0 := hv.ne'
  have hquot : ((a + b) + c) / v < ⊤ := ENNReal.div_lt_top hnum.ne hden
  have hmono := ENNReal.toReal_mono hquot.ne hX
  have hrewrite : (((a + b) + c) / v).toReal =
      a.toReal / v.toReal + b.toReal / v.toReal + c.toReal / v.toReal := by
    rw [ENNReal.toReal_div,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ha.ne, hb.ne⟩) hc.ne,
      add_div, ENNReal.toReal_add ha.ne hb.ne, add_div]
  rw [ENNReal.toReal_div, hrewrite] at hmono
  rw [ENNReal.toReal_div]
  exact hmono

omit [NeZero N] in
/-- Real form of the fixed-radius cell/cube/annulus comparison. Finiteness of the uncut and
cut-off integrals is explicit; cube volumes are finite and the physical denominator is positive.
The rescaling identity in `affineCutoff_rescaled_cell_lower` has already matched the dilated cell
volume with the physical-cube normalization. -/
theorem affineCutoff_cell_le_inner_ruusc_and_annulus_toReal
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    {L : Sp N → Mat m N → ℝ≥0∞}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (u : W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hball : Metric.closedBall x₀ (ρ / 2) ⊆ Ω) (t : ℝ)
    {η c : ℝ≥0}
    (hru : ∀ z ξ, L z (t • ξ) ≤
      (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c)
    (houter : (∫⁻ y in cube ρ x₀, L (ε⁻¹ • y) (u.grad y)) < ⊤)
    (hcut : (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
      L (ε⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y)) < ⊤) :
    (Ytp (ENNReal.ofReal p) L (cube (ρ / ε) (ε⁻¹ • x₀)) (t • A) /
      volume (cube (ρ / ε) (ε⁻¹ • x₀))).toReal ≤
      (((1 + (η : ℝ≥0∞)) *
        (∫⁻ y in cube ρ x₀, L (ε⁻¹ • y) (u.grad y))).toReal /
        (volume (cube ρ x₀)).toReal) +
      (((η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀)).toReal /
        (volume (cube ρ x₀)).toReal) +
      ((∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
        L (ε⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) u a A x₀ hs ρ x₀ y)).toReal /
        (volume (cube ρ x₀)).toReal) := by
  have hvolpos : 0 < volume (cube ρ x₀) := volume_cube_pos hρ x₀
  have hinnerVolTop : volume (cube (s * ρ) x₀) < ⊤ :=
    (volume_cube_ne_top (s * ρ) x₀).lt_top
  have hA : ((1 + (η : ℝ≥0∞)) *
      ∫⁻ y in cube ρ x₀, L (ε⁻¹ • y) (u.grad y)) < ⊤ :=
    ENNReal.mul_lt_top (by simp) houter
  have hB : ((η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀)) < ⊤ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) hinnerVolTop
  have hcomp := affineCutoff_cell_le_inner_ruusc_and_annulus
    (N := N) (m := m) hΩopen hΩbounded u a A x₀ hs hρ hε hball t hru
  exact toReal_div_le_sum_three_of_ENNReal hvolpos hA hB hcut hcomp

/-- A real limsup estimate for an eventual affine upper bound. The boundedness hypotheses make the
limsup operations real-valued; nonnegativity of the left sequence supplies its lower bound. -/
theorem limsup_le_affine_of_eventually_le {F E : ℕ → ℝ} {a b d : ℝ}
    (hb : 0 ≤ b) (hFbounded : IsBoundedUnder (· ≤ ·) atTop F)
    (hFlimsup : limsup F atTop ≤ d)
    (hEbounded : IsBoundedUnder (· ≤ ·) atTop E)
    (hEnonneg : ∀ n, 0 ≤ E n)
    (hEupper : ∀ᶠ n in atTop, E n ≤ a + b * F n) :
    limsup E atTop ≤ a + b * d := by
  have hEcobounded : IsCoboundedUnder (· ≤ ·) atTop E :=
    Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Filter.Eventually.of_forall hEnonneg)
  apply (Filter.limsup_le_iff hEcobounded hEbounded).2
  intro y hy
  let δ : ℝ := (y - (a + b * d)) / (2 * (b + 1))
  have hδ : 0 < δ := by
    apply div_pos
    · linarith
    · nlinarith
  have hFevent : ∀ᶠ n in atTop, F n < d + δ :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hFlimsup (by linarith))
  filter_upwards [hFevent, hEupper] with n hFn hEn
  calc
    E n ≤ a + b * F n := hEn
    _ ≤ a + b * (d + δ) := by gcongr
    _ < y := by
      have hnum : 0 < y - (a + b * d) := by linarith
      have hden : 0 < 2 * (b + 1) := by nlinarith
      have hratio : b / (2 * (b + 1)) < 1 :=
        (div_lt_one hden).2 (by nlinarith)
      have hprod := mul_lt_mul_of_pos_right hratio hnum
      have hprod' : b * δ < y - (a + b * d) := by
        calc
          b * δ = (b / (2 * (b + 1))) * (y - (a + b * d)) := by
            simp only [δ]
            ring
          _ < y - (a + b * d) := by simpa using hprod
      nlinarith [hprod']

/-- Pass successively to a sequence limit and a limsup bound in an inequality with three
nonnegative-energy contributions. This is the real-valued limit step used first in the sequence
index and then in the admissible cube radii. -/
theorem le_of_tendsto_add_limsup {X A C : ℕ → ℝ} {x a b d : ℝ}
    (hX : Tendsto X atTop (𝓝 x)) (hA : Tendsto A atTop (𝓝 a))
    (hCbounded : IsBoundedUnder (· ≤ ·) atTop C)
    (hC : limsup C atTop ≤ d)
    (hineq : ∀ᶠ n in atTop, X n ≤ A n + b + C n) :
    x ≤ a + b + d := by
  by_contra hnot
  have hgap : 0 < x - (a + b + d) := by linarith
  let δ : ℝ := (x - (a + b + d)) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hXevent : ∀ᶠ n in atTop, x - δ < X n :=
    hX.eventually (Ioi_mem_nhds (by linarith))
  have hAevent : ∀ᶠ n in atTop, A n < a + δ :=
    hA.eventually (Iio_mem_nhds (by linarith))
  have hCevent : ∀ᶠ n in atTop, C n < d + δ :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hC (by linarith)) hCbounded
  obtain ⟨n, ⟨⟨hx, ha⟩, hc⟩, hi⟩ :=
    ((hXevent.and hAevent).and hCevent).and hineq |>.exists
  have := hi
  dsimp [δ] at hgap hx ha hc
  linarith

omit [NeZero N] in
/-- Concrete fixed-radius cell/cube/annulus passage. It combines the rescaled cell lower bound
with the real comparison and a supplied limsup bound for the cut annulus. Eventual finiteness of
the cut energy suffices; no value at the finitely many exceptional indices is converted from
`ℝ≥0∞`. -/
theorem affineCutoff_cell_ratio_le_of_limsup_annulus
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    {L : Sp N → Mat m N → ℝ≥0∞} {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    (hG : ConvexENN G) (hgrowth : HasGGrowth G α β L)
    (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a : Tgt m) (A : Mat m N)
    (x₀ : Sp N) (hA : A ∈ closure (dom G)) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℕ → ℝ) (φ : ℕ → ℕ) (hε : ∀ n, 0 < ε (φ n))
    (hball : Metric.closedBall x₀ (ρ / 2) ⊆ Ω)
    {η c : ℝ≥0}
    (hru : ∀ z ξ, L z (t • ξ) ≤
      (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c)
    (houter : Tendsto (fun n => ∫⁻ y in cube ρ x₀,
      L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)) atTop (𝓝 (μ (cube ρ x₀))))
    (houterFinite : ∀ n, (∫⁻ y in cube ρ x₀,
      L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)) < ⊤)
    (hcutFinite : ∀ᶠ n in atTop,
      (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
        L ((ε (φ n))⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a A x₀ hs ρ x₀ y)) < ⊤)
    (hcell : Tendsto (fun n =>
      Ytp (ENNReal.ofReal p) L (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀)) (t • A) /
        volume (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀))) atTop
      (𝓝 (Hp (ENNReal.ofReal p) L (t • A))))
    (hcutBounded : IsBoundedUnder (· ≤ ·) atTop (fun n =>
      (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
        L ((ε (φ n))⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a A x₀ hs ρ x₀ y)).toReal /
        (volume (cube ρ x₀)).toReal))
    {d : ℝ} (hcutLimsup : limsup (fun n =>
      (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
        L ((ε (φ n))⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a A x₀ hs ρ x₀ y)).toReal /
        (volume (cube ρ x₀)).toReal) atTop ≤ d) :
    (Hp (ENNReal.ofReal p) L (t • A)).toReal ≤
      ((1 + (η : ℝ≥0∞)).toReal * (μ (cube ρ x₀)).toReal /
          (volume (cube ρ x₀)).toReal) +
        (((η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀)).toReal /
          (volume (cube ρ x₀)).toReal) + d := by
  let V : ℝ := (volume (cube ρ x₀)).toReal
  let X : ℕ → ℝ := fun n =>
    (Ytp (ENNReal.ofReal p) L (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀)) (t • A) /
      volume (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀))).toReal
  let Aseq : ℕ → ℝ := fun n =>
    (((1 + (η : ℝ≥0∞)) *
      ∫⁻ y in cube ρ x₀, L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)).toReal) / V
  let Cseq : ℕ → ℝ := fun n =>
    (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
      L ((ε (φ n))⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a A x₀ hs ρ x₀ y)).toReal / V
  let b : ℝ :=
    (((η : ℝ≥0∞) * c * volume (cube (s * ρ) x₀)).toReal) / V
  have hV : 0 < V := by
    dsimp [V]
    rw [volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le]
    exact pow_pos hρ _
  have hμtop : μ (cube ρ x₀) < ⊤ := measure_lt_top μ _
  have hGt : G (t • A) < ⊤ := by
    have hmem := hG.smul_mem_interior_dom h0 hA (le_of_lt ht) ht1
    have hdom : t • A ∈ dom G := interior_subset hmem
    simpa [dom] using hdom
  have hHpFinite : Hp (ENNReal.ofReal p) L (t • A) < ⊤ := by
    exact lt_of_le_of_lt (hgrowth.Hp_le (ENNReal.ofReal p) (t • A))
      (ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hGt⟩))
  have hcellFinite : ∀ n,
      Ytp (ENNReal.ofReal p) L (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀)) (t • A) /
        volume (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀)) < ⊤ := by
    intro n
    let U := cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀)
    let C : ℝ≥0∞ := (β : ℝ≥0∞) * (1 + G (t • A))
    have hC : C < ⊤ := by
      dsimp [C]
      exact ENNReal.mul_lt_top (by simp)
        (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hGt⟩)
    have hY : Ytp (ENNReal.ofReal p) L U (t • A) ≤ C * volume U := by
      refine (Ytp_le_lintegral (ENNReal.ofReal p) L U (t • A)).trans ?_
      calc
        ∫⁻ y in U, L y (t • A) ≤ ∫⁻ y in U, C :=
          lintegral_mono fun y => (hgrowth y (t • A)).2
        _ = C * volume U := by rw [setLIntegral_const]
    have hUtop : volume U < ⊤ := volume_cube_ne_top _ _ |>.lt_top
    have hYtop : Ytp (ENNReal.ofReal p) L U (t • A) < ⊤ :=
      lt_of_le_of_lt hY (ENNReal.mul_lt_top hC hUtop)
    have hYtop' : Ytp (ENNReal.ofReal p) L
        (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀)) (t • A) < ⊤ := by
      simpa [U] using hYtop
    have hUpos : 0 < volume (cube (ρ / ε (φ n)) ((ε (φ n))⁻¹ • x₀)) :=
      volume_cube_pos (div_pos hρ (hε n)) _
    exact ENNReal.div_lt_top hYtop'.ne (Ne.symm hUpos.ne)
  have hcellReal : Tendsto X atTop
      (𝓝 (Hp (ENNReal.ofReal p) L (t • A)).toReal) := by
    dsimp [X]
    exact (ENNReal.tendsto_toReal_iff (fun n => (hcellFinite n).ne)
      hHpFinite.ne).2 hcell
  have houterReal : Tendsto (fun n =>
      (∫⁻ y in cube ρ x₀, L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)).toReal)
      atTop (𝓝 (μ (cube ρ x₀)).toReal) :=
    (ENNReal.tendsto_toReal_iff (fun n => (houterFinite n).ne) hμtop.ne).2 houter
  have hAseq : Tendsto Aseq atTop
      (𝓝 (((1 + (η : ℝ≥0∞)).toReal * (μ (cube ρ x₀)).toReal) / V)) := by
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 + (η : ℝ≥0∞)).toReal)
        atTop (𝓝 ((1 + (η : ℝ≥0∞)).toReal))).mul houterReal
    have heq : (fun n => (((1 + (η : ℝ≥0∞)) *
        ∫⁻ y in cube ρ x₀, L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)).toReal) / V) =
        fun n => ((1 + (η : ℝ≥0∞)).toReal *
          (∫⁻ y in cube ρ x₀, L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)).toReal) / V := by
      funext n
      rw [ENNReal.toReal_mul]
    dsimp [Aseq]
    rw [heq]
    exact hmul.div_const V
  have hineq : ∀ᶠ n in atTop, X n ≤ Aseq n + b + Cseq n := by
    filter_upwards [hcutFinite] with n hcutn
    have hcomp := affineCutoff_cell_le_inner_ruusc_and_annulus_toReal
      (N := N) (m := m) hΩopen hΩbounded (uₙ (φ n)) a A x₀ hs hρ (hε n) hball t hru
      (houterFinite n) hcutn
    dsimp [X, Aseq, Cseq, b, V]
    exact hcomp
  exact le_of_tendsto_add_limsup hcellReal hAseq hcutBounded hcutLimsup hineq

/-- A countable family of almost-everywhere estimates holds simultaneously off one null set. -/
theorem ae_nat_forall {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P : ℕ → α → Prop} (hP : ∀ j, ∀ᵐ x ∂μ, P j x) :
    ∀ᵐ x ∂μ, ∀ j, P j x := by
  rw [ae_all_iff]
  exact hP

/-- The right-hand side left after sending `s` to one converges to the density when `η → 0`.
The RU-usc constant is a fixed input, independent of the sequence of tolerances. -/
theorem tendsto_ruusc_density_error {f c : ℝ≥0∞}
    {η : ℕ → ℝ≥0} (hη : Tendsto (fun j => (η j).toReal) atTop (𝓝 0)) :
    Tendsto (fun j => (1 + (η j).toReal) * f.toReal +
      (η j).toReal * c.toReal) atTop (𝓝 f.toReal) := by
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hfirst : Tendsto (fun j => (1 + (η j).toReal) * f.toReal) atTop
      (𝓝 (1 * f.toReal)) := by
    simpa [one_mul] using (hconst.add hη).mul_const f.toReal
  have hsecond : Tendsto (fun j => (η j).toReal * c.toReal) atTop
      (𝓝 (0 * c.toReal)) := hη.mul_const c.toReal
  simpa using hfirst.add hsecond

omit [NeZero N] in
/-- Eliminate the cut-off ratio `s` from the uniform-in-`s` cell bound. The coefficients of
`1-s^N` are fixed real numbers, so the limit at `s → 1⁻` leaves only the density and the fixed
ru-usc error `η c`. -/
theorem hp_toReal_le_ruusc_bound_of_uniform_s
    {q : ℝ≥0∞} {L : Sp N → Mat m N → ℝ≥0∞} {ξ : Mat m N}
    {f c : ℝ≥0∞} {η : ℝ≥0} {D B : ℝ}
    (hbound : ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
      (Hp q L ξ).toReal ≤
        (1 + (η : ℝ≥0∞)).toReal * f.toReal +
          ((η : ℝ≥0∞) * c).toReal * s ^ N +
          D * (1 - s ^ N) + B * ((1 - s ^ N) * f.toReal)) :
    (Hp q L ξ).toReal ≤
      (1 + (η : ℝ≥0∞)).toReal * f.toReal +
        ((η : ℝ≥0∞) * c).toReal := by
  let F : ℝ → ℝ := fun s =>
    (1 + (η : ℝ≥0∞)).toReal * f.toReal +
      ((η : ℝ≥0∞) * c).toReal * s ^ N +
      D * (1 - s ^ N) + B * ((1 - s ^ N) * f.toReal)
  have hid : Tendsto id (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun s : ℝ => s ^ N) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using hid.pow N
  have hrem : Tendsto (fun s : ℝ => 1 - s ^ N) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (show Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] 1) (𝓝 1) from
      tendsto_const_nhds).sub hpow
  have hF : Tendsto F (𝓝[<] (1 : ℝ))
      (𝓝 ((1 + (η : ℝ≥0∞)).toReal * f.toReal +
        ((η : ℝ≥0∞) * c).toReal)) := by
    dsimp [F]
    have hηs := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => ((η : ℝ≥0∞) * c).toReal) (𝓝[<] 1)
      (𝓝 ((η : ℝ≥0∞) * c).toReal)).mul hpow
    have hDrem := (tendsto_const_nhds : Tendsto (fun _ : ℝ => D)
      (𝓝[<] 1) (𝓝 D)).mul hrem
    have hBrem := (tendsto_const_nhds : Tendsto (fun _ : ℝ => B)
      (𝓝[<] 1) (𝓝 B)).mul (hrem.mul_const f.toReal)
    convert (((tendsto_const_nhds.add hηs).add hDrem).add hBrem) using 1; ring_nf
  have hlt : ∀ᶠ s in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hpos0 : ∀ᶠ s in 𝓝 (1 : ℝ), 0 < s := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with s hs
    exact hs
  have hpos : ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hpos0
  have hEventually : (fun _ : ℝ => (Hp q L ξ).toReal) ≤ᶠ[𝓝[<] (1 : ℝ)] F := by
    filter_upwards [hlt, hpos] with s hbelow habove
    have hs : s ∈ Ioo (0 : ℝ) 1 := ⟨habove, hbelow⟩
    simpa [F] using hbound s hs
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hF hEventually

omit [NeZero N] in
/-- Radial conclusion from upper bounds along factors tending to one. This isolates the last
limit step of the pointwise argument: the sequence of cell values converges to the radial
envelope by `lsc_of_HW`, while its real values are bounded by a sequence converging to the finite
density. -/
theorem radial_Hp_le_of_tendsto_toReal_bound
    {q : ℝ≥0∞} {L : Sp N → Mat m N → ℝ≥0∞} {ξ : Mat m N}
    (hL : RUUSC L) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝[<] (1 : ℝ)))
    {f : ℝ≥0∞} (hf : f < ⊤) {U : ℕ → ℝ}
    (hU : Tendsto U atTop (𝓝 f.toReal))
    (hfinite : ∀ j, Hp q L (t j • ξ) < ⊤)
    (hbound : ∀ j, (Hp q L (t j • ξ)).toReal ≤ U j) :
    radial (Hp q L) ξ ≤ f := by
  have hradial := (lsc_of_HW (q := q) hL).2.2 ξ
  have hseq : Tendsto (fun j => Hp q L (t j • ξ)) atTop
      (𝓝 (radial (Hp q L) ξ)) := hradial.comp ht
  by_contra hnot
  have hlt : f < radial (Hp q L) ξ := lt_of_not_ge hnot
  obtain ⟨z, hfz, hzr⟩ := exists_between hlt
  have hzTop : z < ⊤ := lt_of_lt_of_le hzr le_top
  have hfreal : f.toReal < z.toReal :=
    (ENNReal.toReal_lt_toReal hf.ne hzTop.ne).mpr hfz
  have hseqEvent : ∀ᶠ j in atTop, z < Hp q L (t j • ξ) :=
    hseq.eventually (Ioi_mem_nhds hzr)
  have hUevent : ∀ᶠ j in atTop, U j < z.toReal :=
    hU.eventually (Iio_mem_nhds hfreal)
  obtain ⟨j, hj, hUj⟩ := hseqEvent.and hUevent |>.exists
  have hrealLower := ENNReal.toReal_mono (hfinite j).ne (le_of_lt hj)
  linarith [hbound j]

omit [NeZero N] in
/-- Complete the `η → 0` and radial limits once the fixed-parameter cell/cut-off argument has
given its bounds. All tolerances share the same constant `c`; the estimate at factor `t j` is an
explicit input, so this lemma does not infer it from an estimate at the annular factor `θ`. -/
theorem radial_Hp_le_of_ruusc_sequence_bounds
    {q : ℝ≥0∞} {L : Sp N → Mat m N → ℝ≥0∞} {ξ : Mat m N}
    (hL : RUUSC L) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝[<] (1 : ℝ)))
    {η : ℕ → ℝ≥0} (hη : Tendsto (fun j => (η j).toReal) atTop (𝓝 0))
    {f c : ℝ≥0∞} (hf : f < ⊤)
    (hfinite : ∀ j, Hp q L (t j • ξ) < ⊤)
    (hbound : ∀ j, (Hp q L (t j • ξ)).toReal ≤
      (1 + (η j).toReal) * f.toReal + (η j).toReal * c.toReal) :
    radial (Hp q L) ξ ≤ f := by
  have hU := tendsto_ruusc_density_error (f := f) (c := c) hη
  exact radial_Hp_le_of_tendsto_toReal_bound
    (N := N) (m := m) (q := q) (L := L) (ξ := ξ) hL ht hf hU hfinite hbound

/-- Convert an eventually affine `ℝ≥0∞` estimate to the real limsup estimate used after
portmanteau. Every extended quantity is finite where `toReal` is used; the proof never subtracts
extended reals. -/
theorem limsup_toReal_le_affine_of_ENNReal
    {E F : ℕ → ℝ≥0∞} {A B : ℝ≥0∞} {d : ℝ}
    (hA : A < ⊤) (hB : B < ⊤) (hFfin : ∀ n, F n < ⊤)
    (hFbounded : IsBoundedUnder (· ≤ ·) atTop (fun n => (F n).toReal))
    (hFlimsup : limsup (fun n => (F n).toReal) atTop ≤ d)
    (hEbounded : IsBoundedUnder (· ≤ ·) atTop (fun n => (E n).toReal))
    (hEupper : ∀ᶠ n in atTop, E n ≤ A + B * F n) :
    limsup (fun n => (E n).toReal) atTop ≤ A.toReal + B.toReal * d := by
  have hrealupper : ∀ᶠ n in atTop,
      (E n).toReal ≤ A.toReal + B.toReal * (F n).toReal := by
    filter_upwards [hEupper] with n hn
    have hRHSfinite : A + B * F n < ⊤ := by
      apply ENNReal.add_lt_top.2
      exact ⟨hA, ENNReal.mul_lt_top hB (hFfin n)⟩
    have hEn : E n < ⊤ := lt_of_le_of_lt hn hRHSfinite
    have hmono := ENNReal.toReal_mono hRHSfinite.ne hn
    have hrewrite : (A + B * F n).toReal = A.toReal + B.toReal * (F n).toReal := by
      rw [ENNReal.toReal_add hA.ne (ENNReal.mul_ne_top hB.ne (hFfin n).ne),
        ENNReal.toReal_mul]
    rw [← hrewrite]
    exact hmono
  exact limsup_le_affine_of_eventually_le (F := fun n => (F n).toReal)
    (E := fun n => (E n).toReal) (a := A.toReal) (b := B.toReal) (d := d)
    ENNReal.toReal_nonneg hFbounded hFlimsup hEbounded
    (fun n => ENNReal.toReal_nonneg) hrealupper

/-- Real-valued numerical form of the boundary-layer subtraction argument. A lower bound on the
liminf of the inner energy and convergence of the total energy control the limsup of the
nonnegative remainder. The real-valued formulation makes the subtraction explicit and avoids
undefined `∞ - ∞` operations; the conversion from the extended integrals is handled separately. -/
theorem limsup_remainder_le_of_sum_tendsto {A B C : ℕ → ℝ} {a b : ℝ}
    (hA : Tendsto A atTop (𝓝 a)) (hb : b ≤ liminf B atTop)
    (hadd : ∀ n, A n = B n + C n) (hB : ∀ n, 0 ≤ B n)
    (hC : ∀ n, 0 ≤ C n) :
    limsup C atTop ≤ a - b := by
  have hlimsup : IsCoboundedUnder (· ≤ ·) atTop C :=
    Filter.isCoboundedUnder_le_of_eventually_le atTop (by
      filter_upwards with n
      exact hC n)
  have hCupper : ∀ᶠ n in atTop, C n ≤ a + 1 := by
    filter_upwards [hA.eventually (Iio_mem_nhds (show a < a + 1 by linarith))]
      with n hn
    have hCn : C n ≤ A n := by rw [hadd]; linarith [hB n]
    linarith
  have hbounded : IsBoundedUnder (· ≤ ·) atTop C :=
    Filter.isBoundedUnder_of_eventually_le hCupper
  apply (Filter.limsup_le_iff hlimsup hbounded).2
  intro y hy
  let δ := (y - (a - b)) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hAevent : ∀ᶠ n in atTop, A n < a + δ :=
    hA.eventually (Iio_mem_nhds (by linarith))
  have hBevent : ∀ᶠ n in atTop, b - δ < B n := by
    by_contra hnot
    have hfrequent : ∃ᶠ n in atTop, B n ≤ b - δ :=
      (Filter.not_eventually.1 hnot).mono fun n hn => le_of_not_gt hn
    have hliminf := Filter.liminf_le_of_frequently_le hfrequent
      (Filter.isBoundedUnder_of_eventually_ge (show ∀ᶠ n in atTop, 0 ≤ B n from
        Filter.Eventually.of_forall hB))
    linarith
  filter_upwards [hAevent, hBevent] with n hAn hBn
  have hCn : C n = A n - B n := by rw [hadd n]; ring
  rw [hCn]
  dsimp [δ] at *
  linarith

/-- Extended-real version of the preceding subtraction lemma when all terms are finite. The
portmanteau lower bound is converted to a real `liminf` using its eventual characterization; this
avoids subtracting extended reals and does not require the inner cube boundary to be null. -/
theorem limsup_toReal_remainder_le {A B C : ℕ → ℝ≥0∞} {a b : ℝ≥0∞}
    (ha : a < ⊤) (hb : b < ⊤)
    (hA : Tendsto A atTop (𝓝 a)) (hB : b ≤ liminf B atTop)
    (hadd : ∀ n, A n = B n + C n)
    (hAfin : ∀ n, A n < ⊤) (hBfin : ∀ n, B n < ⊤)
    (hCfin : ∀ n, C n < ⊤) :
    limsup (fun n => (C n).toReal) atTop ≤ a.toReal - b.toReal := by
  have hAreal : Tendsto (fun n => (A n).toReal) atTop (𝓝 a.toReal) :=
    (ENNReal.tendsto_toReal_iff (fun n => (hAfin n).ne) ha.ne).2 hA
  have hBnonneg : ∀ n, 0 ≤ (B n).toReal := fun n => ENNReal.toReal_nonneg
  have hCnonneg : ∀ n, 0 ≤ (C n).toReal := fun n => ENNReal.toReal_nonneg
  have hBupper : ∀ᶠ n in atTop, (B n).toReal ≤ a.toReal + 1 := by
    filter_upwards [hAreal.eventually (Iio_mem_nhds (show a.toReal < a.toReal + 1 by linarith))]
      with n hn
    have hBA : B n ≤ A n := by rw [hadd]; exact le_add_of_nonneg_right bot_le
    exact (ENNReal.toReal_mono (hAfin n).ne hBA).trans hn.le
  have hBbound : IsCoboundedUnder (· ≥ ·) atTop (fun n => (B n).toReal) :=
    Filter.isCoboundedUnder_ge_of_eventually_le atTop hBupper
  have hBreal : b.toReal ≤ liminf (fun n => (B n).toReal) atTop := by
    apply le_of_forall_lt
    intro c hc
    by_cases hcneg : c < 0
    · have h0 : (0 : ℝ) ≤ liminf (fun n => (B n).toReal) atTop :=
        Filter.le_liminf_of_le (hf := hBbound)
          (h := Filter.Eventually.of_forall hBnonneg)
      linarith
    · have hc0 : 0 ≤ c := le_of_not_gt hcneg
      let d : ℝ := (c + b.toReal) / 2
      have hcd : c < d := by dsimp [d]; linarith
      have hdb : d < b.toReal := by dsimp [d]; linarith
      have hd0 : 0 ≤ d := by dsimp [d]; linarith
      have hdb' : ENNReal.ofReal d < b := by
        apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hb.ne).mp
        simpa [ENNReal.toReal_ofReal hd0] using hdb
      have hdl : ENNReal.ofReal d < liminf B atTop := hdb'.trans_le hB
      rw [Filter.liminf_eq] at hdl
      obtain ⟨z, hz, hdz⟩ := lt_sSup_iff.mp hdl
      have hzEvent : ∀ᶠ n in atTop, z ≤ B n := hz
      have hdEvent : ∀ᶠ n in atTop, d < (B n).toReal := by
        filter_upwards [hzEvent] with n hn
        have hzfin : z ≠ ⊤ := ne_top_of_le_ne_top (hBfin n).ne hn
        have hdzReal : d < z.toReal := by
          have htmp := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hzfin).mpr hdz
          simpa [ENNReal.toReal_ofReal hd0] using htmp
        exact lt_of_lt_of_le hdzReal (ENNReal.toReal_mono (hBfin n).ne hn)
      have hdlower : d ≤ liminf (fun n => (B n).toReal) atTop :=
        Filter.le_liminf_of_le (hf := hBbound)
          (h := hdEvent.mono fun _ hn => le_of_lt hn)
      exact lt_of_lt_of_le hcd hdlower
  have haddReal : ∀ n, (A n).toReal = (B n).toReal + (C n).toReal := by
    intro n
    rw [hadd n, ENNReal.toReal_add (hBfin n).ne (hCfin n).ne]
  exact limsup_remainder_le_of_sum_tendsto hAreal hBreal haddReal hBnonneg hCnonneg

omit [NeZero N] in
/-- Portmanteau form of the annulus estimate. The total energy converges on the outer open cube,
the inner open-set portmanteau inequality supplies the lower bound, and exact additivity splits
off the annulus. Finiteness is explicit so the real subtraction is always defined. -/
theorem limsup_remainder_le_of_portmanteau {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    {A B C : ℕ → ℝ≥0∞} {U V : Set (Sp N)}
    (hA : Tendsto A atTop (𝓝 (μ U)))
    (hopen : μ V ≤ liminf B atTop)
    (hadd : ∀ n, A n = B n + C n)
    (hAfin : ∀ n, A n < ⊤)
    (hBmono : ∀ n, B n ≤ A n) (hCmono : ∀ n, C n ≤ A n) :
    limsup (fun n => (C n).toReal) atTop ≤ (μ U).toReal - (μ V).toReal := by
  have hU : μ U < ⊤ := measure_lt_top μ U
  have hV : μ V < ⊤ := measure_lt_top μ V
  have hBfin : ∀ n, B n < ⊤ := fun n => (ne_top_of_le_ne_top (hAfin n).ne (hBmono n)).lt_top
  have hCfin : ∀ n, C n < ⊤ := fun n => (ne_top_of_le_ne_top (hAfin n).ne (hCmono n)).lt_top
  exact limsup_toReal_remainder_le hU hV hA hopen hadd hAfin hBfin hCfin

omit [NeZero N] in
/-- Annulus-energy localization on centered cubes. The inner cube is open and only its open-set
portmanteau lower bound is used. The boundary of `cube (s * ρ) x₀` may have positive `μ`-measure:
it belongs to the annulus `cube ρ x₀ \ cube (s * ρ) x₀`, exactly as in the additive split. -/
theorem limsup_cube_annulus_energy_le {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    {F : ℕ → Sp N → ℝ≥0∞} {ρ s : ℝ} (hρ : 0 < ρ)
    (hs : s ∈ Ioo (0 : ℝ) 1) (x₀ : Sp N)
    (houter : Tendsto (fun n => ∫⁻ y in cube ρ x₀, F n y)
      atTop (𝓝 (μ (cube ρ x₀))))
    (hinner : μ (cube (s * ρ) x₀) ≤
      liminf (fun n => ∫⁻ y in cube (s * ρ) x₀, F n y) atTop)
    (hfinite : ∀ n, ∫⁻ y in cube ρ x₀, F n y < ⊤) :
    limsup (fun n => (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, F n y).toReal) atTop ≤
      (μ (cube ρ x₀)).toReal - (μ (cube (s * ρ) x₀)).toReal := by
  let A := fun n => ∫⁻ y in cube ρ x₀, F n y
  let B := fun n => ∫⁻ y in cube (s * ρ) x₀, F n y
  let C := fun n => ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, F n y
  have hsubset : cube (s * ρ) x₀ ⊆ cube ρ x₀ := by
    intro y hy
    simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
    intro i
    obtain ⟨hlo, hhi⟩ := hy i
    constructor <;> nlinarith [hs.2, hρ]
  have hCsubset : cube ρ x₀ \ cube (s * ρ) x₀ ⊆ cube ρ x₀ := sdiff_subset
  have hadd : ∀ n, A n = B n + C n := by
    intro n
    exact lintegral_cube_eq_inner_add_annulus (N := N) hρ hs x₀ (F n)
  have hBmono : ∀ n, B n ≤ A n := fun n => lintegral_mono_set hsubset
  have hCmono : ∀ n, C n ≤ A n := fun n => lintegral_mono_set hCsubset
  exact limsup_remainder_le_of_portmanteau (N := N) houter hinner hadd hfinite hBmono hCmono

omit [NeZero N] in
/-- At one outer radius, convert an eventual extended-real affine bound for the cut-off energy
into a real limsup bound normalized by the outer cube. The non-cut-off annulus limsup is supplied
by portmanteau; no nullity of the inner boundary is assumed. -/
theorem limsup_cutoff_annulus_ratio_le_of_affine_bound
    {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    {F : ℕ → Sp N → ℝ≥0∞} {Ecut : ℕ → ℝ≥0∞} {A B : ℝ≥0∞}
    {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ∈ Ioo (0 : ℝ) 1) (x₀ : Sp N)
    (houter : Tendsto (fun n => ∫⁻ y in cube ρ x₀, F n y)
      atTop (𝓝 (μ (cube ρ x₀))))
    (hinner : μ (cube (s * ρ) x₀) ≤
      liminf (fun n => ∫⁻ y in cube (s * ρ) x₀, F n y) atTop)
    (hfinite : ∀ n, ∫⁻ y in cube ρ x₀, F n y < ⊤)
    (hA : A < ⊤) (hB : B < ⊤)
    (hcut : ∀ᶠ n in atTop,
      Ecut n ≤ A + B * (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, F n y)) :
    Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun n => (Ecut n).toReal / (volume (cube ρ x₀)).toReal) ∧
      limsup (fun n => (Ecut n).toReal / (volume (cube ρ x₀)).toReal) atTop ≤
        A.toReal / (volume (cube ρ x₀)).toReal +
          (B.toReal / (volume (cube ρ x₀)).toReal) *
            ((μ (cube ρ x₀)).toReal - (μ (cube (s * ρ) x₀)).toReal) := by
  let Fann : ℕ → ℝ≥0∞ := fun n => ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀, F n y
  let Fout : ℕ → ℝ≥0∞ := fun n => ∫⁻ y in cube ρ x₀, F n y
  let V : ℝ := (volume (cube ρ x₀)).toReal
  have hV : 0 < V := by
    dsimp [V]
    rw [volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le]
    exact pow_pos hρ _
  have hμouter : μ (cube ρ x₀) < ⊤ := measure_lt_top μ _
  have hμinner : μ (cube (s * ρ) x₀) < ⊤ := measure_lt_top μ _
  have houterReal : Tendsto (fun n => (Fout n).toReal) atTop
      (𝓝 (μ (cube ρ x₀)).toReal) :=
    (ENNReal.tendsto_toReal_iff (fun n => (hfinite n).ne) hμouter.ne).2 houter
  have hFann_le : ∀ n, Fann n ≤ Fout n := by
    intro n
    exact lintegral_mono_set sdiff_subset
  have hFann_finite : ∀ n, Fann n < ⊤ := by
    intro n
    exact lt_of_le_of_lt (hFann_le n) (hfinite n)
  have hFann_upper_event : ∀ᶠ n in atTop,
      (Fann n).toReal ≤ (μ (cube ρ x₀)).toReal + 1 := by
    filter_upwards [houterReal.eventually (Iio_mem_nhds (by linarith :
      (μ (cube ρ x₀)).toReal < (μ (cube ρ x₀)).toReal + 1))] with n hn
    exact (ENNReal.toReal_mono (hfinite n).ne (hFann_le n)).trans hn.le
  have hFann_bounded : IsBoundedUnder (· ≤ ·) atTop (fun n => (Fann n).toReal) := by
    exact Filter.isBoundedUnder_of_eventually_le hFann_upper_event
  have hlimsupF : limsup (fun n => (Fann n).toReal) atTop ≤
      (μ (cube ρ x₀)).toReal - (μ (cube (s * ρ) x₀)).toReal := by
    exact limsup_cube_annulus_energy_le (N := N) hρ hs x₀ houter hinner hfinite
  have hEupperReal : ∀ᶠ n in atTop,
      (Ecut n).toReal ≤ A.toReal + B.toReal * (Fann n).toReal := by
    filter_upwards [hcut] with n hn
    have hRHSfinite : A + B * Fann n < ⊤ := by
      exact ENNReal.add_lt_top.2 ⟨hA, ENNReal.mul_lt_top hB (hFann_finite n)⟩
    have hmono := ENNReal.toReal_mono hRHSfinite.ne hn
    have hrewrite : (A + B * Fann n).toReal = A.toReal + B.toReal * (Fann n).toReal := by
      rw [ENNReal.toReal_add hA.ne (ENNReal.mul_ne_top hB.ne (hFann_finite n).ne),
        ENNReal.toReal_mul]
    rw [← hrewrite]
    exact hmono
  have hnormalized_upper : ∀ᶠ n in atTop,
      (Ecut n).toReal / V ≤ A.toReal / V + (B.toReal / V) * (Fann n).toReal := by
    filter_upwards [hEupperReal] with n hn
    have hdiv := div_le_div_of_nonneg_right hn hV.le
    calc
      (Ecut n).toReal / V ≤
          (A.toReal + B.toReal * (Fann n).toReal) / V := hdiv
      _ = A.toReal / V + (B.toReal / V) * (Fann n).toReal := by
        field_simp [ne_of_gt hV]
  have hnormalized_bounded : IsBoundedUnder (· ≤ ·) atTop
      (fun n => (Ecut n).toReal / V) := by
    have hupper : ∀ᶠ n in atTop,
        (Ecut n).toReal / V ≤
          (A.toReal + B.toReal * ((μ (cube ρ x₀)).toReal + 1)) / V := by
      filter_upwards [hEupperReal, hFann_upper_event] with n hE hF
      apply div_le_div_of_nonneg_right _ hV.le
      calc
        (Ecut n).toReal ≤ A.toReal + B.toReal * (Fann n).toReal := hE
        _ ≤ A.toReal + B.toReal * ((μ (cube ρ x₀)).toReal + 1) := by gcongr
    exact Filter.isBoundedUnder_of_eventually_le hupper
  have hlimsup_normalized := limsup_le_affine_of_eventually_le
    (F := fun n => (Fann n).toReal) (E := fun n => (Ecut n).toReal / V)
    (a := A.toReal / V) (b := B.toReal / V)
    (d := (μ (cube ρ x₀)).toReal - (μ (cube (s * ρ) x₀)).toReal)
    (by positivity) hFann_bounded hlimsupF hnormalized_bounded
    (fun n => by positivity) hnormalized_upper
  refine ⟨?_, ?_⟩
  · simpa [V] using hnormalized_bounded
  · simpa [Fann, V] using hlimsup_normalized

omit [NeZero N] in
/-- Integrated coercive estimate after the ru-usc rescaling. This is the precise estimate needed
for the `G(θ ∇uₙ)` term in the cut-off bound. The pointwise ru-usc inequality is assumed only
almost everywhere on the integration set, matching the essential-supremum cut-off estimates. -/
theorem HasGGrowth.lintegral_G_scaled_le_ruusc
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hgrowth : HasGGrowth G α β L) (hα : 0 < α)
    {S : Set (Sp N)} {θ : ℝ} {η c : ℝ≥0}
    (x : Sp N → Sp N) (grad : Sp N → Mat m N)
    (hLmeas : AEMeasurable (fun y => L (x y) (grad y)) (volume.restrict S))
    (hru : ∀ᵐ y ∂(volume.restrict S),
      L (x y) (θ • grad y) ≤
        (1 + (η : ℝ≥0∞)) * L (x y) (grad y) + (η : ℝ≥0∞) * c) :
    ∫⁻ y in S, G (θ • grad y) ≤
      (α : ℝ≥0∞)⁻¹ *
        ((1 + (η : ℝ≥0∞)) * (∫⁻ y in S, L (x y) (grad y)) +
          (η : ℝ≥0∞) * c * volume S) := by
  let αE : ℝ≥0∞ := α
  have hα0 : αE ≠ 0 := by simp [αE, hα.ne']
  have hαtop : αE ≠ ⊤ := by simp [αE]
  have hpoint : ∀ᵐ y ∂(volume.restrict S),
      G (θ • grad y) ≤ αE⁻¹ *
        ((1 + (η : ℝ≥0∞)) * L (x y) (grad y) + (η : ℝ≥0∞) * c) := by
    filter_upwards [hru] with y hy
    calc
      G (θ • grad y) = αE⁻¹ * (αE * G (θ • grad y)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hα0 hαtop, one_mul]
      _ ≤ αE⁻¹ * L (x y) (θ • grad y) :=
        mul_le_mul_of_nonneg_left (hgrowth (x y) (θ • grad y)).1 bot_le
      _ ≤ αE⁻¹ *
          ((1 + (η : ℝ≥0∞)) * L (x y) (grad y) + (η : ℝ≥0∞) * c) :=
        mul_le_mul_of_nonneg_left hy bot_le
  have hsum : AEMeasurable
      (fun y => (1 + (η : ℝ≥0∞)) * L (x y) (grad y) + (η : ℝ≥0∞) * c)
      (volume.restrict S) := (hLmeas.const_mul _).add aemeasurable_const
  calc
    ∫⁻ y in S, G (θ • grad y) ≤
        ∫⁻ y in S, αE⁻¹ *
          ((1 + (η : ℝ≥0∞)) * L (x y) (grad y) + (η : ℝ≥0∞) * c) :=
      lintegral_mono_ae hpoint
    _ = αE⁻¹ *
        ((1 + (η : ℝ≥0∞)) * (∫⁻ y in S, L (x y) (grad y)) +
          (η : ℝ≥0∞) * c * volume S) := by
      rw [MeasureTheory.lintegral_const_mul'' _ hsum]
      congr 1
      calc
        ∫⁻ y in S,
            (1 + (η : ℝ≥0∞)) * L (x y) (grad y) + (η : ℝ≥0∞) * c =
          (1 + (η : ℝ≥0∞)) * (∫⁻ y in S, L (x y) (grad y)) +
            (η : ℝ≥0∞) * c * volume S := by
          have hcoef : (1 + (η : ℝ≥0∞)) ≠ ⊤ :=
            ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.coe_ne_top⟩
          rw [MeasureTheory.lintegral_add_right' _ aemeasurable_const,
            MeasureTheory.lintegral_const_mul' _ _ hcoef,
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top,
            MeasureTheory.setLIntegral_const]
          simp [mul_assoc]

omit [NeZero N] in
/-- Combine the fixed-scale affine cut-off estimate with the integrated ru-usc/coercivity bound.
The cut-off energy is bounded by the exact constants from
`ConvexENN.affineCutoff_integrated_annulus_bound`, while the gradient-growth term is replaced
using `HasGGrowth.lintegral_G_scaled_le_ruusc`. This lemma is at a fixed integration set and
sequence index; it does not assert a limit in the radius. -/
theorem ConvexENN.affineCutoff_integrated_annulus_ruusc_bound
    {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hgrowth : HasGGrowth G α β L) (hα : 0 < α)
    {S : Set (Sp N)} {η c : ℝ≥0} {θ : ℝ}
    (x : ℕ → Sp N → Sp N) (grad : ℕ → Sp N → Mat m N)
    (Ecut : ℕ → ℝ≥0∞) (K : ℝ≥0∞)
    (hLmeas : ∀ n, AEMeasurable (fun y => L (x n y) (grad n y))
      (volume.restrict S))
    (hru : ∀ n, ∀ᵐ y ∂(volume.restrict S),
      L (x n y) (θ • grad n y) ≤
        (1 + (η : ℝ≥0∞)) * L (x n y) (grad n y) + (η : ℝ≥0∞) * c)
    (n₀ : ℕ) (hcut : ∀ n ≥ n₀,
      Ecut n ≤ (β : ℝ≥0∞) *
        (K * volume S + ∫⁻ y in S, G (θ • grad n y))) :
    ∀ n ≥ n₀, Ecut n ≤ (β : ℝ≥0∞) *
      (K * volume S + (α : ℝ≥0∞)⁻¹ *
        ((1 + (η : ℝ≥0∞)) * (∫⁻ y in S, L (x n y) (grad n y)) +
          (η : ℝ≥0∞) * c * volume S)) := by
  intro n hn
  have hG := hgrowth.lintegral_G_scaled_le_ruusc (N := N) (m := m) hα (x n) (grad n)
    (hLmeas n) (hru n)
  calc
    Ecut n ≤ (β : ℝ≥0∞) *
        (K * volume S + ∫⁻ y in S, G (θ • grad n y)) := hcut n hn
    _ ≤ (β : ℝ≥0∞) *
        (K * volume S + (α : ℝ≥0∞)⁻¹ *
          ((1 + (η : ℝ≥0∞)) * (∫⁻ y in S, L (x n y) (grad n y)) +
            (η : ℝ≥0∞) * c * volume S)) := by
      gcongr

omit [NeZero N] in
/-- Apply the fixed-scale cut-off and ru-usc estimates to the oscillating sequence
`xₙ(y) = εₙ⁻¹ • y`, using the externally supplied finite remainder bound `M`. The radius and
index thresholds are uniform in `εₙ`; the output combines the cut-off energy with the exact
coercivity constants `α`, `β` and ru-usc error `η c`. -/
theorem ConvexENN.affineCutoff_integrated_annulus_ruusc_bound_uniform_eps
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hgrowth : HasGGrowth G α β L) (hα : 0 < α)
    (h0 : (0 : Mat m N) ∈ interior (dom G)) (hLm : Measurable (uncurry L))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρmax : ℝ} (hρmax : 0 < ρmax)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Metric.closedBall x₀ (ρ / 2) ⊆ Ω)
    (hdom : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → ∀ n,
      ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
        (uₙ n).grad y ∈ dom G)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    {M : ℝ≥0∞}
    (hM : ∃ ρrem : ℝ, 0 < ρrem ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρrem → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          G ((t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              ((uₙ n).toFun y - affineMap a₀ A x₀ y))) ≤ M)
    (ε : ℕ → ℝ) {η : ℝ≥0} {c : ℝ≥0}
    (hru : ∀ z ξ, L z (θ • ξ) ≤
      (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ ρmax ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        AEMeasurable (fun y => L ((ε n)⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs ρ x₀ y))
          (volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)) ∧
        ∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
          L ((ε n)⁻¹ • y)
            (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs ρ x₀ y) ≤
          (β : ℝ≥0∞) *
            (((1 + M + G (θ • A) + (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c) *
                volume (cube ρ x₀ \ cube (s * ρ) x₀) +
              (α : ℝ≥0∞)⁻¹ * (1 + (η : ℝ≥0∞)) *
                (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
                  L ((ε n)⁻¹ • y) ((uₙ n).grad y)))) := by
  obtain ⟨ρ₀, hρ₀, hρ₀max, hfixed⟩ :=
    hG.affineCutoff_integrated_annulus_bound_uniform_eps (N := N) (m := m)
      hgrowth h0 hLm hΩopen hΩbounded uₙ a₀ A x₀ hs hρmax hball hdom
      ht htθ hθ hM
  refine ⟨ρ₀, hρ₀, hρ₀max, fun ρ hρ hρsmall => ?_⟩
  obtain ⟨n₀, hfixedρ⟩ := hfixed ρ hρ hρsmall
  refine ⟨n₀, fun n hn => ?_⟩
  have hρmax' : ρ < ρmax := lt_of_lt_of_le hρsmall hρ₀max
  let S := cube ρ x₀ \ cube (s * ρ) x₀
  let xosc : ℕ → Sp N → Sp N := fun j y => (ε j)⁻¹ • y
  let grad : ℕ → Sp N → Mat m N := fun j y => (uₙ j).grad y
  let Ecut : ℕ → ℝ≥0∞ := fun j => ∫⁻ y in S,
    L (xosc j y) (t • affineCutoffGrad (N := N) (m := m) (uₙ j) a₀ A x₀ hs ρ x₀ y)
  let K : ℝ≥0∞ := 1 + M + G (θ • A)
  have hSΩ : S ⊆ Ω := by
    intro y hy
    change y ∈ cube ρ x₀ \ cube (s * ρ) x₀ at hy
    rw [cube_eq_ball hρ] at hy
    exact hball ρ hρ hρmax' (Metric.ball_subset_closedBall hy.1)
  have hLmeasS : ∀ j, AEMeasurable (fun y => L (xosc j y) (grad j y))
      (volume.restrict S) := by
    intro j
    let uj := (uₙ j).restrict hSΩ
    exact hLm.comp_aemeasurable
      ((measurable_const_smul ((ε j)⁻¹)).aemeasurable.prodMk
        uj.memLp_grad.1.aemeasurable)
  have hruS : ∀ j, ∀ᵐ y ∂(volume.restrict S),
      L (xosc j y) (θ • grad j y) ≤
        (1 + (η : ℝ≥0∞)) * L (xosc j y) (grad j y) + (η : ℝ≥0∞) * c := by
    intro j
    filter_upwards with y
    exact hru (xosc j y) (grad j y)
  have hcut : ∀ j ≥ n₀, Ecut j ≤ (β : ℝ≥0∞) *
      (K * volume S + ∫⁻ y in S, G (θ • grad j y)) := by
    intro j hj
    have h := (hfixedρ j hj (ε j)).2
    simpa [Ecut, K, S, xosc, grad, add_mul] using h
  have hcombined := ConvexENN.affineCutoff_integrated_annulus_ruusc_bound
    (N := N) (m := m) hgrowth hα xosc grad Ecut K hLmeasS hruS n₀ hcut
  have h := hcombined n hn
  refine ⟨?_, ?_⟩
  · simpa [Ecut, S, xosc] using (hfixedρ n hn (ε n)).1
  · convert h using 1; ring

omit [NeZero N] in
/-- The uniform integrated estimate makes the cut-off annulus energy finite eventually, provided
the uncut outer-cube energies are finite. The estimate is applied at each fixed admissible radius;
its witnesses remain independent of the oscillation scale. -/
theorem affineCutoff_annulus_energy_finite_eventually
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hgrowth : HasGGrowth G α β L) (hα : 0 < α)
    (h0 : (0 : Mat m N) ∈ interior (dom G)) (hLm : Measurable (uncurry L))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρmax : ℝ} (hρmax : 0 < ρmax)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Metric.closedBall x₀ (ρ / 2) ⊆ Ω)
    (hdom : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → ∀ n,
      ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
        (uₙ n).grad y ∈ dom G)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    {M : ℝ≥0∞} (hMtop : M < ⊤) (hM : ∃ ρrem : ℝ, 0 < ρrem ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρrem → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          G ((t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              ((uₙ n).toFun y - affineMap a₀ A x₀ y))) ≤ M)
    (ε : ℕ → ℝ) {η c : ℝ≥0}
    (hru : ∀ z ξ, L z (θ • ξ) ≤
      (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c)
    (hGθA : G (θ • A) < ⊤) :
    ∃ ρ₀, 0 < ρ₀ ∧ ρ₀ ≤ ρmax ∧
      ∀ ρ, 0 < ρ → ρ < ρ₀ →
        (∀ n, (∫⁻ y in cube ρ x₀, L ((ε n)⁻¹ • y) ((uₙ n).grad y)) < ⊤) →
        ∃ n₀, ∀ n ≥ n₀,
          (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
            L ((ε n)⁻¹ • y)
              (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs ρ x₀ y)) < ⊤ := by
  obtain ⟨ρ₀, hρ₀, hρ₀max, hbound⟩ :=
    Homogenization.ConvexENN.affineCutoff_integrated_annulus_ruusc_bound_uniform_eps
      (N := N) (m := m) hG hgrowth hα h0 hLm hΩopen hΩbounded uₙ a₀ A x₀ hs
      hρmax hball hdom ht htθ hθ hM ε hru
  refine ⟨ρ₀, hρ₀, hρ₀max, ?_⟩
  intro ρ hρ hρsmall houter
  obtain ⟨n₀, hboundρ⟩ := hbound ρ hρ hρsmall
  refine ⟨n₀, fun n hn => ?_⟩
  have hvolS : volume (cube ρ x₀ \ cube (s * ρ) x₀) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono sdiff_subset) (volume_cube_ne_top ρ x₀).lt_top
  have hraw : (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
      L ((ε n)⁻¹ • y) ((uₙ n).grad y)) ≤
      ∫⁻ y in cube ρ x₀, L ((ε n)⁻¹ • y) ((uₙ n).grad y) :=
    lintegral_mono_set sdiff_subset
  have hrawTop : (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
      L ((ε n)⁻¹ • y) ((uₙ n).grad y)) < ⊤ :=
    lt_of_le_of_lt hraw (houter n)
  have hαinv : (α : ℝ≥0∞)⁻¹ < ⊤ :=
    ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr hα)
  have hKtail : (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hαinv (by simp)) (by simp)
  have hK : 1 + M + G (θ • A) + (α : ℝ≥0∞)⁻¹ *
      (η : ℝ≥0∞) * c < ⊤ := by
    apply ENNReal.add_lt_top.2
    exact ⟨ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨by simp, hMtop⟩, hGθA⟩, hKtail⟩
  have htermA : ((1 + M + G (θ • A) +
      (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c) *
      volume (cube ρ x₀ \ cube (s * ρ) x₀)) < ⊤ :=
    ENNReal.mul_lt_top hK hvolS
  have htermB : ((α : ℝ≥0∞)⁻¹ * (1 + (η : ℝ≥0∞)) *
      (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
        L ((ε n)⁻¹ • y) ((uₙ n).grad y))) < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hαinv (by simp)) hrawTop
  have hRHS : (β : ℝ≥0∞) *
      ((1 + M + G (θ • A) + (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c) *
          volume (cube ρ x₀ \ cube (s * ρ) x₀) +
        (α : ℝ≥0∞)⁻¹ * (1 + (η : ℝ≥0∞)) *
          (∫⁻ y in cube ρ x₀ \ cube (s * ρ) x₀,
            L ((ε n)⁻¹ • y) ((uₙ n).grad y))) < ⊤ := by
    exact ENNReal.mul_lt_top (by simp)
      (ENNReal.add_lt_top.2 ⟨htermA, htermB⟩)
  exact lt_of_le_of_lt (hboundρ n hn).2 hRHS


omit [NeZero N] in
/-- Ratio of the volumes of the inner and outer centered cubes. Since `cube ρ x` uses side
length `ρ`, the exact ratio is `s^N`. -/
theorem volume_cube_inner_ratio {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ∈ Ioo (0 : ℝ) 1)
    (x₀ : Sp N) :
    (volume (cube (s * ρ) x₀)).toReal / (volume (cube ρ x₀)).toReal = s ^ N := by
  rw [volume_cube, volume_cube, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg hs.1.le hρ.le), ENNReal.toReal_ofReal hρ.le]
  rw [div_eq_iff (ne_of_gt (pow_pos hρ N))]
  rw [← mul_pow]

omit [NeZero N] in
/-- The volume of the set-theoretic annulus, normalized by the outer cube volume, is exactly
`1 - s^N`. The inner boundary is part of the annulus, so no boundary-null fact is needed. -/
theorem volume_cube_annulus_ratio {ρ s : ℝ} (hρ : 0 < ρ)
    (hs : s ∈ Ioo (0 : ℝ) 1) (x₀ : Sp N) :
    (volume (cube ρ x₀ \ cube (s * ρ) x₀)).toReal /
      (volume (cube ρ x₀)).toReal = 1 - s ^ N := by
  have hsubset : cube (s * ρ) x₀ ⊆ cube ρ x₀ := by
    intro y hy
    simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
    intro i
    obtain ⟨hlo, hhi⟩ := hy i
    constructor <;> nlinarith [hs.2, hρ]
  have hset : cube ρ x₀ = cube (s * ρ) x₀ ∪
      (cube ρ x₀ \ cube (s * ρ) x₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hy
      by_cases hi : y ∈ cube (s * ρ) x₀
      · exact Or.inl hi
      · exact Or.inr ⟨hy, hi⟩
    · rintro (hy | ⟨hy, _⟩)
      · exact hsubset hy
      · exact hy
  have hadd : volume (cube ρ x₀) =
      volume (cube (s * ρ) x₀) + volume (cube ρ x₀ \ cube (s * ρ) x₀) := by
    calc
      volume (cube ρ x₀) = volume (cube (s * ρ) x₀ ∪
          (cube ρ x₀ \ cube (s * ρ) x₀)) := congrArg volume hset
      _ = volume (cube (s * ρ) x₀) + volume (cube ρ x₀ \ cube (s * ρ) x₀) :=
        measure_union disjoint_sdiff_right
          ((isOpen_cube ρ x₀).measurableSet.diff
            (isOpen_cube (s * ρ) x₀).measurableSet)
  have houter : volume (cube ρ x₀) < ⊤ := (volume_cube_ne_top _ _).lt_top
  have hinner : volume (cube (s * ρ) x₀) < ⊤ := (volume_cube_ne_top _ _).lt_top
  have hannulus : volume (cube ρ x₀ \ cube (s * ρ) x₀) < ⊤ :=
    lt_of_le_of_lt (measure_mono sdiff_subset) houter
  have hreal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hinner.ne hannulus.ne] at hreal
  have hratio := volume_cube_inner_ratio (N := N) hρ hs x₀
  have hVpos : 0 < (volume (cube ρ x₀)).toReal := by
    rw [volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le]
    exact pow_pos hρ _
  have hVne : (volume (cube ρ x₀)).toReal ≠ 0 := hVpos.ne'
  calc
    (volume (cube ρ x₀ \ cube (s * ρ) x₀)).toReal /
        (volume (cube ρ x₀)).toReal =
        ((volume (cube ρ x₀)).toReal -
          (volume (cube (s * ρ) x₀)).toReal) /
            (volume (cube ρ x₀)).toReal := by
      have hsub : (volume (cube ρ x₀ \ cube (s * ρ) x₀)).toReal =
          (volume (cube ρ x₀)).toReal -
            (volume (cube (s * ρ) x₀)).toReal := by linarith [hreal]
      rw [hsub]
    _ = 1 - (volume (cube (s * ρ) x₀)).toReal /
        (volume (cube ρ x₀)).toReal := by field_simp [hVne]
    _ = 1 - s ^ N := by rw [← hratio]

omit [NeZero N] in
/-- At a point where the centered-cube density tends to the finite value `f`, the normalized
measure of the annulus `Qρ \ Q(sρ)` tends to `(1-s^N)f`. This uses finite additivity and the exact
volume ratio; the inner boundary is included in the annulus, so no boundary-null hypothesis is
needed. -/
theorem tendsto_measure_cube_annulus_ratio {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (x₀ : Sp N) {f : ℝ≥0∞} (hf : f < ⊤)
    (hdensity : Tendsto
      (fun ρ : ℝ => μ (cube ρ x₀) / volume (cube ρ x₀))
      (𝓝[>] (0 : ℝ)) (𝓝 f)) :
    Tendsto (fun ρ : ℝ =>
      (μ (cube ρ x₀ \ cube (s * ρ) x₀) / volume (cube ρ x₀)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 - s ^ N) * f.toReal)) := by
  have hscale : Tendsto (fun ρ : ℝ => s * ρ)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have hzero : Tendsto (fun ρ : ℝ => s * ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hid : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      simpa using hid.const_mul s
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact mul_pos hs.1 (by simpa using hρ)
  have houterReal : Tendsto
      (fun ρ : ℝ => (μ (cube ρ x₀) / volume (cube ρ x₀)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 f.toReal) :=
    (ENNReal.tendsto_toReal hf.ne).comp hdensity
  have hinnerENN := hdensity.comp hscale
  have hinnerReal : Tendsto
      (fun ρ : ℝ => (μ (cube (s * ρ) x₀) / volume (cube (s * ρ) x₀)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 f.toReal) :=
    (ENNReal.tendsto_toReal hf.ne).comp hinnerENN
  have hratio : Tendsto
      (fun ρ : ℝ => s ^ N *
        (μ (cube (s * ρ) x₀) / volume (cube (s * ρ) x₀)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (s ^ N * f.toReal)) :=
    tendsto_const_nhds.mul hinnerReal
  have hmeasureAdd : ∀ ρ : ℝ, 0 < ρ →
      μ (cube ρ x₀) = μ (cube (s * ρ) x₀) +
        μ (cube ρ x₀ \ cube (s * ρ) x₀) := by
    intro ρ hρ
    have hsubset : cube (s * ρ) x₀ ⊆ cube ρ x₀ := by
      intro y hy
      simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
      intro i
      obtain ⟨hlo, hhi⟩ := hy i
      constructor <;> nlinarith [hs.2, hρ]
    have hset : cube ρ x₀ = cube (s * ρ) x₀ ∪
        (cube ρ x₀ \ cube (s * ρ) x₀) := by
      ext y
      simp only [Set.mem_union, Set.mem_sdiff]
      constructor
      · intro hy
        by_cases hi : y ∈ cube (s * ρ) x₀
        · exact Or.inl hi
        · exact Or.inr ⟨hy, hi⟩
      · rintro (hy | ⟨hy, _⟩)
        · exact hsubset hy
        · exact hy
    exact (congrArg μ hset).trans (measure_union disjoint_sdiff_right
      ((isOpen_cube ρ x₀).measurableSet.diff (isOpen_cube (s * ρ) x₀).measurableSet))
  have hidentity : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (μ (cube ρ x₀ \ cube (s * ρ) x₀) / volume (cube ρ x₀)).toReal =
        (μ (cube ρ x₀) / volume (cube ρ x₀)).toReal -
          s ^ N * (μ (cube (s * ρ) x₀) / volume (cube (s * ρ) x₀)).toReal := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ' : 0 < ρ := by simpa using hρ
    have hμo : μ (cube ρ x₀) < ⊤ := measure_lt_top μ _
    have hμi : μ (cube (s * ρ) x₀) < ⊤ := measure_lt_top μ _
    have hμa : μ (cube ρ x₀ \ cube (s * ρ) x₀) < ⊤ := measure_lt_top μ _
    have hvolo : volume (cube ρ x₀) < ⊤ := by simp [volume_cube]
    have hvoli : volume (cube (s * ρ) x₀) < ⊤ := by simp [volume_cube]
    have hvolo0 : (volume (cube ρ x₀)).toReal ≠ 0 := by
      rw [volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ'.le]
      exact (pow_pos hρ' N).ne'
    have hvoli0 : (volume (cube (s * ρ) x₀)).toReal ≠ 0 := by
      rw [volume_cube, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (mul_nonneg hs.1.le hρ'.le)]
      exact (pow_pos (mul_pos hs.1 hρ') N).ne'
    have hmeasureR := congrArg ENNReal.toReal (hmeasureAdd ρ hρ')
    rw [ENNReal.toReal_add hμi.ne hμa.ne] at hmeasureR
    rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div,
      ]
    have hvolratio := volume_cube_inner_ratio (N := N) hρ' hs x₀
    rw [← hvolratio]
    field_simp [hvolo0, hvoli0] at hmeasureR ⊢
    linarith
  have hsub := houterReal.sub hratio
  have hidentity' :
      (fun ρ : ℝ =>
        (μ (cube ρ x₀) / volume (cube ρ x₀)).toReal -
          s ^ N * (μ (cube (s * ρ) x₀) / volume (cube (s * ρ) x₀)).toReal) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ρ =>
          (μ (cube ρ x₀ \ cube (s * ρ) x₀) / volume (cube ρ x₀)).toReal) := by
    filter_upwards [hidentity] with ρ hρ
    exact hρ.symm
  have hlimit := hsub.congr' hidentity'
  have htarget : f.toReal - s ^ N * f.toReal = (1 - s ^ N) * f.toReal := by ring
  simpa [htarget] using hlimit

/-- **The lower bound** (Proposition `main result` (i) of [oah-jpm-zorgati14], on `O = Ω`):
the Γ-liminf half of `CitedAHM14`, under the same hypotheses. -/
def LowerBoundStatement : Prop :=
  (N : ℝ) < p → ∀ Ω : Set (Sp N), IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
    HasLipschitzBoundary Ω →
    ∀ (G : Mat m N → ℝ≥0∞) (α β c₀ : ℝ≥0) (L : Sp N → Mat m N → ℝ≥0∞),
      ConvexENN G → (0 : Mat m N) ∈ interior (dom G) → 0 < α → 0 < c₀ →
      Measurable (uncurry L) → IsPeriodic L → IsCoercive p c₀ L → HasGGrowth G α β L →
      RUUSC L →
      ∀ u : W1p N m (ENNReal.ofReal p) Ω,
        intHom (radial (Hp (ENNReal.ofReal p) L)) u ≤ GammaLiminf (intFun L) u

/-- The exact local conclusion sought in Proposition 2.1(i): the integral on every open
`O ⊆ Ω` is bounded by the local Γ-liminf `Iminus`. This statement is deliberately separate from
the older whole-domain `LowerBoundStatement`. -/
def LocalLowerBoundStatement : Prop :=
  (N : ℝ) < p → ∀ Ω : Set (Sp N), IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
    HasLipschitzBoundary Ω →
    ∀ O : Set (Sp N), IsOpen O → O ⊆ Ω →
      ∀ (G : Mat m N → ℝ≥0∞) (α β c₀ : ℝ≥0) (L : Sp N → Mat m N → ℝ≥0∞),
        ConvexENN G → (0 : Mat m N) ∈ interior (dom G) → 0 < α → 0 < c₀ →
        Measurable (uncurry L) → IsPeriodic L → IsCoercive p c₀ L → HasGGrowth G α β L →
        RUUSC L →
        ∀ u : W1p N m (ENNReal.ofReal p) Ω,
          ∫⁻ x in O, radial (Hp (ENNReal.ofReal p) L) (u.grad x) ≤ Iminus L O u


omit [NeZero N] in
/-- Normalize fixed-radius annulus limsup bounds along a positive sequence of admissible radii.
The measure contribution uses `tendsto_measure_cube_annulus_ratio`; the volume contribution has
the exact ratio `1 - s^N`. -/
theorem limsup_cutoff_annulus_normalized_along_radii
    {μ : Measure (Sp N)} [IsFiniteMeasure μ] {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (x₀ : Sp N) {f : ℝ≥0∞} (hf : f < ⊤)
    (hdensity : Tendsto
      (fun ρ : ℝ => μ (cube ρ x₀) / volume (cube ρ x₀))
      (𝓝[>] (0 : ℝ)) (𝓝 f))
    (ρ : ℕ → ℝ) (hρpos : ∀ k, 0 < ρ k)
    (hρ : Tendsto ρ atTop (𝓝 0)) {C₀ C₁ : ℝ} (Ecut : ℕ → ℕ → ℝ≥0∞)
    (hfixed : ∀ᶠ k in atTop,
      Filter.IsBoundedUnder (· ≤ ·) atTop (fun n =>
        (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) ∧
      limsup (fun n => (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) atTop ≤
        C₀ * ((volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal) +
        C₁ * ((μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal)) :
    limsup (fun k => limsup (fun n =>
      (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) atTop) atTop ≤
        (1 - s ^ N) * (C₀ + C₁ * f.toReal) := by
  have hρwithin : Tendsto ρ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ρ hρ
      (Filter.Eventually.of_forall hρpos)
  have hmeasure := tendsto_measure_cube_annulus_ratio (N := N) hs x₀ hf hdensity
  have hmeasureρ : Tendsto
      (fun k => (μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀) /
        volume (cube (ρ k) x₀)).toReal) atTop (𝓝 ((1 - s ^ N) * f.toReal)) := by
    exact hmeasure.comp hρwithin
  have hmeasureρ' : Tendsto
      (fun k => (μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
        (volume (cube (ρ k) x₀)).toReal) atTop
      (𝓝 ((1 - s ^ N) * f.toReal)) := by
    have heq : (fun k => (μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀) /
        volume (cube (ρ k) x₀)).toReal) =
        fun k => (μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal := by
      funext k
      rw [ENNReal.toReal_div]
    exact hmeasureρ.congr' (Filter.Eventually.of_forall fun k => congrFun heq k)
  have hvolumeρ : Tendsto
      (fun k => (volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
        (volume (cube (ρ k) x₀)).toReal) atTop (𝓝 (1 - s ^ N)) := by
    have heq : (fun k => (volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
        (volume (cube (ρ k) x₀)).toReal) = fun _ => 1 - s ^ N := by
      funext k
      exact volume_cube_annulus_ratio (N := N) (hρpos k) hs x₀
    rw [heq]
    exact tendsto_const_nhds
  have hupper : Tendsto
      (fun k => C₀ * ((volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal) +
        C₁ * ((μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal)) atTop
      (𝓝 ((1 - s ^ N) * (C₀ + C₁ * f.toReal))) := by
    have hC₀ : Tendsto (fun _ : ℕ => C₀) atTop (𝓝 C₀) := tendsto_const_nhds
    have hC₁ : Tendsto (fun _ : ℕ => C₁) atTop (𝓝 C₁) := tendsto_const_nhds
    have h := (hC₀.mul hvolumeρ).add (hC₁.mul hmeasureρ')
    convert h using 1
    ext k
    ring_nf
  have hnonneg : ∀ᶠ k in atTop, 0 ≤ limsup (fun n =>
      (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) atTop := by
    filter_upwards [hfixed] with k hk
    exact Filter.le_limsup_of_frequently_le
      (Filter.Frequently.of_forall fun n =>
        div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hk.1
  have hleftCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun k => limsup (fun n =>
        (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) atTop) := by
    change Filter.IsCobounded (· ≤ ·)
      (Filter.map (fun k => limsup (fun n =>
        (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) atTop) atTop)
    rw [Filter.IsCobounded]
    refine ⟨0, ?_⟩
    intro a ha
    have ha' : ∀ᶠ k in atTop, limsup (fun n =>
        (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) atTop ≤ a :=
      Filter.eventually_map.mp ha
    have hall := hnonneg.and ha'
    obtain ⟨k, hnonnegk, hk⟩ := hall.exists
    exact le_trans hnonnegk hk
  have hrightBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun k => C₀ * ((volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal) +
        C₁ * ((μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal)) := by
    apply Filter.isBoundedUnder_of_eventually_le
      (a := (1 - s ^ N) * (C₀ + C₁ * f.toReal) + 1)
    have hev := hupper.eventually (Iio_mem_nhds (show
        (1 - s ^ N) * (C₀ + C₁ * f.toReal) <
          (1 - s ^ N) * (C₀ + C₁ * f.toReal) + 1 by linarith))
    filter_upwards [hev] with k hk
    linarith
  calc
    limsup (fun k => limsup (fun n =>
        (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) atTop) atTop ≤
        limsup (fun k => C₀ *
          ((volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
            (volume (cube (ρ k) x₀)).toReal) +
          C₁ * ((μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
            (volume (cube (ρ k) x₀)).toReal)) atTop :=
      Filter.limsup_le_limsup (hfixed.mono fun _ hk => hk.2)
        hleftCobounded hrightBounded
    _ = (1 - s ^ N) * (C₀ + C₁ * f.toReal) := hupper.limsup_eq

omit [NeZero N] in
/-- For a fixed `ru-usc` constant, each tolerance has one threshold controlling all radial
factors above it. The constant is an input, so it cannot vary with `η`. -/
theorem RUUSCWith.radial_interval_le_affine {c : ℝ≥0}
    {L : Sp N → Mat m N → ℝ≥0∞} (hruusc : RUUSCWith c L)
    (η : ℝ≥0) (hη : 0 < η) :
    ∃ t₀ : ℝ, t₀ < 1 ∧
      ∀ t : ℝ, t₀ < t → t < 1 → ∀ z ξ,
        L z (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c := by
  have hle := hruusc.le_affine hη
  obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hle
  refine ⟨t₀, ht₀, ?_⟩
  intro t htt ht1 z ξ
  exact hsub ⟨htt, ht1⟩ z ξ

omit [NeZero N] in
/-- With `c` fixed, the additive `ru-usc` error `η c` tends to zero as `η → 0`. -/
theorem tendsto_eta_mul_fixed_ruusc_const (c : ℝ≥0) :
    Tendsto (fun η : ℝ≥0 => (η : ℝ≥0∞) * c) (𝓝 0) (𝓝 0) := by
  have hη : Tendsto (fun η : ℝ≥0 => (η : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_coe.tendsto (0 : ℝ≥0))
  have hmul : Tendsto (fun η : ℝ≥0 => (η : ℝ≥0∞) * c) (𝓝 0)
      (𝓝 ((0 : ℝ≥0∞) * c)) :=
    ENNReal.Tendsto.mul_const hη (Or.inr ENNReal.coe_ne_top)
  simpa using hmul

omit [NeZero N] in
/-- Fix the constant in the definition of `RUUSC` once, before quantifying over tolerances.
For every `η > 0`, the same `c` has a threshold `t₀` controlling every `t ∈ (t₀,1)`. -/
theorem RUUSC.radial_interval_le_affine {L : Sp N → Mat m N → ℝ≥0∞}
    (hruusc : RUUSC L) :
    ∃ c : ℝ≥0, 0 < c ∧ RUUSCWith c L ∧
      ∀ η : ℝ≥0, 0 < η → ∃ t₀ : ℝ, t₀ < 1 ∧
        ∀ t : ℝ, t₀ < t → t < 1 → ∀ z ξ,
          L z (t • ξ) ≤ (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c := by
  obtain ⟨c, hc, hwith⟩ := hruusc
  refine ⟨c, hc, hwith, ?_⟩
  intro η hη
  exact hwith.radial_interval_le_affine (N := N) (m := m) η hη

omit [NeZero N] in
/-- Choose positive tolerances tending to zero and radial factors tending to one from below,
with each factor above the RU-usc threshold for its own tolerance. The constant `c` is fixed in
`hruusc` before this sequence is chosen. -/
theorem RUUSCWith.exists_tolerance_and_radial_sequences
    {L : Sp N → Mat m N → ℝ≥0∞} {c : ℝ≥0} (hruusc : RUUSCWith c L) :
    ∃ η : ℕ → ℝ≥0, ∃ t : ℕ → ℝ,
      Tendsto (fun j => (η j).toReal) atTop (𝓝 0) ∧
      Tendsto t atTop (𝓝[<] (1 : ℝ)) ∧
      (∀ j, 0 < η j) ∧ (∀ j, 0 < t j ∧ t j < 1) ∧
      ∀ j z ξ, L z (t j • ξ) ≤
        (1 + (η j : ℝ≥0∞)) * L z ξ + (η j : ℝ≥0∞) * c := by
  let η : ℕ → ℝ≥0 := fun j => 1 / ((j : ℝ≥0) + 1)
  have hηpos : ∀ j, 0 < η j := by
    intro j
    dsimp [η]
    positivity
  have hη : Tendsto (fun j => (η j).toReal) atTop (𝓝 0) := by
    simpa [η] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let t₀ : ℕ → ℝ := fun j => Classical.choose
    (hruusc.radial_interval_le_affine (N := N) (m := m) (η j) (hηpos j))
  have ht₀ : ∀ j, t₀ j < 1 := fun j => (Classical.choose_spec
    (hruusc.radial_interval_le_affine (N := N) (m := m) (η j) (hηpos j))).1
  have hthreshold : ∀ j t' (ht'₀ : t₀ j < t') (ht'₁ : t' < 1) z ξ,
      L z (t' • ξ) ≤ (1 + (η j : ℝ≥0∞)) * L z ξ + (η j : ℝ≥0∞) * c := by
    intro j t' ht'₀ ht'₁ z ξ
    exact (Classical.choose_spec
      (hruusc.radial_interval_le_affine (N := N) (m := m) (η j) (hηpos j))).2
      t' ht'₀ ht'₁ z ξ
  let b : ℕ → ℝ := fun j => max (t₀ j) (max 0 (1 - (η j).toReal))
  let t : ℕ → ℝ := fun j => (b j + 1) / 2
  have hb : ∀ j, b j < 1 := by
    intro j
    dsimp [b]
    apply max_lt_iff.mpr
    constructor
    · exact ht₀ j
    · apply max_lt_iff.mpr
      exact ⟨by norm_num, by linarith [hηpos j]⟩
  have htpos : ∀ j, 0 < t j := by
    intro j
    dsimp [t]
    have hzero : 0 ≤ b j :=
      le_trans (le_max_left 0 _) (le_max_right _ _)
    linarith
  have htlt : ∀ j, t j < 1 := by
    intro j
    dsimp [t]
    linarith [hb j]
  have htabove : ∀ j, t₀ j < t j := by
    intro j
    dsimp [t]
    have h₀b : t₀ j ≤ b j := le_max_left _ _
    linarith [hb j]
  have htlim : Tendsto t atTop (𝓝 (1 : ℝ)) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      have hevent : ∀ᶠ j in atTop, (η j).toReal < 1 - a :=
        hη.eventually (Iio_mem_nhds (by linarith))
      filter_upwards [hevent] with j hj
      have hlow : 1 - (η j).toReal ≤ b j :=
        le_trans (le_max_right 0 _) (le_max_right _ _)
      dsimp [t]
      linarith
    · intro a ha
      exact Filter.Eventually.of_forall fun j => (htlt j).trans ha
  have htwithin : Tendsto t atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t htlim
      (Filter.Eventually.of_forall fun j => htlt j)
  refine ⟨η, t, hη, htwithin, hηpos, fun j => ⟨htpos j, htlt j⟩, ?_⟩
  intro j z ξ
  exact hthreshold j (t j) (htabove j) (htlt j) z ξ

omit [NeZero N] in
/-- Choose `θ > t` above the threshold for the same fixed `RUUSCWith c L` constant. This is the
larger radial factor used on the annulus; the estimate at `t` is obtained separately from the
threshold lemma. -/
theorem RUUSC.exists_theta_le_affine {L : Sp N → Mat m N → ℝ≥0∞}
    {c : ℝ≥0} (hruusc : RUUSCWith c L) {t : ℝ} (ht : t < 1)
    {η : ℝ≥0} (hη : 0 < η) :
    ∃ θ : ℝ, t < θ ∧ θ < 1 ∧
      ∀ z ξ, L z (θ • ξ) ≤
        (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c := by
  obtain ⟨t₀, ht₀, hbound⟩ :=
    hruusc.radial_interval_le_affine (N := N) (m := m) η hη
  let a := max t t₀
  have ha : a < 1 := max_lt_iff.mpr ⟨ht, ht₀⟩
  obtain ⟨θ, hθa, hθ1⟩ := exists_between ha
  refine ⟨θ, (le_max_left _ _).trans_lt hθa, hθ1, ?_⟩
  exact hbound θ ((le_max_right _ _).trans_lt hθa) hθ1

omit [NeZero N] in
/-- Combine the uniform affine cut-off estimate, a supplied common finite bound `M` for the
remainder, the fixed-radius portmanteau bound, and the normalized annulus limit. The same `M`
appears in the final coefficient; the estimate is uniform in the oscillation sequence. -/
theorem affineCutoff_uniform_eps_limsup_normalized
    {μ : Measure (Sp N)} [IsFiniteMeasure μ]
    {G : Mat m N → ℝ≥0∞} (hG : ConvexENN G)
    {α β : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hgrowth : HasGGrowth G α β L) (hα : 0 < α)
    (h0 : (0 : Mat m N) ∈ interior (dom G)) (hLm : Measurable (uncurry L))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω) (a₀ : Tgt m) (A : Mat m N)
    (x₀ : Sp N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {ρmax : ℝ} (hρmax : 0 < ρmax)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Metric.closedBall x₀ (ρ / 2) ⊆ Ω)
    (hdom : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → ∀ n,
      ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
        (uₙ n).grad y ∈ dom G)
    {t θ : ℝ} (ht : 0 < t) (htθ : t < θ) (hθ : θ < 1)
    {M : ℝ≥0∞} (hMtop : M < ⊤)
    (hM : ∃ ρrem : ℝ, 0 < ρrem ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρrem → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube ρ x₀ \ cube (s * ρ) x₀)),
          G ((t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs ρ x₀) y).smulRight
              ((uₙ n).toFun y - affineMap a₀ A x₀ y))) ≤ M)
    (ε : ℕ → ℝ) {η : ℝ≥0} {c : ℝ≥0}
    (hru : ∀ z ξ, L z (θ • ξ) ≤
      (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c)
    {f : ℝ≥0∞} (hf : f < ⊤)
    (hdensity : Tendsto (fun ρ : ℝ => μ (cube ρ x₀) / volume (cube ρ x₀))
      (𝓝[>] (0 : ℝ)) (𝓝 f))
    (ρ : ℕ → ℝ) (hρpos : ∀ k, 0 < ρ k)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (houter : ∀ k, Tendsto
      (fun n => ∫⁻ y in cube (ρ k) x₀,
        L ((ε n)⁻¹ • y) ((uₙ n).grad y))
      atTop (𝓝 (μ (cube (ρ k) x₀))))
    (hinner : ∀ k, μ (cube (s * ρ k) x₀) ≤
      liminf (fun n => ∫⁻ y in cube (s * ρ k) x₀,
        L ((ε n)⁻¹ • y) ((uₙ n).grad y)) atTop)
    (hfinite : ∀ k n, (∫⁻ y in cube (ρ k) x₀,
      L ((ε n)⁻¹ • y) ((uₙ n).grad y)) < ⊤)
    (hGθA : G (θ • A) < ⊤) :
    limsup (fun k => limsup (fun n =>
      (∫⁻ y in cube (ρ k) x₀ \ cube (s * ρ k) x₀,
        L ((ε n)⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs
            (ρ k) x₀ y)).toReal /
        (volume (cube (ρ k) x₀)).toReal) atTop) atTop ≤
      (1 - s ^ N) *
        (((β : ℝ≥0∞) *
            (1 + M + G (θ • A) +
              (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal +
          ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
            (1 + (η : ℝ≥0∞))).toReal * f.toReal) ∧
      ∀ᶠ k in atTop,
        Filter.IsBoundedUnder (· ≤ ·) atTop (fun n =>
          (∫⁻ y in cube (ρ k) x₀ \ cube (s * ρ k) x₀,
            L ((ε n)⁻¹ • y)
              (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs
                (ρ k) x₀ y)).toReal / (volume (cube (ρ k) x₀)).toReal) ∧
        limsup (fun n =>
          (∫⁻ y in cube (ρ k) x₀ \ cube (s * ρ k) x₀,
            L ((ε n)⁻¹ • y)
              (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs
                (ρ k) x₀ y)).toReal / (volume (cube (ρ k) x₀)).toReal) atTop ≤
          ((β : ℝ≥0∞) *
              (1 + M + G (θ • A) +
                (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal *
            ((volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
              (volume (cube (ρ k) x₀)).toReal) +
          ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
              (1 + (η : ℝ≥0∞))).toReal *
            ((μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
              (volume (cube (ρ k) x₀)).toReal) := by
  obtain ⟨ρ₀, hρ₀, hρ₀max, hcutUniform⟩ :=
    hG.affineCutoff_integrated_annulus_ruusc_bound_uniform_eps
      (N := N) (m := m) hgrowth hα h0 hLm hΩopen hΩbounded uₙ a₀ A x₀ hs
      hρmax hball hdom ht htθ hθ hM ε hru
  let K' : ℝ≥0∞ := 1 + M + G (θ • A) +
    (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c
  let D : ℝ≥0∞ := (β : ℝ≥0∞) * K'
  let B : ℝ≥0∞ := (β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
    (1 + (η : ℝ≥0∞))
  let C₀ : ℝ := D.toReal
  let C₁ : ℝ := B.toReal
  let Ecut : ℕ → ℕ → ℝ≥0∞ := fun k n =>
    ∫⁻ y in cube (ρ k) x₀ \ cube (s * ρ k) x₀,
      L ((ε n)⁻¹ • y)
        (t • affineCutoffGrad (N := N) (m := m) (uₙ n) a₀ A x₀ hs
          (ρ k) x₀ y)
  let F : ℕ → Sp N → ℝ≥0∞ := fun n y =>
    L ((ε n)⁻¹ • y) ((uₙ n).grad y)
  have hK : K' < ⊤ := by
    have hαEpos : 0 < (α : ℝ≥0∞) := ENNReal.coe_pos.mpr hα
    have hαinv : (α : ℝ≥0∞)⁻¹ < ⊤ :=
      ENNReal.inv_lt_top.mpr hαEpos
    dsimp [K']
    apply ENNReal.add_lt_top.2
    constructor
    · exact ENNReal.add_lt_top.2
        ⟨ENNReal.add_lt_top.2 ⟨by simp, hMtop⟩, hGθA⟩
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top hαinv (by simp)) (by simp)
  have hD : D < ⊤ := by
    dsimp [D]
    exact ENNReal.mul_lt_top (by simp) hK
  have hB : B < ⊤ := by
    have hαEpos : 0 < (α : ℝ≥0∞) := ENNReal.coe_pos.mpr hα
    have hαinv : (α : ℝ≥0∞)⁻¹ < ⊤ :=
      ENNReal.inv_lt_top.mpr hαEpos
    dsimp [B]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by simp) hαinv) (by simp)
  have hρsmall : ∀ᶠ k in atTop, ρ k < ρ₀ :=
    hρ.eventually (Iio_mem_nhds hρ₀)
  have hfixed : ∀ᶠ k in atTop,
      Filter.IsBoundedUnder (· ≤ ·) atTop (fun n =>
        (Ecut k n).toReal / (volume (cube (ρ k) x₀)).toReal) ∧
      limsup (fun n => (Ecut k n).toReal /
        (volume (cube (ρ k) x₀)).toReal) atTop ≤
        C₀ * ((volume (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal) +
        C₁ * ((μ (cube (ρ k) x₀ \ cube (s * ρ k) x₀)).toReal /
          (volume (cube (ρ k) x₀)).toReal) := by
    filter_upwards [hρsmall] with k hρk
    obtain ⟨n₀, hcutk⟩ := hcutUniform (ρ k) (hρpos k) hρk
    let S := cube (ρ k) x₀ \ cube (s * ρ k) x₀
    have hcut : ∀ᶠ n in atTop,
        Ecut k n ≤ D * volume S + B * (∫⁻ y in S, F n y) := by
      exact Filter.eventually_atTop.2 ⟨n₀, fun n hn => by
        have hh := hcutk n hn
        calc
          Ecut k n ≤ (β : ℝ≥0∞) *
              ((1 + M + G (θ • A) + (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c) *
                volume S +
                (α : ℝ≥0∞)⁻¹ * (1 + (η : ℝ≥0∞)) *
                  (∫⁻ y in S, F n y)) := by
            simpa [Ecut, F, S] using hh.2
          _ = D * volume S + B * (∫⁻ y in S, F n y) := by
            dsimp [D, B, K']
            ring⟩
    have hA : D * volume S < ⊤ := by
      have hvolS : volume S < ⊤ := by
        exact lt_of_le_of_lt (measure_mono sdiff_subset)
          (by simp [volume_cube])
      exact ENNReal.mul_lt_top hD hvolS
    have hBtop : B < ⊤ := hB
    have hfixedk := limsup_cutoff_annulus_ratio_le_of_affine_bound
      (N := N) (μ := μ) (F := F) (Ecut := fun n => Ecut k n)
      (A := D * volume S) (B := B) (hρpos k) hs x₀ (houter k) (hinner k)
      (fun n => hfinite k n) hA hBtop hcut
    have hadd : μ (cube (ρ k) x₀) =
        μ (cube (s * ρ k) x₀) + μ S := by
      have hsubset : cube (s * ρ k) x₀ ⊆ cube (ρ k) x₀ := by
        intro y hy
        simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
        intro i
        obtain ⟨hlo, hhi⟩ := hy i
        constructor <;> nlinarith [hs.2, hρpos k]
      have hset : cube (ρ k) x₀ =
          cube (s * ρ k) x₀ ∪ S := by
        ext y
        simp only [Set.mem_union]
        constructor
        · intro hy
          by_cases hi : y ∈ cube (s * ρ k) x₀
          · exact Or.inl hi
          · exact Or.inr ⟨hy, hi⟩
        · rintro (hy | ⟨hy, _⟩)
          · exact hsubset hy
          · exact hy
      have hdisj : Disjoint (cube (s * ρ k) x₀) S := disjoint_sdiff_right
      have hmeas : MeasurableSet S :=
        (isOpen_cube (ρ k) x₀).measurableSet.diff
          (isOpen_cube (s * ρ k) x₀).measurableSet
      exact (congrArg μ hset).trans (measure_union hdisj hmeas)
    have hrealAdd := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (measure_lt_top μ _).ne (measure_lt_top μ _).ne]
      at hrealAdd
    have hmeasureDiff :
        (μ (cube (ρ k) x₀)).toReal -
          (μ (cube (s * ρ k) x₀)).toReal = (μ S).toReal := by
      linarith
    have hV : 0 < (volume (cube (ρ k) x₀)).toReal := by
      rw [volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal (hρpos k).le]
      exact pow_pos (hρpos k) _
    have hcoeffA : (D * volume S).toReal /
        (volume (cube (ρ k) x₀)).toReal =
        C₀ * ((volume S).toReal /
          (volume (cube (ρ k) x₀)).toReal) := by
      rw [ENNReal.toReal_mul]
      dsimp [C₀]
      ring
    have hcoeffB :
        (B.toReal / (volume (cube (ρ k) x₀)).toReal) *
          ((μ (cube (ρ k) x₀)).toReal -
            (μ (cube (s * ρ k) x₀)).toReal) =
        C₁ * ((μ S).toReal /
          (volume (cube (ρ k) x₀)).toReal) := by
      rw [hmeasureDiff]
      dsimp [C₁]
      field_simp [ne_of_gt hV]
    refine ⟨hfixedk.1, ?_⟩
    rw [hcoeffA, hcoeffB] at hfixedk
    simpa [S] using hfixedk.2
  have hdouble := limsup_cutoff_annulus_normalized_along_radii
    (N := N) (μ := μ) hs x₀ hf hdensity ρ hρpos hρ
    (C₀ := C₀) (C₁ := C₁) Ecut hfixed
  exact ⟨hdouble, hfixed⟩

/-- Extract once the subsequence, energy measure, and almost-everywhere point data used by the
cut-off argument. This result is independent of the annulus parameter `s`, the radial factors
`t, θ`, and the ru-usc tolerance `η`; in particular its admissible radii can be reused as
`s → 1`. -/
theorem affineCutoff_extract_data_of_cited
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω O : Set (Sp N)}
    (hcompact : CitedSobolevCompact N m p) (hdiff : CitedSobolevDiff N m p)
    (hmeasure : CitedMeasureLimit N) (hp : (N : ℝ) < p)
    (hΩopen : IsOpen Ω) (hOopen : IsOpen O) (hOΩ : O ⊆ Ω)
    (hObounded : Bornology.IsBounded O)
    {G : Mat m N → ℝ≥0∞} {α β c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (hα : 0 < α) (hc₀ : 0 < c₀)
    (hLm : Measurable (uncurry L)) (hcoercive : IsCoercive p c₀ L)
    (hgrowth : HasGGrowth G α β L)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (ε : ℕ → ℝ) (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto uₙ atTop (𝓝 u)) {E ell : ℝ≥0∞}
    (hE : E < ⊤) (henergyBound : ∀ n, intFunOn L (ε n) O (uₙ n) ≤ E)
    (henergy : Tendsto (fun n => intFunOn L (ε n) O (uₙ n)) atTop (𝓝 ell))
    (hell : ell < ⊤) :
    ∃ φ : ℕ → ℕ, ∃ μ : Measure (Sp N), StrictMono φ ∧ IsFiniteMeasure μ ∧
      μ Oᶜ = 0 ∧
      (∀ U : Set (Sp N), IsOpen U → U ⊆ O →
        μ U ≤ liminf (fun n => intFunOn L (ε (φ n)) U (uₙ (φ n))) atTop) ∧
      (∀ K : Set (Sp N), IsCompact K → K ⊆ O →
        limsup (fun n => intFunOn L (ε (φ n)) K (uₙ (φ n))) atTop ≤ μ K) ∧
      (∫⁻ x in O, μ.rnDeriv volume x ≤ μ O ∧ μ O ≤ ell) ∧
      ∀ᵐ x ∂(volume.restrict O),
        ∃ a₀ : Tgt m,
          Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
            eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x) x y) ⊤
              (volume.restrict (cube ρ x))) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
          μ.rnDeriv volume x < ⊤ ∧
          Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
            (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) ∧
          (∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
            ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
              μ (frontier (cube (ρ k) x)) = 0 ∧
              Tendsto (fun n => intFunOn L (ε (φ n)) (cube (ρ k) x)
                (uₙ (φ n))) atTop (𝓝 (μ (cube (ρ k) x)))) ∧
          (u.grad x ∈ closure (dom G)) := by
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpnonneg : 0 ≤ p := hNnonneg.trans (le_of_lt hp)
  obtain ⟨Cgrad, hCgradTop, hCgrad⟩ :=
    hcoercive.sequence_grad_integral_bound hpnonneg hc₀ hOΩ hLm ε uₙ hE henergyBound
  have hdom : ∀ n, ∀ᵐ x ∂(volume.restrict O), (uₙ n).grad x ∈ dom G :=
    hgrowth.ae_mem_domOn_sequence hα hLm hOΩ ε uₙ hE henergyBound
  obtain ⟨φ, μ, hφ, hμfinite, hμO, hportOpen, hportCompact, hmass, hgood⟩ :=
    hmeasure.extract_energy_step1 hcompact hp hOΩ hOopen hObounded hG hLm ε uₙ u hu
      ⟨E, hE, henergyBound⟩ ⟨Cgrad, hCgradTop, hCgrad⟩ hdom ell hell henergy
  have hDiffΩ := hdiff hp Ω hΩopen u
  have hDiffO : ∀ᵐ x ∂(volume.restrict O), ∃ a₀ : Tgt m,
      Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
        eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x) x y) ⊤
          (volume.restrict (cube ρ x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact ae_restrict_of_subset (U := Ω) (V := O) (hVU := hOΩ) (hP := hDiffΩ)
  refine ⟨φ, μ, hφ, hμfinite, hμO, hportOpen, hportCompact, hmass, ?_⟩
  filter_upwards [hgood, hDiffO] with x hx hdx
  rcases hx with ⟨hf, hdensity, hrays, hgradx⟩
  rcases hdx with ⟨a₀, hDiffPoint⟩
  exact ⟨a₀, hDiffPoint, hf, hdensity, hrays, hgradx⟩

/-- For fixed `t,η`, choose one `θ` before quantifying over `s`. On one full-measure set, use
the same extracted affine slope and admissible radii for every `s`; the finite remainder bound
`M₀` is common to all `s` and is passed into each normalized limsup estimate. The `RUUSCWith c L`
input keeps `c` independent of `η`; this lemma selects the estimate at `θ` for the annulus. The
separate radial estimate at `t` is consumed by the fixed-scale interior comparison. -/
theorem affineCutoff_boundary_layer_of_cited
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω O : Set (Sp N)}
    (hcompact : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O) (hOΩ : O ⊆ Ω)
    {G : Mat m N → ℝ≥0∞} {α β c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hα : 0 < α) (hc₀ : 0 < c₀) (hLm : Measurable (uncurry L))
    (hcoercive : IsCoercive p c₀ L) (hgrowth : HasGGrowth G α β L)
    (hperiodic : IsPeriodic L)
    {c : ℝ≥0} (hc : 0 < c) (hruusc : RUUSCWith c L)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (ε : ℕ → ℝ) (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto uₙ atTop (𝓝 u)) {E : ℝ≥0∞}
    (hE : E < ⊤) (henergyBound : ∀ n, intFunOn L (ε n) O (uₙ n) ≤ E)
    (φ : ℕ → ℕ) (μ : Measure (Sp N)) (hφ : StrictMono φ)
    (hεpos : ∀ n, 0 < ε (φ n))
    [IsFiniteMeasure μ]
    (hportOpen : ∀ U : Set (Sp N), IsOpen U → U ⊆ O →
      μ U ≤ liminf (fun n => intFunOn L (ε (φ n)) U (uₙ (φ n))) atTop)
    (hgood : ∀ᵐ x ∂(volume.restrict O),
      ∃ a₀ : Tgt m,
        Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
          eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x) x y) ⊤
            (volume.restrict (cube ρ x))) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        μ.rnDeriv volume x < ⊤ ∧
        Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) ∧
        (∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
          ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
            μ (frontier (cube (ρ k) x)) = 0 ∧
            Tendsto (fun n => intFunOn L (ε (φ n)) (cube (ρ k) x)
              (uₙ (φ n))) atTop (𝓝 (μ (cube (ρ k) x)))) ∧
        u.grad x ∈ closure (dom G))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) {η : ℝ≥0} (hη : 0 < η)
    (hεscale : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hru_t : ∀ z ξ, L z (t • ξ) ≤
      (1 + (η : ℝ≥0∞)) * L z ξ + (η : ℝ≥0∞) * c) :
    0 < c ∧ ∃ θ : ℝ, t < θ ∧ θ < 1 ∧
      ∀ᵐ x ∂(volume.restrict O),
        ∃ a₀ : Tgt m, ∃ ρ : ℕ → ℝ, StrictAnti ρ ∧
          Tendsto ρ atTop (𝓝 0) ∧
          (∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
            μ (frontier (cube (ρ k) x)) = 0 ∧
            Tendsto (fun n => intFunOn L (ε (φ n)) (cube (ρ k) x)
              (uₙ (φ n))) atTop (𝓝 (μ (cube (ρ k) x)))) ∧
          (∃ M₀ : ℝ≥0∞, M₀ < ⊤ ∧
            (∀ (s' : ℝ) (hs' : s' ∈ Ioo (0 : ℝ) 1),
              ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
                ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ₀ → ∃ n₀ : ℕ,
                  ∀ n, n ≥ n₀ →
                    ∀ᵐ y ∂(volume.restrict (cube ρ' x \ cube (s' * ρ') x)),
                      G ((t / (1 - t / θ)) •
                        ((fderiv ℝ (cutoff hs' ρ' x) y).smulRight
                          ((uₙ (φ n)).toFun y - affineMap a₀ (u.grad x) x y))) ≤ M₀) ∧
          ∀ (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1),
            limsup (fun k => limsup (fun n =>
              (∫⁻ y in cube (ρ k) x \ cube (s * ρ k) x,
                L ((ε (φ n))⁻¹ • y)
                  (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a₀
                    (u.grad x) x hs (ρ k) x y)).toReal /
                (volume (cube (ρ k) x)).toReal) atTop) atTop ≤
              (1 - s ^ N) *
                (((β : ℝ≥0∞) *
                  (1 + M₀ + G (θ • u.grad x) +
                    (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal +
                  ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
                    (1 + (η : ℝ≥0∞))).toReal * (μ.rnDeriv volume x).toReal) ∧
            (∀ᶠ k in atTop,
              (Hp (ENNReal.ofReal p) L (t • u.grad x)).toReal ≤
                ((1 + (η : ℝ≥0∞)).toReal * (μ (cube (ρ k) x)).toReal /
                    (volume (cube (ρ k) x)).toReal) +
                  (((η : ℝ≥0∞) * c * volume (cube (s * ρ k) x)).toReal /
                    (volume (cube (ρ k) x)).toReal) +
                  ((β : ℝ≥0∞) *
                      (1 + M₀ + G (θ • u.grad x) +
                        (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal *
                    ((volume (cube (ρ k) x \ cube (s * ρ k) x)).toReal /
                      (volume (cube (ρ k) x)).toReal) +
                  ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
                      (1 + (η : ℝ≥0∞))).toReal *
                    ((μ (cube (ρ k) x \ cube (s * ρ k) x)).toReal /
                      (volume (cube (ρ k) x)).toReal)) ∧
            (Hp (ENNReal.ofReal p) L (t • u.grad x)).toReal ≤
              (1 + (η : ℝ≥0∞)).toReal * (μ.rnDeriv volume x).toReal +
                ((η : ℝ≥0∞) * c).toReal * s ^ N +
                ((β : ℝ≥0∞) *
                    (1 + M₀ + G (θ • u.grad x) +
                      (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal * (1 - s ^ N) +
                ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
                    (1 + (η : ℝ≥0∞))).toReal *
                  ((1 - s ^ N) * (μ.rnDeriv volume x).toReal) ∧
            ∀ᶠ k in atTop, ∃ n₀ : ℕ, ∀ n ≥ n₀,
              (∫⁻ y in cube (ρ k) x \ cube (s * ρ k) x,
                L ((ε (φ n))⁻¹ • y)
                  (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a₀
                    (u.grad x) x hs (ρ k) x y)) < ⊤) := by
  refine ⟨hc, ?_⟩
  obtain ⟨θ, htθ, hθ, hru⟩ :=
    RUUSC.exists_theta_le_affine (N := N) (m := m) hruusc ht1 hη
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpnonneg : 0 ≤ p := hNnonneg.trans (le_of_lt hp)
  obtain ⟨Cgrad, hCgradTop, hCgrad⟩ :=
    hcoercive.sequence_grad_integral_bound hpnonneg hc₀ hOΩ hLm ε uₙ hE henergyBound
  have hdom : ∀ n, ∀ᵐ x ∂(volume.restrict O), (uₙ n).grad x ∈ dom G :=
    hgrowth.ae_mem_domOn_sequence hα hLm hOΩ ε uₙ hE henergyBound
  have hgradφ : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n,
      ∫⁻ y in O, ‖(uₙ (φ n)).grad y‖ₑ ^ p ≤ C :=
    ⟨Cgrad, hCgradTop, fun n => hCgrad (φ n)⟩
  refine ⟨θ, htθ, hθ, ?_⟩
  filter_upwards [hgood, ae_restrict_mem hOopen.measurableSet] with x hx hxO
  rcases hx with ⟨a₀, hDiffPoint, hf, hdensity, ⟨ρ, hρanti, hρtend, hrays⟩, hgradx⟩
  have hremInputs : ∀ (s' : ℝ) (hs' : s' ∈ Ioo (0 : ℝ) 1),
      (∀ η' : ℝ, 0 < η' → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ₀ →
          ∀ᵐ y ∂(volume.restrict (cube ρ' x \ cube (s' * ρ') x)),
            ‖u.toFun y - affineMap a₀ (u.grad x) x y‖ ≤ η' * ρ') ∧
      (∀ η' : ℝ, 0 < η' → ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ₁ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
          ∀ᵐ y ∂(volume.restrict (cube ρ' x \ cube (s' * ρ') x)),
            ‖(uₙ (φ n)).toFun y - u.toFun y‖ ≤ η' * ρ') := by
    intro s' hs'
    have hrem' := affineCutoff_remainder_ae_small_of_cited
      (N := N) (m := m) hcompact hp hOopen hOΩ u (fun n => uₙ (φ n))
      (hu.comp hφ.tendsto_atTop) hgradφ hxO a₀ hDiffPoint hs'
      ht htθ hθ 1 (by norm_num)
    exact ⟨hrem'.1, hrem'.2.1⟩
  obtain ⟨M₀, hM₀, hM₀all⟩ :=
    hG.affineCutoff_remainder_ae_uniform_bound_all_s (N := N) (m := m)
      h0 u (fun n => uₙ (φ n)) a₀ (u.grad x) x ht htθ hθ
      (fun s' hs' => (hremInputs s' hs').1)
      (fun s' hs' => (hremInputs s' hs').2)
  let R : ℝ := Classical.choose (Metric.isOpen_iff.1 hOopen x hxO)
  have hR : 0 < R := (Classical.choose_spec
    (Metric.isOpen_iff.1 hOopen x hxO)).1
  have hballO : Metric.ball x R ⊆ O := (Classical.choose_spec
    (Metric.isOpen_iff.1 hOopen x hxO)).2
  have hball : ∀ r : ℝ, 0 < r → r < R → Metric.closedBall x (r / 2) ⊆ Ω := by
    intro r hr hrR y hy
    apply hOΩ
    apply hballO
    rw [Metric.mem_ball, dist_eq_norm]
    have hy' : dist y x ≤ r / 2 := Metric.mem_closedBall.mp hy
    rw [dist_eq_norm] at hy'
    exact hy'.trans_lt (by linarith)
  have hGθ : G (θ • u.grad x) < ⊤ := by
    have hint := hG.smul_mem_interior_dom h0 hgradx (le_of_lt (lt_trans ht htθ)) hθ
    have hdomθ : θ • u.grad x ∈ dom G := interior_subset hint
    simpa [dom] using hdomθ
  have hGt : G (t • u.grad x) < ⊤ := by
    have hint := hG.smul_mem_interior_dom h0 hgradx (le_of_lt ht) ht1
    have hdomt : t • u.grad x ∈ dom G := interior_subset hint
    simpa [dom] using hdomt
  refine ⟨a₀, ρ, hρanti, hρtend, hrays,
    ⟨M₀, hM₀, hM₀all, ?_⟩⟩
  intro s hs
  have hdomOnR : ∀ r : ℝ, 0 < r → r < R → ∀ n,
      ∀ᵐ y ∂(volume.restrict (cube r x \ cube (s * r) x)),
        (uₙ (φ n)).grad y ∈ dom G := by
    intro r hr hrR n
    have hS : cube r x \ cube (s * r) x ⊆ O := by
      intro y hy
      apply hballO
      have hycube : y ∈ cube r x := hy.1
      rw [cube_eq_ball hr] at hycube
      exact Metric.ball_subset_ball (by linarith) hycube
    exact ae_restrict_of_subset (U := O) (V := cube r x \ cube (s * r) x)
      (hVU := hS) (hP := hdom (φ n))
  have houter : ∀ k, Tendsto
      (fun n => ∫⁻ y in cube (ρ k) x,
        L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)) atTop
      (𝓝 (μ (cube (ρ k) x))) := by
    intro k
    simpa [intFunOn] using (hrays k).2.2.2
  have hinner : ∀ k, μ (cube (s * ρ k) x) ≤ liminf (fun n =>
      ∫⁻ y in cube (s * ρ k) x,
        L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)) atTop := by
    intro k
    have hinnerOpen : IsOpen (cube (s * ρ k) x) := isOpen_cube _ _
    have hinnerSub : cube (s * ρ k) x ⊆ O := by
      intro y hy
      have hout : y ∈ cube (ρ k) x := by
        simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
        intro i
        obtain ⟨hlo, hhi⟩ := hy i
        constructor <;> nlinarith [hs.2, (hrays k).1]
      exact (hrays k).2.1 (subset_closure hout)
    simpa [intFunOn] using hportOpen (cube (s * ρ k) x) hinnerOpen hinnerSub
  have hfinite : ∀ k n, (∫⁻ y in cube (ρ k) x,
      L ((ε (φ n))⁻¹ • y) ((uₙ (φ n)).grad y)) < ⊤ := by
    intro k n
    have hcubeO : cube (ρ k) x ⊆ O := fun y hy => (hrays k).2.1 (subset_closure hy)
    have hmono := (lintegral_mono_set hcubeO :
      intFunOn L (ε (φ n)) (cube (ρ k) x) (uₙ (φ n)) ≤
        intFunOn L (ε (φ n)) O (uₙ (φ n)))
    have hle : intFunOn L (ε (φ n)) (cube (ρ k) x) (uₙ (φ n)) ≤ E :=
      hmono.trans (henergyBound (φ n))
    have hfinite' : intFunOn L (ε (φ n)) (cube (ρ k) x) (uₙ (φ n)) < ⊤ :=
      lt_of_le_of_lt hle hE
    simpa [intFunOn] using hfinite'
  obtain ⟨ρrem, hρrem, hM₀s⟩ := hM₀all s hs
  have hM₀cert : ∃ ρrem : ℝ, 0 < ρrem ∧
      ∀ r : ℝ, 0 < r → r < ρrem → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ᵐ y ∂(volume.restrict (cube r x \ cube (s * r) x)),
          G ((t / (1 - t / θ)) •
            ((fderiv ℝ (cutoff hs r x) y).smulRight
              ((uₙ (φ n)).toFun y - affineMap a₀ (u.grad x) x y))) ≤ M₀ :=
    ⟨ρrem, hρrem, hM₀s⟩
  obtain ⟨ρfin, hρfin, hρfinmax, hcutFinite⟩ :=
    affineCutoff_annulus_energy_finite_eventually
      (N := N) (m := m) hG hgrowth hα h0 hLm hΩopen hΩbounded
      (fun n => uₙ (φ n)) a₀ (u.grad x) x hs (ρmax := R) hR hball hdomOnR
      ht htθ hθ hM₀ hM₀cert (fun n => ε (φ n)) hru hGθ
  have hρevent : ∀ᶠ k in atTop, ρ k < ρfin ∧ ρ k < R := by
    filter_upwards [hρtend.eventually (Iio_mem_nhds hρfin),
      hρtend.eventually (Iio_mem_nhds hR)] with k hkfin hkR
    exact ⟨hkfin, hkR⟩
  have hcutFiniteRadii : ∀ᶠ k in atTop, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (∫⁻ y in cube (ρ k) x \ cube (s * ρ k) x,
        L ((ε (φ n))⁻¹ • y)
          (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a₀
            (u.grad x) x hs (ρ k) x y)) < ⊤ := by
    filter_upwards [hρevent] with k ⟨hkfin, hkR⟩
    exact hcutFinite (ρ k) (hrays k).1 hkfin (hfinite k)
  have hresult := affineCutoff_uniform_eps_limsup_normalized
    (N := N) (m := m) (μ := μ) hG hgrowth hα h0 hLm hΩopen hΩbounded
    (fun n => uₙ (φ n)) a₀ (u.grad x) x hs hR hball hdomOnR ht htθ hθ
    hM₀ hM₀cert (fun n => ε (φ n)) hru hf hdensity ρ
    (fun k => (hrays k).1) hρtend houter hinner hfinite hGθ
  have hHpEvent : ∀ᶠ k in atTop,
      (Hp (ENNReal.ofReal p) L (t • u.grad x)).toReal ≤
        ((1 + (η : ℝ≥0∞)).toReal * (μ (cube (ρ k) x)).toReal /
            (volume (cube (ρ k) x)).toReal) +
          (((η : ℝ≥0∞) * c * volume (cube (s * ρ k) x)).toReal /
            (volume (cube (ρ k) x)).toReal) +
          ((β : ℝ≥0∞) *
              (1 + M₀ + G (θ • u.grad x) +
                (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal *
            ((volume (cube (ρ k) x \ cube (s * ρ k) x)).toReal /
              (volume (cube (ρ k) x)).toReal) +
          ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
              (1 + (η : ℝ≥0∞))).toReal *
            ((μ (cube (ρ k) x \ cube (s * ρ k) x)).toReal /
              (volume (cube (ρ k) x)).toReal) := by
    filter_upwards [hρevent, hcutFiniteRadii, hresult.2] with k hkρ hkcut hfix
    rcases hkρ with ⟨hkfin, hkR⟩
    rcases hkcut with ⟨n₀, hn₀⟩
    rcases hfix with ⟨hbounded, hlimsup⟩
    have hcell := Ytp_cell_ratio_tendsto_Hp_subsequence
      (N := N) (m := m) (p := ENNReal.ofReal p) hperiodic hgrowth hGt
      (hrays k).1 x ε φ hεscale hφ.tendsto_atTop
    have hballk := hball (ρ k) (hrays k).1 hkR
    have hcutFinite : ∀ᶠ n in atTop,
        (∫⁻ y in cube (ρ k) x \ cube (s * ρ k) x,
          L ((ε (φ n))⁻¹ • y)
            (t • affineCutoffGrad (N := N) (m := m) (uₙ (φ n)) a₀
              (u.grad x) x hs (ρ k) x y)) < ⊤ :=
      Filter.eventually_atTop.2 ⟨n₀, hn₀⟩
    have hcellBound := affineCutoff_cell_ratio_le_of_limsup_annulus
      (N := N) (m := m) hG hgrowth h0 hΩopen hΩbounded uₙ a₀ (u.grad x) x hgradx
      ht ht1 hs (ρ := ρ k) (hrays k).1 ε φ hεpos hballk hru_t
      (houter k) (hfinite k) hcutFinite hcell hbounded hlimsup
    simpa [add_assoc] using hcellBound
  let Q : ℕ → Set (Sp N) := fun k => cube (ρ k) x
  let S : ℕ → Set (Sp N) := fun k => Q k \ cube (s * ρ k) x
  let U₁ : ℕ → ℝ := fun k =>
    (1 + (η : ℝ≥0∞)).toReal * (μ (Q k)).toReal /
      (volume (Q k)).toReal
  let U₂ : ℕ → ℝ := fun k =>
    (((η : ℝ≥0∞) * c * volume (cube (s * ρ k) x)).toReal /
      (volume (Q k)).toReal)
  let U₃ : ℕ → ℝ := fun k =>
    ((β : ℝ≥0∞) *
        (1 + M₀ + G (θ • u.grad x) +
          (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal *
      ((volume (S k)).toReal / (volume (Q k)).toReal)
  let U₄ : ℕ → ℝ := fun k =>
    ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
        (1 + (η : ℝ≥0∞))).toReal *
      ((μ (S k)).toReal / (volume (Q k)).toReal)
  let U : ℕ → ℝ := fun k => U₁ k + U₂ k + U₃ k + U₄ k
  have hρwithin : Tendsto ρ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ρ hρtend
      (Filter.Eventually.of_forall fun k => (hrays k).1)
  have hdensityρ : Tendsto
      (fun k => (μ (cube (ρ k) x) / volume (cube (ρ k) x)).toReal) atTop
      (𝓝 (μ.rnDeriv volume x).toReal) :=
    (ENNReal.tendsto_toReal hf.ne).comp (hdensity.comp hρwithin)
  have hratio_outer : ∀ k,
      (μ (cube (ρ k) x)).toReal / (volume (cube (ρ k) x)).toReal =
        (μ (cube (ρ k) x) / volume (cube (ρ k) x)).toReal := by
    intro k
    rw [ENNReal.toReal_div]
  have hterm₁ : Tendsto (fun k =>
      (1 + (η : ℝ≥0∞)).toReal * (μ (cube (ρ k) x)).toReal /
        (volume (cube (ρ k) x)).toReal)
      atTop (𝓝 ((1 + (η : ℝ≥0∞)).toReal *
        (μ.rnDeriv volume x).toReal)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (1 + (η : ℝ≥0∞)).toReal) atTop
        (𝓝 ((1 + (η : ℝ≥0∞)).toReal))).mul hdensityρ
    have heq : (fun k => (1 + (η : ℝ≥0∞)).toReal *
        (μ (cube (ρ k) x)).toReal / (volume (cube (ρ k) x)).toReal) =
        fun k => (1 + (η : ℝ≥0∞)).toReal *
          (μ (cube (ρ k) x) / volume (cube (ρ k) x)).toReal := by
      funext k
      calc
        _ = (1 + (η : ℝ≥0∞)).toReal *
            ((μ (cube (ρ k) x)).toReal / (volume (cube (ρ k) x)).toReal) := by
          have hV : 0 < (volume (cube (ρ k) x)).toReal := by
            rw [volume_cube, ENNReal.toReal_pow,
              ENNReal.toReal_ofReal ((hrays k).1).le]
            exact pow_pos (hrays k).1 _
          field_simp [ne_of_gt hV]
        _ = (1 + (η : ℝ≥0∞)).toReal *
            (μ (cube (ρ k) x) / volume (cube (ρ k) x)).toReal := by
          rw [hratio_outer]
    rw [heq]
    exact h
  have hinnerRatio : Tendsto (fun k =>
      (volume (cube (s * ρ k) x)).toReal /
        (volume (cube (ρ k) x)).toReal) atTop (𝓝 (s ^ N)) := by
    have heq : (fun k => (volume (cube (s * ρ k) x)).toReal /
        (volume (cube (ρ k) x)).toReal) = fun _ => s ^ N := by
      funext k
      exact volume_cube_inner_ratio (N := N) ((hrays k).1) hs x
    rw [heq]
    exact tendsto_const_nhds
  have hCη : (η : ℝ≥0∞) * c < ⊤ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top
  have hterm₂ : Tendsto (fun k =>
      (((η : ℝ≥0∞) * c * volume (cube (s * ρ k) x)).toReal /
        (volume (cube (ρ k) x)).toReal)) atTop
      (𝓝 (((η : ℝ≥0∞) * c).toReal * s ^ N)) := by
    have heq : (fun k =>
        (((η : ℝ≥0∞) * c * volume (cube (s * ρ k) x)).toReal /
          (volume (cube (ρ k) x)).toReal)) = fun k =>
        ((η : ℝ≥0∞) * c).toReal *
          ((volume (cube (s * ρ k) x)).toReal /
            (volume (cube (ρ k) x)).toReal) := by
      funext k
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
      ring
    rw [heq]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      ((η : ℝ≥0∞) * c).toReal) atTop
      (𝓝 (((η : ℝ≥0∞) * c).toReal))).mul hinnerRatio
  have hvolAnnulus : Tendsto (fun k =>
      (volume (S k)).toReal / (volume (Q k)).toReal) atTop
      (𝓝 (1 - s ^ N)) := by
    have heq : (fun k => (volume (S k)).toReal / (volume (Q k)).toReal) =
        fun _ => 1 - s ^ N := by
      funext k
      exact volume_cube_annulus_ratio (N := N) ((hrays k).1) hs x
    rw [heq]
    exact tendsto_const_nhds
  have hmeasureAnnulus₀ := tendsto_measure_cube_annulus_ratio
    (N := N) hs x hf hdensity
  have hmeasureAnnulus : Tendsto (fun k =>
      (μ (S k)).toReal / (volume (Q k)).toReal) atTop
      (𝓝 ((1 - s ^ N) * (μ.rnDeriv volume x).toReal)) := by
    have heq : (fun k => (μ (S k) / volume (Q k)).toReal) = fun k =>
        (μ (S k)).toReal / (volume (Q k)).toReal := by
      funext k
      rw [ENNReal.toReal_div]
    have h := hmeasureAnnulus₀.comp hρwithin
    have h' : Tendsto (fun k => (μ (cube (ρ k) x \ cube (s * ρ k) x) /
        volume (cube (ρ k) x)).toReal) atTop
        (𝓝 ((1 - s ^ N) * (μ.rnDeriv volume x).toReal)) := h
    rw [heq] at h'
    exact h'
  have hC := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      ((β : ℝ≥0∞) * (1 + M₀ + G (θ • u.grad x) +
        (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal) atTop
        (𝓝 ((β : ℝ≥0∞) * (1 + M₀ + G (θ • u.grad x) +
        (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal)).mul hvolAnnulus
  have hD := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
        (1 + (η : ℝ≥0∞))).toReal) atTop
        (𝓝 ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
        (1 + (η : ℝ≥0∞))).toReal)).mul hmeasureAnnulus
  have hU : Tendsto U atTop (𝓝
      ((1 + (η : ℝ≥0∞)).toReal * (μ.rnDeriv volume x).toReal +
        ((η : ℝ≥0∞) * c).toReal * s ^ N +
        ((β : ℝ≥0∞) *
          (1 + M₀ + G (θ • u.grad x) +
            (α : ℝ≥0∞)⁻¹ * (η : ℝ≥0∞) * c)).toReal * (1 - s ^ N) +
        ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
          (1 + (η : ℝ≥0∞))).toReal *
          ((1 - s ^ N) * (μ.rnDeriv volume x).toReal))) := by
    change Tendsto (fun k => U₁ k + U₂ k + U₃ k + U₄ k) atTop _
    change Tendsto U₁ atTop _ at hterm₁
    change Tendsto U₂ atTop _ at hterm₂
    change Tendsto U₃ atTop _ at hC
    change Tendsto U₄ atTop _ at hD
    exact (((hterm₁.add hterm₂).add hC).add hD)
  have hHpEventU : (fun _ : ℕ =>
      (Hp (ENNReal.ofReal p) L (t • u.grad x)).toReal) ≤ᶠ[atTop] U := by
    filter_upwards [hHpEvent] with k hk
    simpa [U, U₁, U₂, U₃, U₄, Q, S] using hk
  have hHpLimit := le_of_tendsto_of_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (Hp (ENNReal.ofReal p) L (t • u.grad x)).toReal) atTop
        (𝓝 ((Hp (ENNReal.ofReal p) L (t • u.grad x)).toReal)))
    hU hHpEventU
  exact ⟨hresult.1, hHpEvent, hHpLimit, hcutFiniteRadii⟩

/-- Assemble the fixed-parameter cut-off estimates into the pointwise density inequality. The
ru-usc constant is selected once, before the tolerance sequence; the good sets for each pair
`(t j, η j)` are intersected by `ae_nat_forall`, and `lsc_of_HW` supplies the radial limit. -/
theorem affineCutoff_pointwise_density_of_cited
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω O : Set (Sp N)}
    (hcompact : CitedSobolevCompact N m p) (hp : (N : ℝ) < p)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O) (hOΩ : O ⊆ Ω)
    {G : Mat m N → ℝ≥0∞} {α β c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hα : 0 < α) (hc₀ : 0 < c₀) (hLm : Measurable (uncurry L))
    (hcoercive : IsCoercive p c₀ L) (hgrowth : HasGGrowth G α β L)
    (hperiodic : IsPeriodic L) (hruusc : RUUSC L)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (ε : ℕ → ℝ) (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hu : Tendsto uₙ atTop (𝓝 u)) {E : ℝ≥0∞}
    (hE : E < ⊤) (henergyBound : ∀ n, intFunOn L (ε n) O (uₙ n) ≤ E)
    (φ : ℕ → ℕ) (μ : Measure (Sp N)) (hφ : StrictMono φ)
    (hεpos : ∀ n, 0 < ε (φ n)) [IsFiniteMeasure μ]
    (hportOpen : ∀ U : Set (Sp N), IsOpen U → U ⊆ O →
      μ U ≤ liminf (fun n => intFunOn L (ε (φ n)) U (uₙ (φ n))) atTop)
    (hgood : ∀ᵐ x ∂(volume.restrict O),
      ∃ a₀ : Tgt m,
        Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ⁻¹ *
          eLpNorm (fun y => u.toFun y - affineMap a₀ (u.grad x) x y) ⊤
            (volume.restrict (cube ρ x))) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        μ.rnDeriv volume x < ⊤ ∧
        Tendsto (fun ρ : ℝ => μ (cube ρ x) / volume (cube ρ x))
          (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) ∧
        (∃ ρ : ℕ → ℝ, StrictAnti ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
          ∀ k, 0 < ρ k ∧ closure (cube (ρ k) x) ⊆ O ∧
            μ (frontier (cube (ρ k) x)) = 0 ∧
            Tendsto (fun n => intFunOn L (ε (φ n)) (cube (ρ k) x)
              (uₙ (φ n))) atTop (𝓝 (μ (cube (ρ k) x)))) ∧
        u.grad x ∈ closure (dom G))
    (hεscale : Tendsto ε atTop (𝓝[>] (0 : ℝ))) :
    ∀ᵐ x ∂(volume.restrict O),
      radial (Hp (ENNReal.ofReal p) L) (u.grad x) ≤ μ.rnDeriv volume x := by
  obtain ⟨c, hc, hruWith, _⟩ := hruusc.radial_interval_le_affine (N := N) (m := m)
  obtain ⟨η, t, hη, ht, hηpos, htpos, hruSeq⟩ :=
    hruWith.exists_tolerance_and_radial_sequences (N := N) (m := m)
  have hparameter : ∀ j, ∀ᵐ x ∂(volume.restrict O),
      μ.rnDeriv volume x < ⊤ ∧ u.grad x ∈ closure (dom G) ∧
        (Hp (ENNReal.ofReal p) L (t j • u.grad x)).toReal ≤
          (1 + (η j).toReal) * (μ.rnDeriv volume x).toReal +
            (η j).toReal * c.toReal := by
    intro j
    obtain ⟨_, θ, htθ, hθ, hboundary⟩ :=
      affineCutoff_boundary_layer_of_cited (N := N) (m := m)
        hcompact hp hΩopen hΩbounded hOopen hOΩ hG h0 hα hc₀ hLm hcoercive hgrowth
        hperiodic hc hruWith u ε uₙ hu hE henergyBound φ μ hφ hεpos hportOpen hgood
        (htpos j).1 (htpos j).2 (hηpos j) hεscale (hruSeq j)
    filter_upwards [hboundary, hgood] with x hbx hx
    rcases hx with ⟨a₀, hdiff, hf, hdensity, hrays, hgradx⟩
    rcases hbx with ⟨a₁, ρ, hanti, hρtend, hrays', M₀, hM₀, hM₀all, hboundAll⟩
    have hbound : ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
        (Hp (ENNReal.ofReal p) L (t j • u.grad x)).toReal ≤
          (1 + (η j : ℝ≥0∞)).toReal * (μ.rnDeriv volume x).toReal +
            ((η j : ℝ≥0∞) * c).toReal * s ^ N +
            ((β : ℝ≥0∞) *
              (1 + M₀ + G (θ • u.grad x) +
                (α : ℝ≥0∞)⁻¹ * (η j : ℝ≥0∞) * c)).toReal * (1 - s ^ N) +
            ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
              (1 + (η j : ℝ≥0∞))).toReal *
                ((1 - s ^ N) * (μ.rnDeriv volume x).toReal) := by
      intro s hs
      exact (hboundAll s hs).2.2.1
    have hηbound := hp_toReal_le_ruusc_bound_of_uniform_s
      (N := N) (m := m) (q := ENNReal.ofReal p) (L := L) (ξ := t j • u.grad x)
      (f := μ.rnDeriv volume x) (c := c) (η := η j)
      (D := ((β : ℝ≥0∞) *
        (1 + M₀ + G (θ • u.grad x) +
          (α : ℝ≥0∞)⁻¹ * (η j : ℝ≥0∞) * c)).toReal)
      (B := ((β : ℝ≥0∞) * (α : ℝ≥0∞)⁻¹ *
        (1 + (η j : ℝ≥0∞))).toReal) hbound
    have hcoeff : (1 + (η j : ℝ≥0∞)).toReal = 1 + (η j).toReal := by
      rw [ENNReal.toReal_add ENNReal.one_ne_top ENNReal.coe_ne_top]
      simp
    have herr : ((η j : ℝ≥0∞) * c).toReal = (η j).toReal * c.toReal := by
      rw [ENNReal.toReal_mul]
      simp
    exact ⟨hf, hgradx, by
      rw [hcoeff, herr] at hηbound
      exact hηbound⟩
  have hparameterAll := ae_nat_forall hparameter
  filter_upwards [hgood, hparameterAll] with x hx hparams
  rcases hx with ⟨a₀, hdiff, hf, hdensity, hrays, hgradx⟩
  have hfinite : ∀ j, Hp (ENNReal.ofReal p) L (t j • u.grad x) < ⊤ := by
    intro j
    have hint := hG.smul_mem_interior_dom h0 hgradx
      (le_of_lt (htpos j).1) (htpos j).2
    have hdomt : t j • u.grad x ∈ dom G := interior_subset hint
    have hGt : G (t j • u.grad x) < ⊤ := by simpa [dom] using hdomt
    exact lt_of_le_of_lt (hgrowth.Hp_le (ENNReal.ofReal p) (t j • u.grad x))
      (ENNReal.mul_lt_top (by simp)
        (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hGt⟩))
  have hbound : ∀ j,
      (Hp (ENNReal.ofReal p) L (t j • u.grad x)).toReal ≤
        (1 + (η j).toReal) * (μ.rnDeriv volume x).toReal +
          (η j).toReal * c.toReal := fun j => (hparams j).2.2
  exact radial_Hp_le_of_ruusc_sequence_bounds (N := N) (m := m)
    (q := ENNReal.ofReal p) (c := (c : ℝ≥0∞))
    hruusc ht hη hf hfinite hbound

/-- For a sequence with uniformly finite energy and a finite energy limit, the pointwise density
bound integrates to the local lower bound. The measure, subsequence, and good-point data are
extracted once by `affineCutoff_extract_data_of_cited`. -/
theorem localLowerBound_sequence_of_cited
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω O : Set (Sp N)}
    (hcompact : CitedSobolevCompact N m p) (hdiff : CitedSobolevDiff N m p)
    (hmeasure : CitedMeasureLimit N) (hp : (N : ℝ) < p)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O) (hOΩ : O ⊆ Ω) (hObounded : Bornology.IsBounded O)
    {G : Mat m N → ℝ≥0∞} {α β c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hα : 0 < α) (hc₀ : 0 < c₀) (hLm : Measurable (uncurry L))
    (hcoercive : IsCoercive p c₀ L) (hgrowth : HasGGrowth G α β L)
    (hperiodic : IsPeriodic L) (hruusc : RUUSC L)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (ε : ℕ → ℝ) (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hεpos : ∀ n, 0 < ε n) (hεscale : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hu : Tendsto uₙ atTop (𝓝 u))
    {E ell : ℝ≥0∞} (hE : E < ⊤)
    (henergyBound : ∀ n, intFunOn L (ε n) O (uₙ n) ≤ E)
    (henergy : Tendsto (fun n => intFunOn L (ε n) O (uₙ n)) atTop (𝓝 ell))
    (hell : ell < ⊤) :
    ∫⁻ x in O, radial (Hp (ENNReal.ofReal p) L) ((u.grad) x) ≤ ell := by
  obtain ⟨φ, μ, hφ, hμfinite, hμO, hportOpen, _, hmass, hgood⟩ :=
    affineCutoff_extract_data_of_cited (N := N) (m := m)
      hcompact hdiff hmeasure hp hΩopen hOopen hOΩ
      hObounded hG hα hc₀ hLm hcoercive hgrowth u ε uₙ hu hE henergyBound henergy hell
  have : IsFiniteMeasure μ := hμfinite
  have hpoint := affineCutoff_pointwise_density_of_cited (N := N) (m := m)
    hcompact hp hΩopen hΩbounded
    hOopen hOΩ hG h0 hα hc₀ hLm hcoercive hgrowth hperiodic hruusc u ε uₙ hu
    hE henergyBound φ μ hφ (fun n => hεpos (φ n)) hportOpen hgood hεscale
  calc
    ∫⁻ x in O, radial (Hp (ENNReal.ofReal p) L) (u.grad x)
        ≤ ∫⁻ x in O, μ.rnDeriv volume x := lintegral_mono_ae hpoint
    _ ≤ μ O := hmass.1
    _ ≤ ell := hmass.2

/-- The local lower bound for any sequence whose energies converge to a finite value. A finite
initial segment may have infinite energy, so shift past it before applying the uniform-bound
version; the shift preserves all limits and positivity assumptions. -/
theorem localLowerBound_of_sequence_of_cited
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {Ω O : Set (Sp N)}
    (hcompact : CitedSobolevCompact N m p) (hdiff : CitedSobolevDiff N m p)
    (hmeasure : CitedMeasureLimit N) (hp : (N : ℝ) < p)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O) (hOΩ : O ⊆ Ω) (hObounded : Bornology.IsBounded O)
    {G : Mat m N → ℝ≥0∞} {α β c₀ : ℝ≥0} {L : Sp N → Mat m N → ℝ≥0∞}
    (hG : ConvexENN G) (h0 : (0 : Mat m N) ∈ interior (dom G))
    (hα : 0 < α) (hc₀ : 0 < c₀) (hLm : Measurable (uncurry L))
    (hcoercive : IsCoercive p c₀ L) (hgrowth : HasGGrowth G α β L)
    (hperiodic : IsPeriodic L) (hruusc : RUUSC L)
    (u : W1p N m (ENNReal.ofReal p) Ω)
    (ε : ℕ → ℝ) (uₙ : ℕ → W1p N m (ENNReal.ofReal p) Ω)
    (hεpos : ∀ n, 0 < ε n) (hεscale : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hu : Tendsto uₙ atTop (𝓝 u)) {ell : ℝ≥0∞}
    (henergy : Tendsto (fun n => intFunOn L (ε n) O (uₙ n)) atTop (𝓝 ell))
    (hell : ell < ⊤) :
    ∫⁻ x in O, radial (Hp (ENNReal.ofReal p) L) (u.grad x) ≤ ell := by
  have hboundEventually : ∀ᶠ n in atTop,
      intFunOn L (ε n) O (uₙ n) ≤ ENNReal.ofReal (ell.toReal + 1) := by
    have hlt : ell < ENNReal.ofReal (ell.toReal + 1) := by
      calc
        ell = ENNReal.ofReal ell.toReal := (ENNReal.ofReal_toReal hell.ne).symm
        _ < ENNReal.ofReal (ell.toReal + 1) :=
          ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2 (by linarith)
    filter_upwards [henergy.eventually (Iio_mem_nhds hlt)] with n hn
    exact hn.le
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hboundEventually
  let shift : ℕ → ℕ := fun n => n + n₀
  have hshift : Tendsto shift atTop atTop := tendsto_add_atTop_nat n₀
  have henergyBound : ∀ n,
      intFunOn L (ε (shift n)) O (uₙ (shift n)) ≤
        ENNReal.ofReal (ell.toReal + 1) := by
    intro n
    exact hn₀ (shift n) (by dsimp [shift]; omega)
  exact localLowerBound_sequence_of_cited (N := N) (m := m)
    hcompact hdiff hmeasure hp hΩopen hΩbounded
    hOopen hOΩ hObounded hG h0 hα hc₀ hLm hcoercive hgrowth hperiodic hruusc u
    (fun n => ε (shift n)) (fun n => uₙ (shift n))
    (fun n => hεpos (shift n)) (hεscale.comp hshift) (hu.comp hshift)
    (E := ENNReal.ofReal (ell.toReal + 1)) (ell := ell)
    ENNReal.ofReal_lt_top
    henergyBound (henergy.comp hshift) hell

/-- Proposition 2.1(i), in its local form: the integral of the radial cell formula on `O` is
bounded by the local Γ-liminf. The proof reduces the Γ-liminf to a sequence, shifts past any
initial infinite-energy terms, extracts the energy measure, applies the pointwise density bound,
and integrates it. -/
theorem localLowerBound_of_cited {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hcompact : CitedSobolevCompact N m p) (hdiff : CitedSobolevDiff N m p)
    (hmeasure : CitedMeasureLimit N) : LocalLowerBoundStatement N m p := by
  intro hp Ω hΩopen hΩbounded hΩne hΩlip O hOopen hOΩ G α β c₀ L hG h0 hα hc₀ hLm
    hperiodic hcoercive hgrowth hruusc u
  let Φ : ℝ≥0∞ := ∫⁻ x in O, radial (Hp (ENNReal.ofReal p) L) (u.grad x)
  let F : ℝ → W1p N m (ENNReal.ofReal p) Ω → ℝ≥0∞ :=
    fun ε v => intFunOn L ε O v
  apply le_GammaLiminf_of_seq F u Φ
  intro ε v ell hεpos hεscale hv hell henergy
  have hObounded : Bornology.IsBounded O := hΩbounded.subset hOΩ
  have hseq := localLowerBound_of_sequence_of_cited (N := N) (m := m)
    hcompact hdiff hmeasure hp
    hΩopen hΩbounded hOopen hOΩ hObounded
    hG h0 hα hc₀ hLm hcoercive hgrowth hperiodic hruusc u ε v hεpos hεscale hv
    henergy hell
  simpa [F, Φ, Iminus, LocalLowerBoundStatement] using hseq

end Statements

/-- Consistency check: `LowerBoundStatement` is exactly the Γ-liminf half of `CitedAHM14`. -/
theorem CitedAHM14.lowerBound {N m : ℕ} [NeZero N] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (h : CitedAHM14 N m p) : LowerBoundStatement N m p :=
  fun hp Ω hΩo hΩb hΩne hΩL G α β c₀ L hG h0 hα hc₀ hLm hLp hLc hLg hLr u =>
    (h hp Ω hΩo hΩb hΩne hΩL G α β c₀ L hG h0 hα hc₀ hLm hLp hLc hLg hLr u).1

/-- The local lower bound implies the whole-domain one (take `O = Ω`; `Iminus L Ω u` is
`GammaLiminf (intFun L) u` by definition). -/
theorem LocalLowerBoundStatement.lowerBound {N m : ℕ} [NeZero N] {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (h : LocalLowerBoundStatement N m p) :
    LowerBoundStatement N m p :=
  fun hp Ω hΩo hΩb hΩne hΩL G α β c₀ L hG h0 hα hc₀ hLm hLp hLc hLg hLr u =>
    h hp Ω hΩo hΩb hΩne hΩL Ω hΩo subset_rfl G α β c₀ L hG h0 hα hc₀ hLm hLp hLc hLg hLr u

end Homogenization
