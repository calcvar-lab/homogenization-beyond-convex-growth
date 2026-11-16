import Homogenization.GammaConvergence
import Homogenization.Jensen

/-!
# The main theorem (Theorem `main-Ggrowth`)

Formal statement of Theorem `main-Ggrowth` of `Homogenization_beyond_convex_growthV1.tex` and its
proof, **conditional on explicitly stated results** that are not formalized here. No `axiom` and
no `sorry` is used: every unformalized ingredient is a hypothesis of `main_Ggrowth`, whose type is
a `Prop`-valued definition below.

* Results cited from other papers (not proved in the paper either):
  - `CitedAHM14` — Theorem `th:AHM11` ([oah-jpm-zorgati14, Theorem 1.1]);
  - `CitedAffineApprox` — Proposition `approx-affine-etoile-cite` ([oah-jpm11, Prop. 3.15]),
    since proved as `citedAffineApprox_holds` (`AffineApprox.lean`);
  - `CitedZaffLocLip` — Proposition `Zenvelopefacts-cite` (i) ([fonseca88]; its proof in the
    appendix of the paper itself relies on two further cited results).
* Steps 3 and 4 appear here as hypotheses `Step3Statement` and `Step4Statement`; they are
  **proved** in `Homogenization.Step3` (`step3`) and `Homogenization.Step4` (`step4`), together
  with Proposition `prop:densityHaff` (`Homogenization.DensityHaff`) and the half of Proposition
  `prop:densityZaff` used in Step 3 (`Homogenization.DensityZaff`). Step 4 uses Theorem
  `Vitali-envelope-cite` ([oah-cloz-jpm17, Thm. A.16]) as the hypothesis `CitedVitaliEnvelope`.
* **`main_Ggrowth_final`** (in `Homogenization.DensityZaff`) is a conditional formalization of the
  main theorem: its proof uses (Z1)–(Z8), the standing assumptions, and four results supplied as
  hypotheses: `CitedAHM14`, `CitedAffineApprox`, `CitedVitaliEnvelope` and `CitedZaffLocLip`.
  Their interfaces and dependencies are listed below.
* Three of them are now proved in Lean, in files downstream of this one: `CitedAHM14`
  (`citedAHM14_holds`), `CitedAffineApprox` (`citedAffineApprox_holds`) and `CitedZaffLocLip`
  (`citedZaffLocLip`). `CitedVitaliEnvelope` is replaced by the proved inequality
  `vitaliEnvelopeUpper`, which is all that Step 4 needs; it is itself proved, downstream, by
  `citedVitaliEnvelope_holds` (`VitaliEquality.lean`). The theorems of this file
  keep these results as hypotheses; the main theorem without cited hypothesis is
  `main_Ggrowth_final_unconditional` (`AHM14.lean`).

The Γ-convergence logic of Steps 1, 2 and 5 is `gammaConverges_of_steps`; this file also proves
the inequality `𝒴_loc I_ε ≤ I_ε` of Step 1 from (Z7), the verification of the hypotheses of the
cited theorems (periodicity, growth, ru-usc, continuity of `Λ`), and the use of (Z8).

## A remark on the statement of the cited results

* `CitedAffineApprox` and `CitedZaffLocLip` are stated without Borel measurability of the
  integrand: the paper applies them to `Λ = 𝒵_aff ℋ_aff(𝒴_loc W)` and to `ℋ_aff(𝒴_loc W)`, whose
  Borel measurability is not established there. For `CitedZaffLocLip` this is harmless (for
  `θ = Aff` the integrand `L(ξ + ∇φ)` is a.e. a simple function). For `CitedAffineApprox`, the
  paper explains (after Proposition `approx-affine-etoile-cite`) that the proof only uses the
  measurability of `L` on `int(dom G)`, where `L` is continuous: dilation, mollification and
  piecewise affine interpolation keep the gradients in `s · cl(dom G) ⊂ int(dom G)`. This is the
  argument of `citedAffineApprox_holds` (`AffineApprox.lean`).
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- The standing hypotheses (Z1)–(Z8) of §3.2 on `G` and `W`, the exponent being `p`. -/
structure Hypotheses (p : ℝ) (G : Mat m N → ℝ≥0∞) (W : Sp N → Mat m N → ℝ≥0∞) : Prop where
  measurable_G : Measurable G
  measurable_W : Measurable (uncurry W)
  /-- (Z1) -/
  convex : ConvexENN G
  lsc : LowerSemicontinuous G
  zero_mem_interior : (0 : Mat m N) ∈ interior (dom G)
  /-- (Z2) -/
  periodic : IsPeriodic W
  /-- (Z3) -/
  setGrowth : ∃ α β : ℝ≥0, 0 < α ∧ 0 < β ∧ ∀ ξ (U : Set (Sp N)), IsOpen U →
    Bornology.IsBounded U →
      (α : ℝ≥0∞) * volume U * G ξ ≤ Yt W U ξ ∧ Yt W U ξ ≤ β * volume U * (1 + G ξ)
  /-- (Z4) -/
  coercive : ∃ c₀ : ℝ≥0, 0 < c₀ ∧ IsCoercive p c₀ (Ytloc W)
  /-- (Z5) -/
  ruusc : RUUSC (Ytloc W)
  /-- (Z6) -/
  measurable_Ytloc : Measurable (uncurry (Ytloc W))
  /-- (Z7) -/
  Ytloc_le : ∀ᵐ x, ∀ ξ, Ytloc W x ξ ≤ W x ξ
  /-- (Z8) -/
  Zaff_Haff_le : ∀ ξ, Zaff (Haff (Ytloc W)) ξ ≤ radial (Hp (ENNReal.ofReal p) (Ytloc W)) ξ

/-- The density `Λ = 𝒵_aff ℋ_aff(𝒴_loc W)` delivered by the recovery sequence. -/
noncomputable def Λ (W : Sp N → Mat m N → ℝ≥0∞) : Mat m N → ℝ≥0∞ := Zaff (Haff (Ytloc W))

/-- The homogenized density `\widehat{ℋ(𝒴_loc W)}`. -/
noncomputable def Whom (p : ℝ) (W : Sp N → Mat m N → ℝ≥0∞) : Mat m N → ℝ≥0∞ :=
  radial (Hp (ENNReal.ofReal p) (Ytloc W))

section Statements

variable (N m) [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- **Theorem `th:AHM11`** ([oah-jpm-zorgati14, Theorem 1.1], cited). Proved downstream as
`citedAHM14_holds` (`AHM14.lean`); the theorems of this file keep it as a hypothesis. -/
def CitedAHM14 : Prop :=
  (N : ℝ) < p → ∀ Ω : Set (Sp N), IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
    HasLipschitzBoundary Ω →
    ∀ (G : Mat m N → ℝ≥0∞) (α β c₀ : ℝ≥0) (L : Sp N → Mat m N → ℝ≥0∞),
      ConvexENN G → (0 : Mat m N) ∈ interior (dom G) → 0 < α → 0 < c₀ →
      Measurable (uncurry L) → IsPeriodic L → IsCoercive p c₀ L → HasGGrowth G α β L →
      RUUSC L →
      GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun L)
        (intHom (radial (Hp (ENNReal.ofReal p) L)))

/-- **Proposition `approx-affine-etoile-cite`** ([oah-jpm11, Proposition 3.15]):
energy-preserving approximation by piecewise affine functions. Proved downstream as
`citedAffineApprox_holds` (`AffineApprox.lean`); the theorems of this file keep it as a
hypothesis, discharged in `main_Ggrowth_final_unconditional` (`AHM14.lean`). -/
def CitedAffineApprox : Prop :=
  (N : ℝ) < p → ∀ Ω : Set (Sp N), StandingDomain Ω →
    ∀ (G : Mat m N → ℝ≥0∞) (α β : ℝ≥0), ConvexENN G → LowerSemicontinuous G →
      (0 : Mat m N) ∈ interior (dom G) → 0 < α →
      ∀ L : Mat m N → ℝ≥0∞, HasGGrowth G α β (fun _ => L) → RUUSC (fun _ => L) →
        ContinuousOn L (interior (dom G)) →
        ∀ u : W1p N m (ENNReal.ofReal p) Ω, intHom L u < ⊤ →
          ∃ φ : ℕ → W1p N m (ENNReal.ofReal p) Ω, (∀ n, φ n ∈ AffSet (ENNReal.ofReal p) Ω) ∧
            Tendsto (fun n => eLpNorm ((φ n).toFun - u.toFun) (ENNReal.ofReal p)
              (volume.restrict Ω)) atTop (𝓝 0) ∧
            Tendsto (fun n => eLpNorm ((φ n).grad - u.grad) (ENNReal.ofReal p)
              (volume.restrict Ω)) atTop (𝓝 0) ∧
            limsup (fun n => intHom L (φ n)) atTop ≤ intHom L u

/-- **Proposition `Zenvelopefacts-cite` (i)** ([fonseca88]): `𝒵_aff L` is locally Lipschitz on the
interior of its effective domain. -/
def CitedZaffLocLip : Prop :=
  ∀ L : Mat m N → ℝ≥0∞, ∀ ξ ∈ interior (dom (Zaff L)),
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 ξ, LipschitzOnWith K (fun ζ => (Zaff L ζ).toReal) s

variable {N m p}

/-- **Step 3** of the proof (`eq:4.13-4.14`): recovery sequence for piecewise affine data. -/
def Step3Statement (W : Sp N → Mat m N → ℝ≥0∞) (Ω : Set (Sp N)) : Prop :=
  ∀ φ ∈ AffSet (m := m) (ENNReal.ofReal p) Ω, intHom (Λ W) φ < ⊤ →
    ∃ v : ℝ → W1p N m (ENNReal.ofReal p) Ω, Tendsto v (𝓝[>] 0) (𝓝 φ) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), v ε ∈ AffSet (ENNReal.ofReal p) Ω) ∧
      limsup (fun ε => intFun (Ytloc W) ε (v ε)) (𝓝[>] 0) ≤ intHom (Λ W) φ

/-- **Step 4** of the proof (`eq:4.2`): for every `ε > 0`, every `u ∈ Aff(Ω)` is the `Lᵖ`-limit of
a sequence `ψ_k ∈ W^{1,p}(Ω)` with `limsup_k I_ε(ψ_k) ≤ 𝒴_loc I_ε(u)`. -/
def Step4Statement (W : Sp N → Mat m N → ℝ≥0∞) (Ω : Set (Sp N)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ u ∈ AffSet (m := m) (ENNReal.ofReal p) Ω,
    ∃ ψ : ℕ → W1p N m (ENNReal.ofReal p) Ω, Tendsto ψ atTop (𝓝 u) ∧
      limsup (fun k => intFun (p := ENNReal.ofReal p) W ε (ψ k)) atTop ≤ intFun (Ytloc W) ε u

end Statements

/-! ### Formalized parts of the proof -/

/-- Step 1: (Z7) gives `𝒴_loc I_ε ≤ I_ε`, the null set being dilated by `ε`. -/
theorem intFun_Ytloc_le {P : ℝ≥0∞} {Ω : Set (Sp N)} {W : Sp N → Mat m N → ℝ≥0∞}
    (h7 : ∀ᵐ x, ∀ ξ, Ytloc W x ξ ≤ W x ξ) {ε : ℝ} (hε : ε ≠ 0) (u : W1p N m P Ω) :
    intFun (Ytloc W) ε u ≤ intFun W ε u := by
  have hae : ∀ᵐ x ∂(volume : Measure (Sp N)), ∀ ξ, Ytloc W (ε⁻¹ • x) ξ ≤ W (ε⁻¹ • x) ξ := by
    rw [ae_iff] at h7 ⊢
    have : {x : Sp N | ¬∀ ξ, Ytloc W (ε⁻¹ • x) ξ ≤ W (ε⁻¹ • x) ξ} =
        (ε⁻¹ • · : Sp N → Sp N) ⁻¹' {y | ¬∀ ξ, Ytloc W y ξ ≤ W y ξ} := rfl
    rw [this, Measure.addHaar_preimage_smul _ (inv_ne_zero hε), h7, mul_zero]
  exact lintegral_mono_ae (ae_restrict_of_ae (hae.mono fun x hx => hx _))

/-- `dom Λ = dom G` and continuity of `Λ` on `int(dom G)` (Lemma `lem:consequences` (iv)). -/
theorem continuousOn_of_growth_of_locLip {G L : Mat m N → ℝ≥0∞} {α β : ℝ≥0} (hα : 0 < α)
    (hL : HasGGrowth G α β (fun _ : Sp N => Zaff L))
    (hLip : ∀ ξ ∈ interior (dom (Zaff L)),
      ∃ K : ℝ≥0, ∃ s ∈ 𝓝 ξ, LipschitzOnWith K (fun ζ => (Zaff L ζ).toReal) s) :
    ContinuousOn (Zaff L) (interior (dom G)) := by
  have hdom : dom (Zaff L) = dom G := by
    ext ξ
    obtain ⟨h1, h2⟩ := hL 0 ξ
    simp only [dom, Set.mem_ofPred_eq]
    constructor
    · intro h
      have : (α : ℝ≥0∞) * G ξ < ⊤ := h1.trans_lt h
      exact ENNReal.lt_top_of_mul_ne_top_right this.ne (by simpa using hα.ne')
    · intro h
      exact h2.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
        (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, h⟩))
  intro ξ hξ
  rw [← hdom] at hξ
  obtain ⟨K, s, hs, hKs⟩ := hLip ξ hξ
  have hcont : ContinuousAt (fun ζ => ENNReal.ofReal (Zaff L ζ).toReal) ξ :=
    ENNReal.continuous_ofReal.continuousAt.comp (hKs.continuousOn.continuousAt hs)
  have heq : (fun ζ => ENNReal.ofReal (Zaff L ζ).toReal) =ᶠ[𝓝 ξ] Zaff L := by
    filter_upwards [isOpen_interior.mem_nhds hξ] with ζ hζ
    exact ENNReal.ofReal_toReal (interior_subset hζ).ne
  exact (hcont.congr heq).continuousWithinAt

/-- **Theorem `main-Ggrowth`.** Under the standing assumptions on `Ω`, the hypotheses (Z1)–(Z8),
the cited results `CitedAHM14`, `CitedAffineApprox`, `CitedZaffLocLip`, and Steps 3 and 4 of the
proof, the functionals `I_ε(u) = ∫_Ω W(x/ε, ∇u)` Γ(Lᵖ)-converge to
`u ↦ ∫_Ω \widehat{ℋ(𝒴_loc W)}(∇u)`. -/
theorem main_Ggrowth [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : (N : ℝ) < p)
    {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} (hW : Hypotheses p G W)
    (hAHM : CitedAHM14 N m p) (hApprox : CitedAffineApprox N m p)
    (hLip : CitedZaffLocLip N m)
    (h3 : Step3Statement (p := p) W Ω) (h4 : Step4Statement (p := p) W Ω) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W) (intHom (Whom p W)) := by
  obtain ⟨α, β, hα, -, h3set⟩ := hW.setGrowth
  obtain ⟨c₀, hc₀, h4coer⟩ := hW.coercive
  -- consequences of the hypotheses
  have hgrowth : HasGGrowth G α β (Ytloc W) := HasGGrowth.Ytloc h3set
  have hΛgrowth : HasGGrowth G α β (fun _ : Sp N => Λ W) :=
    (hgrowth.Haff hW.convex).Zaff hW.convex
  have hΛruusc : RUUSC (fun _ : Sp N => Λ W) := hW.ruusc.Zaff_Haff
  have hΛcont : ContinuousOn (Λ W) (interior (dom G)) :=
    continuousOn_of_growth_of_locLip hα hΛgrowth (hLip _)
  have hΛle : ∀ u : W1p N m (ENNReal.ofReal p) Ω, intHom (Λ W) u ≤ intHom (Whom p W) u :=
    fun u => lintegral_mono fun x => hW.Zaff_Haff_le _
  refine gammaConverges_of_steps (intFun W) (intFun (Ytloc W)) (AffSet _ Ω) _ (intHom (Λ W))
    ?_ ?_ hΛle ?_ h3 ?_
  · -- Step 1: `𝒴_loc I_ε ≤ I_ε`
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) u
    exact intFun_Ytloc_le hW.Ytloc_le hε.ne' u
  · -- Step 1: Theorem `th:AHM11` applied to `𝒴_loc W`
    exact hAHM hp Ω hΩ.isOpen hΩ.bounded hΩ.nonempty hΩ.lipschitz G α β c₀ (Ytloc W) hW.convex
      hW.zero_mem_interior hα hc₀ hW.measurable_Ytloc hW.periodic.Ytloc h4coer hgrowth hW.ruusc
  · -- Step 2: Proposition `approx-affine-etoile-cite` applied to `Λ`
    intro u hu
    obtain ⟨φ, hφA, hφ, -, hφlim⟩ := hApprox hp Ω hΩ G α β hW.convex hW.lsc
      hW.zero_mem_interior hα (Λ W) hΛgrowth hΛruusc hΛcont u ((hΛle u).trans_lt hu)
    refine ⟨φ, hφA, ?_, hφlim⟩
    rw [EMetric.tendsto_nhds]
    intro η hη
    filter_upwards [hφ.eventually_lt_const hη] with n hn
    rwa [W1p.edist_def]
  · -- Step 4
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) u hu
    exact h4 ε hε u hu

end Homogenization
