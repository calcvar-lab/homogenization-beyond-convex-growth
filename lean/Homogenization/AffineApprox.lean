import Homogenization.AffSetCompetitor

/-!
# Proposition `approx-affine-etoile-cite` (step 5)

For a strongly star-shaped bounded open `Ω` (`StandingDomain`), `G` convex, l.s.c., with
`0 ∈ int dom G`, and `L` with `G`-growth, ru-usc and continuous on `int dom G`, every
`u ∈ W^{1,p}(Ω)` with finite energy is the limit, in `W^{1,p}(Ω)`, of piecewise affine functions
`φₙ ∈ Aff(Ω)` with `limsup ∫_Ω L(∇φₙ) ≤ ∫_Ω L(∇u)` (`citedAffineApprox_holds`). This proves the
`Prop` `CitedAffineApprox N m p` of `Main.lean`; the theorems upstream of this file keep it as a
hypothesis `hApprox`, which can now be discharged with `citedAffineApprox_holds`.
-/

open MeasureTheory Filter Topology Set Function Metric
open scoped ENNReal NNReal Convolution Pointwise

namespace Homogenization

variable {N m : ℕ}

/-- Strong star-shapedness: some `x₀ ∈ Ω` is such that every homothety of ratio `s ∈ ]0,1[` and
center `x₀` maps `cl Ω` into `Ω`. -/
theorem IsStronglyStarShaped.homothety_mem {Ω : Set (Sp N)} (h : IsStronglyStarShaped Ω) :
    ∃ x₀ ∈ Ω, ∀ s : ℝ, 0 < s → s < 1 → ∀ z ∈ closure Ω, homothety x₀ s z ∈ Ω := by
  obtain ⟨x₀, hx₀, hstar⟩ := h
  refine ⟨x₀, hx₀, fun s hs0 hs1 z hz => ?_⟩
  have hcl : z - x₀ ∈ closure ((fun y => y - x₀) '' Ω) := by
    have hc : Continuous fun y : Sp N => y - x₀ := continuous_id.sub continuous_const
    exact image_closure_subset_closure_image hc ⟨z, hz, rfl⟩
  have h1 := hstar s⁻¹ (one_lt_inv₀ hs0 |>.2 hs1) hcl
  obtain ⟨w, ⟨y, hy, rfl⟩, hw⟩ := h1
  have : homothety x₀ s z = y := by
    simp only [homothety]
    rw [← hw]
    change x₀ + s • (s⁻¹ • (y - x₀)) = y
    rw [smul_inv_smul₀ hs0.ne']
    abel
  rw [this]; exact hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `homothety x₀ s` as a composition `x ↦ s • (x - x₀) + x₀`. -/
theorem homothety_eq_comp (x₀ : Sp N) (s : ℝ) (x : Sp N) :
    homothety x₀ s x = s • (x - x₀) + x₀ := by
  simp only [homothety]; abel

omit [NormedSpace ℝ E] in
/-- `F ∘ (x ↦ x₀ + s(x - x₀))` is in `Lᵖ` with `F`. -/
theorem MemLp.comp_homothety {p : ℝ≥0∞} (hpT : p ≠ ⊤) {F : Sp N → E} (hF : MemLp F p volume)
    (x₀ : Sp N) {s : ℝ} (hs : s ≠ 0) : MemLp (fun x => F (homothety x₀ s x)) p volume := by
  refine ⟨hF.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_homothety x₀ hs), ?_⟩
  set F' : Sp N → E := fun y => F (y + x₀)
  have hF' : MemLp F' p volume := hF.comp_measurePreserving (measurePreserving_add_right _ x₀)
  have e : (fun x => F (homothety x₀ s x)) = (fun w => F' (s • w)) ∘ fun x => x - x₀ := by
    funext x; simp [F', homothety_eq_comp]
  rw [e, eLpNorm_comp_measurePreserving _ (measurePreserving_sub_right volume x₀)]
  · rw [eLpNorm_comp_smul hpT hF'.1 hs]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
      ENNReal.ofReal_ne_top) hF'.2
  · exact hF'.1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul volume hs)

/-- **Continuity of homotheties of center `x₀` in `Lᵖ(ℝᴺ)`.** -/
theorem tendsto_eLpNorm_comp_homothety_sub {p : ℝ} (hp : 1 ≤ p) {F : Sp N → E}
    (hF : MemLp F (ENNReal.ofReal p) volume) (x₀ : Sp N) :
    Tendsto (fun s : ℝ => eLpNorm (fun x => F (homothety x₀ s x) - F x) (ENNReal.ofReal p)
      volume) (𝓝 1) (𝓝 0) := by
  set F' : Sp N → E := fun y => F (y + x₀)
  have hF' : MemLp F' (ENNReal.ofReal p) volume :=
    hF.comp_measurePreserving (measurePreserving_add_right _ x₀)
  refine (tendsto_eLpNorm_comp_smul_sub hp hF').congr' ?_
  filter_upwards [eventually_ne_nhds one_ne_zero] with s hs
  have e : (fun x => F (homothety x₀ s x) - F x) =
      (fun w => F' (s • w) - F' w) ∘ fun x => x - x₀ := by
    funext x; simp [F', homothety_eq_comp]
  rw [e, eLpNorm_comp_measurePreserving _ (measurePreserving_sub_right volume x₀)]
  exact (hF'.1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul volume hs)).sub
    hF'.1

/-- A weak-gradient identity only depends on the gradient up to a.e. equality. -/
theorem HasWeakGrad.congr_ae {U : Set (Sp N)} {f : Sp N → Tgt m} {g g' : Sp N → Mat m N}
    (hfg : HasWeakGrad U f g) (hgg : g =ᵐ[volume] g') : HasWeakGrad U f g' := by
  intro ψ hψ hcs hsupp v
  rw [hfg ψ hψ hcs hsupp v]
  congr 1
  exact integral_congr_ae (hgg.mono fun y hy => by
    change ψ y • g y v = ψ y • g' y v
    rw [hy])

/-- **Measurable extension of a `W^{1,p}(Ω)` function.** `1_Ω u` and a measurable version of
`1_Ω ∇u` are in `Lᵖ(ℝᴺ)`, and the latter is a weak gradient of the former on `Ω`. -/
theorem W1p.exists_extension {p : ℝ≥0∞} {Ω : Set (Sp N)} (hΩ : IsOpen Ω)
    (u : W1p N m p Ω) :
    ∃ gm : Sp N → Mat m N, Measurable gm ∧ gm =ᵐ[volume] Ω.indicator u.grad ∧
      MemLp gm p volume ∧ MemLp (Ω.indicator u.toFun) p volume ∧
      HasWeakGrad Ω (Ω.indicator u.toFun) gm := by
  have hgLp : MemLp (Ω.indicator u.grad) p volume :=
    (memLp_indicator_iff_restrict (μ := volume) (p := p) (f := u.grad)
      hΩ.measurableSet).2 u.memLp_grad
  have hfLp : MemLp (Ω.indicator u.toFun) p volume :=
    (memLp_indicator_iff_restrict (μ := volume) (p := p) (f := u.toFun)
      hΩ.measurableSet).2 u.memLp
  refine ⟨hgLp.1.mk _, hgLp.1.stronglyMeasurable_mk.measurable, hgLp.1.ae_eq_mk.symm,
    hgLp.ae_eq hgLp.1.ae_eq_mk, hfLp, ?_⟩
  exact u.weak.indicator.congr_ae hgLp.1.ae_eq_mk

/-- Choice of `η` in the ru-usc bound. -/
theorem exists_ruusc_eta {E V : ℝ≥0∞} (hE : E ≠ ⊤) (hV : V ≠ ⊤) (c : ℝ≥0) {a : ℝ≥0∞}
    (ha : E < a) : ∃ η : ℝ≥0, 0 < η ∧ (1 + (η : ℝ≥0∞)) * E + η * c * V < a := by
  have hlim : Tendsto (fun η : ℝ≥0 => (1 + (η : ℝ≥0∞)) * E + η * c * V) (𝓝 0)
      (𝓝 ((1 + ((0 : ℝ≥0) : ℝ≥0∞)) * E + ((0 : ℝ≥0) : ℝ≥0∞) * c * V)) := by
    have h1 : Tendsto (fun η : ℝ≥0 => (η : ℝ≥0∞)) (𝓝 0) (𝓝 ((0 : ℝ≥0) : ℝ≥0∞)) :=
      ENNReal.continuous_coe.tendsto 0
    refine (ENNReal.Tendsto.mul_const (tendsto_const_nhds.add h1) (Or.inr hE)).add ?_
    exact ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.coe_ne_top))
      (Or.inr hV)
  simp only [ENNReal.coe_zero, add_zero, one_mul, zero_mul] at hlim
  obtain ⟨η, hη, hηpos⟩ := ((tendsto_nhdsWithin_of_tendsto_nhds hlim).eventually
    (gt_mem_nhds ha)).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ≥0))) |>.exists
  exact ⟨η, hηpos, hη⟩

/-- For `s → 1⁻`, the dilated ru-usc bound stays below `a`. -/
theorem eventually_ruusc_dilation_lt {E V : ℝ≥0∞} (hE : E ≠ ⊤) (c η : ℝ≥0)
    {a : ℝ≥0∞} (ha : (1 + (η : ℝ≥0∞)) * E + η * c * V < a) :
    ∀ᶠ s in 𝓝[<] (1 : ℝ),
      (1 + (η : ℝ≥0∞)) * (ENNReal.ofReal |(s ^ N)⁻¹| * E) + η * c * V < a := by
  have hcont : ContinuousAt (fun s : ℝ => ENNReal.ofReal |(s ^ N)⁻¹|) 1 :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((continuous_abs.continuousAt).comp ((continuousAt_id.pow N).inv₀ (by simp)))
  have h1 : ENNReal.ofReal |((1 : ℝ) ^ N)⁻¹| = 1 := by simp
  have hlim : Tendsto (fun s : ℝ =>
      (1 + (η : ℝ≥0∞)) * (ENNReal.ofReal |(s ^ N)⁻¹| * E) + η * c * V) (𝓝 1)
      (𝓝 ((1 + (η : ℝ≥0∞)) * (1 * E) + η * c * V)) := by
    have := hcont.tendsto; rw [h1] at this
    refine (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const this (Or.inr hE))
      (Or.inr (by simp))).add tendsto_const_nhds
  rw [one_mul] at hlim
  exact nhdsWithin_le_nhds (hlim.eventually (gt_mem_nhds ha))

/-- **Continuity of `g ↦ s g(x₀ + s(· - x₀))` in `Lᵖ`** as `s → 1`. -/
theorem tendsto_eLpNorm_smul_comp_homothety_sub {p : ℝ} (hp : 1 ≤ p) {F : Sp N → E}
    (hF : MemLp F (ENNReal.ofReal p) volume) (x₀ : Sp N) :
    Tendsto (fun s : ℝ => eLpNorm (fun x => s • F (homothety x₀ s x) - F x) (ENNReal.ofReal p)
      volume) (𝓝 1) (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have h1 := tendsto_eLpNorm_comp_homothety_sub hp hF x₀
  set C := eLpNorm F (ENNReal.ofReal p) volume
  have hC : C ≠ ⊤ := hF.2.ne
  have hbound : ∀ᶠ s in 𝓝 (1 : ℝ),
      eLpNorm (fun x => s • F (homothety x₀ s x) - F x) (ENNReal.ofReal p) volume ≤
        ‖s‖ₑ * eLpNorm (fun x => F (homothety x₀ s x) - F x) (ENNReal.ofReal p) volume +
          ‖s - 1‖ₑ * C := by
    filter_upwards [eventually_ne_nhds one_ne_zero] with s hs0
    have hm1 : AEStronglyMeasurable (fun x => F (homothety x₀ s x) - F x) volume :=
      (hF.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_homothety x₀ hs0)).sub hF.1
    have e : (fun x => s • F (homothety x₀ s x) - F x) =
        (s • fun x => F (homothety x₀ s x) - F x) + (s - 1) • F := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_sub, sub_smul, one_smul]
      abel
    rw [e]
    refine (eLpNorm_add_le (hm1.const_smul s) (hF.1.const_smul _) hp1).trans ?_
    rw [eLpNorm_const_smul, eLpNorm_const_smul]
  have hlim : Tendsto (fun s : ℝ =>
      ‖s‖ₑ * eLpNorm (fun x => F (homothety x₀ s x) - F x) (ENNReal.ofReal p) volume +
        ‖s - 1‖ₑ * C) (𝓝 1) (𝓝 (‖(1 : ℝ)‖ₑ * 0 + ‖(1 : ℝ) - 1‖ₑ * C)) := by
    have hn : Tendsto (fun s : ℝ => ‖s‖ₑ) (𝓝 1) (𝓝 ‖(1 : ℝ)‖ₑ) :=
      continuous_enorm.tendsto 1
    have hn' : Tendsto (fun s : ℝ => ‖s - 1‖ₑ) (𝓝 1) (𝓝 ‖(1 : ℝ) - 1‖ₑ) :=
      (continuous_enorm.comp (continuous_id.sub continuous_const)).tendsto 1
    exact (ENNReal.Tendsto.mul hn (Or.inr (by simp)) h1 (Or.inr (by simp))).add
      (ENNReal.Tendsto.mul_const hn' (Or.inr hC))
  simp only [mul_zero, sub_self, enorm_zero, zero_mul, add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hbound

/-- `exists_affSet_energy_close` with, in addition, the a.e. closeness of the gradients. -/
theorem exists_affSet_energy_grad_close {P : ℝ≥0∞} {Ω : Set (Sp N)} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {f : Sp N → Tgt m} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) {V : Set (Mat m N)} (hVo : IsOpen V) {L : Mat m N → ℝ≥0∞}
    (hLc : ContinuousOn L V) (hLfin : ∀ ξ ∈ V, L ξ ≠ ⊤) {K : Set (Mat m N)} (hK : IsCompact K)
    (hKV : K ⊆ V) (hfK : ∀ x ∈ Ω, fderiv ℝ f x ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : W1p N m P Ω, φ ∈ AffSet P Ω ∧ (∀ x, ‖φ.toFun x - f x‖ ≤ ε) ∧
      (∀ᵐ x, ‖φ.grad x - fderiv ℝ f x‖ ≤ ε) ∧
      (∫⁻ x in Ω, L (φ.grad x)) ≤
        (∫⁻ x in Ω, L (fderiv ℝ f x)) + ENNReal.ofReal ε * volume Ω := by
  obtain ⟨δ', hδ', hmod⟩ := exists_uniform_modulus_of_continuousOn hVo hLc hLfin hK hKV hε
  obtain ⟨h, hh, hsup, hgrad⟩ := exists_pwInterp_approx_of_contDiff hf hfs (lt_min hε hδ')
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfs one_ne_zero
  have hLip := lipschitzWith_pwInterp hC hh
  let φ : W1p N m P Ω :=
    { toFun := pwInterp h f
      grad := fderiv ℝ (pwInterp h f)
      memLp := memLp_of_lipschitzWith hΩo hΩb hLip
      memLp_grad := memLp_fderiv_of_lipschitzWith hΩb hLip
      weak := LipschitzWith.hasWeakGrad hLip Ω }
  refine ⟨φ, ⟨pwInterp_isPWAffine hΩo hΩb hC hh, Eventually.of_forall fun _ => rfl⟩,
    fun x => (hsup x).trans (min_le_left _ _),
    hgrad.mono fun x hx => hx.trans (min_le_left _ _), ?_⟩
  have hpt : ∀ᵐ x ∂volume.restrict Ω, L (φ.grad x) ≤ L (fderiv ℝ f x) + ENNReal.ofReal ε := by
    filter_upwards [ae_restrict_of_ae hgrad, ae_restrict_mem hΩo.measurableSet] with x hx hxΩ
    exact (hmod _ (hfK x hxΩ) _ (hx.trans (min_le_right _ _))).1
  calc (∫⁻ x in Ω, L (φ.grad x))
      ≤ ∫⁻ x in Ω, (L (fderiv ℝ f x) + ENNReal.ofReal ε) := lintegral_mono_ae hpt
    _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]


/-- **One step of the affine approximation** (Proposition `approx-affine-etoile-cite`): for every
`ε > 0` there is `φ ∈ AffSet` with `‖φ - u‖_{Lᵖ(Ω)} ≤ ε`, `‖∇φ - ∇u‖_{Lᵖ(Ω)} ≤ ε` and
`∫_Ω L(∇φ) ≤ ∫_Ω L(∇u) + ε`. Proof: dilation `u ∘ A` with `A = x₀ + s(· - x₀)`, `s → 1⁻`
(ru-usc), local mollification (`limsup_lintegral_mollSeq_le`), then Kuhn interpolation
(`exists_affSet_energy_grad_close`). -/
theorem exists_affSet_approx_step [NeZero N] {p : ℝ} (hp : 1 ≤ p) {Ω : Set (Sp N)}
    (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} (hG : ConvexENN G)
    (hGlsc : LowerSemicontinuous G) (h0 : (0 : Mat m N) ∈ interior (dom G)) (hα : 0 < α)
    {L : Mat m N → ℝ≥0∞} (hLgr : HasGGrowth G α β (fun _ => L)) (hLru : RUUSC (fun _ => L))
    (hLc : ContinuousOn L (interior (dom G))) (u : W1p N m (ENNReal.ofReal p) Ω)
    (hu : intHom L u < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : W1p N m (ENNReal.ofReal p) Ω, φ ∈ AffSet (ENNReal.ofReal p) Ω ∧
      eLpNorm (φ.toFun - u.toFun) (ENNReal.ofReal p) (volume.restrict Ω) ≤ ENNReal.ofReal ε ∧
      eLpNorm (φ.grad - u.grad) (ENNReal.ofReal p) (volume.restrict Ω) ≤ ENNReal.ofReal ε ∧
      intHom L φ ≤ intHom L u + ENNReal.ofReal ε := by
  -- setting
  obtain ⟨x₀, -, hstar⟩ := hΩ.starShaped.homothety_mem
  obtain ⟨c, -, hru⟩ := hLru
  set E := intHom L u
  have hE : E ≠ ⊤ := hu.ne
  have hΩo := hΩ.isOpen
  have hV : volume Ω ≠ ⊤ := hΩ.bounded.measure_lt_top.ne
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨gm, hgm, hgmeq, hgmLp, hHLp, hweak⟩ := u.exists_extension hΩo
  set H := Ω.indicator u.toFun
  have hGm : Measurable G := hGlsc.measurable
  have hLG : ∀ ξ, L ξ ≤ β * (1 + G ξ) := fun ξ => (hLgr 0 ξ).2
  have hGL : ∀ ξ, (α : ℝ≥0∞) * G ξ ≤ L ξ := fun ξ => (hLgr 0 ξ).1
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  -- finiteness of the energies on `Ω`
  have hGfin : ∀ᵐ y ∂volume.restrict Ω, G (u.grad y) < ⊤ := by
    have hm : AEMeasurable (fun y => G (u.grad y)) (volume.restrict Ω) :=
      hGm.comp_aemeasurable u.memLp_grad.1.aemeasurable
    have hle : (α : ℝ≥0∞) * ∫⁻ y in Ω, G (u.grad y) ≤ E := by
      rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact lintegral_mono fun y => hGL _
    have hα0 : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
    have hfin : ∫⁻ y in Ω, G (u.grad y) ≠ ⊤ := by
      intro htop; rw [htop, ENNReal.mul_top hα0] at hle; exact hE (top_le_iff.1 hle)
    exact ae_lt_top' hm hfin
  have hGint : ∫⁻ y in Ω, G (u.grad y) ≠ ⊤ := by
    have hle : (α : ℝ≥0∞) * ∫⁻ y in Ω, G (u.grad y) ≤ E := by
      rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact lintegral_mono fun y => hGL _
    have hα0 : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
    intro htop; rw [htop, ENNReal.mul_top hα0] at hle; exact hE (top_le_iff.1 hle)
  have hLfin : ∀ᵐ y ∂volume.restrict Ω, L (u.grad y) < ⊤ := hGfin.mono fun y hy =>
    lt_of_le_of_lt (hLG _) (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hy⟩))
  have hG0 : G 0 < ⊤ := (interior_subset h0 : (0 : Mat m N) ∈ dom G)
  have hdom : ∀ᵐ y ∂volume, gm y ∈ dom G := by
    have h1 : ∀ᵐ y ∂volume, y ∈ Ω → G (u.grad y) < ⊤ :=
      (ae_restrict_iff' hΩo.measurableSet).1 hGfin
    filter_upwards [h1, hgmeq] with y hy hyg
    change G (gm y) < ⊤
    rw [hyg]
    by_cases hyΩ : y ∈ Ω
    · rw [indicator_of_mem hyΩ]; exact hy hyΩ
    · rw [indicator_of_notMem hyΩ]; exact hG0
  -- choice of `η` and `s`
  obtain ⟨η, hη, hηlt⟩ := exists_ruusc_eta hE hV c (a := E + ENNReal.ofReal (ε / 4))
    (ENNReal.lt_add_right hE (ENNReal.ofReal_pos.2 hε4).ne')
  have hev1 := eventually_ruusc_dilation_lt (N := N) hE c η hηlt
  have hev2 := lintegral_homothety_ruusc_le hΩo.measurableSet
    (fun s hs0 hs1 z hz => hstar s hs0 hs1 z (subset_closure hz)) hru hLfin hη
  have hev3 : ∀ᶠ s in 𝓝[<] (1 : ℝ),
      eLpNorm (fun x => H (homothety x₀ s x) - H x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (ε / 4) :=
    nhdsWithin_le_nhds ((ENNReal.tendsto_nhds_zero.1
      (tendsto_eLpNorm_comp_homothety_sub hp hHLp x₀)) _ (ENNReal.ofReal_pos.2 hε4))
  have hev4 : ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s := nhdsWithin_le_nhds (lt_mem_nhds one_pos)
  have hev7 : ∀ᶠ s in 𝓝[<] (1 : ℝ),
      eLpNorm (fun x => s • gm (homothety x₀ s x) - gm x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (ε / 4) :=
    nhdsWithin_le_nhds ((ENNReal.tendsto_nhds_zero.1
      (tendsto_eLpNorm_smul_comp_homothety_sub hp hgmLp x₀)) _ (ENNReal.ofReal_pos.2 hε4))
  obtain ⟨s, h1, h2, h3, h7, hs0, hs1⟩ :=
    (hev1.and (hev2.and (hev3.and (hev7.and (hev4.and self_mem_nhdsWithin))))).exists
  have hdil : ∫⁻ z in Ω, L (s • u.grad (homothety x₀ s z)) < E + ENNReal.ofReal (ε / 4) :=
    (h2 hs0).trans_lt h1
  -- the open set `U = A⁻¹ Ω ⊇ cl Ω` and the margin `δ`
  have hAc : Continuous (homothety (N := N) x₀ s) := by unfold homothety; fun_prop
  set U := homothety x₀ s ⁻¹' Ω
  have hUo : IsOpen U := hΩo.preimage hAc
  have hclU : closure Ω ⊆ U := fun z hz => hstar s hs0 hs1 z hz
  obtain ⟨δ, hδ, hδU⟩ :=
    hΩ.bounded.isCompact_closure.exists_cthickening_subset_open hUo hclU
  have hball : ∀ z ∈ Ω, closedBall z δ ⊆ U := fun z hz =>
    (closedBall_subset_cthickening (subset_closure hz) δ).trans hδU
  have hUb : Bornology.IsBounded U := by
    have hAinv : Continuous (homothety (N := N) x₀ s⁻¹) := by unfold homothety; fun_prop
    refine (hΩ.bounded.isCompact_closure.image hAinv).isBounded.subset fun z hz => ?_
    refine ⟨homothety x₀ s z, subset_closure hz, ?_⟩
    simp only [homothety, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul,
      add_sub_cancel]
  -- the dilated function and gradient
  set φ₀ : Sp N → Tgt m := fun x => H (homothety x₀ s x)
  set Gs : Sp N → Mat m N := fun x => s • gm (homothety x₀ s x)
  have hφ₀Lp : MemLp φ₀ (ENNReal.ofReal p) volume :=
    Homogenization.MemLp.comp_homothety hpT hHLp x₀ hs0.ne'
  have hGsLp : MemLp Gs (ENNReal.ofReal p) volume :=
    (Homogenization.MemLp.comp_homothety hpT hgmLp x₀ hs0.ne').const_smul s
  have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hGsm : Measurable Gs := (hgm.comp hAc.measurable).const_smul s
  have hweakS : HasWeakGrad U φ₀ Gs := hweak.comp_homothety hs0.ne' x₀
  obtain ⟨hSc, hSconv, hSint⟩ := hG.smul_closure_dom h0 hs0.le hs1
  have hGsS : ∀ᵐ x ∂volume, Gs x ∈ (s : ℝ) • closure (dom G) := by
    filter_upwards [(quasiMeasurePreserving_homothety x₀ hs0.ne').tendsto_ae.eventually hdom]
      with x hx
    exact smul_mem_smul_set (subset_closure hx)
  -- `gm ∘ A = ∇u ∘ A` a.e. on `Ω`
  have hgmA : ∀ᵐ z ∂volume.restrict Ω, gm (homothety x₀ s z) = u.grad (homothety x₀ s z) := by
    filter_upwards [ae_restrict_of_ae
      ((quasiMeasurePreserving_homothety x₀ hs0.ne').tendsto_ae.eventually
      hgmeq), ae_restrict_mem hΩo.measurableSet] with z hz hzΩ
    rw [hz, indicator_of_mem (hstar s hs0 hs1 z (subset_closure hzΩ))]
  -- integrability of `1_U G(Gs)`
  have hF : Integrable (U.indicator fun y => (G (Gs y)).toReal) volume := by
    have hpt : ∀ y, G (Gs y) ≤ G (gm (homothety x₀ s y)) + G 0 := fun y => by
      have h := hG (gm (homothety x₀ s y)) 0 s.toNNReal (by
        rw [Real.toNNReal_le_one]; exact hs1.le)
      rw [smul_zero, add_zero, Real.coe_toNNReal _ hs0.le] at h
      refine h.trans (add_le_add ?_ ?_)
      · calc (s.toNNReal : ℝ≥0∞) * G (gm (homothety x₀ s y))
            ≤ 1 * G (gm (homothety x₀ s y)) := by
              gcongr; exact_mod_cast Real.toNNReal_le_one.2 hs1.le
          _ = _ := one_mul _
      · calc ((1 - s.toNNReal : ℝ≥0) : ℝ≥0∞) * G 0 ≤ 1 * G 0 := by
              gcongr; exact_mod_cast tsub_le_self
          _ = G 0 := one_mul _
    have hgmΩ : ∫⁻ y in Ω, G (gm y) = ∫⁻ y in Ω, G (u.grad y) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hgmeq, ae_restrict_mem hΩo.measurableSet] with y hy hyΩ
      rw [hy, indicator_of_mem hyΩ]
    have hlt : ∫⁻ y in U, G (Gs y) < ⊤ := by
      calc ∫⁻ y in U, G (Gs y) ≤ ∫⁻ y in U, (G (gm (homothety x₀ s y)) + G 0) :=
            lintegral_mono hpt
        _ = (∫⁻ y in U, G (gm (homothety x₀ s y))) + G 0 * volume U := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ = ENNReal.ofReal |(s ^ N)⁻¹| * (∫⁻ y in Ω, G (u.grad y)) + G 0 * volume U := by
            rw [setLIntegral_comp_homothety (fun y => G (gm y)) hs0 x₀ hΩo.measurableSet, hgmΩ]
        _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_top_iff_ne_top.2 hGint), ENNReal.mul_lt_top hG0 hUb.measure_lt_top⟩
    have hm : AEMeasurable (U.indicator fun y => G (Gs y)) volume :=
      ((hGm.comp hGsm).indicator hUo.measurableSet).aemeasurable
    have hint := integrable_toReal_of_lintegral_ne_top hm
      (by rw [lintegral_indicator hUo.measurableSet]; exact hlt.ne)
    refine hint.congr (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ U <;> simp [hy]
  obtain ⟨hvals, hlimsup⟩ := limsup_lintegral_mollSeq_le hΩo hV hδ hball
    (hφ₀Lp.locallyIntegrable hp1') hGsm (hGsLp.locallyIntegrable hp1') hweakS hG hGlsc hSc
    hSconv hSint hGsS hLc hLG hF
  have hGsΩ : ∫⁻ z in Ω, L (Gs z) = ∫⁻ z in Ω, L (s • u.grad (homothety x₀ s z)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgmA] with z hz
    simp only [Gs, hz]
  -- choice of the mollification index
  have hrOut : Tendsto (fun n : ℕ => (halfBump (N := N)
      (show 0 < δ / ((n : ℝ) + 2) by positivity)).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hmolLp := tendsto_eLpNorm_bump_convolution_sub hp hφ₀Lp hrOut
  have hlt2 : E + ENNReal.ofReal (ε / 4) < E + ENNReal.ofReal (ε / 2) :=
    ENNReal.add_lt_add_left hE ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  have hev5 : ∀ᶠ n in atTop, ∫⁻ z in Ω, L (fderiv ℝ (mollSeq hδ φ₀ n) z) <
      E + ENNReal.ofReal (ε / 2) :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt (hlimsup.trans (hGsΩ.le.trans hdil.le)) hlt2)
  have hev6 : ∀ᶠ n in atTop, eLpNorm (mollSeq hδ φ₀ n - φ₀) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (ε / 4) :=
    (ENNReal.tendsto_nhds_zero.1 hmolLp) _ (ENNReal.ofReal_pos.2 hε4)
  have hev8 : ∀ᶠ n : ℕ in atTop, eLpNorm ((halfBump (N := N)
      (show 0 < δ / ((n : ℝ) + 2) by positivity)).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] Gs - Gs) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (ε / 4) :=
    (ENNReal.tendsto_nhds_zero.1 (tendsto_eLpNorm_bump_convolution_sub hp hGsLp hrOut)) _
      (ENNReal.ofReal_pos.2 hε4)
  obtain ⟨n, hn5, hn6, hn8⟩ := (hev5.and (hev6.and hev8)).exists
  set f := mollSeq hδ φ₀ n
  set ηn := halfBump (N := N) (show 0 < δ / ((n : ℝ) + 2) by positivity)
  -- regularity of `f`
  have hφ₀cs : HasCompactSupport φ₀ := by
    refine HasCompactSupport.of_support_subset_isCompact hUb.isCompact_closure fun x hx => ?_
    refine subset_closure ?_
    by_contra hxU
    exact hx (show φ₀ x = 0 from
      indicator_of_notMem (show homothety x₀ s x ∉ Ω from hxU) u.toFun)
  have hfC : ContDiff ℝ (⊤ : ℕ∞) f :=
    ηn.hasCompactSupport_normed.contDiff_convolution_left _ ηn.contDiff_normed
      (hφ₀Lp.locallyIntegrable hp1')
  have hfcs : HasCompactSupport f := ηn.hasCompactSupport_normed.convolution _ hφ₀cs
  have hfC1 : ContDiff ℝ 1 f := hfC.of_le (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := (hfC1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hfcs.fderiv (𝕜 := ℝ))
  set K : Set (Mat m N) := ((s : ℝ) • closure (dom G)) ∩ closedBall 0 M
  have hK : IsCompact K := (isCompact_closedBall 0 M).inter_left hSc
  have hKV : K ⊆ interior (dom G) := inter_subset_left.trans hSint
  have hfK : ∀ x ∈ Ω, fderiv ℝ f x ∈ K := fun x hx =>
    ⟨hvals n x hx, by rw [mem_closedBall, dist_zero_right]; exact hM x⟩
  have hLfin' : ∀ ξ ∈ interior (dom G), L ξ ≠ ⊤ := fun ξ hξ =>
    (lt_of_le_of_lt (hLG ξ) (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, (show ξ ∈ dom G from interior_subset hξ)⟩))).ne
  -- the tolerance `ε'`
  have hVp : volume Ω ^ (ENNReal.ofReal p).toReal⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hV
  obtain ⟨e₁, he₁, he₁lt⟩ := ENNReal.exists_nnreal_pos_mul_lt hV
    (ENNReal.ofReal_pos.2 hε4).ne'
  obtain ⟨e₂, he₂, he₂lt⟩ := ENNReal.exists_nnreal_pos_mul_lt hVp
    (ENNReal.ofReal_pos.2 hε4).ne'
  set ε' : ℝ := min (e₁ : ℝ) (e₂ : ℝ)
  have hε' : 0 < ε' := lt_min (by exact_mod_cast he₁) (by exact_mod_cast he₂)
  obtain ⟨φ, hφA, hφsup, hφgrad, hφE⟩ := exists_affSet_energy_grad_close (P := ENNReal.ofReal p) hΩo
    hΩ.bounded hfC1 hfcs isOpen_interior hLc hLfin' hK hKV hfK hε'
  have hε'1 : ENNReal.ofReal ε' ≤ e₁ := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hε'2 : ENNReal.ofReal ε' ≤ e₂ := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hsum : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) ≤
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε4.le hε4.le, ← ENNReal.ofReal_add (by positivity) hε4.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hp1'' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hp1'
  refine ⟨φ, hφA, ?_, ?_, ?_⟩
  · -- the `Lᵖ(Ω)` error
    have hp1'' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hp1'
    have hcongr : φ.toFun - u.toFun =ᵐ[volume.restrict Ω]
        (φ.toFun - f) + (f - φ₀) + (φ₀ - H) := by
      filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
      simp only [Pi.add_apply, Pi.sub_apply, H, indicator_of_mem hx]
      abel
    have hm1 : AEStronglyMeasurable (φ.toFun - f) (volume.restrict Ω) :=
      φ.memLp.1.sub hfC.continuous.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (f - φ₀) (volume.restrict Ω) :=
      (hfC.continuous.aestronglyMeasurable.sub hφ₀Lp.1).restrict
    have hm3 : AEStronglyMeasurable (φ₀ - H) (volume.restrict Ω) :=
      (hφ₀Lp.1.sub hHLp.1).restrict
    have hb1 : eLpNorm (φ.toFun - f) (ENNReal.ofReal p) (volume.restrict Ω) ≤
        ENNReal.ofReal (ε / 4) := by
      refine (eLpNorm_le_of_ae_bound (C := ε') (Eventually.of_forall fun x => hφsup x)).trans ?_
      rw [Measure.restrict_apply_univ]
      calc volume Ω ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal ε'
          ≤ volume Ω ^ (ENNReal.ofReal p).toReal⁻¹ * e₂ := by gcongr
        _ = e₂ * volume Ω ^ (ENNReal.ofReal p).toReal⁻¹ := mul_comm _ _
        _ ≤ _ := he₂lt.le
    have hb2 : eLpNorm (f - φ₀) (ENNReal.ofReal p) (volume.restrict Ω) ≤
        ENNReal.ofReal (ε / 4) :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hn6
    have hb3 : eLpNorm (φ₀ - H) (ENNReal.ofReal p) (volume.restrict Ω) ≤
        ENNReal.ofReal (ε / 4) :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans h3
    rw [eLpNorm_congr_ae hcongr]
    calc eLpNorm ((φ.toFun - f) + (f - φ₀) + (φ₀ - H)) (ENNReal.ofReal p) (volume.restrict Ω)
        ≤ eLpNorm (φ.toFun - f) (ENNReal.ofReal p) (volume.restrict Ω) +
            eLpNorm (f - φ₀) (ENNReal.ofReal p) (volume.restrict Ω) +
            eLpNorm (φ₀ - H) (ENNReal.ofReal p) (volume.restrict Ω) := by
          refine (eLpNorm_add_le (hm1.add hm2) hm3 hp1'').trans ?_
          gcongr
          exact eLpNorm_add_le hm1 hm2 hp1''
      _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
          gcongr
      _ ≤ _ := hsum
  · -- the gradient error
    have hconv : ∀ x ∈ Ω, fderiv ℝ f x =
        (ηn.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Gs) x := by
      intro x hx
      have hr : ηn.rOut ≤ δ := by
        change δ / ((n : ℝ) + 2) ≤ δ
        exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      exact fderiv_convolution_eq_convolution_grad_local (φg := (φ₀, Gs))
        (hφ₀Lp.locallyIntegrable hp1') (hGsLp.locallyIntegrable hp1') hweakS ηn
        ((closedBall_subset_closedBall hr).trans (hball x hx))
    set C := ηn.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Gs
    have hcongr : φ.grad - u.grad =ᵐ[volume.restrict Ω]
        (φ.grad - fderiv ℝ f) + (C - Gs) + (Gs - gm) := by
      filter_upwards [ae_restrict_mem hΩo.measurableSet, ae_restrict_of_ae hgmeq] with x hx hgx
      simp only [Pi.add_apply, Pi.sub_apply, hgx, indicator_of_mem hx, ← hconv x hx]
      abel
    have hfdC : Continuous (fderiv ℝ f) := hfC1.continuous_fderiv one_ne_zero
    have hm1 : AEStronglyMeasurable (φ.grad - fderiv ℝ f) (volume.restrict Ω) :=
      φ.memLp_grad.1.sub hfdC.aestronglyMeasurable
    have hCc : Continuous C := ηn.hasCompactSupport_normed.continuous_convolution_left _
      ηn.continuous_normed (hGsLp.locallyIntegrable hp1')
    have hm2 : AEStronglyMeasurable (C - Gs) (volume.restrict Ω) :=
      hCc.aestronglyMeasurable.sub hGsm.aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (Gs - gm) (volume.restrict Ω) :=
      (hGsm.sub hgm).aestronglyMeasurable
    have hb1 : eLpNorm (φ.grad - fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict Ω) ≤
        ENNReal.ofReal (ε / 4) := by
      refine (eLpNorm_le_of_ae_bound (C := ε') (ae_restrict_of_ae hφgrad)).trans ?_
      rw [Measure.restrict_apply_univ]
      calc volume Ω ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal ε'
          ≤ volume Ω ^ (ENNReal.ofReal p).toReal⁻¹ * e₂ := by gcongr
        _ = e₂ * volume Ω ^ (ENNReal.ofReal p).toReal⁻¹ := mul_comm _ _
        _ ≤ _ := he₂lt.le
    have hb2 : eLpNorm (C - Gs) (ENNReal.ofReal p) (volume.restrict Ω) ≤
        ENNReal.ofReal (ε / 4) :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hn8
    have hb3 : eLpNorm (Gs - gm) (ENNReal.ofReal p) (volume.restrict Ω) ≤
        ENNReal.ofReal (ε / 4) :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans h7
    rw [eLpNorm_congr_ae hcongr]
    calc eLpNorm ((φ.grad - fderiv ℝ f) + (C - Gs) + (Gs - gm)) (ENNReal.ofReal p)
          (volume.restrict Ω)
        ≤ eLpNorm (φ.grad - fderiv ℝ f) (ENNReal.ofReal p) (volume.restrict Ω) +
            eLpNorm (C - Gs) (ENNReal.ofReal p) (volume.restrict Ω) +
            eLpNorm (Gs - gm) (ENNReal.ofReal p) (volume.restrict Ω) :=
          (eLpNorm_add_le (hm1.add hm2) hm3 hp1'').trans
            (add_le_add_left (eLpNorm_add_le hm1 hm2 hp1'') _)
      _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
          add_le_add (add_le_add hb1 hb2) hb3
      _ ≤ _ := hsum
  · -- the energy
    have hb : ENNReal.ofReal ε' * volume Ω ≤ ENNReal.ofReal (ε / 4) :=
      (mul_le_mul' hε'1 le_rfl).trans he₁lt.le
    have h34 : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) hε4.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc intHom L φ = ∫⁻ x in Ω, L (φ.grad x) := rfl
      _ ≤ (∫⁻ x in Ω, L (fderiv ℝ f x)) + ENNReal.ofReal ε' * volume Ω := hφE
      _ ≤ (E + ENNReal.ofReal (ε / 2)) + ENNReal.ofReal (ε / 4) := add_le_add hn5.le hb
      _ = E + (ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4)) := add_assoc _ _ _
      _ ≤ E + ENNReal.ofReal ε := by gcongr

/-- **Proposition `approx-affine-etoile-cite`** ([oah-jpm11, Proposition 3.15]), proved: the
statement `CitedAffineApprox N m p` holds. For `u ∈ W^{1,p}(Ω)` with finite energy, there are
piecewise affine `φₙ ∈ Aff(Ω)` with `φₙ → u` and `∇φₙ → ∇u` in `Lᵖ(Ω)` and
`limsup ∫_Ω L(∇φₙ) ≤ ∫_Ω L(∇u)`. The hypothesis `N < p` of the statement is not used. -/
theorem citedAffineApprox_holds [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    CitedAffineApprox N m p := by
  intro _ Ω hΩ G α β hG hGlsc h0 hα L hLgr hLru hLc u hu
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 Fact.out
  have hεn : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose φ hA h1 h2 h3 using fun n : ℕ =>
    exists_affSet_approx_step hp hΩ hG hGlsc h0 hα hLgr hLru hLc u hu (hεn n)
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨φ, hA, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) h1, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) h2, ?_⟩
  have hlim : Tendsto (fun n : ℕ => intHom L u + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (intHom L u)) := by
    simpa using (tendsto_const_nhds (x := intHom L u)).add ht
  calc limsup (fun n => intHom L (φ n)) atTop
      ≤ limsup (fun n : ℕ => intHom L u + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop :=
        limsup_le_limsup (Eventually.of_forall h3)
    _ = intHom L u := hlim.limsup_eq

end Homogenization
