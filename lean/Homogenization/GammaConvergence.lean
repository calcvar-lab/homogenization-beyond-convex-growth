import Mathlib

/-!
# Γ-convergence of families indexed by `ε → 0⁺`

Abstract part of `Homogenization_beyond_convex_growthV1.tex`, §2.1 (definition of the Γ(Lᵖ)-limits)
and the Γ-convergence logic of the proof of Theorem `main-Ggrowth`.

The ambient space `X` is a pseudo-extended-metric space: in the application `X = W^{1,p}(Ω;ℝᵐ)`
with the (pseudo-)distance of `Lᵖ(Ω;ℝᵐ)`. Families are maps `ℝ → X` and `ε → 0` means the filter
`𝓝[>] 0`, exactly as in the paper.

## Main results

* `GammaLimsup_le_limsup_of_approx`: the diagonal argument of Step 5.
* `GammaLimsup_mono` and `limsup_add_ofReal_le`: auxiliary monotonicity and limit estimates.
* `lscEnv`: the sequential lower semicontinuous envelope (used in `RadialRep.lean`).
* `GammaLimsup_le_liminf`: the Γ-limsup is sequentially lower semicontinuous (used in Step 2).
* `gammaConverges_of_steps`: Steps 1–5 of the proof of Theorem `main-Ggrowth`, at the level of
  abstract functionals.
-/

open Filter Topology Set
open scoped ENNReal

namespace Homogenization

section Defs

variable {X : Type*} [TopologicalSpace X]

/-- `Γ-liminf_{ε→0} F_ε (u) = inf { liminf F_ε(u_ε) : u_ε → u }`. -/
noncomputable def GammaLiminf (F : ℝ → X → ℝ≥0∞) (u : X) : ℝ≥0∞ :=
  ⨅ (v : ℝ → X) (_ : Tendsto v (𝓝[>] 0) (𝓝 u)), liminf (fun ε => F ε (v ε)) (𝓝[>] 0)

/-- `Γ-limsup_{ε→0} F_ε (u) = inf { limsup F_ε(u_ε) : u_ε → u }`. -/
noncomputable def GammaLimsup (F : ℝ → X → ℝ≥0∞) (u : X) : ℝ≥0∞ :=
  ⨅ (v : ℝ → X) (_ : Tendsto v (𝓝[>] 0) (𝓝 u)), limsup (fun ε => F ε (v ε)) (𝓝[>] 0)

/-- `{F_ε}` Γ-converges to `Fhom`: `Fhom ≤ Γ-liminf` and `Γ-limsup ≤ Fhom`. -/
def GammaConverges (F : ℝ → X → ℝ≥0∞) (Fhom : X → ℝ≥0∞) : Prop :=
  ∀ u, Fhom u ≤ GammaLiminf F u ∧ GammaLimsup F u ≤ Fhom u

/-- The sequential lower semicontinuous envelope
`f̄(u) = inf { liminf f(uₙ) : uₙ → u }`. -/
noncomputable def lscEnv (f : X → ℝ≥0∞) (u : X) : ℝ≥0∞ :=
  ⨅ (s : ℕ → X) (_ : Tendsto s atTop (𝓝 u)), liminf (fun n => f (s n)) atTop

theorem GammaLimsup_le {F : ℝ → X → ℝ≥0∞} {u : X} {v : ℝ → X}
    (hv : Tendsto v (𝓝[>] 0) (𝓝 u)) :
    GammaLimsup F u ≤ limsup (fun ε => F ε (v ε)) (𝓝[>] 0) :=
  iInf₂_le v hv

theorem GammaLiminf_le_GammaLimsup (F : ℝ → X → ℝ≥0∞) (u : X) :
    GammaLiminf F u ≤ GammaLimsup F u :=
  iInf₂_mono fun _ _ => liminf_le_limsup

/-- Monotonicity of the Γ-liminf (used in Step 1 with `J = 𝒴_loc I_ε ≤ I_ε`). -/
theorem GammaLiminf_mono {I J : ℝ → X → ℝ≥0∞}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u, J ε u ≤ I ε u) (u : X) :
    GammaLiminf J u ≤ GammaLiminf I u :=
  iInf₂_mono fun _ _ => liminf_le_liminf (h.mono fun _ hε => hε _)

/-- Monotonicity of the Γ-limsup. -/
theorem GammaLimsup_mono {I J : ℝ → X → ℝ≥0∞}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u, J ε u ≤ I ε u) (u : X) :
    GammaLimsup J u ≤ GammaLimsup I u :=
  iInf₂_mono fun _ _ => limsup_le_limsup (h.mono fun _ hε => hε _)

theorem lscEnv_le (f : X → ℝ≥0∞) (u : X) : lscEnv f u ≤ f u := by
  refine (iInf₂_le (fun _ => u) tendsto_const_nhds).trans ?_
  simp

end Defs

section EMetric

variable {X : Type*} [PseudoEMetricSpace X]

/-- A point realizing the lower semicontinuous envelope up to `δ`, at distance `< δ`. -/
theorem exists_near_le_lscEnv (f : X → ℝ≥0∞) (x : X) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ w, edist w x < δ ∧ f w ≤ lscEnv f x + δ := by
  by_cases htop : lscEnv f x = ⊤
  · exact ⟨x, by simpa using hδ, by simp [htop]⟩
  have hlt : lscEnv f x < lscEnv f x + δ := ENNReal.lt_add_right htop hδ.ne'
  obtain ⟨s, hs, hlim⟩ : ∃ s : ℕ → X, Tendsto s atTop (𝓝 x) ∧
      liminf (fun n => f (s n)) atTop < lscEnv f x + δ := by
    simpa [lscEnv, iInf_lt_iff] using hlt
  have h1 : ∃ᶠ n in atTop, f (s n) < lscEnv f x + δ :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hlim
  have h2 : ∀ᶠ n in atTop, edist (s n) x < δ := (EMetric.tendsto_nhds.1 hs) δ hδ
  obtain ⟨n, hn1, hn2⟩ := (h1.and_eventually h2).exists
  exact ⟨s n, hn2, hn1.le⟩

theorem tendsto_ofReal_nhdsGT_zero :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun ε : ℝ => ENNReal.ofReal ε) (𝓝 0) (𝓝 (ENNReal.ofReal 0)) :=
    ENNReal.continuous_ofReal.tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

/-- If `edist (w ε) (v ε) ≤ ρ ε → 0` and `v ε → u`, then `w ε → u`. -/
theorem tendsto_of_edist_le {ι : Type*} {l : Filter ι} {v w : ι → X} {u : X} {ρ : ι → ℝ≥0∞}
    (hv : Tendsto v l (𝓝 u)) (hρ : Tendsto ρ l (𝓝 0))
    (hw : ∀ᶠ i in l, edist (w i) (v i) ≤ ρ i) : Tendsto w l (𝓝 u) := by
  rw [EMetric.tendsto_nhds] at hv ⊢
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  filter_upwards [hv _ hη2, hρ.eventually_lt_const hη2, hw]
    with i h1 h2 h3
  calc edist (w i) u ≤ edist (w i) (v i) + edist (v i) u := edist_triangle _ _ _
    _ < η / 2 + η / 2 := ENNReal.add_lt_add (h3.trans_lt h2) h1
    _ = η := ENNReal.add_halves η

/-- `limsup (a ε + ε) ≤ limsup a` along `ε → 0⁺`. -/
theorem limsup_add_ofReal_le (a : ℝ → ℝ≥0∞) :
    limsup (fun ε => a ε + ENNReal.ofReal ε) (𝓝[>] 0) ≤ limsup a (𝓝[>] 0) := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hη' : (0 : ℝ≥0∞) < η := by exact_mod_cast hη
  calc limsup (fun ε => a ε + ENNReal.ofReal ε) (𝓝[>] 0)
      ≤ limsup (fun ε => a ε + η) (𝓝[>] 0) :=
        limsup_le_limsup ((tendsto_ofReal_nhdsGT_zero.eventually_lt_const hη').mono
          fun ε hε => add_le_add_right hε.le _)
    _ = limsup a (𝓝[>] 0) + η :=
        limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)

/-- The inequality used in Step 5 of the proof of the main theorem: if, for `ε` small, `v ε` is
the limit of a sequence along which `limsup I_ε ≤ a ε` (Step 4, `eq:4.2`), then
`Γ-limsup I (u) ≤ limsup a` for every family `v_ε → u`. The proof is the diagonal argument of
Step 5: for each `ε` one term of the sequence is chosen within `ε` of `v ε`. -/
theorem GammaLimsup_le_limsup_of_approx (I : ℝ → X → ℝ≥0∞) (a : ℝ → ℝ≥0∞) {u : X} {v : ℝ → X}
    (hv : Tendsto v (𝓝[>] 0) (𝓝 u))
    (happrox : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ψ : ℕ → X, Tendsto ψ atTop (𝓝 (v ε)) ∧
      limsup (fun k => I ε (ψ k)) atTop ≤ a ε) :
    GammaLimsup I u ≤ limsup a (𝓝[>] 0) := by
  classical
  have key : ∀ ε : ℝ, ∃ w : X, (0 < ε ∧ ∃ ψ : ℕ → X, Tendsto ψ atTop (𝓝 (v ε)) ∧
      limsup (fun k => I ε (ψ k)) atTop ≤ a ε) →
      edist w (v ε) ≤ ENNReal.ofReal ε ∧ I ε w ≤ a ε + ENNReal.ofReal ε := by
    intro ε
    by_cases hε : 0 < ε ∧ ∃ ψ : ℕ → X, Tendsto ψ atTop (𝓝 (v ε)) ∧
        limsup (fun k => I ε (ψ k)) atTop ≤ a ε
    · obtain ⟨hε0, ψ, hψ, hψa⟩ := hε
      have hη : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε0
      by_cases htop : a ε = ⊤
      · exact ⟨v ε, fun _ => ⟨by simp, by simp [htop]⟩⟩
      have hlt : limsup (fun k => I ε (ψ k)) atTop < a ε + ENNReal.ofReal ε :=
        hψa.trans_lt (ENNReal.lt_add_right htop hη.ne')
      have h1 : ∀ᶠ k in atTop, I ε (ψ k) < a ε + ENNReal.ofReal ε :=
        eventually_lt_of_limsup_lt hlt
      have h2 : ∀ᶠ k in atTop, edist (ψ k) (v ε) < ENNReal.ofReal ε :=
        (EMetric.tendsto_nhds.1 hψ) _ hη
      obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
      exact ⟨ψ k, fun _ => ⟨hk2.le, hk1.le⟩⟩
    · exact ⟨v ε, fun h => absurd h hε⟩
  choose w hw using key
  have hgood : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∃ ψ : ℕ → X, Tendsto ψ atTop (𝓝 (v ε)) ∧
      limsup (fun k => I ε (ψ k)) atTop ≤ a ε :=
    (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε) happrox).mono
      fun ε h => ⟨h.1, h.2⟩
  have hw_tend : Tendsto w (𝓝[>] 0) (𝓝 u) :=
    tendsto_of_edist_le hv tendsto_ofReal_nhdsGT_zero (hgood.mono fun ε hε => (hw ε hε).1)
  calc GammaLimsup I u ≤ limsup (fun ε => I ε (w ε)) (𝓝[>] 0) := GammaLimsup_le hw_tend
    _ ≤ limsup (fun ε => a ε + ENNReal.ofReal ε) (𝓝[>] 0) :=
        limsup_le_limsup (hgood.mono fun ε hε => (hw ε hε).2)
    _ ≤ limsup a (𝓝[>] 0) := limsup_add_ofReal_le _

/-- A diagonal extraction along `ε → 0⁺`: if each `P k` holds eventually, then `P (κ ε) ε` holds
eventually for some `κ ε → ∞`. -/
theorem exists_diagonal_nhdsGT (P : ℕ → ℝ → Prop) (hP : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P k ε) :
    ∃ κ : ℝ → ℕ, Tendsto κ (𝓝[>] 0) atTop ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (κ ε) ε := by
  classical
  have hδ : ∀ k, ∃ δ : ℝ, 0 < δ ∧ Ioo 0 δ ⊆ {ε | P k ε} := fun k =>
    (mem_nhdsGT_iff_exists_Ioo_subset.1 (hP k)).imp fun δ h => ⟨h.1, h.2⟩
  choose δ hδpos hδsub using hδ
  -- `d k = min (δ 0, …, δ k, 1/(k+1))`
  let d : ℕ → ℝ := fun k =>
    Nat.rec (min (δ 0) 1) (fun k dk => min dk (min (δ (k + 1)) (1 / ((k : ℝ) + 2)))) k
  have d_succ : ∀ k, d (k + 1) = min (d k) (min (δ (k + 1)) (1 / ((k : ℝ) + 2))) :=
    fun _ => rfl
  have d_pos : ∀ k, 0 < d k := by
    intro k
    induction k with
    | zero => exact lt_min (hδpos 0) one_pos
    | succ k ih =>
      rw [d_succ]
      exact lt_min ih (lt_min (hδpos _) (by positivity))
  have d_le_δ : ∀ k, d k ≤ δ k := by
    intro k
    cases k with
    | zero => exact min_le_left _ _
    | succ k => rw [d_succ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have d_le_inv : ∀ k, d k ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    cases k with
    | zero =>
      change min (δ 0) 1 ≤ 1 / (((0 : ℕ) : ℝ) + 1)
      simp
    | succ k =>
      rw [d_succ]
      refine (min_le_right _ _).trans ((min_le_right _ _).trans (le_of_eq ?_))
      push_cast; ring_nf
  have d_anti : Antitone d := by
    refine antitone_nat_of_succ_le fun k => ?_
    rw [d_succ]; exact min_le_left _ _
  have hex : ∀ ε : ℝ, 0 < ε → ∃ k, d (k + 1) ≤ ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    refine ⟨k, (d_le_inv (k + 1)).trans ?_⟩
    refine le_trans ?_ hk.le
    gcongr
    linarith
  let κ : ℝ → ℕ := fun ε => if h : ∃ k, d (k + 1) ≤ ε then Nat.find h else 0
  have hκ_lt : ∀ ε, 0 < ε → ε < d 0 → ε < d (κ ε) := by
    intro ε hε hε0
    have h := hex ε hε
    simp only [κ, dif_pos h]
    rcases hn : Nat.find h with _ | j
    · exact hε0
    · have := Nat.find_min h (show j < Nat.find h by omega)
      exact lt_of_not_ge this
  refine ⟨κ, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro K
    filter_upwards [Ioo_mem_nhdsGT (d_pos K)] with ε hε
    by_contra hlt
    push Not at hlt
    have h := hex ε hε.1
    have hspec := Nat.find_spec h
    have hκ : κ ε = Nat.find h := by simp only [κ, dif_pos h]
    rw [hκ] at hlt
    have : d K ≤ d (Nat.find h + 1) := d_anti (show Nat.find h + 1 ≤ K by omega)
    linarith [hε.2]
  · filter_upwards [Ioo_mem_nhdsGT (d_pos 0)] with ε hε
    exact hδsub _ ⟨hε.1, (hκ_lt ε hε.1 hε.2).trans_le (d_le_δ _)⟩

/-- The local infimum `inf_{w ∈ U} F_ε w`. -/
noncomputable def locInf (F : ℝ → X → ℝ≥0∞) (U : Set X) (ε : ℝ) : ℝ≥0∞ := ⨅ w ∈ U, F ε w

theorem limsup_locInf_le_GammaLimsup (F : ℝ → X → ℝ≥0∞) {u : X} {U : Set X} (hU : U ∈ 𝓝 u) :
    limsup (locInf F U) (𝓝[>] 0) ≤ GammaLimsup F u :=
  le_iInf₂ fun v hv => limsup_le_limsup ((hv.eventually_mem hU).mono fun _ hε => iInf₂_le _ hε)

/-- The hard half of the topological characterization of the Γ-limsup (a diagonal argument). -/
theorem GammaLimsup_le_iSup_locInf (F : ℝ → X → ℝ≥0∞) (u : X) :
    GammaLimsup F u ≤
      ⨆ k : ℕ, limsup (locInf F (Metric.eball u (((k : ℝ≥0∞) + 1)⁻¹))) (𝓝[>] 0) := by
  classical
  set S := ⨆ k : ℕ, limsup (locInf F (Metric.eball u (((k : ℝ≥0∞) + 1)⁻¹))) (𝓝[>] 0)
  by_cases hS : S = ⊤
  · rw [hS]; exact le_top
  let r : ℕ → ℝ≥0∞ := fun k => ((k : ℝ≥0∞) + 1)⁻¹
  have hr_pos : ∀ k, 0 < r k := fun k => ENNReal.inv_pos.2 (by simp)
  have hr_tend : Tendsto r atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero
    have h2 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      this.comp (tendsto_add_atTop_nat 1)
    simpa [r] using h2
  let P : ℕ → ℝ → Prop := fun k ε => ∃ w ∈ Metric.eball u (r k), F ε w < S + r k
  have hP : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P k ε := by
    intro k
    have hlt : limsup (locInf F (Metric.eball u (r k))) (𝓝[>] 0) < S + r k :=
      lt_of_le_of_lt (le_iSup (fun k : ℕ =>
        limsup (locInf F (Metric.eball u (((k : ℝ≥0∞) + 1)⁻¹))) (𝓝[>] 0)) k)
        (ENNReal.lt_add_right hS (hr_pos k).ne')
    filter_upwards [eventually_lt_of_limsup_lt hlt] with ε hε
    simp only [locInf, iInf_lt_iff] at hε
    obtain ⟨w, hw, h⟩ := hε
    exact ⟨w, hw, h⟩
  obtain ⟨κ, hκ, hPκ⟩ := exists_diagonal_nhdsGT P hP
  let v : ℝ → X := fun ε => if h : P (κ ε) ε then h.choose else u
  have hv_spec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      edist (v ε) u < r (κ ε) ∧ F ε (v ε) < S + r (κ ε) := by
    filter_upwards [hPκ] with ε hε
    simp only [v, dif_pos hε]
    exact ⟨hε.choose_spec.1, hε.choose_spec.2⟩
  have hrκ : Tendsto (fun ε => r (κ ε)) (𝓝[>] 0) (𝓝 0) := hr_tend.comp hκ
  have hv : Tendsto v (𝓝[>] 0) (𝓝 u) :=
    tendsto_of_edist_le tendsto_const_nhds hrκ (hv_spec.mono fun _ h => h.1.le)
  calc GammaLimsup F u ≤ limsup (fun ε => F ε (v ε)) (𝓝[>] 0) := GammaLimsup_le hv
    _ ≤ limsup (fun ε => S + r (κ ε)) (𝓝[>] 0) :=
        limsup_le_limsup (hv_spec.mono fun _ h => h.2.le)
    _ = S := by
        have : Tendsto (fun ε => S + r (κ ε)) (𝓝[>] 0) (𝓝 (S + 0)) :=
          tendsto_const_nhds.add hrκ
        rw [add_zero] at this
        exact this.limsup_eq

/-- The Γ-limsup is sequentially lower semicontinuous. -/
theorem GammaLimsup_le_liminf (F : ℝ → X → ℝ≥0∞) {u : X} {s : ℕ → X}
    (hs : Tendsto s atTop (𝓝 u)) :
    GammaLimsup F u ≤ liminf (fun n => GammaLimsup F (s n)) atTop := by
  refine (GammaLimsup_le_iSup_locInf F u).trans (iSup_le fun k => ?_)
  have hball : IsOpen (Metric.eball u (((k : ℝ≥0∞) + 1)⁻¹)) := Metric.isOpen_eball
  have hmem : ∀ᶠ n in atTop, s n ∈ Metric.eball u (((k : ℝ≥0∞) + 1)⁻¹) :=
    hs (Metric.eball_mem_nhds u (ENNReal.inv_pos.2 (by simp)))
  refine le_liminf_of_le (by isBoundedDefault) (hmem.mono fun n hn => ?_)
  exact limsup_locInf_le_GammaLimsup F (hball.mem_nhds hn)

/-- Abstract diagonal upper bound for `Γ-limsup`: families whose distances vanish and whose
energies are bounded by `a k` yield the bound `limsup a`. This statement has no application to
`intFun`, no `vitaliEnv` estimate, and no passage `t → 1`; Proposition 2.1(ii) is not proved. -/
theorem GammaLimsup_le_limsup_of_diagonal (F : ℝ → X → ℝ≥0∞) (u : X)
    (v : ℕ → ℝ → X) (r a : ℕ → ℝ≥0∞)
    (hr : Tendsto r atTop (𝓝 0))
    (hdist : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), edist (v k ε) u ≤ r k)
    (henergy : ∀ k, limsup (fun ε => F ε (v k ε)) (𝓝[>] 0) ≤ a k) :
    GammaLimsup F u ≤ limsup a atTop := by
  classical
  let P : ℕ → ℝ → Prop := fun k ε =>
    edist (v k ε) u ≤ r k ∧ F ε (v k ε) ≤ a k + ((k : ℝ≥0∞) + 1)⁻¹
  have hP : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P k ε := by
    intro k
    by_cases hak : a k = ⊤
    · filter_upwards [hdist k] with ε hε
      exact ⟨hε, by simp [hak]⟩
    · have δpos : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
      have hlt : a k < a k + ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.lt_add_right hak δpos.ne'
      have hev := eventually_lt_of_limsup_lt (lt_of_le_of_lt (henergy k) hlt)
      filter_upwards [hdist k, hev] with ε hε₁ hε₂
      exact ⟨hε₁, hε₂.le⟩
  obtain ⟨κ, hκ, hPκ⟩ := exists_diagonal_nhdsGT P hP
  let w : ℝ → X := fun ε => v (κ ε) ε
  have hspec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      edist (w ε) u ≤ r (κ ε) ∧
        F ε (w ε) ≤ a (κ ε) + ((κ ε : ℝ≥0∞) + 1)⁻¹ := by
    filter_upwards [hPκ] with ε hε
    exact hε
  have hrκ : Tendsto (fun ε => r (κ ε)) (𝓝[>] 0) (𝓝 0) := hr.comp hκ
  have hw : Tendsto w (𝓝[>] 0) (𝓝 u) :=
    tendsto_of_edist_le tendsto_const_nhds hrκ (hspec.mono fun _ h => h.1)
  let e : ℕ → ℝ≥0∞ := fun k => ((k : ℝ≥0∞) + 1)⁻¹
  have he : Tendsto e atTop (𝓝 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have h' : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 1)
    simpa [e] using h'
  have hek : Tendsto (fun ε => e (κ ε)) (𝓝[>] 0) (𝓝 0) := he.comp hκ
  have hlim : limsup (fun ε => a (κ ε)) (𝓝[>] 0) ≤ limsup a atTop := by
    by_cases htop : limsup a atTop = ⊤
    · rw [htop]; exact le_top
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    have hη' : (0 : ℝ≥0∞) < η := by exact_mod_cast hη
    have htail := eventually_lt_of_limsup_lt (ENNReal.lt_add_right htop hη'.ne')
    exact limsup_le_of_le (u := fun ε => a (κ ε))
      (a := limsup a atTop + η) (by isBoundedDefault)
      ((hκ.eventually htail).mono fun ε hε => hε.le)
  have henergyκ : limsup (fun ε => F ε (w ε)) (𝓝[>] 0) ≤ limsup a atTop := by
    calc limsup (fun ε => F ε (w ε)) (𝓝[>] 0)
        ≤ limsup (fun ε => a (κ ε) + e (κ ε)) (𝓝[>] 0) :=
          limsup_le_limsup (hspec.mono fun _ h => h.2)
      _ ≤ limsup (fun ε => a (κ ε)) (𝓝[>] 0) := by
          refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
          have hη' : (0 : ℝ≥0∞) < η := by exact_mod_cast hη
          have hsmall := hek.eventually_lt_const hη'
          calc limsup (fun ε => a (κ ε) + e (κ ε)) (𝓝[>] 0)
              ≤ limsup (fun ε => a (κ ε) + η) (𝓝[>] 0) :=
                limsup_le_limsup (hsmall.mono fun ε hε => add_le_add_right hε.le _)
            _ = limsup (fun ε => a (κ ε)) (𝓝[>] 0) + η :=
                limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)
      _ ≤ limsup a atTop := hlim
  exact (GammaLimsup_le hw).trans henergyκ


/-- **Steps 1–5 of the proof of Theorem `main-Ggrowth`, abstract form.**

* `I ε` is the functional `I_ε`, `J ε` is `𝒴_loc I_ε`, `A` the piecewise affine functions,
  `Fhom u = ∫ \widehat{ℋ(𝒴_loc W)}(∇u)` and `FΛ u = ∫ Λ(∇u)` with `Λ = 𝒵_aff ℋ_aff(𝒴_loc W)`.
* `hJI` : Step 1 (`𝒴_loc I_ε ≤ I_ε`, from (Z7));
* `hJ` : Γ-convergence of `J` (Theorem `th:AHM11` applied to `𝒴_loc W`);
* `hΛ` : `FΛ ≤ Fhom`, from (Z8);
* `hApprox` : Step 2 (Proposition `approx-affine-etoile-cite` applied to `Λ`);
* `hRecovery` : Step 3 (recovery sequence for piecewise affine data);
* `hKey` : Step 4 (`eq:4.2`: every `u ∈ Aff(Ω)` is the limit of a sequence `ψ_k` with
  `limsup I_ε(ψ_k) ≤ 𝒴_loc I_ε(u)`). -/
theorem gammaConverges_of_steps (I J : ℝ → X → ℝ≥0∞) (A : Set X) (Fhom FΛ : X → ℝ≥0∞)
    (hJI : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u, J ε u ≤ I ε u)
    (hJ : GammaConverges J Fhom)
    (hΛ : ∀ u, FΛ u ≤ Fhom u)
    (hApprox : ∀ u, Fhom u < ⊤ → ∃ φ : ℕ → X, (∀ n, φ n ∈ A) ∧
      Tendsto φ atTop (𝓝 u) ∧ limsup (fun n => FΛ (φ n)) atTop ≤ FΛ u)
    (hRecovery : ∀ φ ∈ A, FΛ φ < ⊤ → ∃ v : ℝ → X, Tendsto v (𝓝[>] 0) (𝓝 φ) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), v ε ∈ A) ∧ limsup (fun ε => J ε (v ε)) (𝓝[>] 0) ≤ FΛ φ)
    (hKey : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u ∈ A, ∃ ψ : ℕ → X, Tendsto ψ atTop (𝓝 u) ∧
      limsup (fun k => I ε (ψ k)) atTop ≤ J ε u) :
    GammaConverges I Fhom := by
  -- Step 5: the Γ-limsup inequality on piecewise affine data.
  have step5 : ∀ φ ∈ A, GammaLimsup I φ ≤ FΛ φ := by
    intro φ hφ
    by_cases htop : FΛ φ = ⊤
    · rw [htop]; exact le_top
    obtain ⟨v, hv, hvA, hvJ⟩ := hRecovery φ hφ (lt_top_iff_ne_top.2 htop)
    calc GammaLimsup I φ ≤ limsup (fun ε => J ε (v ε)) (𝓝[>] 0) :=
          GammaLimsup_le_limsup_of_approx I (fun ε => J ε (v ε)) hv
            (by filter_upwards [hKey, hvA] with ε h1 h2 using h1 _ h2)
      _ ≤ FΛ φ := hvJ
  intro u
  refine ⟨?_, ?_⟩
  · -- Step 1: Γ-liminf inequality.
    exact (hJ u).1.trans (GammaLiminf_mono hJI u)
  · -- Step 2: reduction to piecewise affine data.
    by_cases htop : Fhom u = ⊤
    · rw [htop]; exact le_top
    obtain ⟨φ, hφA, hφ, hφlim⟩ := hApprox u (lt_top_iff_ne_top.2 htop)
    calc GammaLimsup I u ≤ liminf (fun n => GammaLimsup I (φ n)) atTop :=
          GammaLimsup_le_liminf I hφ
      _ ≤ liminf (fun n => FΛ (φ n)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => step5 _ (hφA n))
      _ ≤ limsup (fun n => FΛ (φ n)) atTop := liminf_le_limsup
      _ ≤ FΛ u := hφlim
      _ ≤ Fhom u := hΛ u

end EMetric

end Homogenization
