import Homogenization.Radial
import Homogenization.GammaConvergence

/-!
# Radial representation of ru-usc functions

Formalization of Proposition `prop:radialrep` of `Homogenization_beyond_convex_growthV1.tex`
(radial representation formula of [oahjpm14], with `X = 𝕄`, `u₀ = 0`,
`D = dom f`), for `f : 𝕄 → [0,∞]` and the radial envelope `f̂ = radial f`
(`f̂(ξ) = liminf_{t→1⁻} f(tξ)`).

The lower semicontinuous envelope is `f̄(ξ) = liminf_{ζ→ξ} f(ζ) = liminf f (𝓝 ξ)`, as in
[oahjpm14]. The sequential relaxation `lscEnv f` of `GammaConvergence.lean`
(`f̄ˢ` there) is also treated.

* `prop_radialrep_i` (part (i)): for `f` ru-usc, `f(tξ) → f̂(ξ)` as `t → 1⁻` for every `ξ`, `f̂` is
  ru-usc with the same constant, and `f̄ ≤ f̄ˢ ≤ f̂ ≤ f` everywhere. No star-shapedness is needed
  for these statements in this formalization.
* `prop_radialrep_ii` (part (ii)): if moreover `dom f` is strongly star-shaped
  (`t • closure (dom f) ⊆ dom f` for `0 ≤ t < 1`) and `f` is lower semicontinuous on `dom f`, then
  `f̂ = f̄ = f̄ˢ`, `f̂ = f` on `dom f` and `f̂ = ∞` off `closure (dom f)`.
-/

open Filter Topology Set
open scoped ENNReal NNReal Pointwise

namespace Homogenization

variable {N m : ℕ}

/-- `t • ξ → ξ` as `t → 1⁻`. -/
theorem tendsto_smul_nhdsLT_one (ξ : Mat m N) :
    Tendsto (fun t : ℝ => t • ξ) (𝓝[<] 1) (𝓝 ξ) := by
  have h : Tendsto (fun t : ℝ => t • ξ) (𝓝 1) (𝓝 ((1 : ℝ) • ξ)) :=
    (continuous_id.smul continuous_const).tendsto 1
  rw [one_smul] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- An ru-usc function lies above its radial envelope: `f̂ ≤ f`. -/
theorem RUUSCWith.radial_le {c : ℝ≥0} {f : Mat m N → ℝ≥0∞} (hf : RUUSCWith c (fun _ => f))
    (ξ : Mat m N) : Homogenization.radial f ξ ≤ f ξ := by
  by_contra h
  rw [not_le] at h
  by_cases htop : f ξ = ⊤
  · exact (not_top_lt (htop ▸ h)).elim
  obtain ⟨η, hη, hηb⟩ := exists_eta_affine_lt h htop c
  have hle : Homogenization.radial f ξ ≤ (1 + (η : ℝ≥0∞)) * f ξ + η * c :=
    le_of_tendsto (hf.tendsto_radial ξ) ((hf.le_affine hη).mono fun t ht => ht 0 ξ)
  exact (hle.trans_lt hηb).false

/-- The lower semicontinuous envelope lies below the radial envelope: `f̄ ≤ f̂`
(no hypothesis on `f`). -/
theorem liminf_nhds_le_radial (f : Mat m N → ℝ≥0∞) (ξ : Mat m N) :
    liminf f (𝓝 ξ) ≤ radial f ξ := by
  rw [radial, ← Function.comp_def f, liminf_comp]
  exact liminf_le_liminf_of_le (tendsto_smul_nhdsLT_one ξ)

/-- The lower semicontinuous envelope lies below the sequential one: `f̄ ≤ f̄ˢ`. -/
theorem liminf_nhds_le_lscEnv (f : Mat m N → ℝ≥0∞) (ξ : Mat m N) :
    liminf f (𝓝 ξ) ≤ lscEnv f ξ := by
  unfold lscEnv
  refine le_iInf₂ fun s hs => ?_
  rw [← Function.comp_def f, liminf_comp]
  exact liminf_le_liminf_of_le hs

/-- The (sequential) lower semicontinuous envelope lies below the radial envelope of an ru-usc
function: `f̄ ≤ f̂`. -/
theorem RUUSCWith.lscEnv_le_radial {c : ℝ≥0} {f : Mat m N → ℝ≥0∞}
    (hf : RUUSCWith c (fun _ => f)) (ξ : Mat m N) : lscEnv f ξ ≤ Homogenization.radial f ξ := by
  set t : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa [t, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
    · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simp only [t, mem_Iio]
      linarith
  have hs : Tendsto (fun n => t n • ξ) atTop (𝓝 ξ) := (tendsto_smul_nhdsLT_one ξ).comp ht
  unfold lscEnv
  refine (iInf₂_le (fun n => t n • ξ) hs).trans (le_of_eq ?_)
  exact ((hf.tendsto_radial ξ).comp ht).liminf_eq

/-- Lower semicontinuity relative to the effective domain gives lower semicontinuity at every
point of the domain, since `f = ∞` off `dom f`. -/
theorem lowerSemicontinuousAt_of_on_dom {f : Mat m N → ℝ≥0∞}
    (hlsc : LowerSemicontinuousOn f (dom f)) {ξ : Mat m N} (hξ : ξ ∈ dom f) :
    LowerSemicontinuousAt f ξ := by
  intro y hy
  have h := eventually_nhdsWithin_iff.1 (hlsc ξ hξ y hy)
  filter_upwards [h] with ζ hζ
  by_cases hζd : ζ ∈ dom f
  · exact hζ hζd
  · have : f ζ = ⊤ := by simpa [dom] using hζd
    rw [this]
    exact hy.trans_le le_top

/-- `f̂ = f` on `dom f` for `f` ru-usc and lower semicontinuous at `ξ`. -/
theorem RUUSCWith.radial_eq_of_lowerSemicontinuousAt {c : ℝ≥0} {f : Mat m N → ℝ≥0∞}
    (hf : RUUSCWith c (fun _ => f)) {ξ : Mat m N} (hlsc : LowerSemicontinuousAt f ξ) :
    Homogenization.radial f ξ = f ξ := by
  refine le_antisymm (hf.radial_le ξ) (le_of_forall_lt fun y hy => ?_)
  obtain ⟨z, hyz, hzf⟩ := exists_between hy
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), z < f (t • ξ) :=
    (tendsto_smul_nhdsLT_one ξ).eventually (hlsc z hzf)
  exact hyz.trans_le (ge_of_tendsto (hf.tendsto_radial ξ) (hev.mono fun _ h => h.le))

/-- `f̂ = ∞` off the closure of the effective domain (no hypothesis on `f`). -/
theorem radial_eq_top_of_not_mem_closure {f : Mat m N → ℝ≥0∞} {ξ : Mat m N}
    (hξ : ξ ∉ closure (dom f)) : radial f ξ = ⊤ := by
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), f (t • ξ) = ⊤ := by
    filter_upwards [(tendsto_smul_nhdsLT_one ξ).eventually
      (isClosed_closure.isOpen_compl.mem_nhds hξ)] with t ht
    have : t • ξ ∉ dom f := fun h => ht (subset_closure h)
    simpa [dom] using this
  exact (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)).liminf_eq

/-- `f̂ ≤ f̄` for `f` ru-usc, lower semicontinuous on `dom f`, with `dom f` strongly star-shaped.
This is the inequality `f̂ + χ_{closure D} ≤ f̄` of the proof of the radial representation formula
of [oahjpm14]. -/
theorem RUUSCWith.radial_le_liminf_nhds {c : ℝ≥0} {f : Mat m N → ℝ≥0∞}
    (hf : RUUSCWith c (fun _ => f))
    (hstar : ∀ t : ℝ, 0 ≤ t → t < 1 → t • closure (dom f) ⊆ dom f)
    (hlsc : LowerSemicontinuousOn f (dom f)) (ξ : Mat m N) :
    Homogenization.radial f ξ ≤ liminf f (𝓝 ξ) := by
  by_contra h
  rw [not_le] at h
  obtain ⟨b', hLb', hb'⟩ := exists_between h
  have hfreq : ∃ᶠ ζ in 𝓝 ξ, f ζ < b' :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hLb'
  by_cases hξ : ξ ∈ closure (dom f)
  · obtain ⟨η, hη, hηb⟩ := exists_eta_affine_lt hb' (hb'.trans_le le_top).ne c
    set B := (1 + (η : ℝ≥0∞)) * b' + η * c
    obtain ⟨t, ⟨htB, hta⟩, ht0⟩ := (((hf.tendsto_radial ξ).eventually (lt_mem_nhds hηb)).and
      (hf.le_affine hη)).and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)) |>.exists
    have htξ : t • ξ ∈ dom f := hstar t ht0.1.le ht0.2 (smul_mem_smul_set hξ)
    have hts : Tendsto (fun ζ : Mat m N => t • ζ) (𝓝 ξ) (𝓝 (t • ξ)) :=
      (continuous_const_smul t).tendsto ξ
    have hev : ∀ᶠ ζ in 𝓝 ξ, B < f (t • ζ) :=
      hts.eventually (lowerSemicontinuousAt_of_on_dom hlsc htξ B htB)
    obtain ⟨ζ, hζ1, hζ2⟩ := (hfreq.and_eventually hev).exists
    have : f (t • ζ) ≤ B :=
      (hta 0 ζ).trans (by simp only [B]; gcongr)
    exact (hζ2.trans_le this).false
  · have hev : ∀ᶠ ζ in 𝓝 ξ, ζ ∉ dom f := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hξ] with ζ hζ
      exact fun h => hζ (subset_closure h)
    obtain ⟨ζ, hζ1, hζ2⟩ := (hfreq.and_eventually hev).exists
    exact hζ2 (hζ1.trans (hb'.trans_le le_top))

/-- **Proposition `prop:radialrep` (i).** For `f` ru-usc relatively to `0` (with constant `c`):
the radial limit `f(tξ) → f̂(ξ)` as `t → 1⁻` exists for every `ξ`, `f̂` is ru-usc with the same
constant, and `f̄ ≤ f̄ˢ ≤ f̂ ≤ f` everywhere, where `f̄ = liminf f (𝓝 ·)` is the lower
semicontinuous envelope and `f̄ˢ = lscEnv f` the sequential relaxation.

The paper assumes `dom f` strongly star-shaped; this hypothesis is not needed here. -/
theorem prop_radialrep_i {c : ℝ≥0} {f : Mat m N → ℝ≥0∞} (hf : RUUSCWith c (fun _ => f)) :
    (∀ ξ, Tendsto (fun t : ℝ => f (t • ξ)) (𝓝[<] 1) (𝓝 (radial f ξ))) ∧
      RUUSCWith c (fun _ => radial f) ∧
      ∀ ξ, liminf f (𝓝 ξ) ≤ lscEnv f ξ ∧ lscEnv f ξ ≤ radial f ξ ∧ radial f ξ ≤ f ξ :=
  ⟨hf.tendsto_radial, hf.radial,
    fun ξ => ⟨liminf_nhds_le_lscEnv f ξ, hf.lscEnv_le_radial ξ, hf.radial_le ξ⟩⟩

/-- **Proposition `prop:radialrep` (ii).** If moreover `dom f` is strongly star-shaped
(`t • closure (dom f) ⊆ dom f` for `0 ≤ t < 1`) and `f` is lower semicontinuous on `dom f`, then
`f̂ = f̄ = f̄ˢ` (`f̄ = liminf f (𝓝 ·)`, `f̄ˢ = lscEnv f`) and
`f̂(ξ) = f(ξ)` on `dom f`, `f̂(ξ) = lim_{t→1⁻} f(tξ)` on `frontier (dom f)`, `f̂(ξ) = ∞` off
`closure (dom f)`. -/
theorem prop_radialrep_ii {c : ℝ≥0} {f : Mat m N → ℝ≥0∞} (hf : RUUSCWith c (fun _ => f))
    (hstar : ∀ t : ℝ, 0 ≤ t → t < 1 → t • closure (dom f) ⊆ dom f)
    (hlsc : LowerSemicontinuousOn f (dom f)) :
    (∀ ξ, radial f ξ = liminf f (𝓝 ξ)) ∧ radial f = lscEnv f ∧
      ∀ ξ, (ξ ∈ dom f → radial f ξ = f ξ) ∧
        (ξ ∈ frontier (dom f) → Tendsto (fun t : ℝ => f (t • ξ)) (𝓝[<] 1) (𝓝 (radial f ξ))) ∧
        (ξ ∉ closure (dom f) → radial f ξ = ⊤) :=
  ⟨fun ξ => le_antisymm (hf.radial_le_liminf_nhds hstar hlsc ξ) (liminf_nhds_le_radial f ξ),
    funext fun ξ => le_antisymm ((hf.radial_le_liminf_nhds hstar hlsc ξ).trans
      (liminf_nhds_le_lscEnv f ξ)) (hf.lscEnv_le_radial ξ),
    fun ξ => ⟨fun hξ => hf.radial_eq_of_lowerSemicontinuousAt
        (lowerSemicontinuousAt_of_on_dom hlsc hξ),
      fun _ => hf.tendsto_radial ξ, radial_eq_top_of_not_mem_closure⟩⟩

end Homogenization
