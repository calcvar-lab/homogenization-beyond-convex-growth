import Homogenization.Scaling
import Homogenization.Poincare

/-!
# Step 4 of the proof of Theorem `main-Ggrowth` (`eq:4.2`)

This file proves `Step4Statement` (equation `eq:4.2` of the paper) from the differentiation theorem
for set functions of [oah-cloz-jpm17, Theorem A.16] (Theorem `Vitali-envelope-cite`, stated as
`CitedVitaliEnvelope`; its inequality form is proved in `Vitali.lean`, the equality in
`VitaliEquality.lean`).

The proof follows Step 4 (a)–(f) of the paper:
* (b) the local minimization problems `m_u(A)` are subadditive (`mloc_le_sum`) and dominated by
  `∫_A β(1 + G(∇u))` thanks to the *set-function* bound (Z3) and the rescaling `iInf_rescale`;
* (c) their density is `𝒴_loc W(x/ε, ∇u(x))`, so that `m_u^*(Ω) = 𝒴_loc I_ε(u)`;
* (d) an almost optimal Vitali family gives `ψ_δ = u + ∑ᵢ φᵢ` with `I_ε(ψ_δ) ≤ m_u^δ(Ω) + 2η`;
  `ψ_δ ∈ W^{1,p}(Ω)` (countable gluing, weak gradient computed piece by piece);
* (e) `ψ_δ → u` in `Lᵖ` by Poincaré's inequality on cubes and the `p`-coercivity of `W`;
* (f) conclusion.

## Remark on the paper
In (d) the paper asserts `ψ_δ - u ∈ W^{1,∞}_0(Ω)`; with countably many `φᵢ` whose Lipschitz
constants need not be bounded this is not justified, but `ψ_δ ∈ W^{1,p}(Ω)` holds (by the
coercivity of `W`), which is all the argument needs and what is proved here.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-! ### The local minimization problems and the Vitali envelope -/

/-- `m_u(A) = inf { ∫_A W(y/ε, ∇u(y) + ∇φ(y)) dy : φ ∈ Aff₀(A) }`, with `D = ∇u`. -/
noncomputable def mloc (W : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ) (D : Sp N → Mat m N)
    (A : Set (Sp N)) : ℝ≥0∞ :=
  ⨅ φ ∈ (Aff0 A : Set (Sp N → Tgt m)), ∫⁻ y in A, W (ε⁻¹ • y) (D y + fderiv ℝ φ y)

/-- `𝒱^δ(A)`: countable families of pairwise disjoint open cubes `Q_{ρᵢ}(xᵢ)` with closure in `A`,
side `ρᵢ < δ`, covering `A` up to a null set. Empty cubes (`ρᵢ = 0`) are allowed so that every
countable family can be indexed by `ℕ`; since `S(∅) = 0` for the set functions considered, this
does not change `S^δ`. -/
def VitaliFam (δ : ℝ) (A : Set (Sp N)) : Set (ℕ → ℝ × Sp N) :=
  {c | (∀ i, 0 ≤ (c i).1 ∧ (c i).1 < δ) ∧ (∀ i, closure (cube (c i).1 (c i).2) ⊆ A) ∧
    (Pairwise fun i j => Disjoint (cube (c i).1 (c i).2) (cube (c j).1 (c j).2)) ∧
    volume (A \ ⋃ i, cube (c i).1 (c i).2) = 0}

/-- `S^δ(A) = inf { ∑ᵢ S(Qᵢ) : {Qᵢ} ∈ 𝒱^δ(A) }`. -/
noncomputable def vitaliDelta (S : Set (Sp N) → ℝ≥0∞) (δ : ℝ) (A : Set (Sp N)) : ℝ≥0∞ :=
  ⨅ c ∈ VitaliFam δ A, ∑' i, S (cube (c i).1 (c i).2)

/-- The Vitali envelope `S^*(A) = sup_{δ > 0} S^δ(A)`. -/
noncomputable def vitaliEnv (S : Set (Sp N) → ℝ≥0∞) (A : Set (Sp N)) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), vitaliDelta S δ A

variable (N) in
/-- **Theorem `Vitali-envelope-cite`** ([oah-cloz-jpm17, Theorem A.16]). The finite Radon
measure `ν ≪ 𝓛ᴺ` of the paper is written `ν = g 𝓛ᴺ` with `∫_Ω g < ∞` (Radon–Nikodym). It is
proved in `Homogenization.VitaliEquality` (`citedVitaliEnvelope_holds`). -/
def CitedVitaliEnvelope : Prop :=
  ∀ Ω : Set (Sp N), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ (S : Set (Sp N) → ℝ≥0∞) (g : Sp N → ℝ≥0∞), Measurable g → ∫⁻ x in Ω, g x < ⊤ →
      (∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) →
      (∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
        volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V) →
      ∃ dS : Sp N → ℝ≥0∞,
        (∀ᵐ x ∂(volume.restrict Ω),
          Tendsto (fun ρ => S (cube ρ x) / volume (cube ρ x)) (𝓝[>] 0) (𝓝 (dS x))) ∧
        ∀ A, IsOpen A → A ⊆ Ω → vitaliEnv S A = ∫⁻ x in A, dS x

variable (N) in
/-- The inequality form of Theorem `Vitali-envelope-cite`, which is all that Step 4 uses: the
same hypotheses give a density `dS` along centred cubes with `S^*(A) ≤ ∫_A dS`. It is proved in
`Homogenization.Vitali` (`vitaliEnvelopeUpper`). -/
def VitaliEnvelopeUpper : Prop :=
  ∀ Ω : Set (Sp N), IsOpen Ω → Bornology.IsBounded Ω →
    ∀ (S : Set (Sp N) → ℝ≥0∞) (g : Sp N → ℝ≥0∞), Measurable g → ∫⁻ x in Ω, g x < ⊤ →
      (∀ A, IsOpen A → A ⊆ Ω → S A ≤ ∫⁻ x in A, g x) →
      (∀ A U V, IsOpen A → IsOpen U → IsOpen V → A ⊆ Ω → Disjoint U V → U ∪ V ⊆ A →
        volume (A \ (U ∪ V)) = 0 → S A ≤ S U + S V) →
      ∃ dS : Sp N → ℝ≥0∞,
        (∀ᵐ x ∂(volume.restrict Ω),
          Tendsto (fun ρ => S (cube ρ x) / volume (cube ρ x)) (𝓝[>] 0) (𝓝 (dS x))) ∧
        ∀ A, IsOpen A → A ⊆ Ω → vitaliEnv S A ≤ ∫⁻ x in A, dS x

/-- The cited equality implies its inequality form. -/
theorem CitedVitaliEnvelope.upper (h : CitedVitaliEnvelope N) : VitaliEnvelopeUpper N := by
  intro Ω hΩo hΩb S g hg hgfin hdom hsub
  obtain ⟨dS, hdS, henv⟩ := h Ω hΩo hΩb S g hg hgfin hdom hsub
  exact ⟨dS, hdS, fun A hA hAΩ => (henv A hA hAΩ).le⟩

/-! ### Subadditivity of `m_u` -/

theorem zero_add_sum_mem_Aff0 {A : Set (Sp N)} {n : ℕ} {V : Fin n → Set (Sp N)}
    (hVo : ∀ i, IsOpen (V i)) (hVA : ∀ i, V i ⊆ A)
    (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVf : ∀ i, volume (A ∩ frontier (V i)) = 0) (hVc : volume (A \ ⋃ i, V i) = 0)
    {φ : Fin n → Sp N → Tgt m} (hφ : ∀ i, φ i ∈ Aff0 (V i)) : ∑ i, φ i ∈ Aff0 A := by
  have h := Aff0.add_sum (U := A) (χ := 0) (K := 0) (LipschitzWith.const 0) (fun _ _ => rfl)
    hVo hVA hVd hVf hVc (fun i y _ => hasFDerivAt_const (0 : Tgt m) y) hφ
  rwa [zero_add] at h

/-- **Gluing / subadditivity**: `m_u(A) ≤ ∑ᵢ m_u(Vᵢ)` for an a.e. partition of `A` by open sets
with negligible boundaries in `A`. -/
theorem mloc_le_sum (W : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ) (D : Sp N → Mat m N)
    {A : Set (Sp N)} {n : ℕ} {V : Fin n → Set (Sp N)} (hVo : ∀ i, IsOpen (V i))
    (hVA : ∀ i, V i ⊆ A) (hVd : Pairwise fun i j => Disjoint (V i) (V j))
    (hVf : ∀ i, volume (A ∩ frontier (V i)) = 0) (hVc : volume (A \ ⋃ i, V i) = 0) :
    mloc W ε D A ≤ ∑ i, mloc W ε D (V i) := by
  by_cases htop : ∃ i, mloc W ε D (V i) = ⊤
  · obtain ⟨i, hi⟩ := htop
    rw [ENNReal.sum_eq_top.2 ⟨i, Finset.mem_univ _, hi⟩]; exact le_top
  push Not at htop
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  set η' : ℝ≥0∞ := (η : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)
  have hη' : η' ≠ 0 := by
    simp only [η', ne_eq, ENNReal.div_eq_zero_iff, ENNReal.coe_eq_zero, not_or]
    exact ⟨hη.ne', by simp⟩
  have hex : ∀ i, ∃ φ ∈ (Aff0 (V i) : Set (Sp N → Tgt m)),
      ∫⁻ y in V i, W (ε⁻¹ • y) (D y + fderiv ℝ φ y) < mloc W ε D (V i) + η' := by
    intro i
    have := ENNReal.lt_add_right (htop i) hη'
    simpa [mloc, iInf_lt_iff] using this
  choose φ hφA hφlt using hex
  have hφ0 : ∀ i, ∀ y ∉ V i, φ i y = 0 := fun i => (Aff0.data (hφA i)).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.1
  have hΦ := zero_add_sum_mem_Aff0 hVo hVA hVd hVf hVc hφA
  calc mloc W ε D A ≤ ∫⁻ y in A, W (ε⁻¹ • y) (D y + fderiv ℝ (∑ i, φ i) y) := iInf₂_le _ hΦ
    _ = ∑ i, ∫⁻ y in V i, W (ε⁻¹ • y) (D y + fderiv ℝ (φ i) y) := by
        rw [lintegral_eq_sum_pieces hVo hVA hVd hVc]
        refine Finset.sum_congr rfl fun i _ => setLIntegral_congr_fun (hVo i).measurableSet
          fun y hy => ?_
        have heq : (∑ j, φ j) =ᶠ[𝓝 y] φ i := by
          filter_upwards [(hVo i).mem_nhds hy] with z hz
          exact sum_eq_of_mem_piece hVd hφ0 hz
        rw [heq.fderiv_eq]
    _ ≤ ∑ i, (mloc W ε D (V i) + η') := Finset.sum_le_sum fun i _ => (hφlt i).le
    _ = ∑ i, mloc W ε D (V i) + n * η' := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ ∑ i, mloc W ε D (V i) + η := by
        gcongr
        calc (n : ℝ≥0∞) * η' ≤ ((n : ℝ≥0∞) + 1) * η' := by gcongr; exact le_self_add
          _ = η := ENNReal.mul_div_cancel (by simp) (by simp)

/-- Subadditivity in the form required by Theorem `Vitali-envelope-cite` (ii). -/
theorem mloc_le_add (W : Sp N → Mat m N → ℝ≥0∞) (ε : ℝ) (D : Sp N → Mat m N)
    {A U V : Set (Sp N)} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hsub : U ∪ V ⊆ A) (hnull : volume (A \ (U ∪ V)) = 0) :
    mloc W ε D A ≤ mloc W ε D U + mloc W ε D V := by
  let F : Fin 2 → Set (Sp N) := ![U, V]
  have hunion : (⋃ i, F i) = U ∪ V := by
    ext y; simp [F, Fin.exists_fin_two]
  have hfr : ∀ i, volume (A ∩ frontier (F i)) = 0 := by
    intro i
    refine measure_mono_null (fun y (hy : y ∈ A ∩ frontier (F i)) =>
      (⟨hy.1, fun h => ?_⟩ : y ∈ A \ (U ∪ V))) hnull
    fin_cases i
    · rcases h with h | h
      · exact (hU.frontier_eq ▸ hy.2).2 h
      · exact (hUV.closure_left hV).le_bot ⟨(hU.frontier_eq ▸ hy.2).1, h⟩
    · rcases h with h | h
      · exact (hUV.symm.closure_left hU).le_bot ⟨(hV.frontier_eq ▸ hy.2).1, h⟩
      · exact (hV.frontier_eq ▸ hy.2).2 h
  have h := mloc_le_sum W ε D (V := F) (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i; exacts [subset_union_left.trans hsub, subset_union_right.trans hsub])
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hUV
      · exact hUV.symm
      · exact absurd rfl hij)
    hfr (by rw [hunion]; exact hnull)
  simpa [F, Fin.sum_univ_two] using h

/-! ### Series of functions with disjoint supports -/

theorem tsum_eq_of_disjoint {E : Type*} [NormedAddCommGroup E] {f : ℕ → Sp N → E}
    {Q : ℕ → Set (Sp N)} (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hf0 : ∀ i, ∀ y ∉ Q i, f i y = 0) {i : ℕ} {y : Sp N} (hy : y ∈ Q i) :
    ∑' k, f k y = f i y :=
  tsum_eq_single i fun k hk => hf0 k y fun h => (hQd hk).le_bot ⟨h, hy⟩

theorem tsum_eq_zero_of_notMem {E : Type*} [NormedAddCommGroup E] {f : ℕ → Sp N → E}
    {Q : ℕ → Set (Sp N)} (hf0 : ∀ i, ∀ y ∉ Q i, f i y = 0) {y : Sp N} (hy : y ∉ ⋃ i, Q i) :
    ∑' k, f k y = 0 := by
  rw [show (fun k => f k y) = fun _ => 0 from funext fun k =>
    hf0 k y fun h => hy (mem_iUnion.2 ⟨k, h⟩), tsum_zero]

theorem hasSum_of_disjoint {E : Type*} [NormedAddCommGroup E] {f : ℕ → Sp N → E}
    {Q : ℕ → Set (Sp N)} (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hf0 : ∀ i, ∀ y ∉ Q i, f i y = 0) (y : Sp N) : HasSum (fun k => f k y) (∑' k, f k y) := by
  by_cases hy : ∃ i, y ∈ Q i
  · obtain ⟨i, hi⟩ := hy
    rw [tsum_eq_of_disjoint hQd hf0 hi]
    exact hasSum_single i fun k hk => hf0 k y fun h => (hQd hk).le_bot ⟨h, hi⟩
  · have hy' : y ∉ ⋃ i, Q i := fun h => hy (mem_iUnion.1 h)
    rw [tsum_eq_zero_of_notMem hf0 hy', show (fun k => f k y) = fun _ => 0 from
      funext fun k => hf0 k y fun h => hy' (mem_iUnion.2 ⟨k, h⟩)]
    exact hasSum_zero

theorem measurable_tsum_of_disjoint {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {f : ℕ → Sp N → E} {Q : ℕ → Set (Sp N)}
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) (hf0 : ∀ i, ∀ y ∉ Q i, f i y = 0)
    (hf : ∀ i, Measurable (f i)) : Measurable fun y => ∑' k, f k y :=
  measurable_of_tendsto_metrizable (f := fun n y => ∑ k ∈ Finset.range n, f k y)
    (fun _ => Finset.measurable_sum _ fun k _ => hf k)
    (tendsto_pi_nhds.2 fun y => (hasSum_of_disjoint hQd hf0 y).tendsto_sum_nat)

/-! ### Domination and density of `m_u` (Step 4 (b)–(c)) -/

section PieceData

variable {W : Sp N → Mat m N → ℝ≥0∞} {ε : ℝ} {Ω : Set (Sp N)} {D : Sp N → Mat m N}
  {n : ℕ} {U : Fin n → Set (Sp N)} {ξ : Fin n → Mat m N}

/-- On a piece where `∇u ≡ ξⱼ`, `m_u(B) = εᴺ 𝒴 W(ε⁻¹B, ξⱼ)`. -/
theorem mloc_eq_rescale (hε : 0 < ε) {j : Fin n} (hD : ∀ᵐ y, y ∈ U j → D y = ξ j)
    {B : Set (Sp N)} (hB : MeasurableSet B) (hBU : B ⊆ U j) :
    mloc W ε D B = ENNReal.ofReal (ε ^ N) * Yt W ((ε • ·) ⁻¹' B) (ξ j) := by
  rw [← iInf_rescale W hε hB]
  refine iInf_congr fun φ => iInf_congr fun _ => setLIntegral_congr_fun_ae hB ?_
  filter_upwards [hD] with y hy hyB
  rw [hy (hBU hyB)]

theorem isBounded_preimage_smul {ε : ℝ} (hε : 0 < ε) {S : Set (Sp N)}
    (hS : Bornology.IsBounded S) : Bornology.IsBounded ((ε • ·) ⁻¹' S) := by
  rw [show ((ε • ·) ⁻¹' S : Set (Sp N)) = (fun x => (ε⁻¹)⁻¹ • x) ⁻¹' S by simp,
    Set.preimage_smul_inv₀ (inv_ne_zero hε.ne')]
  exact hS.smul₀ _

theorem volume_preimage_smul_mul {ε : ℝ} (hε : 0 < ε) (S : Set (Sp N)) :
    ENNReal.ofReal (ε ^ N) * volume ((ε • ·) ⁻¹' S) = volume S := by
  rw [Measure.addHaar_preimage_smul _ hε.ne', finrank_Sp, ← mul_assoc,
    abs_of_pos (inv_pos.2 (pow_pos hε N)), ← ENNReal.ofReal_mul (pow_pos hε N).le,
    mul_inv_cancel₀ (pow_pos hε N).ne', ENNReal.ofReal_one, one_mul]

/-- The density `g = ∑ⱼ 1_{Uⱼ} β(1 + G(ξⱼ))` of the dominating measure `ν`. -/
noncomputable def domDensity (G : Mat m N → ℝ≥0∞) (β : ℝ≥0) (U : Fin n → Set (Sp N))
    (ξ : Fin n → Mat m N) (y : Sp N) : ℝ≥0∞ :=
  ∑ j, (U j).indicator (fun _ => (β : ℝ≥0∞) * (1 + G (ξ j))) y

theorem measurable_domDensity (G : Mat m N → ℝ≥0∞) (β : ℝ≥0) (hUo : ∀ j, IsOpen (U j)) :
    Measurable (domDensity G β U ξ) :=
  Finset.measurable_sum _ fun j _ => measurable_const.indicator (hUo j).measurableSet

theorem lintegral_domDensity (G : Mat m N → ℝ≥0∞) (β : ℝ≥0) (hUo : ∀ j, IsOpen (U j))
    (A : Set (Sp N)) :
    ∫⁻ y in A, domDensity G β U ξ y = ∑ j, (β : ℝ≥0∞) * (1 + G (ξ j)) * volume (U j ∩ A) := by
  simp only [domDensity]
  rw [lintegral_finsetSum' _ fun j _ =>
    (measurable_const.indicator (hUo j).measurableSet).aemeasurable]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [setLIntegral_indicator (hUo j).measurableSet, setLIntegral_const]

/-- **Step 4 (b)**: `m_u(A) ≤ ν(A) = ∫_A β(1 + G(∇u))`, by the set-function bound (Z3). -/
theorem mloc_le_domDensity {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0}
    (h3 : ∀ ζ (V : Set (Sp N)), IsOpen V → Bornology.IsBounded V →
      (α : ℝ≥0∞) * volume V * G ζ ≤ Yt W V ζ ∧ Yt W V ζ ≤ β * volume V * (1 + G ζ))
    (hε : 0 < ε) (hΩb : Bornology.IsBounded Ω) (hUo : ∀ j, IsOpen (U j))
    (hUd : Pairwise fun i j => Disjoint (U i) (U j))
    (hUf : ∀ j, volume (Ω ∩ frontier (U j)) = 0) (hUc : volume (Ω \ ⋃ j, U j) = 0)
    (hD : ∀ j, ∀ᵐ y, y ∈ U j → D y = ξ j) {A : Set (Sp N)} (hA : IsOpen A) (hAΩ : A ⊆ Ω) :
    mloc W ε D A ≤ ∫⁻ y in A, domDensity G β U ξ y := by
  have hsum := mloc_le_sum W ε D (A := A) (V := fun j => A ∩ U j)
    (fun j => hA.inter (hUo j)) (fun j => inter_subset_left)
    (fun i j hij => (hUd hij).mono inter_subset_right inter_subset_right)
    (fun j => measure_mono_null (fun y (hy : y ∈ A ∩ frontier (A ∩ U j)) =>
      (⟨hAΩ hy.1, by
      have h1 := frontier_subset_closure hy.2
      have h2 : y ∉ A ∩ U j := fun h => ((hA.inter (hUo j)).frontier_eq ▸ hy.2).2 h
      rw [(hUo j).frontier_eq]
      exact ⟨closure_mono inter_subset_right h1, fun h => h2 ⟨hy.1, h⟩⟩⟩ :
        y ∈ Ω ∩ frontier (U j))) (hUf j))
    (measure_mono_null (fun y (hy : y ∈ A \ ⋃ j, A ∩ U j) => (⟨hAΩ hy.1, fun h => hy.2 (by
      obtain ⟨j, hj⟩ := mem_iUnion.1 h; exact mem_iUnion.2 ⟨j, hy.1, hj⟩)⟩ :
        y ∈ Ω \ ⋃ j, U j)) hUc)
  refine hsum.trans ?_
  rw [lintegral_domDensity G β hUo A]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [inter_comm (U j) A]
  · rw [mloc_eq_rescale hε (hD j) (hA.inter (hUo j)).measurableSet inter_subset_right]
    have hpo : IsOpen ((ε • ·) ⁻¹' (A ∩ U j) : Set (Sp N)) :=
      (hA.inter (hUo j)).preimage (continuous_const_smul ε)
    have hpb := isBounded_preimage_smul hε ((hΩb.subset hAΩ).subset (inter_subset_left (t := U j)))
    calc ENNReal.ofReal (ε ^ N) * Yt W ((ε • ·) ⁻¹' (A ∩ U j)) (ξ j)
        ≤ ENNReal.ofReal (ε ^ N) * (β * volume ((ε • ·) ⁻¹' (A ∩ U j)) * (1 + G (ξ j))) := by
          gcongr; exact (h3 _ _ hpo hpb).2
      _ = β * (1 + G (ξ j)) * volume (A ∩ U j) := by
          rw [← volume_preimage_smul_mul hε (A ∩ U j)]; ring

/-- `∫_Ω g < ∞` (Step 4 (a)): the gradients of `u` lie in `dom G` on pieces of positive measure,
because `𝒴_loc I_ε(u) < ∞` and `𝒴_loc W ≥ α G`. -/
theorem lintegral_domDensity_lt_top {G : Mat m N → ℝ≥0∞} {α β : ℝ≥0} (hα : 0 < α)
    (hgrowth : HasGGrowth G α β (Ytloc W)) (hΩb : Bornology.IsBounded Ω)
    (hUo : ∀ j, IsOpen (U j)) (hUΩ : ∀ j, U j ⊆ Ω) (hD : ∀ j, ∀ᵐ y, y ∈ U j → D y = ξ j)
    (hJ : ∫⁻ x in Ω, Ytloc W (ε⁻¹ • x) (D x) < ⊤) :
    ∫⁻ y in Ω, domDensity G β U ξ y < ⊤ := by
  rw [lintegral_domDensity G β hUo Ω]
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  rw [inter_eq_left.2 (hUΩ j)]
  have hUt : volume (U j) < ⊤ := (hΩb.subset (hUΩ j)).measure_lt_top
  by_cases h0 : volume (U j) = 0
  · rw [h0, mul_zero]; exact ENNReal.zero_lt_top
  have hG : (α : ℝ≥0∞) * G (ξ j) * volume (U j) < ⊤ := by
    calc (α : ℝ≥0∞) * G (ξ j) * volume (U j) = ∫⁻ x in U j, (α : ℝ≥0∞) * G (ξ j) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in U j, Ytloc W (ε⁻¹ • x) (D x) := by
          refine setLIntegral_mono_ae' (hUo j).measurableSet ?_
          filter_upwards [hD j] with x hx hxU
          rw [hx hxU]; exact (hgrowth _ _).1
      _ ≤ ∫⁻ x in Ω, Ytloc W (ε⁻¹ • x) (D x) := lintegral_mono_set (hUΩ j)
      _ < ⊤ := hJ
  have hGt : G (ξ j) < ⊤ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top (by simpa using hα.ne'), ENNReal.top_mul h0] at hG
    exact lt_irrefl _ hG
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hGt⟩)) hUt

theorem cube_subset_ball {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) : cube ρ x ⊆ Metric.ball x ρ := by
  intro y hy
  rw [Metric.mem_ball, dist_pi_lt_iff hρ]
  intro i
  have := hy i (mem_univ i)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [this.1, this.2]

/-- **Step 4 (c)**: the density of `m_u` is `𝒴_loc W(x/ε, ∇u(x))`. -/
theorem density_mloc_eq (hε : 0 < ε) (hΩo : IsOpen Ω) (hUo : ∀ j, IsOpen (U j))
    (hUc : volume (Ω \ ⋃ j, U j) = 0) (hD : ∀ j, ∀ᵐ y, y ∈ U j → D y = ξ j)
    {dS : Sp N → ℝ≥0∞}
    (hdS : ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun ρ => mloc W ε D (cube ρ x) /
      volume (cube ρ x)) (𝓝[>] 0) (𝓝 (dS x))) :
    ∀ᵐ x ∂(volume.restrict Ω), dS x = Ytloc W (ε⁻¹ • x) (D x) := by
  have hcov : ∀ᵐ x ∂(volume.restrict Ω), x ∈ ⋃ j, U j := by
    rw [ae_restrict_iff' hΩo.measurableSet]
    refine ae_iff.2 (measure_mono_null (fun y (hy : ¬(y ∈ Ω → y ∈ ⋃ i, U i)) => ?_) hUc)
    exact ⟨by_contra fun h => hy fun h' => absurd h' h, fun h => hy fun _ => h⟩
  have hDall : ∀ᵐ x ∂(volume.restrict Ω), ∀ j, x ∈ U j → D x = ξ j :=
    ae_restrict_of_ae (ae_all_iff.2 hD)
  filter_upwards [hdS, hcov, hDall] with x hx hxU hxD
  obtain ⟨j, hj⟩ := mem_iUnion.1 hxU
  rw [hxD j hj]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hUo j) x hj
  set h : ℝ → ℝ≥0∞ := fun t => Yt W (cube t (ε⁻¹ • x)) (ξ j) / volume (cube t (ε⁻¹ • x))
  have hc0 : ENNReal.ofReal (ε ^ N) ≠ 0 := by simp [hε, pow_pos]
  have heq : ∀ ρ, 0 < ρ → ρ < r →
      mloc W ε D (cube ρ x) / volume (cube ρ x) = h (ρ / ε) := by
    intro ρ hρ hρr
    have hsub : cube ρ x ⊆ U j := (cube_subset_ball hρ x).trans
      ((Metric.ball_subset_ball hρr.le).trans hball)
    rw [mloc_eq_rescale hε (hD j) (isOpen_cube ρ x).measurableSet hsub,
      preimage_smul_cube hε, volume_cube]
    change _ = Yt W (cube (ρ / ε) (ε⁻¹ • x)) (ξ j) / volume (cube (ρ / ε) (ε⁻¹ • x))
    rw [volume_cube,
      show ENNReal.ofReal ρ = ENNReal.ofReal ε * ENNReal.ofReal (ρ / ε) by
        rw [← ENNReal.ofReal_mul hε.le, mul_div_cancel₀ _ hε.ne'],
      mul_pow, ← ENNReal.ofReal_pow hε.le]
    exact ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top
  have hmul : Tendsto (fun t : ℝ => t * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (continuous_mul_const ε).tendsto (0 : ℝ)
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos ht hε
  have hth : Tendsto h (𝓝[>] 0) (𝓝 (dS x)) := by
    refine (hx.comp hmul).congr' ?_
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t * ε < r := by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (div_pos hr hε)] with t ht ht'
      exact ⟨ht, by have := ht'.2; rwa [lt_div_iff₀ hε] at this⟩
    filter_upwards [hsmall] with t ht
    simp only [Function.comp]
    rw [heq _ (mul_pos ht.1 hε) ht.2, mul_div_cancel_right₀ _ hε.ne']
  exact (hth.limsup_eq).symm

end PieceData

/-! ### Step 4 (d)–(e): the almost optimal competitor `ψ_δ = u + ∑ᵢ φᵢ` -/

section Competitor

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}

/-- Integrability of test-function products (as in `HasWeakGrad.add`). -/
theorem test_integrable (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Sp N → E}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict Ω)) {ψ : Sp N → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω)
    (v : Sp N) :
    Integrable (fun y => fderiv ℝ ψ y v • f y) ∧ Integrable (fun y => ψ y • f y) ∧
      (∀ y ∉ Ω, fderiv ℝ ψ y v = 0) ∧ ∀ y ∉ Ω, ψ y = 0 := by
  have hzero : ∀ y ∉ Ω, y ∉ tsupport ψ := fun y hy h => hy (hsub h)
  have hc1 : Continuous fun y => fderiv ℝ ψ y v :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C1, hC1⟩ := hc1.bounded_above_of_compact_support
    ((hcs.fderiv (𝕜 := ℝ)).mono fun y hy h => hy (by change fderiv ℝ ψ y v = 0; rw [h]; rfl))
  obtain ⟨C2, hC2⟩ := hψ.continuous.bounded_above_of_compact_support hcs
  have hs1 : ∀ y ∉ Ω, fderiv ℝ ψ y v = 0 := fun y hy => by
    have : fderiv ℝ ψ y = 0 := by
      by_contra h; exact hzero y hy (support_fderiv_subset ℝ h)
    rw [this]; rfl
  have hs2 : ∀ y ∉ Ω, ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport (hzero y hy)
  exact ⟨integrable_smul_of_memLp hΩo hΩb hf hc1 hC1 hs1,
    integrable_smul_of_memLp hΩo hΩb hf hψ.continuous hC2 hs2, hs1, hs2⟩

/-- The weak gradient is only determined almost everywhere. -/
theorem HasWeakGrad.congr_grad_ae {U : Set (Sp N)} {f : Sp N → Tgt m} {g g' : Sp N → Mat m N}
    (h : HasWeakGrad U f g) (hgg : g =ᵐ[volume] g') : HasWeakGrad U f g' := by
  intro ψ hψ hcs hsub v
  rw [h ψ hψ hcs hsub v]
  congr 1
  exact integral_congr_ae (hgg.mono fun y hy => by dsimp only; rw [hy])

theorem enorm_rpow_eq_tsum_indicator {E : Type*} [NormedAddCommGroup E]
    {Q : ℕ → Set (Sp N)} (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    {F : Sp N → E} {h : ℕ → Sp N → E} (hFQ : ∀ i, ∀ y ∈ Q i, F y = h i y)
    (hFout : ∀ y ∉ ⋃ i, Q i, F y = 0) (y : Sp N) :
    ‖F y‖ₑ ^ p = ∑' i, (Q i).indicator (fun y => ‖h i y‖ₑ ^ p) y := by
  have hp0 : 0 < p := by linarith [ENNReal.one_le_ofReal.1 hP.out]
  by_cases hy : ∃ i, y ∈ Q i
  · obtain ⟨i, hi⟩ := hy
    rw [hFQ i y hi, tsum_eq_single i fun j hj =>
      indicator_of_notMem (fun h' => (hQd hj).le_bot ⟨h', hi⟩) _, indicator_of_mem hi]
  · have hy' : y ∉ ⋃ i, Q i := fun h' => hy (mem_iUnion.1 h')
    rw [hFout y hy', enorm_zero, ENNReal.zero_rpow_of_pos hp0]
    symm
    exact ENNReal.tsum_eq_zero.2 fun i => indicator_of_notMem (fun h' => hy ⟨i, h'⟩) _

theorem lintegral_enorm_rpow_le_tsum {E : Type*} [NormedAddCommGroup E]
    {Q : ℕ → Set (Sp N)} (hQo : ∀ i, IsOpen (Q i))
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j))
    {F : Sp N → E} {h : ℕ → Sp N → E} (hm : ∀ i, AEStronglyMeasurable (h i) volume)
    (hFQ : ∀ i, ∀ y ∈ Q i, F y = h i y) (hFout : ∀ y ∉ ⋃ i, Q i, F y = 0) :
    ∫⁻ y, ‖F y‖ₑ ^ p ≤ ∑' i, ∫⁻ y, ‖h i y‖ₑ ^ p := by
  rw [lintegral_congr fun y => enorm_rpow_eq_tsum_indicator hQd hFQ hFout y,
    lintegral_tsum fun i => ((hm i).enorm.pow_const p).indicator (hQo i).measurableSet]
  exact ENNReal.tsum_le_tsum fun i => by
    rw [lintegral_indicator (hQo i).measurableSet]
    exact setLIntegral_le_lintegral _ _

/-- **Countable gluing in `W^{1,p}_0`.** Competitors `uᵢ ∈ W^{1,p}_0(Qᵢ)` on pairwise disjoint
open sets `Qᵢ ⊆ O`, whose gradients vanish a.e. off `Qᵢ` and whose `Lᵖ` energies are summable,
glue to `(∑ᵢ uᵢ, ∑ᵢ 𝟙_{Qᵢ} ∇uᵢ) ∈ W^{1,p}_0(O)`. At each point at most one term is nonzero, so the
sums are pointwise and their `Lᵖ` norms are the sums of the pieces'; the weak-gradient identity
is obtained piece by piece and summed with `integral_iUnion`. -/
theorem W1p0.tsum_of_disjoint {O : Set (Sp N)} {Q : ℕ → Set (Sp N)} (hQo : ∀ i, IsOpen (Q i))
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) (hQO : ∀ i, Q i ⊆ O)
    {u : ℕ → (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : ∀ i, u i ∈ W1p0 (ENNReal.ofReal p) (Q i))
    (hgoff : ∀ i, ∀ᵐ y, y ∉ Q i → (u i).2 y = 0)
    (hsum1 : ∑' i, ∫⁻ y, ‖(u i).1 y‖ₑ ^ p < ⊤) (hsum2 : ∑' i, ∫⁻ y, ‖(u i).2 y‖ₑ ^ p < ⊤) :
    ((fun y => ∑' i, (u i).1 y), (fun y => ∑' i, (Q i).indicator (u i).2 y)) ∈
      W1p0 (ENNReal.ofReal p) O := by
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 hP.out
  have hp0 : 0 < p := by linarith
  have hPt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  set f : ℕ → Sp N → Tgt m := fun i => (u i).1 with hf_def
  set g : ℕ → Sp N → Mat m N := fun i => (Q i).indicator (u i).2 with hg_def
  have hf0 : ∀ i, ∀ y ∉ Q i, f i y = 0 := fun i => (hu i).1
  have hg0 : ∀ i, ∀ y ∉ Q i, g i y = 0 := fun i y hy => indicator_of_notMem hy _
  set Φ : Sp N → Tgt m := fun y => ∑' i, f i y with hΦ_def
  set Γ : Sp N → Mat m N := fun y => ∑' i, g i y with hΓ_def
  have hΦQ : ∀ i, ∀ y ∈ Q i, Φ y = f i y := fun i y hy => tsum_eq_of_disjoint hQd hf0 hy
  have hΓQ : ∀ i, ∀ y ∈ Q i, Γ y = (u i).2 y := fun i y hy => by
    change ∑' k, g k y = _
    rw [tsum_eq_of_disjoint hQd hg0 hy]
    exact indicator_of_mem hy _
  have hΦout : ∀ y ∉ ⋃ i, Q i, Φ y = 0 := fun y hy => tsum_eq_zero_of_notMem hf0 hy
  have hΓout : ∀ y ∉ ⋃ i, Q i, Γ y = 0 := fun y hy => tsum_eq_zero_of_notMem hg0 hy
  have hgae : ∀ i, (u i).2 =ᵐ[volume] g i := fun i => by
    filter_upwards [hgoff i] with y hy
    by_cases hyQ : y ∈ Q i
    · exact (indicator_of_mem hyQ _).symm
    · rw [hy hyQ]; exact (indicator_of_notMem hyQ _).symm
  have hfm : ∀ i, AEStronglyMeasurable (f i) volume := fun i => (hu i).2.1.1
  have hgm : ∀ i, AEStronglyMeasurable (g i) volume := fun i =>
    (hu i).2.2.1.1.indicator (hQo i).measurableSet
  have hΦm : AEStronglyMeasurable Φ volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun n y => ∑ i ∈ Finset.range n, f i y)
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun i _ => hfm i)
      (ae_of_all _ fun y => (hasSum_of_disjoint hQd hf0 y).tendsto_sum_nat)
  have hΓm : AEStronglyMeasurable Γ volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun n y => ∑ i ∈ Finset.range n, g i y)
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun i _ => hgm i)
      (ae_of_all _ fun y => (hasSum_of_disjoint hQd hg0 y).tendsto_sum_nat)
  have hΦLp : MemLp Φ (ENNReal.ofReal p) volume := by
    refine ⟨hΦm, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hP0 ENNReal.ofReal_ne_top).2 ?_⟩
    rw [hPt]
    exact (lintegral_enorm_rpow_le_tsum hQo hQd hfm hΦQ hΦout).trans_lt hsum1
  have hΓLp : MemLp Γ (ENNReal.ofReal p) volume := by
    refine ⟨hΓm, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hP0 ENNReal.ofReal_ne_top).2 ?_⟩
    rw [hPt]
    exact (lintegral_enorm_rpow_le_tsum hQo hQd (h := fun i => (u i).2)
      (fun i => (hu i).2.2.1.1) hΓQ hΓout).trans_lt hsum2
  refine ⟨fun y hy => hΦout y fun h' => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 h'
      exact hy (hQO i hi), hΦLp, hΓLp, ?_⟩
  -- the weak-gradient identity, piece by piece
  intro ψt hψ hcs _ v
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_ball (0 : Sp N)
  have hUo : IsOpen (Metric.ball (0 : Sp N) R) := Metric.isOpen_ball
  have hUb : Bornology.IsBounded (Metric.ball (0 : Sp N) R) := Metric.isBounded_ball
  obtain ⟨hi1, -, -, -⟩ := test_integrable hUo hUb (hΦLp.restrict _) hψ hcs hR v
  have hΓv : MemLp (fun y => Γ y v) (ENNReal.ofReal p) volume :=
    hΓLp.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ (Tgt m) v)
  obtain ⟨-, hi2, -, -⟩ := test_integrable hUo hUb (hΓv.restrict _) hψ hcs hR v
  have hout1 : ∀ y ∉ ⋃ i, Q i, fderiv ℝ ψt y v • Φ y = 0 := fun y hy => by
    rw [hΦout y hy, smul_zero]
  have hout2 : ∀ y ∉ ⋃ i, Q i, ψt y • Γ y v = 0 := fun y hy => by
    rw [hΓout y hy]; simp
  have key : ∀ i, ∫ y in Q i, fderiv ℝ ψt y v • Φ y = -∫ y in Q i, ψt y • Γ y v := by
    intro i
    rw [setIntegral_congr_fun (hQo i).measurableSet
        (g := fun y => fderiv ℝ ψt y v • f i y) fun y hy => by rw [hΦQ i y hy],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        rw [hf0 i y hy, smul_zero],
      (hu i).2.2.2 ψt hψ hcs (subset_univ _) v]
    congr 1
    rw [setIntegral_congr_fun (hQo i).measurableSet
        (g := fun y => ψt y • (u i).2 y v) fun y hy => by rw [hΓQ i y hy],
      setIntegral_eq_integral_of_ae_compl_eq_zero ((hgoff i).mono fun y hy hyQ => by
        rw [hy hyQ]; simp)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout1,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hout2,
    integral_iUnion (fun i => (hQo i).measurableSet) hQd hi1.integrableOn,
    integral_iUnion (fun i => (hQo i).measurableSet) hQd hi2.integrableOn]
  simp_rw [key]
  exact tsum_neg

/-- **Step 4 (d)–(e).** Given an almost optimal Vitali family, the competitor
`ψ_δ = u + ∑ᵢ φᵢ ∈ W^{1,p}(Ω)` satisfies `I_ε(ψ_δ) ≤ m_u^δ(Ω) + 2η`, the coercivity bound, and
the Poincaré bound `‖ψ_δ - u‖ᵖ_p ≤ m δᵖ ‖∇ψ_δ - ∇u‖ᵖ_p`. -/
theorem exists_competitor [NeZero N] {W : Sp N → Mat m N → ℝ≥0∞} {ε : ℝ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hε : 0 < ε)
    (u : W1p N m (ENNReal.ofReal p) Ω) {c₀ : ℝ≥0} (hc₀ : 0 < c₀)
    (hcoer : ∀ᵐ x, ∀ ζ : Mat m N, (c₀ : ℝ≥0∞) * ‖ζ‖ₑ ^ p ≤ W x ζ)
    {δ : ℝ} {η : ℝ≥0∞} (hη : 0 < η) (hηt : η ≠ ⊤)
    (hfin : vitaliDelta (mloc W ε u.grad) δ Ω < ⊤) :
    ∃ ψ : W1p N m (ENNReal.ofReal p) Ω,
      intFun W ε ψ ≤ vitaliDelta (mloc W ε u.grad) δ Ω + η + η ∧
      (c₀ : ℝ≥0∞) * ∫⁻ y in Ω, ‖ψ.grad y‖ₑ ^ p ≤ intFun W ε ψ ∧
      ∫⁻ y in Ω, ‖ψ.toFun y - u.toFun y‖ₑ ^ p ≤
        m * ENNReal.ofReal δ ^ p * ∫⁻ y in Ω, ‖ψ.grad y - u.grad y‖ₑ ^ p := by
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 hP.out
  have hp0 : 0 < p := by linarith
  have hPt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  set D := u.grad
  -- an almost optimal Vitali family
  obtain ⟨c, hc, hlt⟩ : ∃ c ∈ VitaliFam δ Ω, ∑' i, mloc W ε D (cube (c i).1 (c i).2) <
      vitaliDelta (mloc W ε D) δ Ω + η := by
    have := ENNReal.lt_add_right hfin.ne hη.ne'
    simpa only [vitaliDelta, iInf_lt_iff, exists_prop] using this
  obtain ⟨hρ, hcl, hQd, hcov⟩ := hc
  set Q : ℕ → Set (Sp N) := fun i => cube (c i).1 (c i).2
  have hQo : ∀ i, IsOpen (Q i) := fun i => isOpen_cube _ _
  have hQΩ : ∀ i, Q i ⊆ Ω := fun i => subset_closure.trans (hcl i)
  -- summable slack
  set w : ℕ → ℝ≥0∞ := fun i => η * 2⁻¹ ^ (i + 1)
  have hw_pos : ∀ i, 0 < w i := fun i => ENNReal.mul_pos hη.ne' (pow_ne_zero _ (by simp))
  have hw_sum : ∑' i, w i = η := by
    simp only [w]
    rw [ENNReal.tsum_mul_left]
    simp_rw [pow_succ']
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  -- almost optimal correctors on the cubes
  have hmfin : ∀ i, mloc W ε D (Q i) < ⊤ := fun i =>
    (ENNReal.le_tsum i).trans_lt (hlt.trans (ENNReal.add_lt_top.2 ⟨hfin, hηt.lt_top⟩))
  have hex : ∀ i, ∃ φ ∈ (Aff0 (Q i) : Set (Sp N → Tgt m)),
      ∫⁻ y in Q i, W (ε⁻¹ • y) (D y + fderiv ℝ φ y) < mloc W ε D (Q i) + w i := by
    intro i
    have := ENNReal.lt_add_right (hmfin i).ne (hw_pos i).ne'
    simpa [mloc, iInf_lt_iff] using this
  choose φ hφA hφlt using hex
  choose Kφ _ _ _ hKφ hφ0 _ using fun i => Aff0.data (hφA i)
  set Γi : ℕ → Sp N → Mat m N := fun i => (Q i).indicator (fderiv ℝ (φ i))
  have hΓ0 : ∀ i, ∀ y ∉ Q i, Γi i y = 0 := fun i y hy => indicator_of_notMem hy _
  set Φ : Sp N → Tgt m := fun y => ∑' i, φ i y
  set Γ : Sp N → Mat m N := fun y => ∑' i, Γi i y
  have hΦ0 : ∀ y ∉ Ω, Φ y = 0 := fun y hy =>
    tsum_eq_zero_of_notMem hφ0 (fun h => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact hy (hQΩ i hi))
  have hΓ0Ω : ∀ y ∉ Ω, Γ y = 0 := fun y hy =>
    tsum_eq_zero_of_notMem hΓ0 (fun h => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact hy (hQΩ i hi))
  have hΦQ : ∀ i, ∀ y ∈ Q i, Φ y = φ i y := fun i y hy => tsum_eq_of_disjoint hQd hφ0 hy
  have hΓQ : ∀ i, ∀ y ∈ Q i, Γ y = fderiv ℝ (φ i) y := fun i y hy => by
    change ∑' k, Γi k y = _
    rw [tsum_eq_of_disjoint hQd hΓ0 hy]; exact indicator_of_mem hy _
  have hΦmeas : Measurable Φ :=
    measurable_tsum_of_disjoint hQd hφ0 fun i => (hKφ i).continuous.measurable
  have hΓmeas : Measurable Γ := measurable_tsum_of_disjoint hQd hΓ0 fun i =>
    (measurable_fderiv ℝ (φ i)).indicator (hQo i).measurableSet
  have hΩQ : Ω =ᵐ[volume] ⋃ i, Q i :=
    ae_eq_set.2 ⟨hcov, by rw [sdiff_eq_empty.2 (iUnion_subset hQΩ), measure_empty]⟩
  have hdecomp : ∀ F : Sp N → ℝ≥0∞, ∫⁻ y in Ω, F y = ∑' i, ∫⁻ y in Q i, F y := fun F => by
    rw [setLIntegral_congr hΩQ, lintegral_iUnion (fun i => (hQo i).measurableSet) hQd]
  -- `∇φᵢ = 0` a.e. off `Qᵢ`
  have hfd_out : ∀ i, ∀ᵐ y, y ∉ Q i → fderiv ℝ (φ i) y = 0 := by
    intro i
    refine ae_iff.2 (measure_mono_null (fun y (hy : ¬(y ∉ Q i → fderiv ℝ (φ i) y = 0)) => ?_)
      (volume_frontier_cube (c i).1 (c i).2))
    change y ∈ frontier (Q i)
    rw [(hQo i).frontier_eq]
    refine ⟨by_contra fun hcl' => hy fun _ => ?_, fun h => hy fun h' => absurd h h'⟩
    have : φ i =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl'] with z hz
      exact hφ0 i z fun h => hz (subset_closure h)
    rw [this.fderiv_eq, fderiv_const_apply]
  -- energy
  have hEnergy : ∫⁻ y in Ω, W (ε⁻¹ • y) (D y + Γ y) ≤
      vitaliDelta (mloc W ε D) δ Ω + η + η := by
    rw [hdecomp]
    calc ∑' i, ∫⁻ y in Q i, W (ε⁻¹ • y) (D y + Γ y)
        = ∑' i, ∫⁻ y in Q i, W (ε⁻¹ • y) (D y + fderiv ℝ (φ i) y) :=
          tsum_congr fun i => setLIntegral_congr_fun (hQo i).measurableSet fun y hy => by
            rw [hΓQ i y hy]
      _ ≤ ∑' i, (mloc W ε D (Q i) + w i) := ENNReal.tsum_le_tsum fun i => (hφlt i).le
      _ = ∑' i, mloc W ε D (Q i) + η := by rw [ENNReal.tsum_add, hw_sum]
      _ ≤ vitaliDelta (mloc W ε D) δ Ω + η + η := by gcongr
  have hEfin : ∫⁻ y in Ω, W (ε⁻¹ • y) (D y + Γ y) < ⊤ :=
    hEnergy.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hfin, hηt.lt_top⟩,
      hηt.lt_top⟩)
  -- coercivity
  have hcoer' : ∀ᵐ y, ∀ ζ : Mat m N, (c₀ : ℝ≥0∞) * ‖ζ‖ₑ ^ p ≤ W (ε⁻¹ • y) ζ := by
    rw [ae_iff] at hcoer ⊢
    have : {y : Sp N | ¬∀ ζ : Mat m N, (c₀ : ℝ≥0∞) * ‖ζ‖ₑ ^ p ≤ W (ε⁻¹ • y) ζ} =
        (ε⁻¹ • · : Sp N → Sp N) ⁻¹' {x | ¬∀ ζ : Mat m N, (c₀ : ℝ≥0∞) * ‖ζ‖ₑ ^ p ≤ W x ζ} :=
      rfl
    rw [this, Measure.addHaar_preimage_smul _ (inv_ne_zero hε.ne'), hcoer, mul_zero]
  have hCoer : (c₀ : ℝ≥0∞) * ∫⁻ y in Ω, ‖D y + Γ y‖ₑ ^ p ≤
      ∫⁻ y in Ω, W (ε⁻¹ • y) (D y + Γ y) := by
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact lintegral_mono_ae (ae_restrict_of_ae (hcoer'.mono fun y hy => hy _))
  have hDΓfin : ∫⁻ y in Ω, ‖D y + Γ y‖ₑ ^ p < ⊤ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top (by exact_mod_cast hc₀.ne')] at hCoer
    exact (lt_irrefl _ (hEfin.trans_le' hCoer))
  -- `Γ ∈ Lᵖ(Ω)`
  have hDint : ∫⁻ y in Ω, ‖D y‖ₑ ^ p < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hP0 ENNReal.ofReal_ne_top
      u.memLp_grad.2
    rwa [hPt] at this
  have hptw : ∀ y, ‖Γ y‖ₑ ^ p ≤ 2 ^ (p - 1) * (‖D y + Γ y‖ₑ ^ p + ‖D y‖ₑ ^ p) := by
    intro y
    have h1 : ‖Γ y‖ₑ ≤ ‖D y + Γ y‖ₑ + ‖D y‖ₑ := by
      have h := nnnorm_sub_le (D y + Γ y) (D y)
      rw [add_sub_cancel_left] at h
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_add]
      exact ENNReal.coe_le_coe.2 h
    exact (ENNReal.rpow_le_rpow h1 hp0.le).trans (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)
  have hΓint : ∫⁻ y in Ω, ‖Γ y‖ₑ ^ p < ⊤ := by
    have hDm : AEMeasurable (fun y => ‖D y‖ₑ ^ p) (volume.restrict Ω) :=
      u.memLp_grad.1.enorm.pow_const p
    calc ∫⁻ y in Ω, ‖Γ y‖ₑ ^ p ≤ ∫⁻ y in Ω, 2 ^ (p - 1) * (‖D y + Γ y‖ₑ ^ p + ‖D y‖ₑ ^ p) :=
          lintegral_mono hptw
      _ = 2 ^ (p - 1) * ((∫⁻ y in Ω, ‖D y + Γ y‖ₑ ^ p) + ∫⁻ y in Ω, ‖D y‖ₑ ^ p) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
            ENNReal.ofNat_ne_top), lintegral_add_right' _ hDm]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith)
          ENNReal.ofNat_ne_top) (ENNReal.add_lt_top.2 ⟨hDΓfin, hDint⟩)
  have hΓLp : MemLp Γ (ENNReal.ofReal p) (volume.restrict Ω) :=
    ⟨hΓmeas.aestronglyMeasurable, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hP0
      ENNReal.ofReal_ne_top).2 (by rwa [hPt])⟩
  -- Poincaré
  have hfd_int : ∀ i, ∫⁻ y, ‖fderiv ℝ (φ i) y‖ₑ ^ p = ∫⁻ y in Q i, ‖Γ y‖ₑ ^ p := by
    intro i
    rw [← setLIntegral_congr_fun (hQo i).measurableSet (f := fun y => ‖fderiv ℝ (φ i) y‖ₑ ^ p)
      fun y hy => by rw [hΓQ i y hy], ← lintegral_indicator (hQo i).measurableSet]
    refine lintegral_congr_ae ((hfd_out i).mono fun y hy => ?_)
    by_cases hyQ : y ∈ Q i
    · rw [indicator_of_mem hyQ]
    · rw [indicator_of_notMem hyQ]
      change ‖fderiv ℝ (φ i) y‖ₑ ^ p = 0
      rw [hy hyQ, enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_pos hp0]
  have hPoinc : ∫⁻ y in Ω, ‖Φ y‖ₑ ^ p ≤ m * ENNReal.ofReal δ ^ p * ∫⁻ y in Ω, ‖Γ y‖ₑ ^ p := by
    rw [hdecomp, hdecomp, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun i => ?_
    calc ∫⁻ y in Q i, ‖Φ y‖ₑ ^ p = ∫⁻ y in Q i, ‖φ i y‖ₑ ^ p :=
          setLIntegral_congr_fun (hQo i).measurableSet fun y hy => by rw [hΦQ i y hy]
      _ ≤ ∫⁻ y, ‖φ i y‖ₑ ^ p := setLIntegral_le_lintegral _ _
      _ ≤ m * ENNReal.ofReal (c i).1 ^ p * ∫⁻ y, ‖fderiv ℝ (φ i) y‖ₑ ^ p :=
          poincare_cube hp (hKφ i) (hφ0 i)
      _ ≤ m * ENNReal.ofReal δ ^ p * ∫⁻ y in Q i, ‖Γ y‖ₑ ^ p := by
          rw [hfd_int i]
          gcongr
          exact (hρ i).2.le
  have hΦLp : MemLp Φ (ENNReal.ofReal p) (volume.restrict Ω) := by
    refine ⟨hΦmeas.aestronglyMeasurable, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hP0
      ENNReal.ofReal_ne_top).2 ?_⟩
    rw [hPt]
    refine hPoinc.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp)
      (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)) hΓint)
  -- the pieces belong to `W^{1,p}_0(Qᵢ)`; glue them (`W1p0.tsum_of_disjoint`)
  have hΓi_ae : ∀ i, fderiv ℝ (φ i) =ᵐ[volume] Γi i := fun i => by
    filter_upwards [hfd_out i] with y hy
    by_cases hyQ : y ∈ Q i
    · exact (indicator_of_mem hyQ _).symm
    · rw [hy hyQ]; exact (indicator_of_notMem hyQ _).symm
  have hΓi_int : ∀ i, ∫⁻ y, ‖Γi i y‖ₑ ^ p = ∫⁻ y in Q i, ‖Γ y‖ₑ ^ p := fun i => by
    rw [← hfd_int i]
    exact lintegral_congr_ae ((hΓi_ae i).mono fun y hy => by dsimp only; rw [hy])
  have hφi_int : ∀ i, ∫⁻ y, ‖φ i y‖ₑ ^ p = ∫⁻ y in Q i, ‖Φ y‖ₑ ^ p := fun i => by
    rw [setLIntegral_congr_fun (hQo i).measurableSet (g := fun y => ‖φ i y‖ₑ ^ p)
      fun y hy => by rw [hΦQ i y hy], ← lintegral_indicator (hQo i).measurableSet]
    refine lintegral_congr fun y => ?_
    by_cases hyQ : y ∈ Q i
    · rw [indicator_of_mem hyQ]
    · rw [indicator_of_notMem hyQ, hφ0 i y hyQ, enorm_zero, ENNReal.zero_rpow_of_pos hp0]
  have hpiece : ∀ i, (φ i, Γi i) ∈ W1p0 (ENNReal.ofReal p) (Q i) := by
    intro i
    have hcsupp : HasCompactSupport (φ i) :=
      HasCompactSupport.intro (isBounded_cube _ _).isCompact_closure fun y hy =>
        hφ0 i y fun h => hy (subset_closure h)
    refine ⟨hφ0 i, (hKφ i).continuous.memLp_of_hasCompactSupport hcsupp,
      ⟨((measurable_fderiv ℝ (φ i)).indicator (hQo i).measurableSet).aestronglyMeasurable, ?_⟩,
      (LipschitzWith.hasWeakGrad (hKφ i) univ).congr_grad_ae (hΓi_ae i)⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hP0 ENNReal.ofReal_ne_top, hPt,
      hΓi_int i]
    exact (lintegral_mono_set (hQΩ i)).trans_lt hΓint
  have hs1 : ∑' i, ∫⁻ y, ‖(φ i, Γi i).1 y‖ₑ ^ p < ⊤ := by
    simp only
    rw [tsum_congr hφi_int, ← hdecomp]
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hP0 ENNReal.ofReal_ne_top hΦLp.2
    rwa [hPt] at h
  have hs2 : ∑' i, ∫⁻ y, ‖(φ i, Γi i).2 y‖ₑ ^ p < ⊤ := by
    simp only
    rw [tsum_congr hΓi_int, ← hdecomp]
    exact hΓint
  have hglue := W1p0.tsum_of_disjoint hQo hQd hQΩ hpiece
    (fun i => ae_of_all _ fun y hy => indicator_of_notMem hy _) hs1 hs2
  have hΓeq : (fun y => ∑' i, (Q i).indicator (φ i, Γi i).2 y) = Γ := by
    funext y
    refine tsum_congr fun i => ?_
    simp only [Γi, indicator_indicator, inter_self]
  have hweak : HasWeakGrad Ω Φ Γ := by
    intro ψt hψ hcs hsub v
    have h := hglue.2.2.2 ψt hψ hcs (subset_univ _) v
    rw [hΓeq] at h
    exact h
  -- the competitor
  let ψ : W1p N m (ENNReal.ofReal p) Ω :=
    { toFun := u.toFun + Φ
      grad := u.grad + Γ
      memLp := memLp_add' u.memLp hΦLp
      memLp_grad := memLp_add' u.memLp_grad hΓLp
      weak := HasWeakGrad.add hΩo hΩb u.memLp u.memLp_grad hΦLp hΓLp u.weak hweak }
  refine ⟨ψ, hEnergy, hCoer, ?_⟩
  have e1 : ∀ y, ψ.toFun y - u.toFun y = Φ y := fun y => add_sub_cancel_left _ _
  have e2 : ∀ y, ψ.grad y - u.grad y = Γ y := fun y => add_sub_cancel_left _ _
  calc ∫⁻ y in Ω, ‖ψ.toFun y - u.toFun y‖ₑ ^ p = ∫⁻ y in Ω, ‖Φ y‖ₑ ^ p :=
        lintegral_congr fun y => by rw [e1]
    _ ≤ m * ENNReal.ofReal δ ^ p * ∫⁻ y in Ω, ‖Γ y‖ₑ ^ p := hPoinc
    _ = m * ENNReal.ofReal δ ^ p * ∫⁻ y in Ω, ‖ψ.grad y - u.grad y‖ₑ ^ p := by
        congr 1; exact lintegral_congr fun y => by rw [e2]

end Competitor

/-! ### Step 4 (f): conclusion -/

/-- **Step 4 of the proof of Theorem `main-Ggrowth`** (`eq:4.2`): for every `ε > 0` and every
piecewise affine `u`, there is a sequence `ψ_k → u` in `Lᵖ` with
`limsup I_ε(ψ_k) ≤ 𝒴_loc I_ε(u)`. -/
theorem step4 [NeZero N] {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)] {Ω : Set (Sp N)}
    (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    (hW : Hypotheses p G W) (hV : VitaliEnvelopeUpper N) : Step4Statement (p := p) W Ω := by
  intro ε hε u hu
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 hP.out
  have hp0 : 0 < p := by linarith
  have hPt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  set J := intFun (Ytloc W) ε u
  by_cases hJ : J = ⊤
  · exact ⟨fun _ => u, tendsto_const_nhds, by rw [hJ]; exact le_top⟩
  have hJt : J < ⊤ := lt_top_iff_ne_top.2 hJ
  obtain ⟨⟨⟨Kφ, hKφ⟩, n, U, ξ, hUo, hUΩ, hUd, hUf, hUc, hφU⟩, hgrad⟩ := hu
  have hΩm := hΩ.isOpen.measurableSet
  have hD : ∀ j, ∀ᵐ y, y ∈ U j → u.grad y = ξ j := by
    intro j
    have := (ae_restrict_iff' hΩm).1 hgrad
    filter_upwards [this] with y hy hyU
    rw [hy (hUΩ j hyU), (hφU j y hyU).fderiv]
  obtain ⟨α, β, hα, -, h3set⟩ := hW.setGrowth
  have hgrowth : HasGGrowth G α β (Ytloc W) := HasGGrowth.Ytloc h3set
  -- Theorem `Vitali-envelope-cite` applied to `m_u`
  obtain ⟨dS, hdS, henv⟩ := hV Ω hΩ.isOpen hΩ.bounded (mloc W ε u.grad) (domDensity G β U ξ)
    (measurable_domDensity G β hUo)
    (lintegral_domDensity_lt_top hα hgrowth hΩ.bounded hUo hUΩ hD hJt)
    (fun A hA hAΩ => mloc_le_domDensity h3set hε hΩ.bounded hUo hUd hUf hUc hD hA hAΩ)
    (fun A U' V' _ hU' hV' _ hUV hsub hnull => mloc_le_add W ε u.grad hU' hV' hUV hsub hnull)
  have hstar : vitaliEnv (mloc W ε u.grad) Ω ≤ J :=
    (henv Ω hΩ.isOpen subset_rfl).trans
      (le_of_eq (lintegral_congr_ae (density_mloc_eq hε hΩ.isOpen hUo hUc hD hdS)))
  have hδ : ∀ δ : ℝ, 0 < δ → vitaliDelta (mloc W ε u.grad) δ Ω ≤ J := fun δ hδ =>
    (le_iSup₂ (f := fun δ (_ : 0 < δ) => vitaliDelta (mloc W ε u.grad) δ Ω) δ hδ).trans hstar
  -- `p`-coercivity of `W` (Lemma `lem:consequences` (ii))
  obtain ⟨c₀, hc₀, h4coer⟩ := hW.coercive
  have hcoer : ∀ᵐ x, ∀ ζ : Mat m N, (c₀ : ℝ≥0∞) * ‖ζ‖ₑ ^ p ≤ W x ζ := by
    filter_upwards [hW.Ytloc_le] with x hx ζ
    refine le_trans (le_of_eq ?_) ((h4coer x ζ).trans (hx ζ))
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
  -- the competitors `ψ_k`, `δ_k = 1/(k+1)`
  set δn : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  set ηn : ℕ → ℝ≥0∞ := fun k => ((k : ℝ≥0∞) + 1)⁻¹
  have hδn : ∀ k, 0 < δn k := fun k => by positivity
  have hηn : ∀ k, 0 < ηn k := fun k => ENNReal.inv_pos.2 (by simp)
  have hηt : ∀ k, ηn k ≠ ⊤ := fun k => by simp [ηn]
  have hη1 : ∀ k, ηn k ≤ 1 := fun k => ENNReal.inv_le_one.2 (by simp)
  have hcomp := fun k => exists_competitor hΩ.isOpen hΩ.bounded hε u hc₀ hcoer (δ := δn k)
    (hηn k) (hηt k) ((hδ _ (hδn k)).trans_lt hJt)
  choose ψ hψE hψC hψP using hcomp
  have hE : ∀ k, intFun W ε (ψ k) ≤ J + ηn k + ηn k := fun k =>
    (hψE k).trans (by gcongr; exact hδ _ (hδn k))
  -- uniform bound on the gradients
  set B := ∫⁻ y in Ω, ‖u.grad y‖ₑ ^ p
  have hB : B < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hP0 ENNReal.ofReal_ne_top
      u.memLp_grad.2
    rwa [hPt] at this
  set C : ℝ≥0∞ := 2 ^ (p - 1) * ((J + 2) / c₀ + B)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith)
    ENNReal.ofNat_ne_top) (ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (by simpa using hJ)
      (by exact_mod_cast hc₀.ne'), hB.ne⟩)
  have hgradbound : ∀ k, ∫⁻ y in Ω, ‖(ψ k).grad y - u.grad y‖ₑ ^ p ≤ C := by
    intro k
    have hX : ∫⁻ y in Ω, ‖(ψ k).grad y‖ₑ ^ p ≤ (J + 2) / c₀ := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hc₀.ne')) (Or.inl
        ENNReal.coe_ne_top), mul_comm]
      refine (hψC k).trans ((hE k).trans ?_)
      rw [add_assoc, show (2 : ℝ≥0∞) = 1 + 1 by norm_num]
      gcongr <;> exact hη1 k
    have hptw : ∀ y, ‖(ψ k).grad y - u.grad y‖ₑ ^ p ≤
        2 ^ (p - 1) * (‖(ψ k).grad y‖ₑ ^ p + ‖u.grad y‖ₑ ^ p) := by
      intro y
      have h1 : ‖(ψ k).grad y - u.grad y‖ₑ ≤ ‖(ψ k).grad y‖ₑ + ‖u.grad y‖ₑ := by
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_add]
        exact ENNReal.coe_le_coe.2 (nnnorm_sub_le _ _)
      exact (ENNReal.rpow_le_rpow h1 hp0.le).trans
        (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)
    calc ∫⁻ y in Ω, ‖(ψ k).grad y - u.grad y‖ₑ ^ p
        ≤ ∫⁻ y in Ω, 2 ^ (p - 1) * (‖(ψ k).grad y‖ₑ ^ p + ‖u.grad y‖ₑ ^ p) := lintegral_mono hptw
      _ = 2 ^ (p - 1) * ((∫⁻ y in Ω, ‖(ψ k).grad y‖ₑ ^ p) + B) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
            ENNReal.ofNat_ne_top), lintegral_add_right' _ (u.memLp_grad.1.enorm.pow_const p)]
      _ ≤ C := mul_le_mul_right (add_le_add hX le_rfl) _
  -- `ψ_k → u` in `Lᵖ(Ω)`
  have hbound : ∀ k, ∫⁻ y in Ω, ‖(ψ k).toFun y - u.toFun y‖ₑ ^ p ≤
      m * ENNReal.ofReal (δn k) ^ p * C := fun k =>
    (hψP k).trans (mul_le_mul_right (hgradbound k) _)
  have hδn0 : Tendsto (fun k => ENNReal.ofReal (δn k)) atTop (𝓝 0) := by
    have : Tendsto δn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp this
    rw [ENNReal.ofReal_zero] at h
    exact h
  have hlim0 : Tendsto (fun k => (m : ℝ≥0∞) * ENNReal.ofReal (δn k) ^ p * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal (δn k) ^ p) atTop (𝓝 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp hδn0
      rw [ENNReal.zero_rpow_of_pos hp0] at h
      exact h
    have h2 := ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.natCast_ne_top m))) (Or.inr hC)
    simpa using h2
  have hint0 : Tendsto (fun k => ∫⁻ y in Ω, ‖(ψ k).toFun y - u.toFun y‖ₑ ^ p) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0 (fun _ => zero_le)
      hbound
  have hψu : Tendsto ψ atTop (𝓝 u) := by
    rw [tendsto_iff_edist_tendsto_0]
    have : ∀ k, edist (ψ k) u = (∫⁻ y in Ω, ‖(ψ k).toFun y - u.toFun y‖ₑ ^ p) ^ (1 / p) := by
      intro k
      rw [W1p.edist_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 ENNReal.ofReal_ne_top, hPt]
      rfl
    refine (tendsto_congr this).2 ?_
    have h := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hint0
    rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 hp0)] at h
    exact h
  -- conclusion
  have hηlim : Tendsto (fun k => J + ηn k + ηn k) atTop (𝓝 (J + 0 + 0)) := by
    have hη0 : Tendsto ηn atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      exact this.congr fun k => by simp [ηn, Function.comp]
    exact (tendsto_const_nhds.add hη0).add hη0
  rw [add_zero, add_zero] at hηlim
  refine ⟨ψ, hψu, ?_⟩
  calc limsup (fun k => intFun W ε (ψ k)) atTop
      ≤ limsup (fun k => J + ηn k + ηn k) atTop := limsup_le_limsup (Eventually.of_forall hE)
    _ = J := hηlim.limsup_eq

/-- **Theorem `main-Ggrowth`, with Steps 3 and 4 formalized.** The only remaining hypotheses are
the cited results (`th:AHM11`, `approx-affine-etoile-cite`, `Zenvelopefacts-cite` (i),
`prop:densityZaff`, `Vitali-envelope-cite`) and Proposition `prop:densityHaff` of the paper. -/
theorem main_Ggrowth_of_cited [NeZero N] (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (N : ℝ) < p) {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) {G : Mat m N → ℝ≥0∞}
    {W : Sp N → Mat m N → ℝ≥0∞} (hW : Hypotheses p G W)
    (hAHM : CitedAHM14 N m p) (hApprox : CitedAffineApprox N m p)
    (hLip : CitedZaffLocLip N m) (hZ : CitedDensityZaff N m) (hV : CitedVitaliEnvelope N)
    (hH : DensityHaff N m) :
    GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω) (intFun W) (intHom (Whom p W)) :=
  main_Ggrowth_of_densities p hp hΩ hW hAHM hApprox hLip hZ.toUpper hH (step4 hΩ hW hV.upper)

end Homogenization
