import Homogenization.Examples.SepConcrete
import Homogenization.Examples.ProperDomainNonconvex

/-!
# Example `ex:sepconcrete`: (B2Sing) fails

`PiClass` and `B2Sing` define the class `Π` and hypothesis (B2Sing) of [oah-leg-jpm-singhom],
as recalled in Section `sec:singular` of the paper. The two facts that the paper cites from
[oah-leg-jpm-singhom, Remarks 2.6 and 2.8] are proved here:
* `PiClass.ae_continuousAt`: every `λ ∈ Π` is continuous a.e.;
* `continuousAt_of_B2Sing_ineq`: under (B2Sing), `W(·,ξ)` is continuous at every continuity
  point of `λ`, when `W(·,ξ)` is finite everywhere.
Hence `B2Sing.ae_continuousAt`, and `sepConcrete_not_B2Sing`: for `ϱ < 1` and `N ≤ m`, the
concrete `W_v` of Example `ex:sepconcrete` does not satisfy (B2Sing). No cited hypothesis is used.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {m N : ℕ}

/-- The class `Π` of [oah-leg-jpm-singhom]: `λ : ℝᴺ → [0,∞[` Lebesgue measurable (`AEMeasurable`)
and essentially bounded (`λ ∈ L^∞`, as in the paper), such that for
every bounded open `U` with `|∂U| = 0` and every small `δ > 0` there is a compact `K_δ ⊆ Ū` with
`|∂K_δ| = 0`, `|Ū \ K_δ| < δ` and `λ|_{K_δ}` continuous. -/
def PiClass (lam : Sp N → ℝ) : Prop :=
  AEMeasurable lam ∧ (∀ x, 0 ≤ lam x) ∧ (∃ C : ℝ, ∀ᵐ x, lam x ≤ C) ∧
  ∀ U : Set (Sp N), IsOpen U → Bornology.IsBounded U → volume (frontier U) = 0 →
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∃ K : Set (Sp N), IsCompact K ∧ K ⊆ closure U ∧
      volume (frontier K) = 0 ∧ volume (closure U \ K) < ENNReal.ofReal δ ∧ ContinuousOn lam K

/-- Hypothesis (B2Sing): there is `λ ∈ Π` with
`W(x₁,ξ) ≤ |λ(x₁) - λ(x₂)| (1 + W(x₂,ξ)) + W(x₂,ξ)` for all `x₁, x₂, ξ`. -/
def B2Sing (W : Sp N → Mat m N → ℝ≥0∞) : Prop :=
  ∃ lam : Sp N → ℝ, PiClass lam ∧ ∀ x₁ x₂ ξ,
    W x₁ ξ ≤ ENNReal.ofReal |lam x₁ - lam x₂| * (1 + W x₂ ξ) + W x₂ ξ

/-- Every `λ ∈ Π` is continuous at a.e. point ([oah-leg-jpm-singhom, Remark 2.6]): on each cube
`U`, the discontinuity points of `λ` in `U` lie in `(Ū \ K_δ) ∪ ∂K_δ`, of measure `< δ`. -/
theorem PiClass.ae_continuousAt {lam : Sp N → ℝ} (h : PiClass lam) :
    ∀ᵐ x, ContinuousAt lam x := by
  have hU : ∀ n : ℕ, volume ({x | ¬ ContinuousAt lam x} ∩ cube (n : ℝ) 0) = 0 := by
    intro n
    obtain ⟨δ₀, hδ₀, hK⟩ := h.2.2.2 (cube (n : ℝ) 0) (isOpen_cube _ _) (isBounded_cube _ _)
      (volume_frontier_cube _ _)
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    set δ := min (ε : ℝ) (δ₀ / 2)
    have hδ : 0 < δ := lt_min hε (by linarith)
    obtain ⟨K, -, hKU, hKf, hKm, hKc⟩ := hK δ hδ (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    have hsub : {x | ¬ ContinuousAt lam x} ∩ cube (n : ℝ) 0 ⊆ (closure (cube (n : ℝ) 0) \ K) ∪
        frontier K := by
      rintro x ⟨hx, hxU⟩
      by_cases hxK : x ∈ K
      · by_cases hxi : x ∈ interior K
        · exact absurd (hKc.continuousAt (mem_interior_iff_mem_nhds.1 hxi)) hx
        · exact Or.inr ⟨subset_closure hxK, hxi⟩
      · exact Or.inl ⟨subset_closure hxU, hxK⟩
    calc volume ({x | ¬ ContinuousAt lam x} ∩ cube (n : ℝ) 0)
        ≤ volume ((closure (cube (n : ℝ) 0) \ K) ∪ frontier K) := measure_mono hsub
      _ ≤ volume (closure (cube (n : ℝ) 0) \ K) + volume (frontier K) := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ + 0 := by rw [hKf]; exact add_le_add hKm.le le_rfl
      _ ≤ 0 + ε := by
          rw [add_zero, zero_add]
          calc ENNReal.ofReal δ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (min_le_left _ _)
            _ = ε := ENNReal.ofReal_coe_nnreal
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hU)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖x‖)
  refine mem_iUnion.2 ⟨n, hx, ?_⟩
  intro i _
  have hi : |x i| ≤ ‖x‖ := by
    have := norm_le_pi_norm x i
    rwa [Real.norm_eq_abs] at this
  simp only [Pi.zero_apply, zero_sub, zero_add, mem_Ioo]
  constructor <;> [have := neg_abs_le (x i); have := le_abs_self (x i)] <;> linarith

/-- Under the (B2Sing) inequality, `W(·,ξ)` is continuous at every continuity point of `λ`,
when `W(·,ξ)` is finite everywhere ([oah-leg-jpm-singhom, Remark 2.8]):
`|W(y,ξ) - W(x,ξ)| ≤ d (1 + W(x,ξ)) (1 + d)` with `d = |λ(y) - λ(x)|`. -/
theorem continuousAt_of_B2Sing_ineq {W : Sp N → Mat m N → ℝ≥0∞} {lam : Sp N → ℝ}
    (hB : ∀ x₁ x₂ ξ, W x₁ ξ ≤ ENNReal.ofReal |lam x₁ - lam x₂| * (1 + W x₂ ξ) + W x₂ ξ)
    {ξ : Mat m N} (hfin : ∀ y, W y ξ ≠ ⊤) {x : Sp N} (hlam : ContinuousAt lam x) :
    ContinuousAt (fun y => W y ξ) x := by
  set w : Sp N → ℝ := fun y => (W y ξ).toReal
  have hw0 : ∀ y, 0 ≤ w y := fun y => ENNReal.toReal_nonneg
  have hreal : ∀ y z, w y ≤ |lam y - lam z| * (1 + w z) + w z := by
    intro y z
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin z⟩), hfin z⟩) (hB y z ξ)
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin z⟩)) (hfin z), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_add ENNReal.one_ne_top (hfin z),
      ENNReal.toReal_one] at h
  have hbound : ∀ y, |w y - w x| ≤
      |lam y - lam x| * (1 + w x) * (1 + |lam y - lam x|) := by
    intro y
    set d := |lam y - lam x|
    have hd : 0 ≤ d := abs_nonneg _
    have h1 := hreal y x
    have h2 := hreal x y
    rw [abs_sub_comm (lam x)] at h2
    have hx0 := hw0 x
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hx0,
      mul_nonneg hd hx0]
  have hwc : ContinuousAt w x := by
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have hd : Tendsto (fun y => |lam y - lam x|) (𝓝 x) (𝓝 0) := by
      have h1 : Tendsto (fun y => lam y - lam x) (𝓝 x) (𝓝 (lam x - lam x)) :=
        hlam.tendsto.sub tendsto_const_nhds
      rw [sub_self] at h1
      simpa using h1.abs
    have hlim : Tendsto (fun y => |lam y - lam x| * (1 + w x) * (1 + |lam y - lam x|)) (𝓝 x)
        (𝓝 0) := by
      have := (hd.mul_const (1 + w x)).mul (hd.const_add 1)
      simpa using this
    refine squeeze_zero (fun y => dist_nonneg) (fun y => ?_) hlim
    rw [Real.dist_eq]
    exact hbound y
  have e : (fun y => W y ξ) = fun y => ENNReal.ofReal (w y) := by
    funext y
    exact (ENNReal.ofReal_toReal (hfin y)).symm
  rw [e]
  exact ENNReal.continuous_ofReal.continuousAt.comp hwc

/-- If (B2Sing) holds and `W(·,ξ)` is finite everywhere, then `W(·,ξ)` is continuous at a.e.
point. -/
theorem B2Sing.ae_continuousAt {W : Sp N → Mat m N → ℝ≥0∞} (h : B2Sing W) {ξ : Mat m N}
    (hfin : ∀ y, W y ξ ≠ ⊤) : ∀ᵐ x, ContinuousAt (fun y => W y ξ) x := by
  obtain ⟨lam, hlam, hB⟩ := h
  filter_upwards [hlam.ae_continuousAt] with x hx
  exact continuousAt_of_B2Sing_ineq hB hfin hx

/-- **Example `ex:sepconcrete`: (B2Sing) fails.** For `ϱ < 1` and `N ≤ m`, the concrete `W_v`
does not satisfy (B2Sing): otherwise `W_v(·,ξ)` would be continuous a.e. for a full-rank `ξ`,
whereas it is discontinuous on `Y \ D_ϱ`, of measure `≥ 1 - ϱ > 0`. -/
theorem sepConcrete_not_B2Sing [NeZero N] {p : ℝ} (hp : (N : ℝ) < p) (hNm : N ≤ m)
    (θ : ℝ≥0) {q : ℕ → Sp N} {r : ℕ → ℝ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    (hr : ∀ j, 0 < r j) (hq : ∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ))
    (hsum : ∑' j, volume (Metric.ball (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ) :
    ¬ B2Sing (properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ) sepConcreteH
      (sepConcreteCoeff hϱ hr hq hsum)) := by
  intro hB
  set ξ := properDomainCoordinateEmbedding (m := m) (N := N) hNm
  have hξ : properDomainJacobian ξ ≠ 0 := properDomainCoordinateEmbedding_mem_sigma hNm
  obtain ⟨hdisc, hvol⟩ := sepConcrete_not_continuousAt hp hNm θ hϱ hr hq hsum
  have hfin : ∀ y, properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ) sepConcreteH
      (sepConcreteCoeff hϱ hr hq hsum) y ξ ≠ ⊤ := fun y => by
    have := dom_properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ) sepConcreteH
      (sepConcreteCoeff hϱ hr hq hsum) y
    have hmem : ξ ∈ dom (properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ)
        sepConcreteH (sepConcreteCoeff hϱ hr hq hsum) y) := by
      rw [this]; exact hξ
    exact hmem.ne
  have hae := hB.ae_continuousAt hfin
  have hnull : volume (cube 1 (0 : Sp N) \ cascSet q r) = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun x hx => ?_) hae
    exact hdisc ξ hξ x hx.2
  rw [hnull] at hvol
  have : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - ϱ) := ENNReal.ofReal_pos.2 (by linarith)
  exact absurd hvol (not_le.2 this)

end Homogenization
