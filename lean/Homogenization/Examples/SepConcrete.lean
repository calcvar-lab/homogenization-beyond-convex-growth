import Homogenization.Examples.ProperDomainSepIV
import Homogenization.Casc

/-!
# Example `ex:sepconcrete`

The concrete data of the paper satisfy (Dg)–(Dab):
* `sepConcreteG`: `g̃(s) = eˢ` (convex, nondecreasing, `g̃(c+s) ≤ 0 + eᶜ g̃(s)`);
* `sepConcreteH`: `H(s) = 1/s`, `H(0) = ∞`, `γ = δ = 1`, `κ = N` (`H(tᴺs) = t⁻ᴺ H(s)`);
* `sepConcreteK`: `K = θ 1_{|ξ|_F ≥ 1}`, bounded, upper semicontinuous, nondecreasing along rays;
* `sepConcreteCoeff`: `a = b = a_ϱ = 1 + 1_{D_ϱ}` (`lemmacasc`), `η = 1`, `Λ = 2`.

`sepConcrete_not_continuousAt`: for every `ξ` with `v(ξ) ≠ 0`, `W_v(·,ξ)` is discontinuous at
every point of `ℝᴺ \ D_ϱ`, a set of measure at least `1 - ϱ` in the unit cell. The paper concludes
that (B2Sing) fails, because (B2Sing) forces `W(·,ξ)` to be continuous a.e.; that step is
`sepConcrete_not_B2Sing` in `SepConcreteB2Sing.lean`. `sepConcrete_sep_iv` applies
`prop:separating` (iv) to these data, without cited hypothesis.

Differences with the paper: the balls in `D_ϱ` are those of the sup norm of `Sp N` (as in
`lemmacasc`), and `|ξ|` in `K` is the Frobenius norm.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {m N : ℕ}

/-- (Dg) for Example `ex:sepconcrete`: `g̃(s) = eˢ`, with `A_c = 0`, `B_c = eᶜ`. -/
noncomputable def sepConcreteG (p : ℝ) (hp : (N : ℝ) < p) : ProperDomainGData N where
  p := p
  dim_lt_p := hp
  gTilde := fun s => ⟨Real.exp s, (Real.exp_pos _).le⟩
  gTilde_convex := fun x y t ht => by
    have h := convexOn_exp.2 (Set.mem_univ (x : ℝ)) (Set.mem_univ (y : ℝ)) t.2
      (sub_nonneg.2 (show (t : ℝ) ≤ 1 by exact_mod_cast ht)) (by simp)
    simp only [smul_eq_mul] at h
    change Real.exp ((t * x + (1 - t) * y : ℝ≥0) : ℝ) ≤ _
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_sub ht, NNReal.coe_one]
    exact h
  gTilde_monotone := fun x y hxy => by
    change Real.exp x ≤ Real.exp y
    exact Real.exp_le_exp.2 (by exact_mod_cast hxy)
  gTilde_shift := fun c => ⟨0, ⟨Real.exp c, (Real.exp_pos _).le⟩, fun s => by
    change Real.exp ((c + s : ℝ≥0) : ℝ) ≤ (0 : ℝ) + Real.exp c * Real.exp s
    rw [NNReal.coe_add, Real.exp_add, zero_add]⟩

/-- (DH) for Example `ex:sepconcrete`: `H(s) = 1/s`, `H(0) = ∞`, with `γ = δ = 1`, `κ = N`. -/
noncomputable def sepConcreteH [NeZero N] : ProperDomainHData N where
  H := fun s => (s : ℝ≥0∞)⁻¹
  dom_iff_pos := fun s => by simp [ENNReal.inv_lt_top, pos_iff_ne_zero]
  upperSemicontinuous :=
    (continuous_inv.comp ENNReal.continuous_coe).upperSemicontinuous
  gamma := 1
  delta := 1
  kappa := N
  gamma_pos := one_pos
  delta_pos := one_pos
  kappa_pos := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  tail_bound := fun s hs => by
    rw [ENNReal.ofReal_one]
    exact ENNReal.inv_le_one.2 (by exact_mod_cast hs)
  scaling := fun t s ht ht1 hs => by
    have htN : 0 < t ^ N := pow_pos ht N
    have hs0 : (0 : ℝ) < s := lt_of_le_of_ne s.2 (by exact_mod_cast hs.symm)
    have key : ∀ u : ℝ≥0, (u : ℝ) = t ^ N * s →
        (u : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (t ^ (-(N : ℝ))) * (s : ℝ≥0∞)⁻¹ := by
      intro u hu
      rw [ENNReal.coe_nnreal_eq u, ENNReal.coe_nnreal_eq s, hu,
        ← ENNReal.ofReal_inv_of_pos (mul_pos htN hs0), ← ENNReal.ofReal_inv_of_pos hs0,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, Real.rpow_natCast,
        mul_inv]
    exact key _ rfl

/-- `|tA|_F = |t| |A|_F`. -/
theorem matrixFrobeniusNorm_smul (t : ℝ) (A : Mat m N) :
    matrixFrobeniusNorm (t • A) = |t| * matrixFrobeniusNorm A := by
  unfold matrixFrobeniusNorm
  rw [map_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- (DK) for Example `ex:sepconcrete`: `K = θ 1_{|ξ|_F ≥ 1}`, bounded, upper semicontinuous,
nondecreasing along rays, with `C_K = θ + 1`. Any `θ ≥ 0` is accepted; for `θ > 0` (the paper's
choice) `K` is moreover nonconvex and discontinuous. -/
noncomputable def sepConcreteK (D : ProperDomainGData N) (hNm : N ≤ m) (θ : ℝ≥0) :
    ProperDomainKData N m D where
  dim_le_m := hNm
  K := {A : Mat m N | 1 ≤ matrixFrobeniusNorm A}.indicator fun _ => θ
  upperSemicontinuous := by
    have hcont : Continuous (matrixFrobeniusNorm (m := m) (N := N)) := by
      unfold matrixFrobeniusNorm; fun_prop
    exact (isClosed_le continuous_const hcont).upperSemicontinuous_indicator (by positivity)
  C_K := θ + 1
  C_K_pos := by positivity
  growth := fun A => by
    have hK : (({A : Mat m N | 1 ≤ matrixFrobeniusNorm A}.indicator (fun _ => θ) A : ℝ≥0) : ℝ)
        ≤ θ := by
      exact_mod_cast indicator_le_self' (fun _ _ => by positivity) A
    have hG : 0 ≤ (properDomainG D A).toReal := ENNReal.toReal_nonneg
    nlinarith [θ.2]
  ray_mono := fun t A ht0 ht1 => by
    by_cases h : 1 ≤ matrixFrobeniusNorm (t • A)
    · have hA : 1 ≤ matrixFrobeniusNorm A := by
        rw [matrixFrobeniusNorm_smul, abs_of_nonneg ht0] at h
        have hF : 0 ≤ matrixFrobeniusNorm A := by unfold matrixFrobeniusNorm; positivity
        nlinarith
      rw [indicator_of_mem (show t • A ∈ {A : Mat m N | 1 ≤ matrixFrobeniusNorm A} from h),
        indicator_of_mem (show A ∈ {A : Mat m N | 1 ≤ matrixFrobeniusNorm A} from hA)]
    · rw [indicator_of_notMem (show t • A ∉ {A : Mat m N | 1 ≤ matrixFrobeniusNorm A} from h)]
      positivity

/-- (Dab) for Example `ex:sepconcrete`: `a = b = a_ϱ = 1 + 1_{D_ϱ}` (`lemmacasc`), `η = 1`,
`Λ = 2`. -/
noncomputable def sepConcreteCoeff {q : ℕ → Sp N} {r : ℕ → ℝ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hr : ∀ j, 0 < r j) (hq : ∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ))
    (hsum : ∑' j, volume (Metric.ball (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ) :
    ProperDomainCoeffData N where
  eta := 1
  Lambda := 2
  eta_pos := one_pos
  eta_le_Lambda := by norm_num
  coeffA := cascCoeff q r
  coeffB := cascCoeff q r
  a_range := (lemmacasc hϱ hr hq hsum).2.2.2.1
  b_range := (lemmacasc hϱ hr hq hsum).2.2.2.1
  a_measurable := (lemmacasc hϱ hr hq hsum).1
  b_measurable := (lemmacasc hϱ hr hq hsum).1
  a_lowerSemicontinuous := (lemmacasc hϱ hr hq hsum).2.2.1
  b_lowerSemicontinuous := (lemmacasc hϱ hr hq hsum).2.2.1
  a_periodic := fun x z => (lemmacasc hϱ hr hq hsum).2.1 z x
  b_periodic := fun x z => (lemmacasc hϱ hr hq hsum).2.1 z x

/-- If `a = b` and `0 < K(ξ) + H(v(ξ)) < ∞`, then `W_v(·,ξ) = G(ξ) + a(·)(K(ξ) + H(v(ξ)))` is
continuous at `x` only if `a` is. -/
theorem continuousAt_coeff_of_continuousAt_Wv (D : ProperDomainGData N)
    (KD : ProperDomainKData N m D) (HD : ProperDomainHData N) (CD : ProperDomainCoeffData N)
    (hab : CD.coeffB = CD.coeffA) {ξ : Mat m N}
    (hc0 : (KD.K ξ : ℝ≥0∞) + HD.H (properDomainJacobian ξ) ≠ 0)
    (hct : (KD.K ξ : ℝ≥0∞) + HD.H (properDomainJacobian ξ) ≠ ⊤) {x : Sp N}
    (hx : ContinuousAt (fun y => properDomainWv D KD HD CD y ξ) x) :
    ContinuousAt CD.coeffA x := by
  set c := (KD.K ξ : ℝ≥0∞) + HD.H (properDomainJacobian ξ)
  have ha0 : ∀ y, 0 ≤ CD.coeffA y := fun y => CD.eta_pos.le.trans (CD.a_range y).1
  have hW : ∀ y, properDomainWv D KD HD CD y ξ =
      properDomainG D ξ + ENNReal.ofReal (CD.coeffA y) * c := by
    intro y
    simp only [properDomainWv, hab, c]
    ring
  have hGt : properDomainG D ξ ≠ ⊤ := (properDomainG_lt_top D ξ).ne
  have hfin : ∀ y, properDomainWv D KD HD CD y ξ ≠ ⊤ := fun y => by
    rw [hW]; exact ENNReal.add_ne_top.2 ⟨hGt, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct⟩
  have hf : ContinuousAt (fun y => (properDomainWv D KD HD CD y ξ).toReal) x :=
    ContinuousAt.comp (g := ENNReal.toReal) (f := fun y => properDomainWv D KD HD CD y ξ)
      (ENNReal.continuousAt_toReal (hfin x)) hx
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc0, hct⟩
  have e : CD.coeffA = fun y =>
      ((properDomainWv D KD HD CD y ξ).toReal - (properDomainG D ξ).toReal) / c.toReal := by
    funext y
    rw [hW, ENNReal.toReal_add hGt (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (ha0 y), add_sub_cancel_left,
      mul_div_cancel_right₀ _ hc]
  rw [e]
  exact (hf.sub continuousAt_const).div_const _

/-- **Example `ex:sepconcrete`.** For the data `g̃ = eˢ`, `H(s) = 1/s`, `K = θ 1_{|ξ|_F ≥ 1}`,
`a = b = a_ϱ`: for every `ξ` with `v(ξ) ≠ 0`, `W_v(·,ξ)` is discontinuous at every point of
`ℝᴺ \ D_ϱ`, a set of measure at least `1 - ϱ` in the unit cell. The paper deduces that (B2Sing)
fails, since (B2Sing) forces `W(·,ξ)` to be continuous a.e.; see `sepConcrete_not_B2Sing`. -/
theorem sepConcrete_not_continuousAt [NeZero N] {p : ℝ} (hp : (N : ℝ) < p) (hNm : N ≤ m)
    (θ : ℝ≥0) {q : ℕ → Sp N} {r : ℕ → ℝ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (hr : ∀ j, 0 < r j)
    (hq : ∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ))
    (hsum : ∑' j, volume (Metric.ball (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ) :
    (∀ ξ : Mat m N, properDomainJacobian ξ ≠ 0 → ∀ x ∉ cascSet q r,
      ¬ ContinuousAt (fun y => properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ)
        sepConcreteH (sepConcreteCoeff hϱ hr hq hsum) y ξ) x) ∧
      ENNReal.ofReal (1 - ϱ) ≤ volume (cube 1 (0 : Sp N) \ cascSet q r) := by
  refine ⟨fun ξ hξ x hx hcont => ?_, (lemmacasc hϱ hr hq hsum).2.2.2.2.2⟩
  have hH : (sepConcreteH (N := N)).H (properDomainJacobian ξ) =
      ((properDomainJacobian ξ : ℝ≥0) : ℝ≥0∞)⁻¹ := rfl
  have hc0 : ((sepConcreteK (sepConcreteG p hp) hNm θ).K ξ : ℝ≥0∞) +
      (sepConcreteH (N := N)).H (properDomainJacobian ξ) ≠ 0 := by
    rw [hH]
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.inv_pos.2 ENNReal.coe_ne_top) le_add_self)
  have hct : ((sepConcreteK (sepConcreteG p hp) hNm θ).K ξ : ℝ≥0∞) +
      (sepConcreteH (N := N)).H (properDomainJacobian ξ) ≠ ⊤ := by
    rw [hH]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.inv_ne_top.2 (by exact_mod_cast hξ)⟩
  exact (lemmacasc hϱ hr hq hsum).2.2.2.2.1 x hx
    (continuousAt_coeff_of_continuousAt_Wv _ _ _ (sepConcreteCoeff hϱ hr hq hsum) rfl hc0 hct
      hcont)

/-- Proposition `prop:separating` (iv) for the concrete data of Example `ex:sepconcrete`:
(H1)–(H8) hold and `∫_Ω W_v(x/ε, ∇u)` Γ-converges, without cited hypothesis
(`properDomainWv_sep_iv`, via `main_Ggrowth_final_unconditional`). -/
theorem sepConcrete_sep_iv [NeZero N] {p : ℝ} (hp : (N : ℝ) < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (hNm : N ≤ m) (θ : ℝ≥0) {q : ℕ → Sp N} {r : ℕ → ℝ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hr : ∀ j, 0 < r j) (hq : ∀ v : Fin N → ℚ, ∃ j z, q j + intVec z = fun i => (v i : ℝ))
    (hsum : ∑' j, volume (Metric.ball (0 : Sp N) (r j)) ≤ ENNReal.ofReal ϱ)
    {Ω : Set (Sp N)} (hΩ : StandingDomain Ω) :
    Hypotheses p (properDomainG (sepConcreteG p hp))
        (properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ) sepConcreteH
          (sepConcreteCoeff hϱ hr hq hsum)) ∧
      GammaConverges (X := W1p N m (ENNReal.ofReal p) Ω)
        (intFun (properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ) sepConcreteH
          (sepConcreteCoeff hϱ hr hq hsum)))
        (intHom (Whom p (properDomainWv (sepConcreteG p hp) (sepConcreteK _ hNm θ) sepConcreteH
          (sepConcreteCoeff hϱ hr hq hsum)))) :=
  have : Fact (1 ≤ ENNReal.ofReal (sepConcreteG p hp).p) := ‹Fact (1 ≤ ENNReal.ofReal p)›
  have h := properDomainWv_sep_iv (sepConcreteG p hp) (sepConcreteK _ hNm θ) sepConcreteH
    (sepConcreteCoeff hϱ hr hq hsum) hΩ
  ⟨h.1, h.2.2⟩

end Homogenization
