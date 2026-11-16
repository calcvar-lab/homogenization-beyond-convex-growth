import Homogenization.DensityHaff
import Homogenization.Step3

/-!
# The subadditive theorem (`AK-SubadditiveTheorem` of [oah-jpm-zorgati14])

Let `S` be a `[0,∞]`-valued set function on bounded open subsets of `ℝᴺ` which is

* subadditive on a.e. partitions into two open sets,
* invariant under integer translations of cubes,
* bounded by `c |A|`.

Then `S(Q_L(w)) / |Q_L(w)| → inf_{k ≥ 1} S(kY) / |kY|` as `L → ∞`, uniformly in the centre `w`
(`SubaddCube.tendsto`), and in particular `S(ε⁻¹ Q) / |ε⁻¹ Q|` converges as `ε → 0⁺` for every
cube `Q` (`SubaddCube.tendsto_eps`). This deterministic version of the Akcoglu–Krengel theorem is
proved directly:

* **upper bound** (`SubaddCube.upper`): `Q_L(w)` contains the grid cells `k(z + Y)` that fit in it;
  they cover `Q_{L-2k}(w)` up to their null boundaries, so
  `S(Q_L(w)) ≤ |Q_L(w)| S(kY)/|kY| + c |Q_L(w) ∖ Q_{L-2k}(w)|`;
* **lower bound** (`SubaddCube.lower`): `Q_L(w)` lies in the integer cube `Q_K(z)`,
  `K = ⌈L⌉ + 1`, `z` the nearest integer point to `w`, so
  `|Q_K| inf_k S(kY)/|kY| ≤ S(Q_K(z)) ≤ S(Q_L(w)) + c |Q_K(z) ∖ Q_L(w)|`.

Here `Y = cube 1 0` is centred at `0`, as in the definition of `Hp`; cubes centred at integer
points are integer translates of each other.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N : ℕ}

/-- The hypotheses of the subadditive theorem. -/
structure SubaddCube (S : Set (Sp N) → ℝ≥0∞) (c : ℝ≥0) : Prop where
  /-- subadditivity on a.e. partitions into two open sets -/
  sub : ∀ A B C : Set (Sp N), IsOpen A → Bornology.IsBounded A → IsOpen B → IsOpen C →
    B ⊆ A → C ⊆ A → Disjoint B C → volume (A \ (B ∪ C)) = 0 → S A ≤ S B + S C
  /-- invariance of cubes under integer translations -/
  inv : ∀ (z : Fin N → ℤ) (ρ : ℝ) (x : Sp N), S (cube ρ (x + zcast z)) = S (cube ρ x)
  /-- domination by the Lebesgue measure -/
  bound : ∀ A : Set (Sp N), IsOpen A → Bornology.IsBounded A → S A ≤ c * volume A

/-! ### A first application: the `Ytp` cell problem -/

variable {m : ℕ}

/-- Addition preserves a global weak gradient. A compactly supported test function is contained in
a bounded open ball; restrict the global `Lᵖ` bounds to that ball and apply the local addition
lemma. This avoids pretending that the whole space is bounded. -/
theorem HasWeakGrad.add_univ {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g : Sp N → Tgt m} {Df Dg : Sp N → Mat m N}
    (hf : MemLp f p volume) (hDf : MemLp Df p volume)
    (hg : MemLp g p volume) (hDg : MemLp Dg p volume)
    (hwf : HasWeakGrad univ f Df) (hwg : HasWeakGrad univ g Dg) :
    HasWeakGrad univ (f + g) (Df + Dg) := by
  intro ψ hψ hcs hts v
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_ball (0 : Sp N)
  let U : Set (Sp N) := Metric.ball 0 R
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUb : Bornology.IsBounded U := Metric.isBounded_ball
  have hsub : tsupport ψ ⊆ U := hR
  have hwfU : HasWeakGrad U f Df := by
    intro χ hχ hχc hχs w
    exact hwf χ hχ hχc (hχs.trans (subset_univ U)) w
  have hwgU : HasWeakGrad U g Dg := by
    intro χ hχ hχc hχs w
    exact hwg χ hχ hχc (hχs.trans (subset_univ U)) w
  exact HasWeakGrad.add hUo hUb (hf.restrict U) (hDf.restrict U) (hg.restrict U)
    (hDg.restrict U) hwfU hwgU ψ hψ hcs hsub v

/-- Add two zero-extended Sobolev competitors on disjoint open sets. -/
theorem W1p0.add {p : ℝ≥0∞} [Fact (1 ≤ p)] {A B C : Set (Sp N)}
    {u v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hBA : B ⊆ A) (hCA : C ⊆ A)
    (hu : u ∈ W1p0 p B) (hv : v ∈ W1p0 p C) :
    (u.1 + v.1, u.2 + v.2) ∈ W1p0 p A := by
  rcases hu with ⟨hu0, huLp, huDLp, huweak⟩
  rcases hv with ⟨hv0, hvLp, hvDLp, hvweak⟩
  refine ⟨?_, memLp_add' huLp hvLp, memLp_add' huDLp hvDLp, ?_⟩
  · intro y hy
    simp [hu0 y (fun h => hy (hBA h)), hv0 y (fun h => hy (hCA h))]
  · exact HasWeakGrad.add_univ huLp huDLp hvLp hvDLp huweak hvweak

/-- Locality of the weak gradient: if a function vanishes almost everywhere on an open set, then
each directional component of its weak gradient vanishes there almost everywhere. This is the
distributional uniqueness theorem from Mathlib applied to each component. -/
theorem HasWeakGrad.eq_zero_on_open {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : Sp N → Tgt m} {g : Sp N → Mat m N} {B : Set (Sp N)}
    (hB : IsOpen B) (hu : u =ᵐ[volume.restrict B] 0)
    (hg : MemLp g p volume) (hweak : HasWeakGrad univ u g) :
    ∀ᵐ y ∂volume, y ∈ B → g y = 0 := by
  have hu' : ∀ᵐ y ∂volume, y ∈ B → u y = 0 :=
    (ae_restrict_iff' hB.measurableSet).1 hu
  have hcomponent : ∀ j : Fin N, ∀ᵐ y ∂volume, y ∈ B →
      g y (Pi.single j (1 : ℝ)) = 0 := by
    intro j
    let v : Sp N := Pi.single j (1 : ℝ)
    let q : Sp N → Tgt m := fun y => g y v
    have hqLp : MemLp q p volume :=
      hg.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ (Tgt m) v)
    have hqLoc : LocallyIntegrable q volume := hqLp.locallyIntegrable Fact.out
    apply hB.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hqLoc.locallyIntegrableOn B)
    intro ψ hψ hcs hts
    have hleft : (fun y => fderiv ℝ ψ y v • u y) =ᵐ[volume] 0 := by
      filter_upwards [hu'] with y hy
      by_cases hys : y ∈ tsupport ψ
      · rw [hy (hts hys)]
        simp
      · have hder : fderiv ℝ ψ y v = 0 := by
          by_contra h
          have hder' : fderiv ℝ ψ y ≠ 0 := by
            intro hz
            apply h
            rw [hz]
            simp
          exact hys (support_fderiv_subset ℝ (by simpa [Function.mem_support] using hder'))
        simp [hder]
    have hweak' := hweak ψ hψ hcs (hts.trans (subset_univ B)) v
    have htest : ∫ y, ψ y • q y = 0 := by
      have h0 : (∫ y, fderiv ℝ ψ y v • u y) = 0 := by
        simpa using integral_congr_ae hleft
      rw [h0] at hweak'
      simpa [q] using hweak'
    exact htest
  have hcomponents : ∀ᵐ y ∂volume, ∀ j : Fin N, y ∈ B →
      g y (Pi.single j (1 : ℝ)) = 0 := ae_all_iff.2 hcomponent
  filter_upwards [hcomponents] with y hy hyB
  apply (matCoordEquiv m N).injective
  funext ij
  rcases ij with ⟨i, j⟩
  rw [matCoordEquiv_apply]
  have hvec := hy j hyB
  simpa using congrFun hvec i

/-- The energy of the sum of two disjointly supported Sobolev correctors splits over the two
open pieces, provided those pieces cover `A` almost everywhere. Locality of the weak gradient is
used to remove the other corrector's gradient on each piece. -/
theorem Ytp_energy_add_split {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {W : Sp N → Mat m N → ℝ≥0∞} {ξ : Mat m N} {A B C : Set (Sp N)}
    {u v : (Sp N → Tgt m) × (Sp N → Mat m N)}
    (_hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C)
    (hBA : B ⊆ A) (hCA : C ⊆ A) (hBC : Disjoint B C)
    (hcover : volume (A \ (B ∪ C)) = 0)
    (hu : u ∈ W1p0 p B) (hv : v ∈ W1p0 p C) :
    (∫⁻ y in A, W y (ξ + (u.2 + v.2) y)) =
      (∫⁻ y in B, W y (ξ + u.2 y)) + ∫⁻ y in C, W y (ξ + v.2 y) := by
  rcases hu with ⟨hu0, huLp, huDLp, huweak⟩
  rcases hv with ⟨hv0, hvLp, hvDLp, hvweak⟩
  have hvzeroB : v.1 =ᵐ[volume.restrict B] 0 := by
    change ∀ᵐ y ∂volume.restrict B, v.1 y = 0
    exact (ae_restrict_iff' hBo.measurableSet).2 <| ae_of_all _ fun y hyB => by
      have hyC : y ∉ C := fun hyC => (Set.disjoint_left.mp hBC) hyB hyC
      exact hv0 y hyC
  have huzeroC : u.1 =ᵐ[volume.restrict C] 0 := by
    change ∀ᵐ y ∂volume.restrict C, u.1 y = 0
    exact (ae_restrict_iff' hCo.measurableSet).2 <| ae_of_all _ fun y hyC => by
      have hyB : y ∉ B := fun hyB => (Set.disjoint_left.mp hBC.symm) hyC hyB
      exact hu0 y hyB
  have hvgradB := HasWeakGrad.eq_zero_on_open hBo hvzeroB hvDLp hvweak
  have hugradC := HasWeakGrad.eq_zero_on_open hCo huzeroC huDLp huweak
  have hvgradB' : ∀ᵐ y ∂volume.restrict B, v.2 y = 0 :=
    (ae_restrict_iff' hBo.measurableSet).2 hvgradB
  have hugradC' : ∀ᵐ y ∂volume.restrict C, u.2 y = 0 :=
    (ae_restrict_iff' hCo.measurableSet).2 hugradC
  have hgradB : (fun y => (u.2 + v.2) y) =ᵐ[volume.restrict B] u.2 := by
    filter_upwards [hvgradB'] with y hy
    ext i
    simp [hy]
  have hgradC : (fun y => (u.2 + v.2) y) =ᵐ[volume.restrict C] v.2 := by
    filter_upwards [hugradC'] with y hy
    ext i
    simp [hy, add_comm]
  have hIB : (∫⁻ y in B, W y (ξ + (u.2 + v.2) y)) =
      ∫⁻ y in B, W y (ξ + u.2 y) := by
    apply lintegral_congr_ae
    filter_upwards [hgradB] with y hy
    rw [hy]
  have hIC : (∫⁻ y in C, W y (ξ + (u.2 + v.2) y)) =
      ∫⁻ y in C, W y (ξ + v.2 y) := by
    apply lintegral_congr_ae
    filter_upwards [hgradC] with y hy
    rw [hy]
  let pieces : Fin 2 → Set (Sp N) := ![B, C]
  have hpieces : (⋃ i, pieces i) = B ∪ C := by
    ext y
    simp [pieces, Fin.exists_fin_two]
  have hpOpen : ∀ i, IsOpen (pieces i) := by
    intro i
    fin_cases i <;> simp [pieces, hBo, hCo]
  have hpSub : ∀ i, pieces i ⊆ A := by
    intro i
    fin_cases i <;> simp [pieces, hBA, hCA]
  have hpDisj : Pairwise fun i j => Disjoint (pieces i) (pieces j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [pieces] using hBC
    · simpa [pieces] using hBC.symm
    · exact (hij rfl).elim
  have hpCover : volume (A \ ⋃ i, pieces i) = 0 := by
    rw [hpieces]
    exact hcover
  rw [lintegral_eq_sum_pieces hpOpen hpSub hpDisj hpCover]
  simp only [Pi.add_apply, Fin.sum_univ_two, Fin.isValue, pieces,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hIB' : (∫⁻ y in B, W y (ξ + (u.2 y + v.2 y))) =
      ∫⁻ y in B, W y (ξ + u.2 y) := by simpa only [Pi.add_apply] using hIB
  have hIC' : (∫⁻ y in C, W y (ξ + (u.2 y + v.2 y))) =
      ∫⁻ y in C, W y (ξ + v.2 y) := by simpa only [Pi.add_apply] using hIC
  rw [hIB', hIC']

/-- Subadditivity of the Sobolev cell problem on two disjoint open pieces that cover the target
up to a null set. The infima need not be attained: when the right side is finite, choose
competitors within half of an arbitrary positive error and then let that error tend to zero. -/
theorem Ytp_sub {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {W : Sp N → Mat m N → ℝ≥0∞} {ξ : Mat m N} {A B C : Set (Sp N)}
    (_hAo : IsOpen A) (_hAb : Bornology.IsBounded A)
    (hBo : IsOpen B) (hCo : IsOpen C)
    (hBA : B ⊆ A) (hCA : C ⊆ A) (hBC : Disjoint B C)
    (hcover : volume (A \ (B ∪ C)) = 0) :
    Ytp p W A ξ ≤ Ytp p W B ξ + Ytp p W C ξ := by
  by_cases htop : Ytp p W B ξ + Ytp p W C ξ = ⊤
  · rw [htop]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hBtop : Ytp p W B ξ ≠ ⊤ := by
    intro hB
    simp [hB] at htop
  have hCtop : Ytp p W C ξ ≠ ⊤ := by
    intro hC
    simp [hC] at htop
  let δ : ℝ≥0∞ := (η : ℝ≥0∞) / 2
  have hδ : δ ≠ 0 := by
    simp [δ, hη.ne']
  have hnearB : ∃ u ∈ (W1p0 p B : Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
      (∫⁻ y in B, W y (ξ + u.2 y)) < Ytp p W B ξ + δ := by
    have hlt := ENNReal.lt_add_right hBtop hδ
    simpa [Ytp, iInf_lt_iff, exists_prop] using hlt
  have hnearC : ∃ v ∈ (W1p0 p C : Set ((Sp N → Tgt m) × (Sp N → Mat m N))),
      (∫⁻ y in C, W y (ξ + v.2 y)) < Ytp p W C ξ + δ := by
    have hlt := ENNReal.lt_add_right hCtop hδ
    simpa [Ytp, iInf_lt_iff, exists_prop] using hlt
  obtain ⟨u, hu, hEu⟩ := hnearB
  obtain ⟨v, hv, hEv⟩ := hnearC
  have hglue : (u.1 + v.1, u.2 + v.2) ∈ W1p0 p A := W1p0.add hBA hCA hu hv
  have henergy :
      (∫⁻ y in B, W y (ξ + u.2 y)) + ∫⁻ y in C, W y (ξ + v.2 y) <
        Ytp p W B ξ + Ytp p W C ξ + η := by
    calc
      _ < (Ytp p W B ξ + δ) + (Ytp p W C ξ + δ) := ENNReal.add_lt_add hEu hEv
      _ = Ytp p W B ξ + Ytp p W C ξ + η := by
        rw [add_add_add_comm, ENNReal.add_halves]
  calc
    Ytp p W A ξ ≤ ∫⁻ y in A, W y (ξ + (u.2 + v.2) y) :=
      iInf₂_le _ hglue
    _ = (∫⁻ y in B, W y (ξ + u.2 y)) + ∫⁻ y in C, W y (ξ + v.2 y) :=
      Ytp_energy_add_split _hAo hBo hCo hBA hCA hBC hcover hu hv
    _ ≤ Ytp p W B ξ + Ytp p W C ξ + η := henergy.le

/-- Translation preserves a global weak-gradient identity. The test function is translated in the
opposite direction, and the integral identities below use invariance of Lebesgue measure under
translations. -/
theorem HasWeakGrad.comp_add {f : Sp N → Tgt m} {g : Sp N → Mat m N}
    (hfg : HasWeakGrad univ f g) (a : Sp N) :
    HasWeakGrad univ (fun y => f (y + a)) (fun y => g (y + a)) := by
  intro ψ hψ hcs _ v
  let ψ' : Sp N → ℝ := fun x => ψ (x + -a)
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) ψ' := by
    exact hψ.comp (contDiff_id.add contDiff_const)
  have hcs' : HasCompactSupport ψ' :=
    hcs.comp_homeomorph (Homeomorph.addRight (-a))
  have hweak := hfg ψ' hψ' hcs' (subset_univ _) v
  have hleft : (∫ y, fderiv ℝ ψ y v • f (y + a)) =
      ∫ x, fderiv ℝ ψ (x + -a) v • f x := by
    let q : Sp N → Tgt m := fun x => fderiv ℝ ψ (x + -a) v • f x
    have h := (measurePreserving_add_right (volume : Measure (Sp N)) a).integral_comp
      (MeasurableEquiv.addRight a).measurableEmbedding q
    simpa [q, add_assoc, add_comm] using h
  have hright : (∫ y, ψ y • g (y + a) v) =
      ∫ x, ψ (x + -a) • g x v := by
    let q : Sp N → Tgt m := fun x => ψ (x + -a) • g x v
    have h := (measurePreserving_add_right (volume : Measure (Sp N)) a).integral_comp
      (MeasurableEquiv.addRight a).measurableEmbedding q
    simpa [q, add_assoc, add_comm] using h
  have hweak' : (∫ x, fderiv ℝ ψ (x + -a) v • f x) =
      -∫ x, ψ (x + -a) • g x v := by
    simpa [ψ', fderiv_comp_add_right] using hweak
  rw [hleft, hweak', ← hright]

/-- Pull a zero-extended Sobolev competitor back by a translation. -/
theorem W1p0.comp_add {p : ℝ≥0∞} {U : Set (Sp N)}
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 p U) (a : Sp N) :
    ((fun y => u.1 (y + a)), (fun y => u.2 (y + a))) ∈
      W1p0 p ((fun y => y + a) ⁻¹' U) := by
  rcases hu with ⟨hu0, huLp, huDLp, huweak⟩
  refine ⟨fun y hy => hu0 (y + a) hy, ?_, ?_, huweak.comp_add a⟩
  · exact huLp.comp_measurePreserving (measurePreserving_add_right volume a)
  · exact huDLp.comp_measurePreserving (measurePreserving_add_right volume a)

/-- One inequality for translation of the Sobolev cell problem. -/
theorem Ytp_preimage_add_le {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞} {a : Sp N}
    (hW : ∀ y, W (y + a) = W y) (U : Set (Sp N)) (ξ : Mat m N) :
    Ytp p W ((fun y => y + a) ⁻¹' U) ξ ≤ Ytp p W U ξ := by
  refine le_iInf₂ fun u hu => (iInf₂_le _ (W1p0.comp_add hu a)).trans ?_
  have hmp := measurePreserving_add_right (volume : Measure (Sp N)) a
  have hemb := (MeasurableEquiv.addRight a).measurableEmbedding
  rw [← hmp.setLIntegral_comp_preimage_emb hemb
    (fun y => W y (ξ + u.2 y)) U]
  simp_rw [hW]
  exact le_rfl

/-- Translation invariance of the Sobolev cell problem for an integrand invariant under that
translation. The reverse inequality uses the opposite shift. -/
theorem Ytp_preimage_add {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞} {a : Sp N}
    (hW : ∀ y, W (y + a) = W y) (U : Set (Sp N)) (ξ : Mat m N) :
    Ytp p W ((fun y => y + a) ⁻¹' U) ξ = Ytp p W U ξ := by
  apply le_antisymm (Ytp_preimage_add_le hW U ξ)
  have hW' : ∀ y, W (y + -a) = W y := fun y => by
    rw [← hW (y + -a), add_assoc, neg_add_cancel, add_zero]
  have h := Ytp_preimage_add_le (p := p) hW' ((fun y => y + a) ⁻¹' U) ξ
  have hpre : (fun y => y + -a) ⁻¹' ((fun y => y + a) ⁻¹' U) = U := by
    ext y
    simp [add_comm]
  simpa only [hpre] using h

/-- Integer periodicity of `W` induces integer-translation invariance of its Sobolev cell
problem. -/
theorem IsPeriodic.Ytp_cube {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    (hW : IsPeriodic W) (z : Fin N → ℤ) (ρ : ℝ) (x : Sp N) (ξ : Mat m N) :
    Ytp p W (cube ρ (x + zcast z)) ξ = Ytp p W (cube ρ x) ξ := by
  let a : Sp N := zcast z
  have hW' : ∀ y, W (y + -a) = W y := by
    intro y
    funext ζ
    have hz := hW (-z) y ζ
    have ha : zcast (-z) = -a := by
      funext i
      simp [a, zcast]
    change W (y + zcast (-z)) ζ = W y ζ at hz
    rw [ha] at hz
    exact hz
  have hc : cube ρ (x + zcast z) = (fun y => y + -a) ⁻¹' cube ρ x := by
    rw [cube_add]
    simp [a, sub_eq_add_neg]
  rw [hc]
  exact Ytp_preimage_add hW' (cube ρ x) ξ

/-- The zero pair is an admissible competitor in the Sobolev cell problem. -/
theorem zero_mem_W1p0 (p : ℝ≥0∞) (A : Set (Sp N)) :
    ((0 : Sp N → Tgt m), (0 : Sp N → Mat m N)) ∈ W1p0 p A := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · exact (MemLp.zero (ε := Tgt m) (p := p) (μ := volume) :
      MemLp (0 : Sp N → Tgt m) p volume)
  · exact (MemLp.zero (ε := Mat m N) (p := p) (μ := volume) :
      MemLp (0 : Sp N → Mat m N) p volume)
  · intro ψ hψ hcs hts v
    simp

/-- Testing `Ytp` with the zero corrector bounds it by the unperturbed energy. -/
theorem Ytp_le_lintegral (p : ℝ≥0∞) (W : Sp N → Mat m N → ℝ≥0∞)
    (A : Set (Sp N)) (ξ : Mat m N) :
    Ytp p W A ξ ≤ ∫⁻ y in A, W y ξ := by
  simp only [Ytp]
  calc (⨅ φg, ⨅ _ : φg ∈ W1p0 p A, ∫⁻ y in A, W y (ξ + φg.2 y))
      ≤ ∫⁻ y in A, W y (ξ + (0 : Sp N → Mat m N) y) :=
        iInf₂_le ((0 : Sp N → Tgt m), (0 : Sp N → Mat m N)) (zero_mem_W1p0 p A)
    _ = ∫⁻ y in A, W y ξ := by simp

/-- A uniform pointwise bound on the unperturbed density gives the volume bound required by
`SubaddCube`. No measurability assumption is needed: monotonicity of the lower integral compares
the energy directly with a constant function. For a growth bound
`W y ξ ≤ β (1 + G ξ)`, this applies whenever the right-hand side is finite, with the corresponding
finite real constant. -/
theorem Ytp_bound_of_pointwise {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    {ξ : Mat m N} {c : ℝ≥0} (hc : ∀ y, W y ξ ≤ c) (A : Set (Sp N)) :
    Ytp p W A ξ ≤ c * volume A := by
  refine (Ytp_le_lintegral p W A ξ).trans ?_
  calc ∫⁻ y in A, W y ξ ≤ ∫⁻ y in A, (c : ℝ≥0∞) := lintegral_mono fun y => hc y
    _ = c * volume A := by rw [setLIntegral_const]

/-- The growth hypothesis on `Yt W` suffices for the volume bound on `Ytp`: by
`Aff₀ ⊆ W^{1,p}_0`, `Ytp ≤ Yt`, so no pointwise upper bound on `W` is needed. Finiteness of
`G ξ` is exactly what lets the growth constant be represented by a finite `ℝ≥0` coefficient. -/
theorem Ytp_bound_of_Yt_growth {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    {G : Mat m N → ℝ≥0∞} {β : ℝ≥0} {ξ : Mat m N} (hξ : G ξ ≠ ⊤)
    (hgrowth : ∀ A : Set (Sp N), IsOpen A → Bornology.IsBounded A →
      Yt W A ξ ≤ β * volume A * (1 + G ξ)) :
    ∃ c : ℝ≥0, ∀ A : Set (Sp N), IsOpen A → Bornology.IsBounded A →
      Ytp p W A ξ ≤ c * volume A := by
  let c : ℝ≥0 := (β * (1 + G ξ)).toNNReal
  have htop : β * (1 + G ξ) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hξ⟩
  refine ⟨c, fun A hAo hAb => ?_⟩
  calc Ytp p W A ξ ≤ Yt W A ξ := Ytp_le_Yt p W hAb ξ
    _ ≤ β * volume A * (1 + G ξ) := hgrowth A hAo hAb
    _ = (β * (1 + G ξ)) * volume A := by ac_rfl
    _ = c * volume A := by rw [← ENNReal.coe_toNNReal htop]

/-- `S(Q_ρ)/|Q_ρ|` for the cube of side `ρ` centred at `0`. -/
noncomputable def cubeRatio (S : Set (Sp N) → ℝ≥0∞) (ρ : ℝ) : ℝ≥0∞ :=
  S (cube ρ 0) / volume (cube ρ (0 : Sp N))

/-- The limit `inf_{k ≥ 1} S(kY)/|kY|`. -/
noncomputable def subaddLimit (S : Set (Sp N) → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ k : ℕ, cubeRatio S ((k : ℝ) + 1)

theorem volume_cube_ne_zero' {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) : volume (cube ρ x) ≠ 0 :=
  (volume_cube_pos hρ x).ne'

namespace SubaddCube

variable {S : Set (Sp N) → ℝ≥0∞} {c : ℝ≥0}

theorem empty (hS : SubaddCube S c) : S ∅ = 0 :=
  le_antisymm ((hS.bound ∅ isOpen_empty Bornology.isBounded_empty).trans (by simp)) zero_le

/-- Finite subadditivity. -/
theorem le_sum (hS : SubaddCube S c) {ι : Type*} (s : Finset ι) {A : Set (Sp N)}
    (hAo : IsOpen A) (hAb : Bornology.IsBounded A) {B : ι → Set (Sp N)}
    (hBo : ∀ i, IsOpen (B i)) (hBA : ∀ i ∈ s, B i ⊆ A)
    (hBd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hcov : volume (A \ ⋃ i ∈ s, B i) = 0) : S A ≤ ∑ i ∈ s, S (B i) := by
  classical
  have key : ∀ t ⊆ s, S (⋃ i ∈ t, B i) ≤ ∑ i ∈ t, S (B i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp [hS.empty]
    | @insert a t ha ih =>
      intro hts
      have hts' : t ⊆ s := (Finset.subset_insert a t).trans hts
      have has : a ∈ s := hts (Finset.mem_insert_self a t)
      have hU : (⋃ i ∈ insert a t, B i) = B a ∪ ⋃ i ∈ t, B i := Finset.set_biUnion_insert a t B
      rw [Finset.sum_insert ha]
      have hUo : IsOpen (⋃ i ∈ t, B i) := isOpen_biUnion fun i _ => hBo i
      have hsubA : (⋃ i ∈ insert a t, B i) ⊆ A := iUnion₂_subset fun i hi => hBA i (hts hi)
      calc S (⋃ i ∈ insert a t, B i) ≤ S (B a) + S (⋃ i ∈ t, B i) := by
            refine hS.sub _ _ _ (isOpen_biUnion fun i _ => hBo i) (hAb.subset hsubA) (hBo a) hUo
              ?_ ?_ ?_ ?_
            · rw [hU]; exact subset_union_left
            · rw [hU]; exact subset_union_right
            · rw [Set.disjoint_iUnion₂_right]
              intro i hi
              exact hBd a has i (hts' hi) fun h => ha (h ▸ hi)
            · rw [hU, sdiff_self, measure_empty]
        _ ≤ S (B a) + ∑ i ∈ t, S (B i) := add_le_add le_rfl (ih hts')
  have hUo : IsOpen (⋃ i ∈ s, B i) := isOpen_biUnion fun i _ => hBo i
  calc S A ≤ S (⋃ i ∈ s, B i) + S ∅ :=
        hS.sub _ _ _ hAo hAb hUo isOpen_empty (iUnion₂_subset hBA) (empty_subset _)
          (Set.disjoint_empty _) (by rwa [union_empty])
    _ ≤ _ := by rw [hS.empty, add_zero]; exact key s subset_rfl

/-- The cubes of side `ρ` centred at integer points all have the value of the centred one. -/
theorem cube_zcast (hS : SubaddCube S c) (ρ : ℝ) (z : Fin N → ℤ) :
    S (cube ρ (zcast z)) = S (cube ρ 0) := by
  simpa using hS.inv z ρ 0

theorem gridCell_eq (hS : SubaddCube S c) (k : ℕ) (z : Fin N → ℤ) :
    S (gridCell ((k : ℝ) + 1) z) = S (cube ((k : ℝ) + 1) 0) := by
  have : ((k : ℝ) + 1) • zcast z = zcast (fun i => ((k : ℤ) + 1) * z i) := by
    funext i
    simp [zcast]
  rw [gridCell, this, hS.cube_zcast]

theorem mem_closure_cube {ρ : ℝ} (hρ : 0 < ρ) {x y : Sp N}
    (h : ∀ i, x i - ρ / 2 ≤ y i ∧ y i ≤ x i + ρ / 2) : y ∈ closure (cube ρ x) := by
  rw [cube, closure_pi_set]
  intro i _
  change y i ∈ closure (Ioo (x i - ρ / 2) (x i + ρ / 2))
  rw [closure_Ioo (by linarith)]
  exact h i

theorem frontier_null_of_finset {ι : Type*} (s : Finset ι) (ρ : ι → ℝ) (x : ι → Sp N)
    {A : Set (Sp N)} (h : A ⊆ closure (⋃ i ∈ s, cube (ρ i) (x i)))
    (h' : Disjoint A (⋃ i ∈ s, cube (ρ i) (x i))) : volume A = 0 := by
  refine measure_mono_null (t := ⋃ i ∈ s, frontier (cube (ρ i) (x i))) ?_
    (le_antisymm ((measure_biUnion_finset_le _ _).trans
      (by simp [volume_frontier_cube])) zero_le)
  intro y hy
  have hy1 := h hy
  rw [Finset.closure_biUnion] at hy1
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy1
  refine mem_iUnion₂.2 ⟨i, hi, ?_⟩
  rw [(isOpen_cube _ _).frontier_eq]
  exact ⟨hyi, fun h'' => Set.disjoint_left.1 h' hy (mem_iUnion₂.2 ⟨i, hi, h''⟩)⟩

/-- **Upper bound**: tiling `Q_L(w)` by the grid cells of side `k + 1` that fit in it. -/
theorem upper (hS : SubaddCube S c) (k : ℕ) (L : ℝ) (w : Sp N) :
    S (cube L w) ≤ volume (cube L w) * cubeRatio S ((k : ℝ) + 1) +
      c * volume (cube L w \ cube (L - 2 * ((k : ℝ) + 1)) w) := by
  classical
  set K : ℝ := (k : ℝ) + 1 with hK_def
  have hK : 0 < K := by positivity
  set P : Set (Fin N → ℤ) :=
    {z | ∀ i, w i - L / 2 ≤ K * z i - K / 2 ∧ K * z i + K / 2 ≤ w i + L / 2} with hP_def
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun i => Icc (⌈(w i - L / 2 + K / 2) / K⌉)
      (⌊(w i + L / 2 - K / 2) / K⌋)) fun i => Set.finite_Icc _ _).subset ?_
    intro z hz i _
    obtain ⟨h1, h2⟩ := hz i
    constructor
    · rw [Int.ceil_le, div_le_iff₀ hK]; linarith
    · rw [Int.le_floor, le_div_iff₀ hK]; linarith
  set T := hPfin.toFinset with hT_def
  have hmemT : ∀ z, z ∈ T ↔ z ∈ P := fun z => Set.Finite.mem_toFinset hPfin
  have hcell : ∀ (z : Fin N → ℤ) (y : Sp N),
      y ∈ gridCell K z ↔ ∀ i, K * z i - K / 2 < y i ∧ y i < K * z i + K / 2 := by
    intro z y
    simp [gridCell, cube, zcast, Set.mem_pi]
  have htileQ : ∀ z ∈ T, gridCell K z ⊆ cube L w := by
    intro z hz y hy
    have hz' := (hmemT z).1 hz
    rw [hcell] at hy
    simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo]
    intro i
    obtain ⟨h1, h2⟩ := hz' i
    obtain ⟨h3, h4⟩ := hy i
    constructor <;> linarith
  have hdisj : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' → Disjoint (gridCell K z) (gridCell K z') :=
    fun z _ z' _ h => gridCell_disjoint hK h
  set B := ⋃ z ∈ T, gridCell K z with hB_def
  have hBo : IsOpen B := isOpen_biUnion fun z _ => isOpen_cube _ _
  have hBQ : B ⊆ cube L w := iUnion₂_subset htileQ
  set R := cube L w \ closure B with hR_def
  have hRo : IsOpen R := (isOpen_cube _ _).sdiff isClosed_closure
  have hsplit : S (cube L w) ≤ S B + S R := by
    refine hS.sub _ _ _ (isOpen_cube _ _) (isBounded_cube _ _) hBo hRo hBQ sdiff_subset
      (Set.disjoint_left.2 fun y hyB hyR => hyR.2 (subset_closure hyB)) ?_
    refine frontier_null_of_finset T (fun _ => K) (fun z => K • zcast z) ?_ ?_
    · rintro y ⟨hyQ, hyBR⟩
      by_contra h
      exact hyBR (Or.inr ⟨hyQ, h⟩)
    · exact Set.disjoint_left.2 fun y hy hyB => hy.2 (Or.inl hyB)
  have hBsum : S B ≤ ∑ z ∈ T, S (gridCell K z) :=
    hS.le_sum T hBo (isBounded_cube L w |>.subset hBQ) (fun z => isOpen_cube _ _)
      (fun z hz => subset_biUnion_of_mem (u := fun z => gridCell K z) hz) hdisj
      (by rw [hB_def, sdiff_self, measure_empty])
  have hsumeq : ∑ z ∈ T, S (gridCell K z) = T.card * S (cube K 0) := by
    rw [Finset.sum_congr rfl fun z _ => hS.gridCell_eq k z, Finset.sum_const, nsmul_eq_mul]
  have hvolB : (T.card : ℝ≥0∞) * volume (cube K (0 : Sp N)) ≤ volume (cube L w) := by
    calc (T.card : ℝ≥0∞) * volume (cube K (0 : Sp N)) = ∑ z ∈ T, volume (gridCell K z) := by
          rw [Finset.sum_congr rfl fun z _ => by rw [gridCell, volume_cube, ← volume_cube K 0],
            Finset.sum_const, nsmul_eq_mul]
      _ = volume B := by
          rw [hB_def, measure_biUnion_finset (fun z _ z' _ h => gridCell_disjoint hK h)
            fun z _ => (isOpen_cube _ _).measurableSet]
      _ ≤ volume (cube L w) := measure_mono hBQ
  have hRsub : R ⊆ cube L w \ cube (L - 2 * K) w := by
    rintro y ⟨hyQ, hyB⟩
    refine ⟨hyQ, fun hyin => hyB ?_⟩
    simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hyin
    set z : Fin N → ℤ := fun i => round (y i / K)
    have hround : ∀ i, K * z i - K / 2 ≤ y i ∧ y i ≤ K * z i + K / 2 := by
      intro i
      have h := abs_sub_round (y i / K)
      rw [abs_le] at h
      have hq : y i = K * (y i / K) := by field_simp
      constructor <;> nlinarith [h.1, h.2]
    have hzT : z ∈ T := by
      rw [hmemT]
      intro i
      obtain ⟨h1, h2⟩ := hround i
      obtain ⟨h3, h4⟩ := hyin i
      constructor <;> linarith
    have hycl : y ∈ closure (gridCell K z) := by
      rw [gridCell]
      refine mem_closure_cube hK fun i => ?_
      simp only [Pi.smul_apply, zcast, smul_eq_mul]
      exact hround i
    exact closure_mono (subset_biUnion_of_mem (u := fun z => gridCell K z) hzT) hycl
  have hvK0 : volume (cube K (0 : Sp N)) ≠ 0 := volume_cube_ne_zero' hK 0
  have hvKt : volume (cube K (0 : Sp N)) ≠ ⊤ := volume_cube_ne_top K 0
  calc S (cube L w) ≤ S B + S R := hsplit
    _ ≤ T.card * S (cube K 0) + c * volume (cube L w \ cube (L - 2 * K) w) := by
        gcongr
        · exact hBsum.trans (le_of_eq hsumeq)
        · exact (hS.bound R hRo ((isBounded_cube L w).subset sdiff_subset)).trans
            (by gcongr)
    _ = ((T.card : ℝ≥0∞) * volume (cube K (0 : Sp N))) * cubeRatio S K +
          c * volume (cube L w \ cube (L - 2 * K) w) := by
        rw [cubeRatio, mul_assoc, ENNReal.mul_div_cancel hvK0 hvKt]
    _ ≤ volume (cube L w) * cubeRatio S K + c * volume (cube L w \ cube (L - 2 * K) w) := by
        gcongr

/-- **Lower bound**: `Q_L(w)` lies in an integer cube of side `⌈L⌉ + 1`. -/
theorem lower (hS : SubaddCube S c) {L : ℝ} (hL : 0 < L) (w : Sp N) :
    volume (cube (((⌈L⌉₊ : ℕ) : ℝ) + 1) (zcast fun i => round (w i))) * subaddLimit S ≤
      S (cube L w) + c * volume (cube (((⌈L⌉₊ : ℕ) : ℝ) + 1) (zcast fun i => round (w i)) \
        cube L w) := by
  set K : ℝ := ((⌈L⌉₊ : ℕ) : ℝ) + 1 with hK_def
  have hK : 0 < K := by positivity
  set z : Fin N → ℤ := fun i => round (w i)
  set Kc := cube K (zcast z) with hKc_def
  have hLK : L + 1 ≤ K := by rw [hK_def]; linarith [Nat.le_ceil L]
  have hsub : cube L w ⊆ Kc := by
    intro y hy
    simp only [hKc_def, cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, zcast, z] at hy ⊢
    intro i
    have h := abs_sub_round (w i)
    rw [abs_le] at h
    obtain ⟨h1, h2⟩ := hy i
    constructor <;> linarith [h.1, h.2]
  have hsplit : S Kc ≤ S (cube L w) + S (Kc \ closure (cube L w)) := by
    refine hS.sub _ _ _ (isOpen_cube _ _) (isBounded_cube _ _) (isOpen_cube _ _)
      ((isOpen_cube _ _).sdiff isClosed_closure) hsub sdiff_subset
      (Set.disjoint_left.2 fun y hy hy' => hy'.2 (subset_closure hy)) ?_
    refine measure_mono_null (fun y hy => ?_) (volume_frontier_cube L w)
    obtain ⟨hyK, hy'⟩ := hy
    rw [(isOpen_cube _ _).frontier_eq]
    refine ⟨?_, fun h => hy' (Or.inl h)⟩
    by_contra h
    exact hy' (Or.inr ⟨hyK, h⟩)
  have hrem : S (Kc \ closure (cube L w)) ≤ c * volume (Kc \ cube L w) :=
    (hS.bound _ ((isOpen_cube _ _).sdiff isClosed_closure)
      ((isBounded_cube _ _).subset sdiff_subset)).trans
      (by gcongr; exact subset_closure)
  have hvK0 : volume (cube K (0 : Sp N)) ≠ 0 := volume_cube_ne_zero' hK 0
  have hvKt : volume (cube K (0 : Sp N)) ≠ ⊤ := volume_cube_ne_top K 0
  have hKc : S Kc = volume (cube K (0 : Sp N)) * cubeRatio S K := by
    rw [hKc_def, hS.cube_zcast, cubeRatio, ENNReal.mul_div_cancel hvK0 hvKt]
  have hm : subaddLimit S ≤ cubeRatio S K := iInf_le (fun k : ℕ => cubeRatio S ((k : ℝ) + 1)) _
  calc volume Kc * subaddLimit S = volume (cube K (0 : Sp N)) * subaddLimit S := by
        rw [hKc_def, volume_cube, volume_cube]
    _ ≤ volume (cube K (0 : Sp N)) * cubeRatio S K := by gcongr
    _ = S Kc := hKc.symm
    _ ≤ S (cube L w) + S (Kc \ closure (cube L w)) := hsplit
    _ ≤ S (cube L w) + c * volume (Kc \ cube L w) := add_le_add le_rfl hrem

theorem ofReal_coe_mul (c : ℝ≥0) (x : ℝ) :
    ENNReal.ofReal ((c : ℝ) * x) = (c : ℝ≥0∞) * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg c), ENNReal.ofReal_coe_nnreal]

theorem cube_subset_cube {L L' : ℝ} (h : L' ≤ L) (w : Sp N) : cube L' w ⊆ cube L w := by
  intro y hy
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hy ⊢
  intro i
  obtain ⟨h1, h2⟩ := hy i
  constructor <;> linarith

theorem cube_subset_round {L : ℝ} (w : Sp N) :
    cube L w ⊆ cube (((⌈L⌉₊ : ℕ) : ℝ) + 1) (zcast fun i => round (w i)) := by
  intro y hy
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, zcast] at hy ⊢
  intro i
  have h := abs_sub_round (w i)
  rw [abs_le] at h
  have hc := Nat.le_ceil L
  obtain ⟨h1, h2⟩ := hy i
  constructor <;> linarith [h.1, h.2]

/-- `|Q_L ∖ Q_{L'}| = |Q_L| (1 - (L'/L)^N)` for nested cubes. -/
theorem volume_cube_diff {L L' : ℝ} (hL : 0 < L) (hL' : 0 ≤ L') (h : L' ≤ L) (w : Sp N) :
    volume (cube L w \ cube L' w) =
      volume (cube L w) * ENNReal.ofReal (1 - (L' / L) ^ N) := by
  rw [measure_sdiff (cube_subset_cube h w) (isOpen_cube _ _).measurableSet.nullMeasurableSet
    (volume_cube_ne_top _ _), volume_cube, volume_cube, ← ENNReal.ofReal_pow hL.le,
    ← ENNReal.ofReal_pow hL', ← ENNReal.ofReal_sub _ (pow_nonneg hL' N),
    ← ENNReal.ofReal_mul (pow_nonneg hL.le N)]
  congr 1
  rw [div_pow, mul_sub, mul_one, mul_div_cancel₀ _ (pow_ne_zero N hL.ne')]

/-- `|Q_K(z) ∖ Q_L(w)| = |Q_L| ((K/L)^N - 1)` when `Q_L(w) ⊆ Q_K(z)`. -/
theorem volume_cube_diff' {L K : ℝ} (hL : 0 < L) (hLK : L ≤ K) {w z : Sp N}
    (h : cube L w ⊆ cube K z) :
    volume (cube K z \ cube L w) = volume (cube L w) * ENNReal.ofReal ((K / L) ^ N - 1) := by
  have hK : 0 ≤ K := hL.le.trans hLK
  rw [measure_sdiff h (isOpen_cube _ _).measurableSet.nullMeasurableSet
    (volume_cube_ne_top _ _), volume_cube, volume_cube, ← ENNReal.ofReal_pow hL.le,
    ← ENNReal.ofReal_pow hK, ← ENNReal.ofReal_sub _ (pow_nonneg hL.le N),
    ← ENNReal.ofReal_mul (pow_nonneg hL.le N)]
  congr 1
  rw [div_pow, mul_sub, mul_one, mul_div_cancel₀ _ (pow_ne_zero N hL.ne')]

theorem ratio_upper (hS : SubaddCube S c) (k : ℕ) {L : ℝ} (hL : 2 * ((k : ℝ) + 1) ≤ L)
    (w : Sp N) :
    S (cube L w) / volume (cube L w) ≤ cubeRatio S ((k : ℝ) + 1) +
      ENNReal.ofReal (c * (1 - ((L - 2 * ((k : ℝ) + 1)) / L) ^ N)) := by
  have hK : 0 < (k : ℝ) + 1 := by positivity
  have hL0 : 0 < L := by linarith
  have h := hS.upper k L w
  rw [volume_cube_diff hL0 (by linarith) (by linarith) w] at h
  refine ENNReal.div_le_of_le_mul (h.trans (le_of_eq ?_))
  rw [ofReal_coe_mul]
  ring

theorem ratio_lower (hS : SubaddCube S c) {L : ℝ} (hL : 1 ≤ L) (w : Sp N) :
    subaddLimit S ≤ S (cube L w) / volume (cube L w) +
      ENNReal.ofReal (c * (((((⌈L⌉₊ : ℕ) : ℝ) + 1) / L) ^ N - 1)) := by
  have hL0 : 0 < L := by linarith
  set K : ℝ := ((⌈L⌉₊ : ℕ) : ℝ) + 1 with hK_def
  have hLK : L ≤ K := by rw [hK_def]; linarith [Nat.le_ceil L]
  have hsub := cube_subset_round (L := L) w
  have h := hS.lower hL0 w
  rw [volume_cube_diff' hL0 hLK hsub] at h
  have hv0 := volume_cube_ne_zero' hL0 w
  have hvt := volume_cube_ne_top L w
  have hvle : volume (cube L w) ≤ volume (cube K (zcast fun i => round (w i))) := by
    rw [volume_cube, volume_cube]; gcongr
  refine (ENNReal.mul_le_mul_iff_right hv0 hvt).1 ?_
  calc volume (cube L w) * subaddLimit S
      ≤ volume (cube K (zcast fun i => round (w i))) * subaddLimit S := by gcongr
    _ ≤ _ := h
    _ = volume (cube L w) * (S (cube L w) / volume (cube L w) +
          ENNReal.ofReal (c * ((K / L) ^ N - 1))) := by
        rw [mul_add, ENNReal.mul_div_cancel hv0 hvt, ofReal_coe_mul]
        ring

end SubaddCube

theorem tendsto_err_up (K c : ℝ) :
    Tendsto (fun L : ℝ => c * (1 - ((L - 2 * K) / L) ^ N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℝ => (L - 2 * K) / L) atTop (𝓝 1) := by
    have : Tendsto (fun L : ℝ => 1 - 2 * K / L) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    field_simp
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub (h1.pow N) |>.const_mul c
  simpa using this

theorem tendsto_err_low {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun L : ℝ => c * (((((⌈L⌉₊ : ℕ) : ℝ) + 1) / L) ^ N - 1)) atTop (𝓝 0) := by
  have hg : Tendsto (fun L : ℝ => c * ((1 + 2 / L) ^ N - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => 1 + 2 / L) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h1
    have := ((h1.pow N).sub (tendsto_const_nhds (x := (1 : ℝ)))).const_mul c
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : 0 < L := by linarith
    have h1 : 1 ≤ (((⌈L⌉₊ : ℕ) : ℝ) + 1) / L := by
      rw [one_le_div hL0]; linarith [Nat.le_ceil L]
    exact mul_nonneg hc (sub_nonneg.2 (one_le_pow₀ h1))
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : 0 < L := by linarith
    have h1 : (((⌈L⌉₊ : ℕ) : ℝ) + 1) / L ≤ 1 + 2 / L := by
      rw [div_le_iff₀ hL0, add_mul, div_mul_cancel₀ _ hL0.ne', one_mul]
      linarith [Nat.ceil_lt_add_one hL0.le]
    gcongr

namespace SubaddCube

variable {S : Set (Sp N) → ℝ≥0∞} {c : ℝ≥0}

/-- **The subadditive theorem.** `S(Q_L(w))/|Q_L(w)| → inf_k S(kY)/|kY|` as `L → ∞`,
uniformly in the centres. -/
theorem tendsto (hS : SubaddCube S c) {ι : Type*} {l : Filter ι} {L : ι → ℝ}
    (hL : Tendsto L l atTop) (w : ι → Sp N) :
    Tendsto (fun i => S (cube (L i) (w i)) / volume (cube (L i) (w i))) l
      (𝓝 (subaddLimit S)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 ha
    have herr := (tendsto_err_low (N := N) (c := (c : ℝ)) c.2).comp hL
    filter_upwards [herr.eventually (gt_mem_nhds (show (0 : ℝ) < r from hr0)),
      hL.eventually (eventually_ge_atTop 1)] with i hi hLi
    have hle : ENNReal.ofReal ((c : ℝ) * (((((⌈L i⌉₊ : ℕ) : ℝ) + 1) / L i) ^ N - 1)) ≤ r := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hi.le
    have h2 := (hS.ratio_lower hLi (w i)).trans (add_le_add le_rfl hle)
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).1 (hr.trans_le h2)
  · obtain ⟨k, hk⟩ := iInf_lt_iff.1 hb
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hk
    have herr := (tendsto_err_up (N := N) ((k : ℝ) + 1) (c : ℝ)).comp hL
    filter_upwards [herr.eventually (gt_mem_nhds (show (0 : ℝ) < r from hr0)),
      hL.eventually (eventually_ge_atTop (2 * ((k : ℝ) + 1)))] with i hi hLi
    have hle : ENNReal.ofReal ((c : ℝ) * (1 - ((L i - 2 * ((k : ℝ) + 1)) / L i) ^ N)) ≤ r := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hi.le
    exact (hS.ratio_upper k hLi (w i)).trans_lt ((add_le_add le_rfl hle).trans_lt hr)

/-- **Corollary `SubadditiveTheorem`**: `S(ε⁻¹ Q_ρ(x))/|ε⁻¹ Q_ρ(x)| → inf_k S(kY)/|kY|` as
`ε → 0⁺`. -/
theorem tendsto_eps (hS : SubaddCube S c) {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    Tendsto (fun ε : ℝ => S (cube (ρ / ε) (ε⁻¹ • x)) / volume (cube (ρ / ε) (ε⁻¹ • x)))
      (𝓝[>] 0) (𝓝 (subaddLimit S)) :=
  hS.tendsto ((tendsto_inv_nhdsGT_zero.const_mul_atTop hρ).congr fun ε =>
    (div_eq_mul_inv ρ ε).symm) _

end SubaddCube

/-- Applying the abstract subadditive theorem to a Sobolev cell set-function. -/
theorem Ytp_cell_tendsto_eps {m : ℕ} {p : ℝ≥0∞} {W : Sp N → Mat m N → ℝ≥0∞}
    {ξ : Mat m N} {c : ℝ≥0} (hS : SubaddCube (fun A => Ytp p W A ξ) c)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    Tendsto (fun ε : ℝ =>
      Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ / volume (cube (ρ / ε) (ε⁻¹ • x)))
      (𝓝[>] 0) (𝓝 (Hp p W ξ)) := by
  simpa [subaddLimit, cubeRatio, Hp] using hS.tendsto_eps hρ x

/-- The Sobolev cell problem `A ↦ Ytp p W A ξ` satisfies the hypotheses of the subadditive
theorem when `W` is periodic and `W(·, ξ)` is bounded by `c`. -/
theorem subaddCube_Ytp {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {W : Sp N → Mat m N → ℝ≥0∞}
    {ξ : Mat m N} {c : ℝ≥0} (hW : IsPeriodic W) (hc : ∀ y, W y ξ ≤ c) :
    SubaddCube (fun A => Ytp p W A ξ) c :=
  ⟨fun _ _ _ hAo hAb hBo hCo hBA hCA hBC hcov => Ytp_sub hAo hAb hBo hCo hBA hCA hBC hcov,
    fun z ρ x => hW.Ytp_cube z ρ x ξ, fun A _ _ => Ytp_bound_of_pointwise hc A⟩

/-- **Corollary `SubadditiveTheorem`** of [oah-jpm-zorgati14]: for `W` periodic with
`W(x, ξ) ≤ β (1 + G ξ)` and `ξ ∈ dom G`,
`Ytp(ε⁻¹ Q_ρ(x), ξ) / |ε⁻¹ Q_ρ(x)| → ℋ_p W(ξ)` as `ε → 0⁺`. -/
theorem Ytp_tendsto_Hp {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {W : Sp N → Mat m N → ℝ≥0∞}
    {G : Mat m N → ℝ≥0∞} {β : ℝ≥0} (hW : IsPeriodic W)
    (hgrowth : ∀ x ξ, W x ξ ≤ β * (1 + G ξ)) {ξ : Mat m N} (hξ : G ξ ≠ ⊤)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Sp N) :
    Tendsto (fun ε : ℝ =>
      Ytp p W (cube (ρ / ε) (ε⁻¹ • x)) ξ / volume (cube (ρ / ε) (ε⁻¹ • x)))
      (𝓝[>] 0) (𝓝 (Hp p W ξ)) := by
  have htop : (β : ℝ≥0∞) * (1 + G ξ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hξ⟩)
  refine Ytp_cell_tendsto_eps (subaddCube_Ytp (c := ((β : ℝ≥0∞) * (1 + G ξ)).toNNReal) hW
    fun y => ?_) hρ x
  rw [ENNReal.coe_toNNReal htop]
  exact hgrowth y ξ

/-- The gradient of a `W^{1,p}_0(U)` competitor vanishes a.e. off `U` when `|∂U| = 0`: on the
open set `ℝᴺ ∖ Ū` the function vanishes, so its weak gradient does (locality). -/
theorem W1p0.ae_grad_eq_zero_off {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Set (Sp N)}
    (hUo : IsOpen U) (hUf : volume (frontier U) = 0)
    {u : (Sp N → Tgt m) × (Sp N → Mat m N)} (hu : u ∈ W1p0 p U) :
    ∀ᵐ y, y ∉ U → u.2 y = 0 := by
  have hBo : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have h0 : u.1 =ᵐ[volume.restrict (closure U)ᶜ] 0 :=
    (ae_restrict_iff' hBo.measurableSet).2 (ae_of_all _ fun y hy =>
      hu.1 y fun h => hy (subset_closure h))
  have hB := HasWeakGrad.eq_zero_on_open hBo h0 hu.2.2.1 hu.2.2.2
  have hfr : ∀ᵐ y, y ∉ frontier U := measure_eq_zero_iff_ae_notMem.1 hUf
  filter_upwards [hB, hfr] with y h1 h2 hyU
  exact h1 fun hcl => h2 ⟨hcl, by rwa [hUo.interior_eq]⟩

/-- **Countable gluing in `W^{1,p}_0`**, for pieces with null boundaries (e.g. cubes). -/
theorem W1p0.tsum_of_disjoint' {m : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {O : Set (Sp N)} {Q : ℕ → Set (Sp N)} (hQo : ∀ i, IsOpen (Q i))
    (hQf : ∀ i, volume (frontier (Q i)) = 0)
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) (hQO : ∀ i, Q i ⊆ O)
    {u : ℕ → (Sp N → Tgt m) × (Sp N → Mat m N)}
    (hu : ∀ i, u i ∈ W1p0 (ENNReal.ofReal p) (Q i))
    (hsum1 : ∑' i, ∫⁻ y, ‖(u i).1 y‖ₑ ^ p < ⊤) (hsum2 : ∑' i, ∫⁻ y, ‖(u i).2 y‖ₑ ^ p < ⊤) :
    ((fun y => ∑' i, (u i).1 y), (fun y => ∑' i, (Q i).indicator (u i).2 y)) ∈
      W1p0 (ENNReal.ofReal p) O :=
  W1p0.tsum_of_disjoint hQo hQd hQO hu
    (fun i => W1p0.ae_grad_eq_zero_off (hQo i) (hQf i) (hu i)) hsum1 hsum2

end Homogenization
