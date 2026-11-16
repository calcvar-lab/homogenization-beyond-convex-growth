import Homogenization.Basic

/-!
# Local Lipschitz regularity from coordinatewise convexity

A local version of Dacorogna, *Direct Methods* (2008), Theorem 2.31, used in Appendix A of the
paper (step (c)). A function `f : (ι → ℝ) → [0,∞]`, finite on an open set `V`, which satisfies the
convexity inequality along coordinate directions whenever the intermediate point lies in `V`, is
locally Lipschitz on `V`. Neither `V` nor the effective domain of `f` is assumed to be convex.

The norm on `ι → ℝ` is the sup norm of the coordinates, so the cubes of the proof are the
closed balls `closedBall x ρ`.
-/

open Set Metric Filter Topology
open scoped ENNReal NNReal

namespace Homogenization

section CoordConvex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The hypothesis of `locallyLipschitzOn_of_coordConvex`: the convexity inequality along each
coordinate direction, at every intermediate point `ξ ∈ V`. -/
def CoordConvexOn (V : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ≥0∞) : Prop :=
  ∀ ξ ∈ V, ∀ i : ι, ∀ s : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
    f ξ ≤ ENNReal.ofReal t * f (ξ + ((1 - t) * s) • Pi.single i 1) +
      ENNReal.ofReal (1 - t) * f (ξ - (t * s) • Pi.single i 1)

variable {V : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ≥0∞}

omit [Fintype ι] in
/-- Segment form of the hypothesis, for the real-valued `toReal ∘ f`, on a coordinate segment
`[p, p + c • eₖ]` contained in a convex set `Q ⊆ V`. -/
theorem CoordConvexOn.segment (hf : CoordConvexOn V f) (hfin : ∀ y ∈ V, f y ≠ ⊤)
    {Q : Set (ι → ℝ)} (hQ : Convex ℝ Q) (hQV : Q ⊆ V) {p : ι → ℝ} {k : ι} {c θ : ℝ}
    (hp : p ∈ Q) (hq : p + c • Pi.single k 1 ∈ Q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (f (p + (θ * c) • Pi.single k 1)).toReal ≤
      (1 - θ) * (f p).toReal + θ * (f (p + c • Pi.single k 1)).toReal := by
  set q := p + c • (Pi.single k (1 : ℝ) : ι → ℝ) with hq_def
  rcases hθ0.eq_or_lt with rfl | hθ0'
  · simp
  rcases hθ1.eq_or_lt with rfl | hθ1'
  · simp [q]
  have hξ : p + (θ * c) • (Pi.single k (1 : ℝ) : ι → ℝ) ∈ Q := by
    have : p + (θ * c) • (Pi.single k (1 : ℝ) : ι → ℝ) = (1 - θ) • p + θ • q := by
      rw [hq_def]; module
    rw [this]; exact hQ hp hq (by linarith) hθ0 (by ring)
  have h := hf _ (hQV hξ) k c θ ⟨hθ0', hθ1'⟩
  have e1 : p + (θ * c) • (Pi.single k (1 : ℝ) : ι → ℝ) +
      ((1 - θ) * c) • (Pi.single k (1 : ℝ) : ι → ℝ) = q := by
    rw [hq_def]; module
  have e2 : p + (θ * c) • (Pi.single k (1 : ℝ) : ι → ℝ) -
      (θ * c) • (Pi.single k (1 : ℝ) : ι → ℝ) = p := by abel
  rw [e1, e2] at h
  have hpt := hfin p (hQV hp)
  have hqt := hfin q (hQV hq)
  have h1 : ENNReal.ofReal θ * f q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqt
  have h2 : ENNReal.ofReal (1 - θ) * f p ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1, h2⟩) h
  rw [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hθ0, ENNReal.toReal_ofReal (by linarith)] at this
  linarith

omit [Fintype ι] in
theorem update_eq_add_single (y : ι → ℝ) (k : ι) (a : ℝ) :
    Function.update y k a = y + (a - y k) • (Pi.single k (1 : ℝ) : ι → ℝ) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp
  · simp [hj]

theorem mem_closedBall_update {x y : ι → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hy : y ∈ closedBall x ρ)
    {k : ι} {a : ℝ} (ha : |a - x k| ≤ ρ) : Function.update y k a ∈ closedBall x ρ := by
  rw [mem_closedBall, dist_pi_le_iff hρ] at hy ⊢
  intro j
  by_cases hj : j = k
  · subst hj; simpa [Real.dist_eq] using ha
  · simpa [Function.update_of_ne hj] using hy j

/-- **Step 1** of `locallyLipschitzOn_of_coordConvex`: `toReal ∘ f` is bounded above on a closed
cube in `V`. -/
theorem CoordConvexOn.bddAbove_closedBall (hf : CoordConvexOn V f) (hfin : ∀ y ∈ V, f y ≠ ⊤)
    {x : ι → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hQV : closedBall x ρ ⊆ V) :
    ∃ A : ℝ, ∀ y ∈ closedBall x ρ, (f y).toReal ≤ A := by
  set W : Set (ι → ℝ) := Set.pi univ fun j => ({x j - ρ, x j + ρ} : Set ℝ)
  have hW : W.Finite := Set.Finite.pi fun j => Set.toFinite _
  have hbdd : BddAbove ((fun y => (f y).toReal) '' W) := (hW.image _).bddAbove
  refine ⟨sSup ((fun y => (f y).toReal) '' W), ?_⟩
  have key : ∀ S : Finset ι, ∀ y ∈ closedBall x ρ,
      (∀ j ∉ S, y j ∈ ({x j - ρ, x j + ρ} : Set ℝ)) →
        (f y).toReal ≤ sSup ((fun y => (f y).toReal) '' W) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro y _ hyS
      exact le_csSup hbdd ⟨y, fun j _ => hyS j (Finset.notMem_empty j), rfl⟩
    | @insert k S hk ih =>
      intro y hy hyS
      have hyk : |y k - x k| ≤ ρ := by
        have := (dist_pi_le_iff hρ.le).1 (mem_closedBall.1 hy) k
        rwa [Real.dist_eq] at this
      set p := Function.update y k (x k - ρ)
      have hp : p ∈ closedBall x ρ :=
        mem_closedBall_update hρ.le hy (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hρ])
      have hq_eq : p + (2 * ρ) • (Pi.single k (1 : ℝ) : ι → ℝ) =
          Function.update y k (x k + ρ) := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [p]; ring
        · simp [p, hj]
      have hq : p + (2 * ρ) • (Pi.single k (1 : ℝ) : ι → ℝ) ∈ closedBall x ρ := by
        rw [hq_eq]
        exact mem_closedBall_update hρ.le hy (by rw [add_sub_cancel_left, abs_of_pos hρ])
      have hcond : ∀ a, a ∈ ({x k - ρ, x k + ρ} : Set ℝ) →
          (f (Function.update y k a)).toReal ≤ sSup ((fun y => (f y).toReal) '' W) := by
        intro a ha
        refine ih _ (mem_closedBall_update hρ.le hy ?_) fun j hj => ?_
        · rcases ha with rfl | rfl
          · rw [sub_sub_cancel_left, abs_neg, abs_of_pos hρ]
          · rw [add_sub_cancel_left, abs_of_pos hρ]
        · by_cases hjk : j = k
          · subst hjk; simpa using ha
          · rw [Function.update_of_ne hjk]
            exact hyS j (by simp [hjk, hj])
      set θ := (y k - (x k - ρ)) / (2 * ρ)
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith [neg_abs_le (y k - x k)]) (by linarith)
      have hθ1 : θ ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith [le_abs_self (y k - x k)]
      have hy_eq : p + (θ * (2 * ρ)) • (Pi.single k (1 : ℝ) : ι → ℝ) = y := by
        have : θ * (2 * ρ) = y k - (x k - ρ) := by
          simp only [θ]; field_simp
        rw [this]
        funext j
        by_cases hj : j = k
        · subst hj; simp [p]
        · simp [p, hj]
      have hseg := hf.segment hfin (convex_closedBall x ρ) hQV hp hq hθ0 hθ1
      rw [hy_eq, hq_eq] at hseg
      have hA1 := hcond _ (Or.inl rfl)
      have hA2 := hcond _ (Or.inr rfl)
      calc (f y).toReal ≤ (1 - θ) * (f p).toReal +
            θ * (f (Function.update y k (x k + ρ))).toReal := hseg
        _ ≤ (1 - θ) * sSup ((fun y => (f y).toReal) '' W) +
            θ * sSup ((fun y => (f y).toReal) '' W) := by
          gcongr
        _ = _ := by ring
  intro y hy
  exact key Finset.univ y hy fun j hj => absurd (Finset.mem_univ j) hj

/-- **Step 2** of `locallyLipschitzOn_of_coordConvex`: an upper bound `A` on a closed cube in `V`
gives the lower bound `2ⁿ f(x) - (2ⁿ - 1) A` on the same cube. -/
theorem CoordConvexOn.lowerBound_closedBall (hf : CoordConvexOn V f) (hfin : ∀ y ∈ V, f y ≠ ⊤)
    {x : ι → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hQV : closedBall x ρ ⊆ V) {A : ℝ}
    (hA : ∀ y ∈ closedBall x ρ, (f y).toReal ≤ A) :
    ∀ y ∈ closedBall x ρ,
      2 ^ Fintype.card ι * (f x).toReal - (2 ^ Fintype.card ι - 1) * A ≤ (f y).toReal := by
  have key : ∀ S : Finset ι, ∀ y ∈ closedBall x ρ, (∀ j ∉ S, y j = x j) →
      2 ^ S.card * (f x).toReal - (2 ^ S.card - 1) * A ≤ (f y).toReal := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro y _ hyS
      have : y = x := funext fun j => hyS j (Finset.notMem_empty j)
      subst this; simp
    | @insert k S hk ih =>
      intro y hy hyS
      have hyk : |y k - x k| ≤ ρ := by
        have := (dist_pi_le_iff hρ.le).1 (mem_closedBall.1 hy) k
        rwa [Real.dist_eq] at this
      set p := Function.update y k (x k)
      set w := Function.update y k (2 * x k - y k)
      have hp : p ∈ closedBall x ρ := mem_closedBall_update hρ.le hy (by simp [hρ.le])
      have hw : w ∈ closedBall x ρ := mem_closedBall_update hρ.le hy (by
        rw [show 2 * x k - y k - x k = -(y k - x k) by ring, abs_neg]; exact hyk)
      have hpS : ∀ j ∉ S, p j = x j := by
        intro j hj
        by_cases hjk : j = k
        · subst hjk; simp [p]
        · simp only [p, Function.update_of_ne hjk]; exact hyS j (by simp [hjk, hj])
      set c := 2 * (y k - x k)
      have hwy : w + c • (Pi.single k (1 : ℝ) : ι → ℝ) = y := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [w, c]; ring
        · simp [w, hj]
      have hwp : w + ((1 / 2 : ℝ) * c) • (Pi.single k (1 : ℝ) : ι → ℝ) = p := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [w, p, c]; ring
        · simp [w, p, hj]
      have hseg := hf.segment hfin (convex_closedBall x ρ) hQV hw (by rw [hwy]; exact hy)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      rw [hwp, hwy] at hseg
      have hIH := ih p hp hpS
      have hAw := hA w hw
      rw [Finset.card_insert_of_notMem hk, pow_succ]
      nlinarith
  intro y hy
  have := key Finset.univ y hy fun j hj => absurd (Finset.mem_univ j) hj
  simpa [Finset.card_univ] using this

/-- **Step 3** of `locallyLipschitzOn_of_coordConvex`: the Lipschitz bound along one coordinate. -/
theorem CoordConvexOn.sub_le_single (hf : CoordConvexOn V f) (hfin : ∀ y ∈ V, f y ≠ ⊤)
    {x : ι → ℝ} {r : ℝ} (hr : 0 < r) (hQV : closedBall x (2 * r) ⊆ V) {A B : ℝ}
    (hA : ∀ y ∈ closedBall x (2 * r), (f y).toReal ≤ A)
    (hB : ∀ y ∈ closedBall x (2 * r), B ≤ (f y).toReal)
    {z : ι → ℝ} (hz : z ∈ closedBall x r) {i : ι} {h : ℝ}
    (hzh : z + h • (Pi.single i (1 : ℝ) : ι → ℝ) ∈ closedBall x r) :
    (f (z + h • (Pi.single i (1 : ℝ) : ι → ℝ))).toReal - (f z).toReal ≤ (A - B) / r * |h| := by
  have h2r : closedBall x r ⊆ closedBall x (2 * r) := closedBall_subset_closedBall (by linarith)
  have hAB : 0 ≤ A - B := by
    have := (hB z (h2r hz)).trans (hA z (h2r hz)); linarith
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hh' : 0 < |h| := abs_pos.2 hh
  set c := h + r * (h / |h|)
  set θ := |h| / (|h| + r)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hθc : θ * c = h := by
    simp only [θ, c]
    field_simp
  have hw : z + c • (Pi.single i (1 : ℝ) : ι → ℝ) ∈ closedBall x (2 * r) := by
    have hzh' := (dist_pi_le_iff hr.le).1 (mem_closedBall.1 hzh)
    have hz' := (dist_pi_le_iff hr.le).1 (mem_closedBall.1 hz)
    rw [mem_closedBall, dist_pi_le_iff (by linarith)]
    intro j
    by_cases hj : j = i
    · subst hj
      have h1 := hzh' j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Real.dist_eq] at h1 ⊢
      have hu : |r * (h / |h|)| = r := by
        rw [abs_mul, abs_div, abs_abs, div_self hh'.ne', mul_one, abs_of_pos hr]
      calc |z j + c - x j| = |(z j + h - x j) + r * (h / |h|)| := by simp only [c]; ring_nf
        _ ≤ |z j + h - x j| + |r * (h / |h|)| := abs_add_le _ _
        _ ≤ 2 * r := by rw [hu]; linarith
    · have := hz' j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hj, if_false, smul_eq_mul,
        mul_zero, add_zero] at this ⊢
      linarith
  have hseg := hf.segment hfin (convex_closedBall x (2 * r)) hQV (h2r hz) hw hθ0 hθ1
  rw [hθc] at hseg
  have hAw := hA _ hw
  have hBz := hB z (h2r hz)
  have hθr : θ ≤ |h| / r := div_le_div_of_nonneg_left hh'.le hr (by linarith)
  calc (f (z + h • (Pi.single i (1 : ℝ) : ι → ℝ))).toReal - (f z).toReal
      ≤ θ * ((f (z + c • (Pi.single i (1 : ℝ) : ι → ℝ))).toReal - (f z).toReal) := by linarith
    _ ≤ θ * (A - B) := by gcongr
    _ ≤ |h| / r * (A - B) := by gcongr
    _ = (A - B) / r * |h| := by ring

/-- **Local version of [dacorogna08, Thm 2.31].** A function which is finite and coordinatewise
convex at the points of an open set `V` is locally Lipschitz on `V`; the neighbourhoods are closed
cubes. -/
theorem locallyLipschitzOn_of_coordConvex (hV : IsOpen V) (hfin : ∀ y ∈ V, f y ≠ ⊤)
    (hf : CoordConvexOn V f) :
    ∀ x ∈ V, ∃ K : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith K (fun y => (f y).toReal) s := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV x hx
  set r := ε / 3
  have hr : 0 < r := by positivity
  have hQV : closedBall x (2 * r) ⊆ V :=
    (closedBall_subset_ball (by simp only [r]; linarith)).trans hball
  obtain ⟨A, hA⟩ := hf.bddAbove_closedBall hfin (by linarith) hQV
  set B := 2 ^ Fintype.card ι * (f x).toReal - (2 ^ Fintype.card ι - 1) * A
  have hB := hf.lowerBound_closedBall hfin (by linarith) hQV hA
  set C := (A - B) / r
  have hsingle : ∀ z ∈ closedBall x r, ∀ i : ι, ∀ h : ℝ,
      z + h • (Pi.single i (1 : ℝ) : ι → ℝ) ∈ closedBall x r →
        |(f (z + h • (Pi.single i (1 : ℝ) : ι → ℝ))).toReal - (f z).toReal| ≤ C * |h| := by
    intro z hz i h hzh
    rw [abs_le]
    refine ⟨?_, hf.sub_le_single hfin hr hQV hA hB hz hzh⟩
    have := hf.sub_le_single hfin hr hQV hA hB hzh (i := i) (h := -h) (by simpa using hz)
    simp only [neg_smul, add_neg_cancel_right, abs_neg] at this
    linarith
  -- Step 4: change the coordinates one at a time.
  have hchain : ∀ z ∈ closedBall x r, ∀ z' ∈ closedBall x r, ∀ S : Finset ι,
      |(f (fun j => if j ∈ S then z' j else z j)).toReal - (f z).toReal| ≤
        C * ∑ j ∈ S, |z' j - z j| := by
    intro z hz z' hz' S
    have hmem : ∀ T : Finset ι, (fun j => if j ∈ T then z' j else z j) ∈ closedBall x r := by
      intro T
      rw [mem_closedBall, dist_pi_le_iff hr.le]
      intro j
      have h1 := (dist_pi_le_iff hr.le).1 (mem_closedBall.1 hz) j
      have h2 := (dist_pi_le_iff hr.le).1 (mem_closedBall.1 hz') j
      split_ifs <;> assumption
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have heq : (fun j => if j ∈ insert k S then z' j else z j) =
          (fun j => if j ∈ S then z' j else z j) +
            (z' k - z k) • (Pi.single k (1 : ℝ) : ι → ℝ) := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [hk]
        · simp [hj]
      have hstep := hsingle _ (hmem S) k (z' k - z k) (heq ▸ hmem (insert k S))
      rw [← heq] at hstep
      rw [Finset.sum_insert hk, mul_add]
      calc _ ≤ |(f (fun j => if j ∈ insert k S then z' j else z j)).toReal -
              (f (fun j => if j ∈ S then z' j else z j)).toReal| +
            |(f (fun j => if j ∈ S then z' j else z j)).toReal - (f z).toReal| :=
            abs_sub_le _ _ _
        _ ≤ _ := by linarith
  have hC : 0 ≤ C := by
    have h1 := hA x (mem_closedBall_self (by linarith))
    have h2 := hB x (mem_closedBall_self (by linarith))
    exact div_nonneg (by linarith) hr.le
  refine ⟨(C * Fintype.card ι).toNNReal, closedBall x r, closedBall_mem_nhds x hr, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun z' hz' z hz => ?_
  have h := hchain z hz z' hz' Finset.univ
  have hfull : (fun j => if j ∈ (Finset.univ : Finset ι) then z' j else z j) = z' := by
    funext j; simp
  rw [hfull] at h
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  calc |(f z').toReal - (f z).toReal| ≤ C * ∑ j, |z' j - z j| := h
    _ ≤ C * (Fintype.card ι * dist z' z) := by
      gcongr
      calc ∑ j, |z' j - z j| ≤ ∑ _j : ι, dist z' z :=
            Finset.sum_le_sum fun j _ => by
              rw [← Real.dist_eq]; exact dist_le_pi_dist z' z j
        _ = Fintype.card ι * dist z' z := by simp
    _ = C * Fintype.card ι * dist z' z := by ring

omit [Fintype ι] in
/-- Transport local Lipschitz regularity from a finite coordinate space through a continuous
linear equivalence. The Lipschitz constant is multiplied by the operator norm of the forward
coordinate map. -/
theorem locallyLipschitzOn_of_coordConvex_equiv
    [Finite ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] (ι → ℝ)) {W : Set E} {g : E → ℝ≥0∞}
    (hW : IsOpen W) (hfin : ∀ x ∈ W, g x ≠ ⊤)
    (hcoord : CoordConvexOn (e '' W) (fun z => g (e.symm z))) :
    ∀ x ∈ W, ∃ K : ℝ≥0, ∃ s ∈ 𝓝 x,
      LipschitzOnWith K (fun y => (g y).toReal) s := by
  have := Fintype.ofFinite ι
  have hW' : IsOpen (e '' W) := e.toHomeomorph.isOpenMap _ hW
  have hfin' : ∀ z ∈ e '' W, g (e.symm z) ≠ ⊤ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    simpa using hfin x hx
  intro x hx
  obtain ⟨K, s, hs, hLip⟩ :=
    locallyLipschitzOn_of_coordConvex hW' hfin' hcoord (e x) ⟨x, hx, rfl⟩
  refine ⟨K * ‖e.toContinuousLinearMap‖₊, e ⁻¹' s, ?_, ?_⟩
  · exact e.continuous.continuousAt.preimage_mem_nhds hs
  · apply LipschitzOnWith.of_dist_le_mul
    intro x' hx' y' hy'
    have hx'' : e x' ∈ s := hx'
    have hy'' : e y' ∈ s := hy'
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hLip) (e x') hx'' (e y') hy''
    calc
      dist ((g x').toReal) ((g y').toReal) =
          dist (((fun z => g (e.symm z)) (e x')).toReal)
            (((fun z => g (e.symm z)) (e y')).toReal) := by simp
      _ ≤ K * dist (e x') (e y') := h
      _ ≤ K * (‖e.toContinuousLinearMap‖₊ * dist x' y') := by
        gcongr
        exact_mod_cast (e.toContinuousLinearMap.dist_le_opNorm x' y')
      _ = (K * ‖e.toContinuousLinearMap‖₊) * dist x' y' := by ring

/-- The contractive form of the transport theorem preserves the coordinate Lipschitz constant. -/
theorem locallyLipschitzOn_of_coordConvex_equiv_of_contractive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] (ι → ℝ)) (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    {W : Set E} {g : E → ℝ≥0∞} (hW : IsOpen W)
    (hfin : ∀ x ∈ W, g x ≠ ⊤)
    (hcoord : CoordConvexOn (e '' W) (fun z => g (e.symm z))) :
    ∀ x ∈ W, ∃ K : ℝ≥0, ∃ s ∈ 𝓝 x,
      LipschitzOnWith K (fun y => (g y).toReal) s := by
  have hW' : IsOpen (e '' W) := e.toHomeomorph.isOpenMap _ hW
  have hfin' : ∀ z ∈ e '' W, g (e.symm z) ≠ ⊤ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    simpa using hfin x hx
  intro x hx
  obtain ⟨K, s, hs, hLip⟩ :=
    locallyLipschitzOn_of_coordConvex hW' hfin' hcoord (e x) ⟨x, hx, rfl⟩
  refine ⟨K, e ⁻¹' s, e.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x' hx' y' hy'
  have h := (lipschitzOnWith_iff_dist_le_mul.mp hLip) (e x') hx' (e y') hy'
  calc
    dist ((g x').toReal) ((g y').toReal) =
        dist (((fun z => g (e.symm z)) (e x')).toReal)
          (((fun z => g (e.symm z)) (e y')).toReal) := by simp
    _ ≤ K * dist (e x') (e y') := h
    _ ≤ K * dist x' y' := by exact mul_le_mul_of_nonneg_left (he x' y') K.2

end CoordConvex

section MatTransport

variable {m N : ℕ} {V : Set (Mat m N)}

/-- Rank-one convexity on a possibly nonconvex set, with the interpolation point in that set. -/
def RankOneConvexOn (V : Set (Mat m N)) (f : Mat m N → ℝ≥0∞) : Prop :=
  ∀ A ∈ V, ∀ d : Tgt m, d ≠ 0 → ∀ ν : Sp N, ‖ν‖ = 1 →
    ∀ s : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      f A ≤ ENNReal.ofReal t * f (A + ((1 - t) * s) • rankOne d ν) +
        ENNReal.ofReal (1 - t) * f (A - (t * s) • rankOne d ν)

/-- Rank-one convexity implies coordinatewise convexity in the row-major matrix coordinates. -/
theorem RankOneConvexOn.coordConvex {f : Mat m N → ℝ≥0∞} (h : RankOneConvexOn V f) :
    CoordConvexOn (matCoordEquiv m N '' V)
      (fun z => f ((matCoordEquiv m N).symm z)) := by
  intro z hz i s t ht
  obtain ⟨A, hA, rfl⟩ := hz
  let d : Tgt m := Pi.single i.1 (1 : ℝ)
  let ν : Sp N := Pi.single i.2 (1 : ℝ)
  have hd : d ≠ 0 := by
    intro hd
    have hi := congrFun hd i.1
    simp [d] at hi
  have hν : ‖ν‖ = 1 := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro j
      by_cases hj : j = i.2 <;> simp [ν, hj]
    · have hi := norm_le_pi_norm ν i.2
      simpa [ν] using hi
  have hunit : matCoordEquiv m N (rankOne d ν) = Pi.single i (1 : ℝ) := by
    simpa [d, ν] using matCoordEquiv_rankOne_single i.1 i.2
  have hinv (c : ℝ) :
        (matCoordEquiv m N).symm
        (matCoordEquiv m N A + c • (Pi.single i (1 : ℝ) : Fin m × Fin N → ℝ)) =
        A + c • rankOne d ν := by
    rw [← hunit]
    apply (matCoordEquiv m N).injective
    simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  have hinv_sub (c : ℝ) :
      (matCoordEquiv m N).symm
        (matCoordEquiv m N A - c • (Pi.single i (1 : ℝ) : Fin m × Fin N → ℝ)) =
        A - c • rankOne d ν := by
    rw [← hunit]
    apply (matCoordEquiv m N).injective
    simp only [map_sub, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  have hrank := h A hA d hd ν hν s t ht
  simpa only [hinv, hinv_sub, ContinuousLinearEquiv.symm_apply_apply] using hrank

/-- Coordinate convexity on matrix space implies local Lipschitz regularity with the same
constant, since every matrix coordinate is bounded by the operator norm. -/
theorem locallyLipschitzOn_of_matCoordConvex {f : Mat m N → ℝ≥0∞} (hV : IsOpen V)
    (hfin : ∀ A ∈ V, f A ≠ ⊤)
    (hcoord : CoordConvexOn (matCoordEquiv m N '' V)
      (fun A => f ((matCoordEquiv m N).symm A))) :
    ∀ A ∈ V, ∃ K : ℝ≥0, ∃ s ∈ 𝓝 A,
      LipschitzOnWith K (fun B => (f B).toReal) s := by
  apply locallyLipschitzOn_of_coordConvex_equiv_of_contractive (matCoordEquiv m N)
  · intro A B
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖matCoordEquiv m N A - matCoordEquiv m N B‖ =
          ‖matCoordEquiv m N (A - B)‖ := by rw [map_sub]
      _ ≤ ‖A - B‖ := matCoordEquiv_norm_le _
  · exact hV
  · exact hfin
  · exact hcoord

end MatTransport

end Homogenization
