import Homogenization.DensityZaff

/-!
# Gluing homothetic copies of a cell test function (Lemma `lem:glue`)

Let `φ ∈ Aff₀(Y)`, let `{a_k + r_k Y}_{k ∈ K}` be a countable family of pairwise disjoint open cubes
contained in `U`, and let `V ⊆ U` be an open set, disjoint from every cube, with `|U ∩ ∂V| = 0`
and `|U ∖ (V ∪ ⋃_k (a_k + r_k Y))| = 0`. The function `Φ` equal to `r_k φ((x - a_k)/r_k)` on
`a_k + r_k Y` and to `0` elsewhere belongs to `Aff₀(U)`, has the Lipschitz constants of `φ`, and
`∇Φ(x) = ∇φ((x - a_k)/r_k)` on each cube. The pieces of `Φ` are the copies of the pieces of `φ`
and the open set `V`, on which `Φ = 0`.
-/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace Homogenization

variable {N m : ℕ}

/-- **Lemma `lem:glue`.** Let `φ ∈ Aff₀(Y)`, let `{cube (r k) (a k)}_{k}` be a countable family of
pairwise disjoint open cubes contained in `U`, and let `V ⊆ U` be open, disjoint from every cube,
with `|U ∩ ∂V| = 0` and `|U ∖ (V ∪ ⋃_k cube (r k) (a k))| = 0`. Then the glued function
`Φ = ∑_k zcopy φ (r k) (a k)` (equal to `r_k φ((x - a_k)/r_k)` on the `k`-th cube and to `0`
elsewhere) belongs to `Aff₀(U)`, is `K`-Lipschitz on `ℝᴺ` whenever `φ` is, and
`∇Φ(x) = ∇φ((x - a_k)/r_k)` for every `x` in the `k`-th cube. Neither openness nor boundedness of
`U` is needed. -/
theorem aff0_glue_cubes {ι : Type*} [Countable ι] {U V : Set (Sp N)} {a : ι → Sp N} {r : ι → ℝ}
    (hr : ∀ k, 0 < r k) (hQU : ∀ k, cube (r k) (a k) ⊆ U)
    (hQd : Pairwise fun k l => Disjoint (cube (r k) (a k)) (cube (r l) (a l)))
    (hVo : IsOpen V) (hVU : V ⊆ U) (hVQ : ∀ k, Disjoint V (cube (r k) (a k)))
    (hVfr : volume (U ∩ frontier V) = 0)
    (hcov : volume (U \ (V ∪ ⋃ k, cube (r k) (a k))) = 0)
    {φ : Sp N → Tgt m} (hφ : φ ∈ Aff0 (cube 1 (0 : Sp N))) :
    ((fun x => ∑' k, zcopy φ (r k) (a k) x) ∈ (Aff0 U : Set (Sp N → Tgt m))) ∧
      (∀ K : ℝ≥0, LipschitzWith K φ →
        LipschitzWith K fun x => ∑' k, zcopy φ (r k) (a k) x) ∧
      ∀ k, ∀ x ∈ cube (r k) (a k),
        fderiv ℝ (fun x => ∑' k, zcopy φ (r k) (a k) x) x = fderiv ℝ φ (affMap (r k) (a k) x) := by
  classical
  obtain ⟨K, n, W0, ζ, hK, h0, hW0o, hW0U, hW0d, hW0f, hW0c, hφW0⟩ := Aff0.data hφ
  set O : ι → Set (Sp N) := fun k => cube (r k) (a k) with hO
  have hOo : ∀ k, IsOpen (O k) := fun k => isOpen_cube _ _
  set f : ι → Sp N → Tgt m := fun k => zcopy φ (r k) (a k) with hf
  have hf0 : ∀ k, ∀ y ∉ O k, f k y = 0 := fun k y hy => zcopy_eq_zero (hr k) _ h0 hy
  set Φ : Sp N → Tgt m := fun x => ∑' k, f k x with hΦ
  have hLip : ∀ K' : ℝ≥0, LipschitzWith K' φ → LipschitzWith K' Φ := fun K' hK' =>
    lipschitzWith_tsum_cells hOo hQd (fun k => zcopy_lipschitz (hr k) _ hK') hf0
  have hΦloc : ∀ k, ∀ x ∈ O k, Φ =ᶠ[𝓝 x] f k := fun k x hx => by
    filter_upwards [(hOo k).mem_nhds hx] with z hz using tsum_cells_of_mem hQd hf0 hz
  have hΦV : ∀ x ∈ V, Φ =ᶠ[𝓝 x] fun _ => (0 : Tgt m) := fun x hx => by
    filter_upwards [hVo.mem_nhds hx] with z hz using
      tsum_cells_of_notMem hf0 fun k hk => (hVQ k).le_bot ⟨hz, hk⟩
  set P : ι → Fin n → Set (Sp N) := fun k l => affMap (r k) (a k) ⁻¹' W0 l with hP
  have hPO : ∀ k l, P k l ⊆ O k := fun k l => by
    change affMap (r k) (a k) ⁻¹' W0 l ⊆ cube (r k) (a k)
    rw [← preimage_affMap_cube (hr k) (a k)]; exact preimage_mono (hW0U l)
  set W : Fin n → Set (Sp N) := fun l => ⋃ k, P k l with hW
  have hOW : ∀ k l, O k ∩ W l ⊆ P k l := by
    rintro k l z ⟨hzO, hzW⟩
    obtain ⟨b, hb⟩ := mem_iUnion.1 hzW
    by_cases hkb : k = b
    · exact hkb ▸ hb
    · exact absurd (hPO b l hb) (Set.disjoint_left.1 (hQd hkb) hzO)
  have hnull : ∀ k (S : Set (Sp N)), volume S = 0 →
      volume (affMap (r k) (a k) ⁻¹' S) = 0 := fun k S hS => by
    rw [volume_preimage_affMap (hr k), hS, mul_zero]
  have hWo : ∀ l, IsOpen (W l) := fun l =>
    isOpen_iUnion fun k => (hW0o l).preimage (continuous_affMap (hr k) _)
  have hWV : ∀ l, Disjoint (W l) V := fun l => Set.disjoint_left.2 fun z hz hzV => by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    exact (hVQ k).le_bot ⟨hzV, hPO k l hk⟩
  have hmemcube : ∀ k y, y ∈ O k → y ∈ affMap (r k) (a k) ⁻¹' cube 1 0 := fun k y hy => by
    rw [preimage_affMap_cube (hr k)]; exact hy
  -- the pieces: the copies of the pieces of `φ`, and `V`
  set Z : Option (Fin n) → Set (Sp N) := fun o => o.elim V W with hZ
  set η : Option (Fin n) → Mat m N := fun o => o.elim 0 ζ with hη
  have hZU : ∀ o, Z o ⊆ U := by
    rintro (_ | l)
    · exact hVU
    · exact iUnion_subset fun k => (hPO k l).trans (hQU k)
  have hPW : IsPWAffine U Φ := by
    refine isPWAffine_of_fintype (hLip K hK).lipschitzOnWith Z η ?_ hZU ?_ ?_ ?_ ?_
    · rintro (_ | l)
      · exact hVo
      · exact hWo l
    · rintro (_ | l) (_ | l') hll'
      · exact absurd rfl hll'
      · exact (hWV l').symm
      · exact hWV l
      · have hne : l ≠ l' := fun h => hll' (h ▸ rfl)
        refine Set.disjoint_left.2 fun z hz hz' => ?_
        obtain ⟨k, hk⟩ := mem_iUnion.1 hz
        obtain ⟨b, hb⟩ := mem_iUnion.1 hz'
        by_cases hkb : k = b
        · subst hkb; exact (hW0d hne).le_bot ⟨hk, hb⟩
        · exact (hQd hkb).le_bot ⟨hPO k l hk, hPO b l' hb⟩
    · rintro (_ | l)
      · exact hVfr
      · refine measure_mono_null (t := (U \ (V ∪ ⋃ k, O k)) ∪
          ⋃ k, affMap (r k) (a k) ⁻¹' (cube 1 0 ∩ frontier (W0 l))) ?_
          (measure_union_null hcov (measure_iUnion_null fun k => hnull k _ (hW0f l)))
        rintro y ⟨hyU, hyf⟩
        by_cases hy : ∃ k, y ∈ O k
        · obtain ⟨k, hk⟩ := hy
          refine Or.inr (mem_iUnion.2 ⟨k, hmemcube k y hk, ?_⟩)
          change y ∈ affMap (r k) (a k) ⁻¹' frontier (W0 l)
          rw [← frontier_preimage_affMap (hr k)]
          exact ⟨closure_mono (hOW k l) ((hOo k).inter_closure ⟨hk, frontier_subset_closure hyf⟩),
            fun hint => hyf.2 (interior_mono (subset_iUnion (fun b => P b l) k) hint)⟩
        · have hyV : y ∉ V := fun hyV => by
            obtain ⟨z, hzV, hzW⟩ := mem_closure_iff.1 (frontier_subset_closure hyf) V hVo hyV
            exact (hWV l).le_bot ⟨hzW, hzV⟩
          exact Or.inl ⟨hyU, fun h => h.elim hyV fun h' => hy (mem_iUnion.1 h')⟩
    · refine measure_mono_null (t := (U \ (V ∪ ⋃ k, O k)) ∪
        ⋃ k, affMap (r k) (a k) ⁻¹' (cube 1 0 \ ⋃ l, W0 l)) ?_
        (measure_union_null hcov (measure_iUnion_null fun k => hnull k _ hW0c))
      rintro y ⟨hyU, hyZ⟩
      by_cases hy : ∃ k, y ∈ O k
      · obtain ⟨k, hk⟩ := hy
        refine Or.inr (mem_iUnion.2 ⟨k, hmemcube k y hk, fun h => hyZ ?_⟩)
        obtain ⟨l, hl⟩ := mem_iUnion.1 h
        exact mem_iUnion.2 ⟨some l, mem_iUnion.2 ⟨k, hl⟩⟩
      · have hyV : y ∉ V := fun hyV => hyZ (mem_iUnion.2 ⟨none, hyV⟩)
        exact Or.inl ⟨hyU, fun h => h.elim hyV fun h' => hy (mem_iUnion.1 h')⟩
    · rintro (_ | l) y hy
      · exact (hasFDerivAt_const (0 : Tgt m) y).congr_of_eventuallyEq (hΦV y hy)
      · obtain ⟨k, hk⟩ := mem_iUnion.1 hy
        exact (zcopy_hasFDerivAt (hr k) (a k) (hφW0 l _ hk)).congr_of_eventuallyEq
          (hΦloc k y (hPO k l hk))
  refine ⟨⟨⟨K, hLip K hK⟩, fun y hy => tsum_cells_of_notMem hf0 fun k h => hy (hQU k h), hPW⟩,
    hLip, fun k x hx => ?_⟩
  rw [(hΦloc k x hx).fderiv_eq]
  exact fderiv_zcopy (hr k) (a k) φ x

end Homogenization
