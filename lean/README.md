# Homogenization beyond convex growth — Lean 4 formalization

Lean 4 / Mathlib formalization of the paper

> O. Anza Hafsa, A. Hachache, M. L. Leghmizi, J.-P. Mandallena,
> *Homogenization of nonconvex unbounded integrals beyond convex growth*.

The main homogenization theorem (Theorem `main-Ggrowth`), the product theorem
(Theorem `th:product` (iii)) and the three examples of the paper are proved **without any
unproved hypothesis**: no `sorry`, no `axiom`, and the main theorems depend only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

The results the paper cites from other works are proved here as well, in particular
Theorem 1.1 of Anza Hafsa–Mandallena–Zorgati (2014) (`citedAHM14_holds`), together with the
Sobolev ingredients it uses: Rellich-type compactness on Lipschitz domains, a.e.
differentiability for `p > N` (Morrey), and the measure-limit lemma. The differentiation theorem
for set functions of Anza Hafsa–Clozeau–Mandallena (2017, Theorem A.16) is proved with its
equality (`citedVitaliEnvelope_holds`), although the main theorem uses only the inequality.

## Main results

| Paper | Lean declaration | File |
|---|---|---|
| Theorem `main-Ggrowth` (Γ-convergence) | `Homogenization.main_Ggrowth_final_unconditional` | `Homogenization/AHM14.lean` |
| Theorem `th:AHM11` ([AHM-Zorgati 2014, Thm 1.1]) | `Homogenization.citedAHM14_holds` | `Homogenization/AHM14.lean` |
| Theorem `Vitali-envelope-cite` ([oah-cloz-jpm17, Thm A.16]), with the equality | `Homogenization.citedVitaliEnvelope_holds` | `Homogenization/VitaliEquality.lean` |
| Proposition 2.1(i) of [AHM-Zorgati 2014], local lower bound | `Homogenization.localLowerBound` | `Homogenization/AHM14.lean` |
| Proposition 2.1(ii) of [AHM-Zorgati 2014], Γ-limsup | `Homogenization.GammaLimsup_le_intHom_radialHp` | `Homogenization/Recovery.lean` |
| Theorem `th:product` (iii) | `Homogenization.th_product_iii_unconditional` | `Homogenization/MeasurableYtloc.lean` |
| Example (separable integrand) | `Homogenization.sepConcrete_sep_iv` | `Homogenization/Examples/SepConcrete.lean` |
| Example (proper domain, (iv)) | `Homogenization.properDomainWv_sep_iv` | `Homogenization/Examples/ProperDomainSepIV.lean` |
| Example (sharp, (iv)) | `Homogenization.properDomainWSharpExample_pd_iv` | `Homogenization/Examples/ProperDomainSharpIV.lean` |

`REGISTRY.md` maps every numbered result of the paper to its Lean declarations and
gives its status.

### Reading the statements

* `Sp N = Fin N → ℝ` carries the sup norm, and `cube ρ x` is the open sup-norm ball of radius
  `ρ / 2`, i.e. the open cube of side `ρ` centred at `x`.
* `W1p N m p Ω` bundles a function, its weak gradient, and the `Lᵖ(Ω)` integrability of both.
* Some intermediate theorems (for instance `main_Ggrowth`, …, `main_Ggrowth_final_two` and the
  `*_of_cited` lemmas of `LowerBound.lean`) still take results of other papers as explicit
  hypotheses, named `Cited*`. These hypotheses are discharged in the files listed above, which give
  the final statements without them.

## Building

Requires [elan](https://github.com/leanprover/elan). The Lean version (`v4.33.0`) and the
Mathlib revision are pinned by `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get   # download the precompiled Mathlib (recommended)
lake build
```

To check the axioms of the main theorems:

```sh
lake env lean scripts/CheckAxioms.lean
```

Each line of the output should read `[propext, Classical.choice, Quot.sound]`.

## References

Citation keys used in the docstrings and in `REGISTRY.md` (they follow the bibliography of the
paper):

* [ball-murat84] J. M. Ball, F. Murat, *W^{1,p}-quasiconvexity and variational problems for
  multiple integrals*, J. Funct. Anal. (1984).
* [dacorogna08] B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer
  (2008).
* [duerinckx-gloria16] M. Duerinckx, A. Gloria, *Stochastic homogenization of nonconvex unbounded
  integral functionals with convex growth*, Arch. Ration. Mech. Anal. (2016).
* [fonseca88] I. Fonseca, *The lower quasiconvex envelope of the stored energy function for an
  elastic crystal*, J. Math. Pures Appl. (1988).
* [oah-cloz-jpm17] O. Anza Hafsa, N. Clozeau, J.-P. Mandallena, *Homogenization of nonconvex
  unbounded singular integrals*, Ann. Math. Blaise Pascal 24 (2017).
* [oah-jpm11] (AHM11) O. Anza Hafsa, J.-P. Mandallena, *Homogenization of nonconvex integrals with
  convex growth*, J. Math. Pures Appl. (2011).
* [oah-jpm-zorgati14] (AHM14) O. Anza Hafsa, J.-P. Mandallena, H. Zorgati, *Homogenization of
  unbounded integrals with quasiconvex growth*, Ann. Mat. Pura Appl. (2015).
* [oah-leg-jpm-singhom] O. Anza Hafsa, M. L. Leghmizi, J.-P. Mandallena, *New results on relaxation
  and homogenization of unbounded singular integrals*, Ric. Mat. 74 (2025).
* [oahjpm14] O. Anza Hafsa, J.-P. Mandallena, *Radial representation of lower semicontinuous
  envelope*, Boll. Unione Mat. Ital. (2014).
* [oahjpm18] O. Anza Hafsa, J.-P. Mandallena, *Relaxation of nonconvex unbounded integrals with
  general growth conditions in Cheeger-Sobolev spaces*, Bull. Sci. Math. (2018). Metric measure
  space version of the differentiation theorem `Vitali-envelope-cite`.

Labels such as `main-Ggrowth`, `th:product` or `Vitali-envelope-cite` are the LaTeX labels of the
corresponding statements in the paper.

## License

License: Apache-2.0. The full text is in `LICENSE`, and the copyright notice in `NOTICE`.
Copyright 2026 Omar Anza Hafsa, Adel Hachache, Mohamed Lamine Leghmizi, Jean-Philippe Mandallena.
The dependencies (Lean 4, Mathlib and the packages it uses) keep their own licenses.
