# Contributing

This repository accompanies the paper *Homogenization of nonconvex unbounded integrals beyond
convex growth* by O. Anza Hafsa, A. Hachache, M. L. Leghmizi and J.-P. Mandallena. The Lean statements
follow version v1.0 of the paper. We welcome:

* reports of errors in the paper, in the Lean statements or in the correspondence given by
  [`lean/REGISTRY.md`](lean/REGISTRY.md);
* reports of build failures (please give the output of `lake build` and your platform);
* proposals that simplify a proof or follow a change of Mathlib.

Please open an issue on GitHub before preparing a pull request, so that we can discuss the change.

## Rules for the Lean code

* Use the Lean version and the Mathlib revision pinned by `lean/lean-toolchain` and
  `lean/lake-manifest.json`.
* Never use `sorry`, `admit`, `native_decide` or new `axiom` declarations.
* Do not change a statement that formalizes a result of the paper unless it differs from the
  paper; in that case, explain the difference in the issue.
* Do not add an unproved hypothesis (in the style of the `Cited*` hypotheses of the intermediate
  theorems) to a final statement.
* For every new or changed declaration, update its row in `lean/REGISTRY.md`.
* State in the docstring what is not proved when a lemma is only a partial step.

## Checks

Run from the `lean/` folder:

```sh
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
```

Each line printed by the last command must list only the axioms `propext`, `Classical.choice`
and `Quot.sound`.
The continuous integration (`.github/workflows/lean_action_ci.yml`) runs the same checks and
rejects any `sorry`, `admit` or `native_decide`, and any `axiom` declaration, in the sources.

## Visual paper

The files of `visual-paper/` are generated from the LaTeX source of the paper by
`visual-paper/build/build.py` (see `visual-paper/README.md`); the source is not part of this
repository.
Report errors in the visual paper through an issue rather than by editing
the generated files.

## Licenses

By contributing, you agree that your contribution to `lean/` is licensed under the Apache License
2.0 and your contribution to `visual-paper/` under CC BY 4.0, as stated in `README.md`.
