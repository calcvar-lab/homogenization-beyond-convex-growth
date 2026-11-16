# Homogenization of nonconvex unbounded integrals beyond convex growth

O. Anza Hafsa, A. Hachache, M. L. Leghmizi, J.-P. Mandallena.

The paper is available on HAL: <https://hal.science/hal-05851819>.

| Folder | Content |
|---|---|
| `visual-paper/` | Interactive reading of the paper: the text at three depths, previews of every cross-reference, the dependency atlas, the hypotheses (H1)–(H8) across the paper, and the Lean status of each result. Online: <https://calcvar-lab.github.io/homogenization-beyond-convex-growth/visual-paper/> (or open `visual-paper/index.html`) |
| `lean/` | Lean 4 / Mathlib formalization (see `lean/README.md`) |

`CORRESPONDENCE.md` points to the correspondence between the paper and the Lean declarations
(`lean/REGISTRY.md`), `formalization.yaml` gives the metadata of the formalization, and
`CONTRIBUTING.md` explains how to report errors and propose changes.

The visual paper links to the Lean sources through the relative path `../lean/Homogenization`, so
the two folders should stay side by side.

## Licenses

| Folder | License |
|---|---|
| `lean/` | Apache License 2.0 (`lean/LICENSE`, copyright notice in `lean/NOTICE`). Lean 4, Mathlib and the other dependencies keep their own licenses |
| `visual-paper/` | Creative Commons Attribution 4.0 International (CC BY 4.0, `visual-paper/LICENSE`), the license of the paper on HAL. The copy of KaTeX in `visual-paper/vendor/` keeps its MIT license, given in `visual-paper/vendor/THIRD_PARTY_LICENSES` |
