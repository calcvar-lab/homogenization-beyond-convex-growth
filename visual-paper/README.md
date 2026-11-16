# Visual Paper

An interactive reading of “Homogenization of nonconvex unbounded integrals beyond convex growth”
(PDF on HAL: <https://hal.science/hal-05851819>).
It is generated from the LaTeX source of the paper and from the registry of the Lean
formalization (`../lean/REGISTRY.md`).

Open `index.html` in a browser. No server and no network are needed.

## What it offers

* **The paper as one continuous text**, in the order of the source, set in the face of its
  formulas (Computer Modern, through the KaTeX fonts), at three depths:
  *Statements* (headings, statements, and the hypotheses (H1)–(H8) as statements),
  *Proof outline* (adds the steps of each proof, each with the results it cites; a step opens in
  place), and *Full text*. Omitted prose is marked by a line that opens it in place.
* **Previews of every cross-reference.** A click on a reference, an equation number, a hypothesis
  or a citation shows its target in the margin, with where it stands in the paper. “Go to” moves
  there, and a return button brings back the reading position.
* **A margin for each result**: its editorial name, its Lean status (with the registry note,
  declarations and files on demand), the hypotheses it mentions, what it uses and what uses it.
* **Atlas**: the dependency graph drawn in columns, foundations on the left, which can be
  enlarged to the whole window (button or key `f`); pointing at a result shows what it rests on
  and what rests on it, through all references.
* **Hypotheses**: a table of the results against (H1)–(H8), read from the explicit references.
* **Lean**: the status of each result, with its declarations, notes and files.
* Search over results, sections, hypotheses and Lean declarations; keys (`?` lists them); light
  and dark themes; text size; phone layout.

Three colours, each with one meaning: blue for references, orange for the hypotheses, blue-green
for Lean. The editorial names of the results shown in the margin are not part of the paper.

The links to the Lean files (`../lean/Homogenization/`) are relative: keep the folders of the
release side by side.

## Rebuilding

    sh build/figures.sh        # figures/<label>.png from the TikZ code of the paper
    cd build && python3 -I build.py

`build/build.py` reads the source of the paper and its `.aux` from a folder `../paper/` next to
`visual-paper/` (the source is not part of this repository; the paper itself is on HAL:
<https://hal.science/hal-05851819>), and `../lean/REGISTRY.md`, and writes `data.js`. It renders the formulas with KaTeX through Node
(any system), or through macOS JavaScriptCore when Node is absent, and prints the number of KaTeX
errors, which should be 0. Both engines give the same `data.js`.
`build/figures.sh` needs `pdflatex` and Ghostscript.

## Checks

`tests/check.js` runs inside the page (paste it in the browser console). It checks that every
cross-reference and citation has a target, that every result, prose piece and proof step of the
source is in the text, that the statements match the source, that the older addresses
(`#/node/…`, `#/sec/…`) reach their target, that no formula failed, and that the Lean marks agree
with the registry. It passes in Chromium, Firefox and WebKit, at desktop and phone widths.

## Files

| File | Content |
|---|---|
| `index.html`, `css/vp.css` | page, typography and themes |
| `js/core.js` | indexes of the data: order, references, hypotheses, Lean status |
| `js/text.js` | the continuous text, margin notes, contents |
| `js/peek.js` | previews of references and citations |
| `js/atlas.js` | the layered dependency drawing (SVG, no library) |
| `js/ledgers.js` | the hypotheses and Lean ledgers |
| `js/app.js` | routes, depth, reading position, search, keys |
| `data.js`, `figures/` | generated content |
| `build/` | generator |
| `tests/check.js` | checks run in the page |
| `vendor/` | KaTeX 0.16.11 (MIT license, see `vendor/THIRD_PARTY_LICENSES`) |
