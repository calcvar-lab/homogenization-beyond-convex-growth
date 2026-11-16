# Correspondence between the paper and the Lean formalization

The correspondence between the statements of the paper and the Lean declarations is given in
[`lean/REGISTRY.md`](lean/REGISTRY.md). For every labelled result of the paper (definitions,
lemmas, propositions, theorems, examples), the registry lists:

* the LaTeX label of the statement in the paper;
* the Lean declarations that formalize it, with links to the source files;
* its status (`proved`, `cited hypothesis` or `not formalized`) and the differences between the
  Lean statement and the paper, if any;
* its main mathematical and formal dependencies.

The main results and their Lean declarations are also summarized in
[`lean/README.md`](lean/README.md#main-results). The visual paper shows the Lean status of each
result next to its statement.
