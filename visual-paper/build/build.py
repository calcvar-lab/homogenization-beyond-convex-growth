#!/usr/bin/env python3
"""Build the visual companion of `Homogenization_beyond_convex_growthV1.tex`.

Reads the source of the paper in ../../paper (or ../../paper-public) (its .tex, which includes the bibliography, and its
.aux for the numbers), and the project's
REGISTRY.md (Lean status). Writes ../data.js, consumed by ../js/*.js. All formulas are rendered
ahead of time with KaTeX, run by Node or, if Node is absent, by macOS's JavaScriptCore (`jsc`);
rendering errors are reported.
"""
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SITE = os.path.dirname(HERE)
ROOT = os.path.dirname(SITE)  # the folder holding paper/ (or paper-public/), visual-paper/ and lean/
PROJECT = os.path.join(ROOT, "paper")
if not os.path.isdir(PROJECT):
    PROJECT = os.path.join(ROOT, "paper-public")
PAPER = "Homogenization_beyond_convex_growthV1"  # basename of the paper source
TEX = os.path.join(PROJECT, PAPER + ".tex")
AUX = os.path.join(PROJECT, PAPER + ".aux")
LEAN_PROJECT = os.path.join(ROOT, "lean")
REGISTRY = os.path.join(LEAN_PROJECT, "REGISTRY.md")
LEAN_DIR = "../lean/Homogenization"  # relative to index.html
JSC = "/System/Library/Frameworks/JavaScriptCore.framework/Versions/Current/Helpers/jsc"


def js_engine():
    """The JavaScript engine that runs render.js: $VP_JS if set, else Node, else macOS jsc."""
    engine = os.environ.get("VP_JS") or shutil.which("node")
    if engine:
        return engine
    if os.path.exists(JSC):
        return JSC
    sys.exit("build.py needs Node (https://nodejs.org) or macOS JavaScriptCore to run KaTeX")

STMT_ENVS = ["theorem", "proposition", "corollary", "lemma", "definition", "remark",
             "remarks", "example", "sublemma"]
ENV_NAME = {"theorem": "Theorem", "proposition": "Proposition", "corollary": "Corollary",
            "lemma": "Lemma", "definition": "Definition", "remark": "Remark",
            "remarks": "Remarks", "example": "Example", "sublemma": "Sub-lemma"}
LIST_LABELS = {  # enumitem lists of the preamble: (kind, math template)
    "hyproman": "roman", "hypabc": "alpha", "hypbullet": "bullet",
    "hypcond": r"\mathrm{H}_{%d}", "hypU": r"\mathrm{A}_{%d}", "hypG": r"\mathrm{G}_{%d}",
    "hypZ": r"\mathrm{C}_{%d}", "hypB": r"\mathrm{B}_{%d}", "hypHtheta": r"\mathrm{H}_{%d}^\theta",
    "hypConv": r"\mathrm{B}_{%d}", "hypConv1": r"\mathrm{Z}_{%d}", "hypD": r"\mathrm{D}_{%d}",
    "enumerate": "arabic", "itemize": "bullet",
}
NICK = {
    "def:cell": "Affine Dirichlet problem", "def:envelopes": "The four envelopes",
    "def:Ggrowth": "G-growth", "prop:radialrep": "Radial representation",
    "prop:Z3suff": "A criterion for (H8)", "lem:measurability": "Measurability (H6) for Σ aₖ(x)Hₖ(ξ)",
    "main-Ggrowth": "Main theorem", "lem:consequences": "Consequences of the hypotheses",
    "lem:ruusc-transfer": "ru-usc transfer to envelopes", "th:AHM11": "Homogenization under convex growth",
    "Vitali-envelope-cite": "Vitali envelope theorem", "Zenvelopefacts-cite": "Properties of Z-envelopes",
    "approx-affine-etoile-cite": "Affine approximation", "prop:densityZaff": "Affine density for Zaff",
    "prop:densityHaff": "Affine density for Haff", "lem:HaffZaff": "Haff versus Zaff",
    "lemma_osc_general": "Localized envelope ≤ integrand",
    "lem:sumosc": "Sums a(x)H(ξ) satisfy (H7)", "lemme_approx_convex_zero": "Convex approximation [DG16]",
    "lemmaUSC_ineq": "Affine vs Sobolev multi-cell", "lem:product": "Product integrands",
    "th:product": "Homogenization of a(x)H(ξ)", "lemmacasc": "A nowhere-continuous coefficient",
    "ex:sepconcrete": "A concrete example", "prop:separating": "Jacobian constraint",
    "lemmaree": "Zaff finite everywhere", "decouplresult": "Decoupled integrands",
    "prop:properdomain": "Growth function infinite on part of M", "lem:BB": "Ben Belgacem variant", "lem:glue": "Gluing copies of a cell test", "lem:YtleZaff": "Cell test copied into any open set",
    "rem:B1c": "Set-function vs pointwise growth", "rem:whyG4": "Why (H5)", "lEnvelopes": "Elementary properties",
    "rem:pdependence": "Dependence on p", "rem:pN": "On p > N", "rem:oscgen": "On the oscillation lemma",
    "rem:reach": "On the reach", "rem:BB": "On Ben Belgacem's lemma",
    "H1": "G convex, lsc, 0 ∈ int dom G", "H2": "Periodicity", "H3": "G-growth of the set function",
    "H4": "p-coercivity", "H5": "Uniform ru-usc", "H6": "Joint measurability",
    "H7": "Localized envelope ≤ W", "H8": "The structural inequality",
}
MAIN_RESULTS = ["main-Ggrowth", "prop:Z3suff", "th:product", "prop:separating",
                "prop:properdomain"]

warnings = []


def warn(msg):
    warnings.append(msg)


# ---------------------------------------------------------------- low-level parsing helpers

def strip_comments(s):
    out = []
    for line in s.split("\n"):
        i = 0
        cut = None
        while i < len(line):
            c = line[i]
            if c == "\\":
                i += 2
                continue
            if c == "%":
                cut = i
                break
            i += 1
        out.append(line if cut is None else line[:cut])
    return "\n".join(out)


def match_brace(s, i, open_="{", close="}"):
    """s[i] == open_; return index of the matching close."""
    depth = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == open_:
            depth += 1
        elif c == close:
            depth -= 1
            if depth == 0:
                return j
        elif open_ == "[" and c == "{":
            j = match_brace(s, j) + 1
            continue
        j += 1
    raise ValueError("unbalanced %s at %d: %r" % (open_, i, s[i:i + 80]))


def read_group(s, i):
    """Skip spaces; if s[i] == '{' return (content, end_index_after)."""
    while i < len(s) and s[i] in " \t\n":
        i += 1
    if i < len(s) and s[i] == "{":
        j = match_brace(s, i)
        return s[i + 1:j], j + 1
    # single token argument
    if i < len(s) and s[i] == "\\":
        m = re.match(r"\\[A-Za-z]+|\\.", s[i:])
        return m.group(0), i + len(m.group(0))
    return s[i:i + 1], i + 1


def read_opt(s, i):
    j = i
    while j < len(s) and s[j] in " \t":
        j += 1
    if j < len(s) and s[j] == "[":
        k = match_brace(s, j, "[", "]")
        return s[j + 1:k], k + 1
    return None, i


def find_env_end(s, name, start):
    """start is just after \\begin{name}; return (end_of_body, after_end)."""
    pat = re.compile(r"\\(begin|end)\{" + re.escape(name) + r"\}")
    depth = 1
    for m in pat.finditer(s, start):
        depth += 1 if m.group(1) == "begin" else -1
        if depth == 0:
            return m.start(), m.end()
    raise ValueError("unterminated env " + name)


# ---------------------------------------------------------------- aux, bbl, macros

def parse_aux():
    labels = {}
    for line in open(AUX, encoding="utf-8", errors="replace"):
        if not line.startswith("\\newlabel{"):
            continue
        i = len("\\newlabel")
        key, i = read_group(line, i)
        body, _ = read_group(line, i)
        parts = []
        j = 0
        while j < len(body):
            if body[j] == "{":
                k = match_brace(body, j)
                parts.append(body[j + 1:k])
                j = k + 1
            else:
                j += 1
        if len(parts) >= 4:
            labels[key] = {"num": parts[0], "page": parts[1], "anchor": parts[3]}
    return labels


def parse_bbl():
    """The bibliography is the `thebibliography` environment included in the .tex file."""
    tex = open(TEX, encoding="utf-8", errors="replace").read()
    i = tex.find("\\begin{thebibliography}")
    j = tex.find("\\end{thebibliography}", i)
    if i < 0 or j < 0:
        sys.exit("no thebibliography environment in " + TEX)
    s = tex[i:j + len("\\end{thebibliography}")]
    items = {}
    for m in re.finditer(r"\\bibitem\[([^\]]*)\]\{([^}]*)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})",
                         s, re.S):
        alpha, key, text = m.group(1), m.group(2), m.group(3)
        items[key] = {"alpha": alpha, "tex": text.strip()}
    return items


def parse_macros(pre):
    macros = {}
    for m in re.finditer(r"\\def\\([A-Za-z]+)\s*\{", pre):
        j = match_brace(pre, m.end() - 1)
        macros["\\" + m.group(1)] = pre[m.end():j]
    for m in re.finditer(r"\\(?:newcommand|renewcommand|DeclareRobustCommand)\*?\s*\{?\\([A-Za-z]+)\}?"
                         r"(?:\[(\d)\])?\s*\{", pre):
        j = match_brace(pre, m.end() - 1)
        macros["\\" + m.group(1)] = pre[m.end():j]
    for m in re.finditer(r"\\DeclareMathOperator\{\\([A-Za-z]+)\}\{(.*?)\}\s*$", pre, re.M):
        macros["\\" + m.group(1)] = r"\operatorname{" + m.group(2).strip("{}") + "}"
    # KaTeX-specific replacements and removals
    for k in ["\\rouge", "\\bleu", "\\com", "\\reallywidehat", "\\bfseries", "\\qedsymbol",
              "\\liminf", "\\limsup", "\\mlongmapsto", "\\medcup", "\\medcap"]:
        macros.pop(k, None)
    macros.update({
        "\\mathds": "\\mathbb", "\\mathbbm": "\\mathbb", "\\reallywidehat": "\\widehat",
        "\\fint": "\\mathop{\\rlap{\\hspace{0.18em}\\raisebox{0.05em}{$-$}}\\int}\\nolimits",
        "\\ind": "\\mathbf{1}", "\\mlongmapsto": "\\longmapsto", "\\phi": "\\varphi",
        "\\medcup": "\\bigcup", "\\medcap": "\\bigcap", "\\qedhere": "",
        "\\BM": "{\\mathcal{H}_{\\rm om}}", "\\swto": "\\overset{*}{\\rightharpoonup}",
        "\\niton": "\\not\\ni", "\\jk": "\\operatorname{P_k}",
    })
    return macros


# ---------------------------------------------------------------- registry (Lean status)

STATUS_MAP = [  # prefixes of the status column of REGISTRY.md
    ("proved under cited hypotheses", "conditional"),
    ("proved from the three cited classical results", "conditional"),
    ("proved without cited hypothesis, in the form of the paper", "proved"),
    ("proved without cited hypothesis for centred cubes", "partial"),
    ("(i) and (ii) proved; (iii) proved without cited hypothesis", "proved"),
    ("both assertions proved without cited hypothesis", "proved"),
    ("`sep:i` proved", "conditional"),
    ("generic statement proved without cited hypothesis", "partial"),
    ("(i) proved without cited hypothesis; (ii)", "conditional"),
    ("clauses (i) and (ii) proved", "conditional"),
    ("proved without cited hypothesis, as stated in the corrected paper", "proved"),
    ("**proved**", "proved"),
    ("proved for", "partial"),
    ("proved (inequality)", "partial"),
    ("proved", "proved"),
    ("partial", "started"),
    ("cited hypothesis", "cited"),
    ("not formalized", "none"),
]
# Rows whose registry wording still lists cited results (a)–(c) that are now proved in Lean
# (2026-10-13: citedSobolevCompact_holds, citedSobolevDiff_holds, citedMeasureLimit_holds,
# citedAHM14_holds, main_Ggrowth_final_unconditional, th_product_iii_unconditional).
STATUS_OVERRIDE = {
    "`th:AHM11`": "proved", "`main result` (i)": "proved", "`main result` (ii)": "proved",
    "`th:product`": "proved", "`prop:separating`": "proved", "`prop:properdomain`": "proved",
    "`lemmaree`": "proved",  # paper's statement: lemmaree_of_jacobian (LemmareeJacobian.lean)
}
STATUS_TEXT = {
    "proved": "Proved in Lean",
    "conditional": "Proved in Lean under cited results",
    "partial": "Proved in Lean (restricted form)",
    "started": "Partly formalized in Lean (main conclusions not yet proved)",
    "cited": "Cited hypothesis in Lean",
    "none": "Not formalized",
}

# English notes, written from REGISTRY.md.
NOTES = {
    "lem:BB": "Proved with no cited hypothesis, with exactly the hypotheses and conclusion of the paper (`lem_BB_paper`, β > 0): R₁F ≤ β(1+G) for the rank-one convex envelope R₁F (`Rone`), with no finiteness hypothesis. (eq:BB) is obtained as Zaff W⁺ ≤ R₁W⁺ ≤ β(1+G) (`Zaff_le_Rone`).",
    "lemmaree": "Proved with no cited hypothesis. Generic form (`lemmaree`, `ZaffFinite.lean`): for N ≤ m, if L is finite at every matrix with trivial kernel then Zaff L is finite everywhere (cross-polytope and pyramid in Aff₀, induction on dim ker ξ; measurability of L is not needed). With the equivalence v(ζ) ≠ 0 ⟺ ker ζ = 0 (`properDomainJacobian_ne_zero_iff`), the paper's Jacobian form follows (`lemmaree_of_jacobian`, `dom_Zaff_eq_univ_of_jacobian`, `LemmareeJacobian.lean`).",
    "th:product": "(i) `Ytloc(aH) = a·Zaff H` a.e. is proved with no cited hypothesis (`th_product_i`, `Product.lean`). (ii) Hypotheses H1–H3 and H5–H7 are proved for aH, including the exact H6: `Ytloc W` is jointly measurable without modification on a null set (`prodW_measurable_Ytloc`, `MeasurableYtloc.lean`); H8 with no cited hypothesis (`th_product_H8`). (iii) The Γ-convergence is proved with no cited hypothesis (`th_product_iii_unconditional`, `MeasurableYtloc.lean`; `th_product_iii` assumes only the measurability of `Ytloc W`). Jensen's inequality is extended to every bounded open set, without |∂U| = 0.",
    "lemmacasc": "Proved with no cited hypothesis (`lemmacasc`, `exists_cascData`, `Casc.lean`): a_ρ = 1 + 1_{D_ρ} is lsc, periodic, discontinuous off D_ρ, and |Y \\ D_ρ| ≥ 1 − ρ. Balls are for the sup norm and Y = ]−1/2,1/2[ᴺ; the enumeration of ℚᴺ ∩ Y is replaced by the only property used, that the translates cover ℚᴺ.",
    "lem:product": "Proved with no cited hypothesis (`lem_product`, `Product.lean`): G ≤ Zaff H ≤ H, dom Zaff H = dom G, radial monotonicity, local Lipschitz continuity, usc. The hypotheses 0 ∈ dom G, singularity on ∂(dom G) and measurability of H are not needed for these conclusions.",
    "lemmaUSC_ineq": "Both assertions proved with no cited hypothesis (`Haff_eq_Hp_of_usc`, `Haff_eq_Hp_of_usc_of_isOpen`, `USCIneq.lean`), using reverse Fatou, the cube case of `lemme_approx_convex_zero` (`approxConvexZero_cube`) and, for open dom G, Hahn–Banach separation.",
    "lemme_approx_convex_zero": "Proved with no cited hypothesis for centred cubes (`approxConvexZero_cube`, `ApproxConvexZero.lean`), the only case used in the paper (in `lemmaUSC_ineq`, with O = k₀Y): φₙ ∈ Aff₀(Q), ∇φₙ → ∇u a.e. and convergence of the Ψ-energies. Proof: Kuhn piecewise affine interpolation of C¹ compactly supported maps (`PwAffineInterp.lean`), then contraction–dilation, mollification and Jensen in W₀^{1,p} (`SmoothApproxW1p0.lean`). Not formalized: the statement for a general Lipschitz domain and the conclusions ∇φₙ ∈ int(dom Ψ) and φₙ → u in W^{1,p}. The former cited hypothesis `CitedApproxConvexZero` has been removed from the project.",
    "lem:sumosc": "Proved with no cited hypothesis (`lem_sumosc`, `SumOsc.lean`) for h = Σᵢ aᵢ Hᵢ: `Ytloc h = Zaff h ≤ h` and usc, with a single null set for all ξ. Measurability of the aᵢ follows from their lsc; measurability of the Hᵢ is not used.",
    "lemma_osc_general": "Proved with no cited hypothesis and no measurability of h (`lemma_osc_general`, `OscGeneral.lean`): `Ytloc h(x,·) = Zaff h(x,·)` and usc a.e. Clause (i) is stated pointwise, `h(x,ξ) ≤ (1+ε) h(z,ξ)` on Q_ρ(x), equivalent to the form with an infimum.",
    "prop:Z3suff": "Proved with no cited hypothesis (`prop_Z3suff`, `USCIneq.lean`, via `approxConvexZero_cube`). Differences from the paper: singularity of G is assumed at every ξ ∉ dom G (equivalent to the paper's condition on ∂(dom G) when dom G is open; that equivalence is not formalized), and measurability of `Ytloc h` (Z6) is assumed.",
    "prop:radialrep": "Proved with no cited hypothesis (`prop_radialrep_i`, `prop_radialrep_ii`, `RadialRep.lean`): radial limit, and the lsc envelope `liminf f (𝓝 ξ)` equals the radial extension; the sequential relaxation `lscEnv` is also treated. Part (i) does not use strong star-shapedness.",
    "def:cell": "Lean definitions `Yt` (affine class `Aff0`) and `Ytp` (Sobolev class `W1p0`).",
    "def:envelopes": "Lean definitions `Ytloc`, `Haff`, `Hp`, `Zaff`.",
    "def:Ggrowth": "Lean predicate `HasGGrowth G α β L`.",
    "lem:measurability": "Proved with no cited hypothesis (`measurable_Ytloc_sumW`, `MeasurableYtlocSum.lean`): for Borel aₖ with values in [η, Λ] (η > 0) and usc Hₖ, `Ytloc(Σ aₖHₖ)` is jointly Borel measurable, without modification on a null set.",
    "main-Ggrowth": "Proved with no cited hypothesis: `main_Ggrowth_final_unconditional` (`AHM14.lean`). All former hypotheses from the literature are proved in Lean: (a) `CitedSobolevCompact` (`citedSobolevCompact_holds`: Morrey on convex sets and a cone cover of Lipschitz domains, `SobolevCompact.lean`, `SobolevCompactUniform.lean`), (b) `CitedSobolevDiff` (`citedSobolevDiff_holds`, Morrey on cubes), (c) `CitedMeasureLimit` (`citedMeasureLimit_holds`, Prokhorov and portmanteau), `CitedAffineApprox` (`citedAffineApprox_holds`), hence `CitedAHM14` (`citedAHM14_holds`). The definitions of these hypotheses are unchanged since the start of the repository. `CitedZaffLocLip` is proved (`citedZaffLocLip`) and the Vitali envelope theorem is replaced by the proved inequality `vitaliEnvelopeUpper`. Only the standard axioms are used.",
    "lem:consequences": "Proved; the continuity statement uses the proved `CitedZaffLocLip`.",
    "lem:ruusc-transfer": "ru-usc is stable under the envelopes `Ytloc`, `Haff`, `Zaff`.",
    "th:AHM11": "Proved with no cited hypothesis (`citedAHM14_holds`, `AHM14.lean`), from the local lower bound `localLowerBound` and the Γ-limsup bound `GammaLimsup_le_intHom_radialHp`, with the three classical interfaces discharged — (a) Sobolev compactness and uniform convergence for p > N (`citedSobolevCompact_holds`), (b) a.e. differentiability of W^{1,p} (`citedSobolevDiff_holds`), (c) weak-* compactness of measures and Alexandrov (`citedMeasureLimit_holds`). The registry row still describes the theorem as proved from (a)–(c). See the components below.",
    "Vitali-envelope-cite": "Both inequalities are proved: `vitaliEnvelopeUpper` gives `vitaliEnv S A ≤ ∫_A dS`, which is all that Step 4 uses, and `citedVitaliEnvelope_holds` gives the equality.",
    "Zenvelopefacts-cite": "Both parts are stated for θ = Aff and arbitrary L, the only form used in the paper, and are proved with no cited hypothesis: (i) the rank-one inequality (`citedZaffLocLip`, `Zaff.rankOneInequality`), along the same route as Appendix A; (ii) domain independence (`aff0_domainIndependence`).",
    "approx-affine-etoile-cite": "Proved (`citedAffineApprox_holds : CitedAffineApprox N m p`, `AffineApprox.lean`, no new hypothesis; N < p is not used). Steps: continuity of dilations and mollifications in Lᵖ (`LpContinuity.lean`); homotheties of weak gradients and local mollification (`HomothetyMollify.lean`, `LocalMollifyEnergy.lean`); piecewise affine competitors in AffSet by Kuhn interpolation (`AffSetCompetitor.lean`); assembly (`exists_affSet_approx_step`). The skeleton theorems of `Main.lean`, `DensityZaff.lean`, `RankOne.lean` and `Vitali.lean` keep `hApprox` as a parameter; it is discharged in `main_Ggrowth_final_unconditional` (`AHM14.lean`).",
    "prop:densityZaff": "Proved with no cited hypothesis, as stated in the corrected paper (nonempty bounded open A with |∂A| = 0; `densityZaff`, `DensityZaffFull.lean`). For general A the upper bound is also proved (`densityZaffUpper`).",
    "prop:densityHaff": "Proved (`densityHaff`): construction of the correctors under growth, periodicity and convexity.",
    "lem:HaffZaff": "(i) `Zaff(Haff L) = Haff L`, (ii) local Lipschitz continuity of `Haff L` on int(dom G), and (iii) `H L = Haff L` on int(dom G) with local Lipschitz continuity of `H L` under usc, are all proved with no cited hypothesis (`Zaff_Haff_eq`, `Haff_locallyLipschitzOn`, `Haff_eq_Hp_of_usc`); (iii) uses the cube case of `lemme_approx_convex_zero`.",
    "prop:properdomain": "Formalized (`ProperDomain*.lean`). (i) geometry of dom G♯, convexity and lsc of G♯, exact boundary, and (ii) domain of W♯ = Σ × C₂ and non-convexity of Σ: proved. (iii) `Zaff G₂ = G₂`, decoupling of `Zaff W♯`, bounds `G♯ ≤ Zaff W♯ ≤ β♯(1+G♯)` uniform in x, and `Ytloc W♯ = Zaff W♯` a.e., usc (`properDomainWSharpExample_Ytloc_eq`, `lem:sumosc` with four terms): proved with no cited hypothesis. (iv) (H1)–(H7) with no cited hypothesis, including exact (H6) and (H8) (`properDomainWSharpExample_hypotheses`), all with no cited hypothesis; Γ-convergence (`properDomainWSharpExample_pd_iv`) with no cited hypothesis.",
    "ex:sepconcrete": "Proved with no cited hypothesis (`SepConcrete.lean`, `SepConcreteB2Sing.lean`): the concrete data g̃ = eˢ, H(s) = 1/s, K = θ·1{|ξ|_F ≥ 1}, a = b = a_ϱ satisfy (Dg)–(Dab); W_v(·,ξ) is discontinuous at every point of ℝᴺ∖D_ϱ (measure ≥ 1−ϱ per cell) whenever v(ξ) ≠ 0 (`sepConcrete_not_continuousAt`); and (B2Sing) fails for ϱ < 1, N ≤ m (`sepConcrete_not_B2Sing`), with the class `PiClass` defined as in the paper (λ Lebesgue measurable, nonnegative, essentially bounded), `B2Sing` and Remarks 2.6 and 2.8 of [AHLM], cited in the paper, proved here (`PiClass.ae_continuousAt`, `continuousAt_of_B2Sing_ineq`). `sepConcrete_sep_iv` applies sep:iv, with no cited hypothesis.",
    "prop:separating": "All four clauses are formalized; sep:i–sep:iii and (H1)–(H8) in sep:iv need no cited hypothesis. sep:i: dom W_v(x,·) = Σ (`dom_properDomainWv`), Σ not convex (`properDomainSigma_not_convex`). sep:ii: `Ytloc W_v = Zaff W_v ≤ W_v` off a single null set of x, usc in ξ (`properDomainWv_sep_ii`, via `lem:sumosc` with three terms G, K, H∘v). sep:iii: `G ≤ Zaff W_v ≤ β(1+G)`, uniform in x (`properDomainWv_Zaff_lower`, `properDomainWv_Zaff_le_growth`). sep:iv: (H1)–(H7) proved with no cited hypothesis, including exact joint measurability (H6) for sums ∑ aₖ(x)Hₖ(ξ) (`measurable_Ytloc_sumW`), and (H8), all with no cited hypothesis; Γ-convergence with density radial(Hp(Zaff W_v)) (`properDomainWv_sep_iv`) with no cited hypothesis.",
    "decouplresult": "Proved (`Zaff_separatedSum_matBlockSplit`) in the affine model `Aff0`, with measurability of the first integrand; the concrete example supplies it (`measurable_properDomainWv`).",
}

AHM14_COMPONENTS = [  # registry rows (by line prefix of column 1) shown under th:AHM11
    ("`AK-SubadditiveTheorem`", "Deterministic subadditive theorem (Akcoglu–Krengel) and the cell limit `Ytp_tendsto_Hp`"),
    ("Countable gluing", "Countable gluing in W₀^{1,p}"),
    ("Continuity of a convex `G`", "Continuity of a convex G on int(dom G)"),
    ("Cut-offs in", "Cut-off functions in W^{1,p} (product rule for weak gradients)"),
    ("Radial envelope and ru-usc", "Radial envelope; ru-usc transfer to H_p"),
    ("Domains and homogenized integrand", "Effective domains, H_p ≤ β(1+G), lower semicontinuity of the homogenized density"),
    ("`main result` (i)", "Lower bound, Prop. 2.1(i) of [AHMZ15] (local form)"),
    ("`main result` (ii)", "Upper bound, Prop. 2.1(ii) of [AHMZ15]"),
    ("Change of scale", "Rescaling of the cell problem"),
    ("Cubes have a Lipschitz boundary", "Cubes have Lipschitz boundary"),
]
ZENV_COMPONENTS = [
    ("Rank-one inequality (Appendix A", "Rank-one inequality for Zaff (laminates)"),
    ("`Zaff (Zaff L) = Zaff L`", "Idempotence Zaff ∘ Zaff = Zaff"),
    ("Separately convex ⇒", "Separately convex ⇒ locally Lipschitz (local Dacorogna, Thm 2.31)"),
    ("Transport to `Mat m N`", "Transport to m×N matrices"),
]
COMPONENT_NOTES = {
    "`main result` (i)": "Proved: `localLowerBound_of_cited` under (a)–(c), all three now proved in Lean (packaged in `citedAHM14_holds`).",
    "`main result` (ii)": "The Γ-limsup half of Prop. 2.1(ii) is proved under the hypotheses of `CitedAHM14`, with no cited hypothesis (`GammaLimsup_le_intHom_radialHp`, `Recovery.lean`; interface (b) is supplied by `citedSobolevDiff_holds`). Chain: local Dirichlet problem `mDirichlet`, its Vitali envelope and the cell/annulus competitor for the contracted background `t • u` (`UpperBound.lean`); Poincaré in `W1p0` on cubes by mollification (`poincare_cube_W1p0`, `Mollify.lean`); near-optimal correctors on a finite family of disjoint cubes, a finite Vitali truncation with small remainder, a fixed-ε recovery competitor and a diagonal argument (`GammaLimsup_le_limsup_of_diagonal`), giving `GammaLimsup ≤ vitaliEnv(limsup mDirichlet)` (`GammaLimsup_le_vitaliEnv_mDirichletLimsup`); then the radial bound and t → 1 (`GammaLimsup_le_intHom_radialHp_of_cited`). The extra hypotheses `Measurable G` and `∫ G(∇u) < ∞` are removed by restricting G to int(dom G) (`intDomRestrict`), applying the bound to s•u, showing Hp = ∞ off the closed domain (Hahn–Banach, `HasGGrowth.Hp_eq_top_of_not_mem_closure_dom`), then s → 1 by ru-usc. Interface (b) is now itself proved (`citedSobolevDiff_holds`, `Morrey.lean`), so the bound holds with no cited hypothesis (packaged in `citedAHM14_holds`).",
}


def parse_registry():
    rows = []
    for line in open(REGISTRY, encoding="utf-8"):
        if not line.startswith("| ") or line.startswith("| Label") or line.startswith("| ---"):
            continue
        cols = [c.strip() for c in line.strip().strip("|").split(" | ")]
        if len(cols) < 4:
            continue
        cols += [""] * (5 - len(cols))  # tolerate a row with a missing cost column
        rows.append(cols)
    return rows


def status_of(text):
    for key, val in STATUS_MAP:
        if text.startswith(key):
            return val
    return None


def decls_of(col):
    names = re.findall(r"`([^`]+)`", col)
    links = re.findall(r"\[`([A-Za-z]+\.lean)`\]\((?:Lean/)?Homogenization/([^)]+)\)", col)
    files = [base for base, _ in links]
    names = [n for n in names if not n.endswith(".lean") and n not in files
             and not re.match(r"^[a-z]+:[A-Za-z-]+$", n)]
    return names[:14], sorted(set(path for _, path in links))


# ---------------------------------------------------------------- LaTeX -> HTML

class Converter:
    def __init__(self, labels, bib, owner_of):
        self.labels = labels
        self.bib = bib
        self.owner_of = owner_of  # label -> (kind, id)
        self.math = []  # list of [tex, display]

    # --- refs
    def ref_tex(self, key):
        """Return the math (KaTeX) form of a reference number, or None for plain text."""
        lab = self.labels.get(key)
        if not lab:
            warn("unknown ref " + key)
            return None, "??"
        raw = lab["num"]
        if "$" in raw:
            t = raw.replace("$", "")
            return t, None
        txt = re.sub(r"\\rm\s*", "", raw)
        txt = txt.replace("{", "").replace("}", "").strip()
        return None, txt

    def mathspan(self, tex, display=False):
        self.math.append([tex, display])
        return "\x00M%d\x00" % (len(self.math) - 1)

    def ref_html(self, key, paren=False):
        t, txt = self.ref_tex(key)
        inner = self.mathspan(t) if t is not None else esc(txt)
        if paren:
            inner = "(" + inner + ")"
        kind, target = self.owner_of.get(key, ("none", ""))
        return ('<a class="ref" href="#" data-goto="%s" data-kind="%s" data-label="%s">%s</a>'
                % (esc(target), kind, esc(key), inner))

    def ref_in_math(self, key, paren=False):
        t, txt = self.ref_tex(key)
        s = t if t is not None else r"\text{%s}" % txt
        return "(" + s + ")" if paren else s

    def cite_html(self, keys, opt):
        parts = []
        for k in [k.strip() for k in keys.split(",")]:
            b = self.bib.get(k)
            if not b:
                warn("unknown cite " + k)
                parts.append(esc(k))
                continue
            parts.append('<a class="cite" href="#" data-bib="%s">%s</a>' % (esc(k), esc(b["alpha"])))
        s = ", ".join(parts)
        if opt:
            s += ", " + self.text(opt)
        return "[" + s + "]"

    # --- math
    def prep_math(self, m):
        m = re.sub(r"\\eqref\{([^}]*)\}", lambda x: self.ref_in_math(x.group(1), True), m)
        m = re.sub(r"\\ref\{([^}]*)\}", lambda x: self.ref_in_math(x.group(1)), m)
        m = re.sub(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}",
                   lambda x: r"\text{[%s]}" % ", ".join(self.bib.get(k.strip(), {"alpha": k})["alpha"]
                                                        for k in x.group(1).split(",")), m)
        m = m.replace(r"\nonumber", r"\notag").replace(r"\qedhere", "").replace(r"\mbox{}", "")
        m = re.sub(r"\\(rouge|bleu)\{", "{", m)
        return m

    def display(self, env, body):
        """Return HTML for a display environment."""
        star = env.endswith("*")
        base = env.rstrip("*")
        labels_here = re.findall(r"\\label\{([^}]*)\}", body)
        anchor = ' id="lbl-%s"' % esc(labels_here[0]) if labels_here else ""
        if base in ("equation", "displaymath", "bracket"):
            tex = body
            if not star and base == "equation":
                if labels_here and r"\tag" not in tex:
                    num = self.labels.get(labels_here[0], {}).get("num", "")
                    tex = re.sub(r"\\label\{[^}]*\}", "", tex) + r"\tag{%s}" % num
                else:
                    tex = re.sub(r"\\label\{[^}]*\}", "", tex)
            else:
                tex = re.sub(r"\\label\{[^}]*\}", "", tex)
            tex = self.prep_math(tex.strip())
        else:  # align / gather families
            rows = re.split(r"\\\\", body)
            out_rows = []
            for r in rows:
                labs = re.findall(r"\\label\{([^}]*)\}", r)
                r = re.sub(r"\\label\{[^}]*\}", "", r)
                if not star and r.strip():
                    if labs and r"\tag" not in r:
                        r += r"\tag{%s}" % self.labels.get(labs[0], {}).get("num", "")
                    elif r"\tag" not in r and r"\notag" not in r and r"\nonumber" not in r:
                        r += r"\notag"
                out_rows.append(r)
            inner = "\\\\".join(out_rows)
            tex = self.prep_math(r"\begin{%s*}%s\end{%s*}" % (base, inner, base) if star or True else "")
            if not star:
                tex = self.prep_math(r"\begin{%s}%s\end{%s}" % (base, inner, base))
        # every label of a multi-line display gets an anchor, not only the first one
        extra = "".join('<span class="anchor" id="lbl-%s"></span>' % esc(l) for l in labels_here[1:])
        return '<div class="dmath"%s>%s%s</div>' % (anchor, extra, self.mathspan(tex, True))

    # --- text
    def text(self, s):
        """Convert a LaTeX text fragment (may contain math, lists, displays) to HTML."""
        out = []
        i = 0
        n = len(s)
        buf = []

        def flush():
            if buf:
                out.append(esc_text("".join(buf)))
                buf.clear()

        while i < n:
            c = s[i]
            if c == "$":
                flush()
                if s.startswith("$$", i):
                    j = s.index("$$", i + 2)
                    out.append(self.display("bracket", s[i + 2:j]))
                    i = j + 2
                else:
                    j = i + 1
                    while s[j] != "$":
                        j += 2 if s[j] == "\\" else 1
                    out.append(self.mathspan(self.prep_math(s[i + 1:j])))
                    i = j + 1
                continue
            if c == "\\":
                m = re.match(r"\\([A-Za-z]+\*?|.)", s[i:])
                cmd = m.group(1)
                j = i + len(m.group(0))
                if cmd == "[":
                    flush()
                    k = s.index("\\]", j)
                    out.append(self.display("bracket", s[j:k]))
                    i = k + 2
                    continue
                if cmd == "(":
                    flush()
                    k = s.index("\\)", j)
                    out.append(self.mathspan(self.prep_math(s[j:k])))
                    i = k + 2
                    continue
                if cmd == "begin":
                    flush()
                    env, j = read_group(s, j)
                    if env in ("equation", "equation*", "align", "align*", "gather", "gather*",
                               "multline", "multline*", "alignat", "alignat*"):
                        a, b = find_env_end(s, env, j)
                        out.append(self.display(env, s[j:a]))
                        i = b
                        continue
                    if env in STMT_ENVS:
                        # a statement stated inside a proof: its own paragraph, without its
                        # optional title, so that the page can rebuild it as a statement block
                        a, b = find_env_end(s, env, j)
                        _, k = read_opt(s, j)
                        out.append("\n\n" + self.text(s[k:a]) + "\n\n")
                        i = b
                        continue
                    if env in LIST_LABELS:
                        a, b = find_env_end(s, env, j)
                        out.append(self.list_html(env, s[j:a]))
                        i = b
                        continue
                    if env == "cases":
                        warn("text-mode cases")
                    a, b = find_env_end(s, env, j)
                    out.append(self.text(s[j:a]))
                    i = b
                    continue
                if cmd in ("ref", "eqref"):
                    flush()
                    key, j = read_group(s, j)
                    out.append(self.ref_html(key, paren=(cmd == "eqref")))
                    i = j
                    continue
                if cmd == "cite":
                    flush()
                    opt, j = read_opt(s, j)
                    keys, j = read_group(s, j)
                    out.append(self.cite_html(keys, opt))
                    i = j
                    continue
                if cmd == "label":
                    flush()
                    key, j = read_group(s, j)
                    out.append('<span class="anchor" id="lbl-%s"></span>' % esc(key))
                    i = j
                    continue
                if cmd in ("emph", "textit", "em"):
                    flush()
                    if cmd == "em":
                        i = j
                        continue
                    arg, j = read_group(s, j)
                    out.append("<em>" + self.text(arg) + "</em>")
                    i = j
                    continue
                if cmd == "url":
                    flush()
                    arg, j = read_group(s, j)
                    out.append('<a class="url" href="%s" rel="noopener">%s</a>' % (esc(arg), esc(arg)))
                    i = j
                    continue
                if cmd == "texttt":
                    flush()
                    arg, j = read_group(s, j)
                    out.append("<code>" + self.text(arg) + "</code>")
                    i = j
                    continue
                if cmd in ("textbf",):
                    flush()
                    arg, j = read_group(s, j)
                    out.append("<strong>" + self.text(arg) + "</strong>")
                    i = j
                    continue
                if cmd in ("textrm", "text", "mbox", "textsf", "textup", "textnormal", "rouge",
                           "bleu", "ensuremath"):
                    flush()
                    arg, j = read_group(s, j)
                    out.append(self.text(arg))
                    i = j
                    continue
                if cmd == "texorpdfstring":
                    flush()
                    a1, j = read_group(s, j)
                    _, j = read_group(s, j)
                    out.append(self.text(a1))
                    i = j
                    continue
                if cmd in ("com", "footnote"):
                    flush()
                    arg, j = read_group(s, j)
                    if cmd == "footnote":
                        out.append('<span class="fn">(' + self.text(arg) + ")</span>")
                    i = j
                    continue
                if cmd in ("textcolor", "color"):
                    _, j = read_group(s, j)
                    i = j
                    continue
                if cmd in ("rm", "bf", "noindent", "medskip", "smallskip", "bigskip", "qedhere",
                           "newblock", "maketitle", "it", "small", "footnotesize", "normalsize",
                           "centering", "hfill", "par", "relax", "indent", "allowbreak",
                           "nobreak", "newline", "linebreak", "displaystyle", "appendix"):
                    if cmd in ("medskip", "bigskip", "par"):
                        buf.append("\n\n")
                    i = j
                    continue
                if cmd == "S":
                    buf.append("§")
                    i = j
                    continue
                if cmd in ("dots", "ldots"):
                    buf.append("…")
                    i = j
                    continue
                if cmd == "item":
                    i = j
                    continue
                if cmd in ("'", '"', "^", "`", "~"):
                    arg, j = read_group(s, j)
                    buf.append({"'": {"e": "é", "E": "É", "a": "á", "o": "ó", "i": "í"},
                                '"': {"o": "ö", "u": "ü", "a": "ä", "e": "ë"},
                                "^": {"i": "î", "\\i": "î", "e": "ê", "o": "ô", "a": "â"},
                                "`": {"e": "è", "a": "à"},
                                "~": {"n": "ñ"}}[cmd].get(arg.strip("{}"), arg))
                    i = j
                    continue
                if cmd in ("&", "%", "_", "#", "{", "}", "$"):
                    buf.append(cmd)
                    i = j
                    continue
                if cmd == ",":
                    buf.append("\u2009")
                    i = j
                    continue
                if cmd in (" ", "\\"):
                    buf.append(" ")
                    i = j
                    continue
                if cmd == "Gamma":
                    buf.append("Γ")
                    i = j
                    continue
                warn("text command \\" + cmd)
                i = j
                continue
            if c == "~":
                buf.append("\u00a0")
                i += 1
                continue
            if c in "{}":
                i += 1
                continue
            if s.startswith("---", i):
                buf.append("—")
                i += 3
                continue
            if s.startswith("--", i):
                buf.append("–")
                i += 2
                continue
            if s.startswith("``", i):
                buf.append("“")
                i += 2
                continue
            if s.startswith("''", i):
                buf.append("”")
                i += 2
                continue
            buf.append(c)
            i += 1
        flush()
        return "".join(out)

    def list_html(self, env, body):
        kind = LIST_LABELS[env]
        start = 1
        opt, k = read_opt(body, 0)
        if opt:
            m = re.search(r"start=(\d+)", opt)
            if m:
                start = int(m.group(1))
            body = body[k:]
        items = re.split(r"\\item\b", body)[1:]
        lis = []
        for idx, it in enumerate(items, start):
            if kind == "roman":
                lab = "(" + roman(idx) + ")"
                lab_html = esc(lab)
            elif kind == "alpha":
                lab_html = "(" + "abcdefghij"[idx - 1] + ")"
            elif kind == "bullet":
                lab_html = "•"
            elif kind == "arabic":
                lab_html = "%d." % idx
            else:
                lab_html = self.mathspan("(" + kind % idx + ")")
            labs = re.findall(r"\\label\{([^}]*)\}", it)
            aid = ' id="lbl-%s"' % esc(labs[0]) if labs else ""
            body_html = self.text(re.sub(r"\\label\{[^}]*\}", "", it, count=1) if labs else it)
            lis.append('<li%s><span class="li-label">%s</span><div class="li-body">%s</div></li>'
                       % (aid, lab_html, paragraphs(body_html, inline=True)))
        return '<ol class="tlist">' + "".join(lis) + "</ol>"


def roman(n):
    return ["", "i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x", "xi", "xii"][n]


def esc(s):
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace('"', "&quot;"))


def esc_text(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def paragraphs(html, inline=False):
    parts = [p.strip() for p in re.split(r"\n\s*\n", html) if p.strip()]
    if inline and len(parts) <= 1:
        return parts[0] if parts else ""
    return "".join("<p>%s</p>" % p for p in parts)


# ---------------------------------------------------------------- document structure

def main():
    raw = open(TEX, encoding="utf-8").read()
    pre, rest = raw.split("\\begin{document}", 1)
    body = rest.split("\\end{document}", 1)[0]
    # the bibliography is included in the .tex (arXiv source); it is rendered from parse_bbl()
    body = re.sub(r"\\begin\{thebibliography\}.*?\\end\{thebibliography\}", "", body, flags=re.S)
    body = strip_comments(body)
    # TikZ figures cannot be rendered by KaTeX: each is replaced by a marker, and by the image that
    # build/figures.sh makes from the same TikZ code (figures/<label>.png), with its caption.
    figs = {}

    def figure_marker(m):
        env = m.group(0)
        lab = re.search(r"\\label\{([^}]*)\}", env)
        cap = re.search(r"\\caption\{", env)
        if not lab:
            return ""
        figs[lab.group(1)] = env[cap.end():match_brace(env, cap.end() - 1)] if cap else ""
        return "\n\n@@VPFIG:%s@@\n\n" % lab.group(1)
    body = re.sub(r"\\begin\{figure\}.*?\\end\{figure\}", figure_marker, body, flags=re.S)
    body = re.sub(r"\\bibliographystyle\{[^}]*\}|\\bibliography\{[^}]*\}|\\tableofcontents|"
                  r"\\setcounter\{[^}]*\}\{[^}]*\}|\\maketitle", "", body)
    pre_nc = strip_comments(pre)
    macros = parse_macros(pre_nc)
    labels = parse_aux()
    bib = parse_bbl()

    # abstract
    abstract = ""
    m = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", body, re.S)
    if m:
        abstract = m.group(1)
        body = body[:m.start()] + body[m.end():]

    # ---- pass 1: locate sections, statements, proofs
    events = []  # (pos, kind, data)
    appendix_pos = body.find("\\appendix")
    for m in re.finditer(r"\\(section|subsection)\*?\{", body):
        j = match_brace(body, m.end() - 1)
        title = body[m.end():j]
        k = j + 1
        lab = None
        mm = re.match(r"\s*\\label\{([^}]*)\}", body[k:])
        if mm:
            lab = mm.group(1)
            k += mm.end()
        events.append((m.start(), m.group(1), {"title": title, "label": lab, "end": k}))
    for env in STMT_ENVS + ["proof"]:
        for m in re.finditer(r"\\begin\{" + env + r"\}", body):
            a, b = find_env_end(body, env, m.end())
            opt, k = read_opt(body, m.end())
            content = body[k:a]
            lab = None
            mm = re.match(r"\s*\\label\{([^}]*)\}", content)
            if mm:
                lab = mm.group(1)
                content = content[mm.end():]
            events.append((m.start(), env, {"opt": opt, "label": lab, "body": content, "end": b}))
    events.sort(key=lambda e: e[0])

    # numbering
    counters = {e: 0 for e in STMT_ENVS}
    sec_n = 0
    sub_n = 0
    in_app = False
    sections = []
    nodes = {}
    order = []
    cur_sec = None
    cur_sub = None
    last_stmt = None
    blocks = []  # (start, end, kind, id) top-level spans for prose extraction
    for pos, kind, d in events:
        if kind == "section":
            if appendix_pos != -1 and pos > appendix_pos and not in_app:
                in_app = True
                sec_n = 0
            sec_n += 1
            sub_n = 0
            num = chr(64 + sec_n) if in_app else str(sec_n)
            sid = d["label"] or "sec-%s" % num
            cur_sec = {"id": sid, "num": num, "title": d["title"], "level": 1, "start": d["end"],
                       "pos": pos, "parent": None}
            sections.append(cur_sec)
            cur_sub = None
            continue
        if kind == "subsection":
            sub_n += 1
            num = "%s.%d" % (cur_sec["num"], sub_n)
            sid = d["label"] or "sec-%s" % num
            cur_sub = {"id": sid, "num": num, "title": d["title"], "level": 2, "start": d["end"],
                       "pos": pos, "parent": cur_sec["id"]}
            sections.append(cur_sub)
            continue
        sec_here = (cur_sub or cur_sec)["id"]
        if kind == "proof":
            target = None
            if d["opt"]:
                r = re.search(r"\\ref\{([^}]*)\}", d["opt"])
                if r:
                    target = r.group(1)
            d["target_label"] = target
            d["fallback"] = last_stmt
            d["section"] = sec_here
            d["pos"] = pos
            pid = "proof-%d" % pos
            nodes[pid] = {"id": pid, "kind": "proof", **d}
            blocks.append((pos, d["end"], "proof", pid))
            continue
        counters[kind] += 1
        num = str(counters[kind])
        nid = d["label"] or "%s-%s" % (kind, num)
        if d["label"] and d["label"] in labels and labels[d["label"]]["num"] != num:
            warn("numbering mismatch %s: aux %s vs %s" % (nid, labels[d["label"]]["num"], num))
        nodes[nid] = {"id": nid, "kind": kind, "num": num, "opt": d["opt"], "label": d["label"],
                      "body": d["body"], "section": sec_here, "pos": pos, "end": d["end"]}
        order.append(nid)
        last_stmt = nid
        blocks.append((pos, d["end"], "stmt", nid))

    # hypotheses H1-H8 as nodes (the hypcond list of the hypotheses subsection)
    hyp_ids = []
    m = re.search(r"\\begin\{hypcond\}", body)
    if m:
        a, b = find_env_end(body, "hypcond", m.end())
        items = re.split(r"\\item\b", body[m.end():a])[1:]
        for idx, it in enumerate(items, 1):
            lab = re.match(r"\s*\\label\{([^}]*)\}", it)
            hid = lab.group(1) if lab else "H%d" % idx
            nodes[hid] = {"id": hid, "kind": "hypothesis", "num": str(idx), "opt": None,
                          "label": hid, "body": it[lab.end():] if lab else it,
                          "section": "subsec:hypotheses", "pos": m.start(), "end": b}
            hyp_ids.append(hid)
        hyp_span = (m.start(), b)
    else:
        hyp_span = (0, 0)

    # attach proofs
    proofs = [n for n in nodes.values() if n["kind"] == "proof"]

    # label owners
    label_pos = [(m.start(), m.group(1)) for m in re.finditer(r"\\label\{([^}]*)\}", body)]
    sec_spans = sorted(sections, key=lambda s: s["pos"])

    def section_at(p):
        cur = None
        for s in sec_spans:
            if s["pos"] <= p:
                cur = s
        return cur["id"] if cur else None

    stmt_spans = [(n["pos"], n["end"], n["id"]) for n in nodes.values()
                  if n["kind"] in STMT_ENVS]
    owner_of = {}
    for p, lab in label_pos:
        own = None
        if hyp_span[0] <= p < hyp_span[1]:
            for h in hyp_ids:
                if lab == h:
                    own = ("node", h)
        if not own:
            for a, b, nid in stmt_spans:
                if a <= p < b:
                    own = ("node", nid)
        if not own:
            for pr in proofs:
                if pr["pos"] <= p < pr["end"]:
                    own = ("proofof", pr["id"])
        if not own:
            own = ("section", section_at(p))
        owner_of[lab] = own
    for s in sections:
        owner_of[s["id"]] = ("section", s["id"])

    # resolve proof parents
    for pr in proofs:
        t = pr["target_label"]
        parent = None
        if t:
            k, v = owner_of.get(t, (None, None))
            parent = v if k == "node" else None
        if not parent:
            parent = pr["fallback"]
        pr["parent"] = parent
        nodes[parent].setdefault("proofs", []).append(pr["id"])
    for lab, (k, v) in list(owner_of.items()):
        if k == "proofof":
            owner_of[lab] = ("node", nodes[v]["parent"])

    conv = Converter(labels, bib, {k: (("node" if a == "node" else "section"), v)
                                   for k, (a, v) in owner_of.items()})
    fig_caps = {k: conv.text(v) for k, v in figs.items()}

    # ---- dependencies
    def refs_in(s):
        out = []
        for m in re.finditer(r"\\(?:eq)?ref\{([^}]*)\}", s):
            k, v = owner_of.get(m.group(1), (None, None))
            if k == "node" and v not in out:
                out.append(v)
        return out

    def cites_in(s):
        out = []
        for m in re.finditer(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", s):
            for k in m.group(1).split(","):
                k = k.strip()
                if k not in out:
                    out.append(k)
        return out

    edges = []
    graph_nodes = [nid for nid, n in nodes.items() if n["kind"] != "proof"]
    for nid in graph_nodes:
        n = nodes[nid]
        st = refs_in(n["body"] + (n["opt"] or ""))
        pf = []
        for pid in n.get("proofs", []):
            pf += [r for r in refs_in(nodes[pid]["body"]) if r not in pf]
        n["uses_stmt"] = [r for r in st if r != nid]
        n["uses_proof"] = [r for r in pf if r != nid and r not in st]
        n["cites"] = cites_in(n["body"] + (n["opt"] or "") +
                              "".join(nodes[p]["body"] for p in n.get("proofs", [])))
        for r in n["uses_stmt"]:
            edges.append({"source": r, "target": nid, "via": "statement"})
        for r in n["uses_proof"]:
            edges.append({"source": r, "target": nid, "via": "proof"})

    # ---- registry
    reg = parse_registry()
    lean = {}

    def row_info(cols):
        names, files = decls_of(cols[1])
        ov = next((v for k, v in STATUS_OVERRIDE.items() if cols[0].startswith(k)), None)
        return {"status": ov or status_of(cols[2]), "decls": names, "files": files,
                "cost": re.sub(r"`", "", cols[4]) if len(cols) > 4 else ""}

    for cols in reg:
        head = cols[0]
        m = re.match(r"`([^`]+)`(\s*\((i|ii)\))?$", head)
        if m and m.group(1) in nodes:
            info = row_info(cols)
            key = m.group(1)
            if key in lean:  # second part of the same statement
                lean[key]["parts"].append({"part": m.group(3), **info})
            else:
                lean[key] = {**info, "parts": ([{"part": m.group(3), **info}] if m.group(3) else [])}
    for key, rows in (("th:AHM11", AHM14_COMPONENTS), ("Zenvelopefacts-cite", ZENV_COMPONENTS)):
        comps = []
        for prefix, title in rows:
            for cols in reg:
                if cols[0].startswith(prefix):
                    info = row_info(cols)
                    comps.append({"title": title, "note": COMPONENT_NOTES.get(prefix, ""), **info})
                    break
            else:
                warn("registry component not found: " + prefix)
        lean.setdefault(key, {"status": None, "decls": [], "files": []})["components"] = comps
    for key, note in NOTES.items():
        if key in lean:
            lean[key]["note"] = note
        else:
            warn("note for unknown registry key " + key)
    for key, info in lean.items():
        info["status_text"] = STATUS_TEXT.get(info["status"], "")

    # ---- HTML conversion
    def title_html(n):
        opt = n.get("opt")
        if not opt:
            return ""
        return conv.text(opt)

    out_nodes = {}
    for nid in graph_nodes:
        n = nodes[nid]
        kind = n["kind"]
        name = ENV_NAME.get(kind, "Hypothesis")
        if kind == "hypothesis":
            display = conv.mathspan(r"(\mathrm{H}_{%s})" % n["num"])
            short = "(H%s)" % n["num"]
        else:
            display = "%s %s" % (name, n["num"])
            short = display
        proofs_html = []
        for pid in n.get("proofs", []):
            p = nodes[pid]
            proofs_html.append({"id": pid, "title": conv.text(p["opt"]) if p["opt"] else "Proof",
                                "steps": split_steps(conv, p["body"]),
                                "section": p["section"]})
        cited = bool(n.get("opt") and "\\cite" in n["opt"])
        out_nodes[nid] = {
            "id": nid, "kind": kind, "num": n["num"], "name": display, "short": short,
            "nick": NICK.get(nid, ""),
            "title": title_html(n), "title_plain": plain(n.get("opt") or "", bib),
            "body": paragraphs(conv.text(n["body"])), "section": n["section"],
            "proofs": proofs_html, "uses_stmt": n["uses_stmt"], "uses_proof": n["uses_proof"],
            "cites": n["cites"], "external": cited, "lean": lean.get(nid),
            "main": nid in MAIN_RESULTS, "search": plain(n["body"], bib)[:600],
        }

    # sections: prose with statement placeholders
    sec_sorted = sorted(sections, key=lambda s: s["pos"])
    out_sections = []
    top_blocks = sorted([b for b in blocks], key=lambda b: b[0])
    for idx, s in enumerate(sec_sorted):
        end = sec_sorted[idx + 1]["pos"] if idx + 1 < len(sec_sorted) else len(body)
        start = s["start"]
        pieces = []
        cur = start
        for a, b, kind, bid in top_blocks:
            if a < start or a >= end:
                continue
            if a < cur:
                continue
            seg = body[cur:a]
            if seg.strip():
                pieces.append({"t": "prose", "html": prose_with_hyp(conv, seg, hyp_ids, nodes)})
            if kind == "stmt":
                pieces.append({"t": "stmt", "id": bid})
            else:
                pieces.append({"t": "proof", "id": bid, "parent": nodes[bid]["parent"]})
            cur = b
        seg = body[cur:end]
        if seg.strip():
            pieces.append({"t": "prose", "html": prose_with_hyp(conv, seg, hyp_ids, nodes)})
        out_sections.append({"id": s["id"], "num": s["num"], "level": s["level"],
                             "parent": s["parent"], "title": conv.text(s["title"]),
                             "title_plain": plain(s["title"], bib), "pieces": pieces})

    out_bib = {k: {"alpha": v["alpha"], "html": conv.text(v["tex"])} for k, v in bib.items()}
    abstract_html = paragraphs(conv.text(abstract))
    title = re.search(r"\\title\{(.*?)\}\s*$", pre_nc, re.M).group(1)

    # ---- render math with KaTeX (jsc)
    os.makedirs(os.path.join(HERE, "tmp"), exist_ok=True)
    mpath = os.path.join(HERE, "tmp", "math.json")
    json.dump(conv.math, open(mpath, "w"))
    json.dump(macros, open(os.path.join(HERE, "tmp", "macros.json"), "w"))
    res = subprocess.run([js_engine(), os.path.join(HERE, "render.js")], cwd=HERE,
                         capture_output=True, text=True)
    if res.returncode != 0:
        print(res.stderr, file=sys.stderr)
        sys.exit(1)
    rendered = json.loads(res.stdout)
    errors = [(conv.math[i][0], r["err"]) for i, r in enumerate(rendered) if not r["ok"]]

    def figure_html(lab):
        num = labels.get(lab, {}).get("num", "")
        img = "figures/%s.png" % re.sub(r"[^A-Za-z0-9]+", "-", lab)
        return ('<figure class="fig" id="lbl-%s"><img src="%s" alt="Figure %s of the paper">'
                '<figcaption><span class="fig-n">Figure %s.</span> %s</figcaption></figure>'
                % (esc(lab), img, num, num, fig_caps.get(lab, "")))

    def fill(html):
        html = re.sub(r"(?:<p>\s*)?@@VPFIG:([^@]+)@@(?:\s*</p>)?", lambda m: figure_html(m.group(1)), html)
        return re.sub("\x00M(\\d+)\x00", lambda m: rendered[int(m.group(1))]["html"], html)

    def fill_obj(o):
        if isinstance(o, str):
            return fill(o)
        if isinstance(o, list):
            return [fill_obj(x) for x in o]
        if isinstance(o, dict):
            return {k: fill_obj(v) for k, v in o.items()}
        return o

    data = fill_obj({
        "title": title, "authors": ", ".join(re.findall(r"\\author(?:\[[^\]]*\])?\{([^{}]*)\}", pre_nc)),
        "abstract": abstract_html, "sections": out_sections, "nodes": out_nodes,
        "order": [o for o in order] + hyp_ids, "edges": edges, "bib": out_bib,
        "main": MAIN_RESULTS, "leanDir": LEAN_DIR, "statusText": STATUS_TEXT,
    })
    with open(os.path.join(SITE, "data.js"), "w", encoding="utf-8") as f:
        f.write("window.PAPER = ")
        json.dump(data, f, ensure_ascii=False)
        f.write(";\n")

    print("sections %d, nodes %d, edges %d, formulas %d, katex errors %d, warnings %d"
          % (len(out_sections), len(out_nodes), len(edges), len(conv.math), len(errors),
             len(warnings)))
    for t, e in errors[:40]:
        print("KATEX:", e[:160], "|", t[:160].replace("\n", " "))
    seen = set()
    for w in warnings:
        if w not in seen:
            print("WARN:", w)
            seen.add(w)


def prose_with_hyp(conv, seg, hyp_ids, nodes):
    return paragraphs(conv.text(seg))


def split_steps(conv, body):
    """Split a proof body at `\\emph{Step k...}` headers."""
    pat = re.compile(r"(?:\\(?:med|small|big)skip\s*)?(?:\\noindent\s*)?\\emph\{\s*Step")
    starts = [m.start() for m in pat.finditer(body)]
    if not starts:
        return [{"title": "", "html": paragraphs(conv.text(body))}]
    steps = []
    if body[:starts[0]].strip():
        steps.append({"title": "", "html": paragraphs(conv.text(body[:starts[0]]))})
    for k, a in enumerate(starts):
        b = starts[k + 1] if k + 1 < len(starts) else len(body)
        seg = body[a:b]
        m = re.search(r"\\emph\{", seg)
        j = match_brace(seg, m.end() - 1)
        head = seg[m.end():j]
        rest = seg[j + 1:]
        # a short descriptive sentence right after the header becomes the subtitle
        sub = ""
        mm = re.match(r"\s*([^\n]{3,120}?\.)\s*\n", rest)
        if mm and "\\[" not in mm.group(1) and "\\begin" not in mm.group(1):
            sub = mm.group(1)
            rest = rest[mm.end():]
        steps.append({"title": conv.text(head.strip()), "sub": conv.text(sub) if sub else "",
                      "html": paragraphs(conv.text(rest))})
    return steps


def plain(s, bib):
    s = re.sub(r"\\cite(?:\[([^\]]*)\])?\{([^}]*)\}",
               lambda m: "[" + ", ".join(bib.get(k.strip(), {"alpha": k})["alpha"]
                                         for k in m.group(2).split(",")) +
               (", " + m.group(1) if m.group(1) else "") + "]", s)
    s = re.sub(r"\\label\{[^}]*\}", "", s)
    s = re.sub(r"\\(?:eq)?ref\{([^}]*)\}", "", s)
    s = re.sub(r"\\[A-Za-z]+", " ", s)
    s = re.sub(r"[{}$\\]", "", s)
    return re.sub(r"\s+", " ", s).strip()


if __name__ == "__main__":
    main()
