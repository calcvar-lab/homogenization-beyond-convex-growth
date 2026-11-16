/* Visual Paper — data indexes shared by the views. Data: window.PAPER (build/build.py). */
(function () {
  "use strict";
  const P = window.PAPER;
  const N = P.nodes;

  const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
  const store = {
    get(k, d) { try { const v = localStorage.getItem("vp2:" + k); return v === null ? d : JSON.parse(v); } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem("vp2:" + k, JSON.stringify(v)); } catch (e) { /* storage unavailable */ } },
  };

  const KIND = {
    theorem: { one: "Theorem", ab: "Thm" }, proposition: { one: "Proposition", ab: "Prop" },
    lemma: { one: "Lemma", ab: "Lem" }, corollary: { one: "Corollary", ab: "Cor" },
    sublemma: { one: "Sublemma", ab: "Sub" }, definition: { one: "Definition", ab: "Def" },
    remark: { one: "Remark", ab: "Rem" }, remarks: { one: "Remarks", ab: "Rems" },
    example: { one: "Example", ab: "Ex" }, hypothesis: { one: "Hypothesis", ab: "" },
  };
  const isRemark = (n) => n.kind === "remark" || n.kind === "remarks";
  const isHyp = (n) => n.kind === "hypothesis";
  /* "Lem 3", "(H5)" */
  const abbr = (n) => isHyp(n) ? n.short : KIND[n.kind].ab + " " + n.num;

  /* ------------------------------------------------------------ sections */
  const sections = P.sections;
  const secById = Object.fromEntries(sections.map((s) => [s.id, s]));
  const topOf = (id) => { let s = secById[id]; while (s && s.parent) s = secById[s.parent]; return s; };
  const secLabel = (s) => (s.level === 1 ? (/^[A-Z]$/.test(s.num) ? "Appendix " : "Section ") : "Section ") + s.num;

  /* order of the statements in the text, and the proofs in the text */
  const docOrder = [];
  const proofById = {};
  sections.forEach((s) => s.pieces.forEach((p) => {
    if (p.t === "stmt") docOrder.push(p.id);
    if (p.t === "proof") {
      const owner = N[p.parent];
      const pr = owner && owner.proofs.find((x) => x.id === p.id);
      if (pr) proofById[p.id] = { proof: pr, owner: p.parent, section: s.id };
    }
  }));
  /* statements given inside a proof (Lemma 13 is stated in the proof of Proposition 8): the
     converter writes them as plain paragraphs after their label anchor; they are put back in the
     order of the text, after the owner of that proof */
  const inPieces = new Set(docOrder);
  const nested = {};
  Object.values(N).forEach((n) => {
    if (isHyp(n) || inPieces.has(n.id)) return;
    for (const pid in proofById) {
      if (proofById[pid].proof.steps.some((st) => st.html.includes(`id="lbl-${n.id}"`))) {
        nested[n.id] = { proof: pid, section: proofById[pid].section, owner: proofById[pid].owner };
        docOrder.splice(docOrder.indexOf(proofById[pid].owner) + 1, 0, n.id);
        break;
      }
    }
  });
  /* the HTML of a proof step with its nested statements rendered by `block` */
  function withNested(html, block) {
    Object.keys(nested).forEach((id) => {
      const a = `<p><span class="anchor" id="lbl-${id}"></span>`;
      const i = html.indexOf(a);
      if (i < 0) return;
      const rest = html.slice(i + a.length).replace(/^\s+/, "");
      const core = N[id].body.replace(/^<p>/, "");
      if (rest.startsWith(core)) html = html.slice(0, i) + block(N[id]) + rest.slice(core.length);
    });
    return html;
  }
  const hyps = Object.values(N).filter(isHyp).sort((a, b) => a.num - b.num);
  const results = docOrder.map((id) => N[id]).filter((n) => !isHyp(n));

  /* ------------------------------------------------------------ edges */
  const uses = {}, usedBy = {};
  P.edges.forEach((e) => {
    (uses[e.target] = uses[e.target] || []).push(e);
    (usedBy[e.source] = usedBy[e.source] || []).push(e);
  });

  /* ------------------------------------------------------------ references in an HTML fragment
     Returns the cross-references in order of appearance: { goto, kind, label }. A range of
     hypotheses written "(H_a)–(H_b)" also yields the hypotheses strictly between a and b, marked
     { range: true }. */
  const REF = /<a class="ref" href="#" data-goto="([^"]+)" data-kind="([^"]+)" data-label="([^"]+)">/g;
  function refsIn(html) {
    const out = [];
    let m;
    REF.lastIndex = 0;
    while ((m = REF.exec(html))) {
      const r = { goto: m[1], kind: m[2], label: m[3], at: m.index };
      const prev = out[out.length - 1];
      if (prev && /^H\d$/.test(prev.goto) && /^H\d$/.test(r.goto)) {
        const between = html.slice(html.indexOf("</a>", prev.at) + 4, r.at);
        if (between === "–" || between === "&ndash;") {
          const a = +prev.goto.slice(1), b = +r.goto.slice(1);
          for (let k = a + 1; k < b; k++) out.push({ goto: "H" + k, kind: "node", label: "H" + k, range: true });
        }
      }
      out.push(r);
    }
    return out;
  }
  /* distinct nodes cited by a fragment, in order of first appearance, without `self` */
  function nodesCited(html, self) {
    const seen = new Set(), out = [];
    refsIn(html).forEach((r) => {
      if (r.kind !== "node" || r.goto === self || !N[r.goto] || seen.has(r.goto)) return;
      seen.add(r.goto); out.push(r.goto);
    });
    return out;
  }

  /* hypotheses referred to by each result, in its statement and in its proofs */
  const hypRefs = {};
  Object.values(N).forEach((n) => {
    if (isHyp(n)) return;
    const st = nodesCited(n.body, n.id).filter((id) => isHyp(N[id]));
    const pf = new Set();
    n.proofs.forEach((p) => p.steps.forEach((s) => nodesCited(s.html, n.id).forEach((id) => { if (isHyp(N[id])) pf.add(id); })));
    hypRefs[n.id] = { stmt: new Set(st), proof: pf };
  });

  /* ------------------------------------------------------------ Lean */
  const STATUS = ["proved", "conditional", "partial", "started", "cited", "none"];
  const status = (n) => (n.lean && n.lean.status) || null;
  const STATUS_TEXT = P.statusText;
  /* a status mark: full disc proved, half disc restricted form, ring not formalized */
  function mark(st, title) {
    const t = title === false ? "" : `<title>${esc(st ? STATUS_TEXT[st] : "Not tracked in the Lean registry")}</title>`;
    const r = 4.2, c = 5.5;
    let g;
    if (st === "proved") g = `<circle cx="${c}" cy="${c}" r="${r}" fill="currentColor"/>`;
    else if (st === "partial" || st === "conditional") g = `<circle cx="${c}" cy="${c}" r="${r}" fill="none" stroke="currentColor" stroke-width="1.2"/><path d="M${c} ${c - r}a${r} ${r} 0 0 1 0 ${2 * r}z" fill="currentColor"/>`;
    else if (st === "started") g = `<circle cx="${c}" cy="${c}" r="${r}" fill="none" stroke="currentColor" stroke-width="1.2"/><path d="M${c} ${c}V${c - r}a${r} ${r} 0 0 1 ${r} ${r}z" fill="currentColor"/>`;
    else if (st === "cited") g = `<path d="M${c} ${c - r - .6}L${c + r + .6} ${c}L${c} ${c + r + .6}L${c - r - .6} ${c}z" fill="none" stroke="currentColor" stroke-width="1.2"/>`;
    else if (st === "none") g = `<circle cx="${c}" cy="${c}" r="${r}" fill="none" stroke="currentColor" stroke-width="1.2"/>`;
    else g = `<circle cx="${c}" cy="${c}" r="1.6" fill="currentColor"/>`;
    return `<svg class="mk mk-${st || "untracked"}" viewBox="0 0 11 11" width="11" height="11" role="img" aria-label="${esc(st ? STATUS_TEXT[st] : "Not tracked in the Lean registry")}">${t}${g}</svg>`;
  }
  const fileHref = (f) => encodeURI(P.leanDir + "/" + f);
  const mdCode = (s) => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>");

  /* ------------------------------------------------------------ links */
  const refLink = (id, text, cls) => {
    const n = N[id];
    return `<a class="ref${cls ? " " + cls : ""}${n && isHyp(n) ? " hyp" : ""}" href="#/r/${encodeURIComponent(id)}" data-goto="${esc(id)}" data-kind="node" data-label="${esc(id)}">${text || (n ? abbr(n) : esc(id))}</a>`;
  };

  window.VP = {
    P, N, esc, store, KIND, isRemark, isHyp, abbr, sections, secById, topOf, secLabel,
    docOrder, proofById, nested, withNested, hyps, results, uses, usedBy, refsIn, nodesCited, hypRefs,
    STATUS, STATUS_TEXT, status, mark, fileHref, mdCode, refLink,
  };
})();
