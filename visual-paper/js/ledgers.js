/* Visual Paper — two ledgers: where the hypotheses (H1)–(H8) appear, and the Lean status. */
(function () {
  "use strict";
  const { N, esc, KIND, isRemark, isHyp, abbr, sections, secById, hyps, hypRefs, status, STATUS,
    STATUS_TEXT, mark, fileHref, mdCode, refLink, store } = window.VP;
  const $ = (s, r) => (r || document).querySelector(s);
  const one = (n) => KIND[n.kind].one + " " + n.num;

  /* results of each section, in the order of the text */
  function bySection(filter) {
    const out = [];
    sections.forEach((s) => {
      const ids = s.pieces.filter((p) => p.t === "stmt" && filter(N[p.id])).map((p) => p.id);
      if (ids.length) out.push({ s, ids });
    });
    return out;
  }
  const secHead = (s, span) => `<tr class="grp"><th colspan="${span}" scope="colgroup"><a href="#/s/${encodeURIComponent(s.id)}"><span class="hn">${esc(s.num)}</span>${window.VP.text.unlink(s.title)}</a></th></tr>`;

  /* ------------------------------------------------------------ hypotheses */
  let onlyUsing = store.get("hyp.only", true);
  function buildHyp() {
    const v = $("#v-hypotheses");
    const cols = hyps.map((h) => h.id);
    const groups = bySection((n) => !isHyp(n) && (!onlyUsing || hypRefs[n.id].stmt.size + hypRefs[n.id].proof.size > 0));
    const count = Object.fromEntries(cols.map((h) => [h, { s: 0, p: 0 }]));
    let rows = "";
    groups.forEach(({ s, ids }) => {
      rows += secHead(s, cols.length + 1);
      ids.forEach((id) => {
        const n = N[id], h = hypRefs[id];
        rows += `<tr><th scope="row">${refLink(id, esc(abbr(n)))}<span class="hl-nick">${esc(n.nick || "")}</span></th>` + cols.map((c, k) => {
          const a = h.stmt.has(c), b = h.proof.has(c);
          if (a) count[c].s++; else if (b) count[c].p++;
          const t = a ? `${one(n)} refers to ${N[c].short} in its statement${b ? " and in its proof" : ""}` : b ? `${one(n)} refers to ${N[c].short} in its proof` : "";
          return `<td data-c="${k}" class="${a ? "hs" : b ? "hp" : ""}"${t ? ` title="${esc(t)}"` : ""}>${a ? '<span class="g" aria-label="statement">■</span>' : b ? '<span class="g" aria-label="proof">□</span>' : ""}</td>`;
        }).join("") + `</tr>`;
      });
    });
    const head = `<tr><th scope="col" class="hl-c0">Result</th>${hyps.map((h, k) => `<th scope="col" data-c="${k}">${refLink(h.id, esc(h.short))}</th>`).join("")}</tr>`;
    const foot = `<tr><th scope="row">Results referring to it</th>${cols.map((c, k) => `<td data-c="${k}">${count[c].s + count[c].p}</td>`).join("")}</tr>`;
    v.innerHTML = `<div class="ledger">
      <header class="lg-h"><p class="sc lg-k">Ledger</p><h1>Where the hypotheses appear</h1>
      <p>Each row is a numbered result, each column a hypothesis. A filled square means that the statement of the result refers to the hypothesis; an open square, that only its proof does. A range written (H<sub>1</sub>)–(H<sub>8</sub>) counts for every hypothesis in it.</p>
      <p class="caveat">The table is read from the explicit references of the text. For the examples of Sections 5 and 6, a reference to a hypothesis usually means that the result <em>verifies</em> it for a given integrand, not that it assumes it. A hypothesis used without being named is not detected.</p></header>
      <dl class="hl-legend">${hyps.map((h) => `<div><dt>${refLink(h.id, esc(h.short))}</dt><dd>${esc(h.nick)}</dd></div>`).join("")}</dl>
      <p class="hl-opt"><label class="ck"><input type="checkbox" id="hl-only"${onlyUsing ? " checked" : ""}> Only the results that refer to a hypothesis</label></p>
      <div class="tscroll"><table class="hl"><thead>${head}</thead><tbody>${rows}</tbody><tfoot>${foot}</tfoot></table></div></div>`;
    $("#hl-only").onchange = (ev) => { onlyUsing = ev.target.checked; store.set("hyp.only", onlyUsing); buildHyp(); };
    const tbl = v.querySelector(".hl");
    tbl.addEventListener("mouseover", (ev) => {
      const c = ev.target.closest("[data-c]");
      tbl.querySelectorAll(".col").forEach((x) => x.classList.remove("col"));
      if (c) tbl.querySelectorAll(`[data-c="${c.dataset.c}"]`).forEach((x) => x.classList.add("col"));
    });
    tbl.addEventListener("mouseleave", () => tbl.querySelectorAll(".col").forEach((x) => x.classList.remove("col")));
  }

  /* ------------------------------------------------------------ Lean */
  function buildLean() {
    const v = $("#v-lean");
    const tracked = Object.values(N).filter((n) => status(n));
    const counts = {};
    tracked.forEach((n) => { counts[status(n)] = (counts[status(n)] || 0) + 1; });
    const summary = STATUS.filter((s) => counts[s]).map((s) => `<li>${mark(s)}<span class="ln-n">${counts[s]}</span> ${esc(STATUS_TEXT[s].replace(/^Proved in Lean/, "proved").replace(/^Not formalized/, "not formalized"))}</li>`).join("");
    const untracked = Object.values(N).filter((n) => !status(n) && !isRemark(n) && !isHyp(n));
    let rows = "";
    bySection((n) => !!status(n)).forEach(({ s, ids }) => {
      rows += secHead(s, 3);
      ids.forEach((id) => {
        const n = N[id], L = n.lean, st = status(n);
        const decls = (L.decls || []).filter((d, i, a) => a.indexOf(d) === i);
        rows += `<tr id="lean-${esc(id)}"><th scope="row">${refLink(id, esc(one(n)))}<span class="hl-nick">${esc(n.nick || "")}</span>${n.external ? '<span class="ext-tag">other paper</span>' : ""}</th>` +
          `<td class="ln-st">${mark(st)} ${esc(STATUS_TEXT[st])}</td>` +
          `<td><details><summary>${decls.slice(0, 2).map((d) => `<code>${esc(d)}</code>`).join(" ")}${decls.length > 2 ? ` <span class="more">and ${decls.length - 2} more</span>` : ""}</summary>` +
          (L.note ? `<p>${mdCode(L.note)}</p>` : "") +
          (decls.length > 2 ? `<p class="decls">${decls.map((d) => `<code>${esc(d)}</code>`).join(" ")}</p>` : "") +
          ((L.files || []).length ? `<p class="files">${L.files.map((f) => `<a href="${fileHref(f)}">${esc(f)}</a>`).join(", ")}</p>` : "") +
          `</details></td></tr>`;
      });
    });
    v.innerHTML = `<div class="ledger">
      <header class="lg-h"><p class="sc lg-k">Ledger</p><h1>The Lean 4 formalization</h1>
      <p>${refLink("main-Ggrowth", "Theorem 1")} is proved in Lean with no hypothesis taken from other papers (<code>main_Ggrowth_final_unconditional</code>, <code>AHM14.lean</code>). The results of other papers that it uses, in particular ${refLink("th:AHM11", "Theorem 2")} and ${refLink("approx-affine-etoile-cite", "Proposition 4")}, are proved in Lean as well. Only the axioms <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code> are used.</p>
      <p>“Proved” means that a Lean proof exists for the formalized statement; “restricted form” that the Lean statement is weaker than the paper’s, as the note of the row explains. The status comes from <code>lean/REGISTRY.md</code>.</p></header>
      <ul class="ln-sum">${summary}${untracked.length ? `<li>${mark(null)}<span class="ln-n">${untracked.length}</span> not in the registry</li>` : ""}</ul>
      <div class="tscroll"><table class="ln"><thead><tr><th scope="col">Result</th><th scope="col">Status</th><th scope="col">Declarations, note and files</th></tr></thead><tbody>${rows}</tbody></table></div>
      ${untracked.length ? `<p class="ln-un">Not in the registry: ${untracked.map((n) => refLink(n.id, esc(one(n)))).join(", ")}.</p>` : ""}
      <p class="ln-un">Remarks and hypotheses are not tracked individually; the hypotheses (H<sub>1</sub>)–(H<sub>8</sub>) are explicit assumptions of the Lean main theorem.</p></div>`;
  }

  window.VP.ledgers = { buildHyp, buildLean };
})();
