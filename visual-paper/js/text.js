/* Visual Paper — the continuous text, its margin notes, and the contents rail. */
(function () {
  "use strict";
  const { P, N, esc, KIND, isRemark, isHyp, abbr, sections, secById, topOf, secLabel, uses, usedBy,
    nodesCited, hypRefs, status, STATUS_TEXT, mark, fileHref, mdCode, refLink, proofById, nested, withNested } = window.VP;

  /* a heading or title without its links, for places that are themselves links */
  const unlink = (html) => html.replace(/<a [^>]*>/g, "").replace(/<\/a>/g, "");
  /* number of words of the running text of an element, formulas excluded (filled after insertion) */
  function countWords(root) {
    root.querySelectorAll("[data-words]").forEach((el) => {
      const src = el.dataset.words === "next-prose" ? el.closest(".elide").nextElementSibling : el.closest(".step").querySelector(".step-body");
      let k = 0;
      const w = document.createTreeWalker(src, NodeFilter.SHOW_TEXT, { acceptNode: (t) => t.parentElement.closest(".katex") ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT });
      while (w.nextNode()) k += (w.currentNode.data.match(/[A-Za-z\u00C0-\u024F]{2,}/g) || []).length;
      el.textContent = k + (k === 1 ? " word" : " words");
    });
  }

  /* ------------------------------------------------------------ margin note of a result */
  function chips(ids, cls) {
    return ids.map((id) => refLink(id, null, cls)).join(" ");
  }
  function leanNote(n) {
    const st = status(n);
    if (!st) {
      return `<div class="mg-lean untracked">${mark(null)}<span>Not tracked in the Lean registry</span></div>`;
    }
    const L = n.lean;
    const decls = (L.decls || []).filter((d, i, a) => a.indexOf(d) === i);
    const files = (L.files || []).map((f) => `<a href="${fileHref(f)}">${esc(f)}</a>`).join(", ");
    const parts = (L.parts || []).map((p) => `<li>${mark(p.status)} Part (${esc(p.part)}): ${esc(STATUS_TEXT[p.status])}</li>`).join("");
    return `<details class="mg-lean st-${st}"><summary>${mark(st)}<span>${esc(STATUS_TEXT[st])}</span></summary>` +
      `<div class="mg-lean-body">${L.note ? `<p>${mdCode(L.note)}</p>` : ""}` +
      (parts ? `<ul class="parts">${parts}</ul>` : "") +
      (decls.length ? `<p class="decls">${decls.map((d) => `<code>${esc(d)}</code>`).join(" ")}</p>` : "") +
      (files ? `<p class="files">${files}</p>` : "") + `</div></details>`;
  }
  function marginNote(n) {
    const h = hypRefs[n.id] || { stmt: new Set(), proof: new Set() };
    const hs = [...h.stmt], hp = [...h.proof].filter((x) => !h.stmt.has(x));
    const u = (uses[n.id] || []).filter((e) => !isHyp(N[e.source]));
    const seen = new Set();
    const useIds = u.filter((e) => !seen.has(e.source) && seen.add(e.source)).sort((a, b) => (a.via === b.via ? 0 : a.via === "statement" ? -1 : 1));
    const by = [...new Set((usedBy[n.id] || []).map((e) => e.target))];
    let html = "";
    if (n.nick) html += `<p class="mg-nick">${esc(n.nick)}</p>`;
    if (!isRemark(n)) html += leanNote(n);
    if (hs.length || hp.length) {
      html += `<p class="mg-row"><span class="mg-k" title="Hypotheses named in the statement or in the proof; a result may assume them or verify them">Mentions</span>` +
        (hs.length ? `<span class="mg-v">${chips(hs.sort(hcmp))}${hs.length ? ' <span class="mg-via">statement</span>' : ""}</span>` : "") +
        (hp.length ? `<span class="mg-v">${chips(hp.sort(hcmp))} <span class="mg-via">proof</span></span>` : "") + `</p>`;
    }
    if (useIds.length) {
      html += `<p class="mg-row"><span class="mg-k">Uses</span><span class="mg-v">` +
        useIds.map((e) => refLink(e.source, null, e.via === "proof" ? "via-proof" : "")).join(" ") + `</span></p>`;
    }
    if (by.length) html += `<p class="mg-row"><span class="mg-k">Used by</span><span class="mg-v">${chips(by)}</span></p>`;
    const links = [];
    const pf = n.proofs[0];
    if (pf && pf.section !== n.section) links.push(`<a href="#/p/${encodeURIComponent(pf.id)}">Proof in ${esc(secLabel(secById[pf.section]))}</a>`);
    if (!isRemark(n)) links.push(`<a href="#/atlas/${encodeURIComponent(n.id)}">In the atlas</a>`);
    html += `<p class="mg-links">${links.join('<span aria-hidden="true"> · </span>')}</p>`;
    return html;
  }
  const hcmp = (a, b) => N[a].num - N[b].num;

  /* ------------------------------------------------------------ statements */
  function runIn(n, body) {
    const lab = isHyp(n) ? n.short : KIND[n.kind].one + " " + n.num;
    const title = n.title ? ` <span class="st-title">(${n.title})</span>` : "";
    const head = `<a class="st-lab" href="#/r/${encodeURIComponent(n.id)}">${esc(lab)}</a>${title}${isHyp(n) ? "" : "."} `;
    if (/^<p>/.test(body)) return "<p>" + head + body.slice(3);
    return `<p class="st-head">${head}</p>` + body;
  }
  function stmtBlock(n, extraCls) {
    const cls = ["blk", "stmt", "k-" + n.kind, n.main ? "main" : "", n.external ? "ext" : "", extraCls || ""].join(" ");
    return `<div class="${cls}" id="r-${esc(n.id)}" data-node="${esc(n.id)}">` +
      `<div class="tx">${runIn(n, n.body)}</div><aside class="mg">${marginNote(n)}</aside></div>`;
  }
  /* the hypotheses as statements, shown at the first two depths in place of the prose list */
  function hypBlocks() {
    return `<div class="blk syn-h"><div class="tx"><p class="syn-note">The hypotheses (H<sub>1</sub>)–(H<sub>8</sub>), as listed in the text below.</p></div></div>` +
      window.VP.hyps.map((h) => `<div class="blk stmt k-hypothesis syn" data-node="${esc(h.id)}" id="h-${esc(h.id)}"><div class="tx"><p><span class="st-lab">${esc(h.short)}</span> <span class="st-nick-in">${esc(h.nick)}</span></p>${h.body}</div>` +
        `<aside class="mg"><p class="mg-row"><span class="mg-k">Cited by</span><span class="mg-v">${hypUsers(h.id)}</span></p></aside></div>`).join("");
  }
  function hypUsers(hid) {
    const ids = window.VP.results.filter((n) => hypRefs[n.id] && (hypRefs[n.id].stmt.has(hid) || hypRefs[n.id].proof.has(hid))).map((n) => n.id);
    return ids.map((id) => refLink(id)).join(" ") || '<span class="mg-via">no numbered result</span>';
  }

  /* ------------------------------------------------------------ proofs */
  function proofBlock(pid) {
    const { proof: p, owner } = proofById[pid];
    const n = N[owner];
    const titled = p.steps.filter((s) => s.title).length;
    const all = new Set();
    p.steps.forEach((s) => nodesCited(s.html, owner).forEach((id) => all.add(id)));
    const meta = (titled ? titled + (titled === 1 ? " step" : " steps") + " · " : "") + all.size + (all.size === 1 ? " result cited" : " results cited");
    let steps = "";
    p.steps.forEach((s, i) => {
      const cited = nodesCited(s.html, owner);
      const label = s.title
        ? `<span class="sn">${s.title}</span>${s.sub ? ` <span class="ss">${s.sub}</span>` : ""}`
        : (p.steps.length > 1 ? `<span class="sn sn-pre">${i === 0 ? "Preliminaries" : "Continuation"}</span>` : `<span class="sn sn-pre">The argument</span>`);
      steps += `<div class="step" data-i="${i}">` +
        `<div class="blk step-row"><div class="tx"><button type="button" class="step-tog" aria-expanded="false">${label}<span class="step-w" data-words="step"></span></button></div>` +
        `<aside class="mg">${cited.length ? `<p class="mg-row"><span class="mg-k">Cites</span><span class="mg-v">${chips(cited)}</span></p>` : ""}</aside></div>` +
        `<div class="step-body tx">${withNested(s.html, (m) => stmtBlock(m, "nested"))}</div></div>`;
    });
    return `<div class="proof" id="pf-${esc(pid)}" data-owner="${esc(owner)}" data-proof="${esc(pid)}">` +
      `<div class="blk pf-row"><div class="tx"><p class="pf-head"><span class="pf-t">${p.title.trim()}.</span> <span class="pf-meta">${meta}</span>` +
      ` <button type="button" class="pf-all">open all steps</button></p></div>` +
      `<aside class="mg">${n.section !== proofById[pid].section ? `<p class="mg-links"><a href="#/r/${encodeURIComponent(owner)}">Statement in ${esc(secLabel(secById[n.section]))}</a></p>` : ""}</aside></div>` +
      `<div class="steps">${steps}</div><p class="qed tx" aria-hidden="true">∎</p></div>`;
  }

  /* ------------------------------------------------------------ the document */
  function titlePage() {
    const mains = P.main.map((id) => {
      const n = N[id];
      return `<li>${mark(status(n))}${refLink(id, esc(KIND[n.kind].one + " " + n.num))}<span class="tp-nick">${esc(n.nick)}</span></li>`;
    }).join("");
    const hl = window.VP.hyps.map((h) => `<li>${refLink(h.id)}<span class="tp-nick">${esc(h.nick)}</span></li>`).join("");
    const toc = sections.filter((s) => s.level === 1).map((s) => `<li><a href="#/s/${encodeURIComponent(s.id)}"><span class="tp-n">${esc(s.num)}</span>${unlink(s.title)}</a></li>`).join("");
    return `<header class="tp" id="top">
      <p class="tp-kind">Research article · reading edition</p>
      <h1 class="tp-title">${esc(P.title)}</h1>
      <p class="tp-auth">${esc(P.authors).replace(/, /g, '<span class="sep">, </span>')}</p>
      <p class="tp-src">PDF on HAL: <a href="https://hal.science/hal-05851819">hal-05851819</a></p>
      <div class="tp-abs"><h2 class="sc">Abstract</h2>${P.abstract}</div>
      <div class="tp-glance">
        <section><h2 class="sc">Main results</h2><ul class="tp-list">${mains}</ul></section>
        <section><h2 class="sc">Hypotheses</h2><ul class="tp-list hyp-list">${hl}</ul></section>
        <section><h2 class="sc">Sections</h2><ol class="tp-list tp-toc">${toc}</ol></section>
      </div>
      <p class="tp-how">A reference in the text opens its target in the margin. The reading depth, at the top, shows the statements only, adds the steps of each proof with the results each step cites, or shows the full text. The marks ${mark("proved", false)} and ${mark("partial", false)} give the Lean status: proved, or proved in a restricted form.</p>
    </header>`;
  }

  function buildDoc() {
    let html = titlePage();
    let open = false;
    sections.forEach((s) => {
      if (s.level === 1) {
        if (open) html += "</section>";
        html += `<section class="sec" id="s-${esc(s.id)}" data-sec="${esc(s.id)}">`;
        open = true;
        html += `<h2 class="h1" data-sec="${esc(s.id)}"><span class="hn">${esc(s.num)}</span>${s.title}</h2>`;
      } else {
        html += `<h3 class="h2" id="s-${esc(s.id)}" data-sec="${esc(s.id)}"><span class="hn">${esc(s.num)}</span>${s.title}</h3>`;
      }
      s.pieces.forEach((p, k) => {
        if (p.t === "prose") {
          if (s.id === "subsec:hypotheses" && k === 0) html += hypBlocks();
          html += `<button type="button" class="elide" aria-expanded="false" title="Show the text omitted here">Text <span data-words="next-prose"></span></button>` +
            `<div class="blk prose"><div class="tx">${p.html}</div></div>`;
        } else if (p.t === "stmt") html += stmtBlock(N[p.id]);
        else if (p.t === "proof" && proofById[p.id]) html += proofBlock(p.id);
      });
    });
    if (open) html += "</section>";
    html += `<footer class="colophon"><p>Text of the LaTeX source of the paper, converted by <code>build/build.py</code>; formulas rendered with KaTeX. Lean status from <code>lean/REGISTRY.md</code>. The editorial names of the results (in the margin) are not part of the paper.</p></footer>`;
    return html;
  }

  /* ------------------------------------------------------------ contents rail */
  function buildRail() {
    let html = `<p class="rail-h sc">Contents</p><ol class="toc">`;
    sections.forEach((s) => {
      const ids = [];
      s.pieces.forEach((p) => {
        if (p.t === "stmt") ids.push(p.id);
        if (p.t === "proof" && proofById[p.id]) Object.keys(nested).forEach((k) => { if (nested[k].proof === p.id) ids.push(k); });
      });
      const res = ids.filter((id) => !isRemark(N[id])).map((id) => {
        const n = N[id];
        return `<a class="tr" href="#/r/${encodeURIComponent(n.id)}" data-node="${esc(n.id)}" title="${esc(KIND[n.kind].one + " " + n.num + (n.nick ? " — " + n.nick : ""))}">${mark(status(n), false)}${esc(abbr(n))}</a>`;
      }).join("");
      html += `<li class="t${s.level}" data-sec="${esc(s.id)}"><a class="ts" href="#/s/${encodeURIComponent(s.id)}"><span class="hn">${esc(s.num)}</span><span class="tt">${unlink(s.title)}</span></a>` +
        (res ? `<span class="trs">${res}</span>` : "") + `</li>`;
    });
    html += `</ol>`;
    return html;
  }

  window.VP.text = { buildDoc, buildRail, stmtBlock, marginNote, countWords, unlink };
})();
