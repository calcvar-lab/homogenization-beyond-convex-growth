/* Checks of the reading edition, run inside the page (paste in the browser console, or inject).
   Prints one line per check and returns the list of failures. */
(function () {
  "use strict";
  const VP = window.VP, N = VP.N, P = VP.P;
  const out = [], fail = [];
  const check = (name, ok, detail) => { out.push((ok ? "ok    " : "FAIL  ") + name + (detail ? " — " + detail : "")); if (!ok) fail.push(name); };
  const doc = document.getElementById("doc");
  const text = (html) => { const d = document.createElement("div"); d.innerHTML = html; d.querySelectorAll(".katex").forEach((k) => k.replaceWith("§")); return d.textContent.replace(/\s+/g, " ").trim(); };

  /* 1. every cross-reference of the text has a target */
  const refs = Array.from(doc.querySelectorAll("a.ref"));
  const bad = refs.filter((a) => !VP.peek.resolve(a.dataset.goto, a.dataset.kind, a.dataset.label)).map((a) => a.dataset.label);
  check("cross-references resolved", bad.length === 0, refs.length + " references" + (bad.length ? ", unresolved: " + [...new Set(bad)].join(", ") : ""));

  /* 2. every citation has an entry */
  const cites = Array.from(doc.querySelectorAll("a.cite"));
  const badC = cites.filter((a) => !P.bib[a.dataset.bib]);
  check("citations resolved", badC.length === 0, cites.length + " citations");

  /* 3. every result of the paper is in the text, once */
  const missing = Object.keys(N).filter((id) => !VP.isHyp(N[id]) && !document.getElementById("r-" + id));
  check("every result is in the text", missing.length === 0, missing.join(", "));
  const ids = Array.from(document.querySelectorAll("[id]")).map((e) => e.id);
  const dup = ids.filter((x, i) => ids.indexOf(x) !== i);
  check("no duplicate element id", dup.length === 0, [...new Set(dup)].slice(0, 8).join(", "));

  /* 4. the text of each statement is the text of the paper */
  const diff = Object.keys(N).filter((id) => {
    if (VP.isHyp(N[id])) return false;
    const el = document.getElementById("r-" + id);
    if (!el) return true;
    const t = text(el.querySelector(".tx").innerHTML);
    return !t.includes(text(N[id].body).slice(0, 400).replace(/^\S+\s*/, ""));
  });
  check("statements match the source", diff.length === 0, diff.join(", "));

  /* 5. every prose piece and every proof step is in the text */
  const flatOf = (t) => t.replace(/[^A-Za-z ]/g, " ").replace(/\s+/g, " ").split(" ").filter((w) => w.length > 3).join(" ");
  const noMath = (el) => { const c = el.cloneNode(true); c.querySelectorAll(".katex").forEach((k) => k.replaceWith(" ")); return c.textContent; };
  const flat = flatOf(noMath(doc));
  let pieces = 0, lost = 0;
  P.sections.forEach((s) => s.pieces.forEach((p) => {
    if (p.t === "prose") { pieces++; const probe = flatOf(text(p.html).replace(/§/g, " ")).split(" ").slice(0, 8).join(" "); if (probe && !flat.includes(probe)) { lost++; out.push("   missing prose: " + probe); } }
  }));
  check("prose pieces present", lost === 0, pieces + " pieces");
  let steps = 0, lostS = 0;
  Object.keys(VP.proofById).forEach((pid) => VP.proofById[pid].proof.steps.forEach((st, i) => {
    steps++;
    const el = document.querySelector(`#pf-${CSS.escape(pid)} .step[data-i="${i}"] .step-body`);
    if (!el) { lostS++; return; }
    const a = flatOf(text(st.html).replace(/§/g, " ")).split(" "), b = flatOf(noMath(el));
    const probe = a.slice(-8).join(" ");
    if (probe && !b.includes(probe)) { lostS++; out.push("   missing step end: " + pid + "/" + i + " " + probe); }
  }));
  check("proof steps present", lostS === 0, steps + " steps");

  /* 6. the routes of the first Visual Paper reach their target */
  const oldRoutes = Object.keys(N).map((id) => ["node", id]).concat(P.sections.map((s) => ["sec", s.id]));
  const badR = oldRoutes.filter(([k, id]) => {
    if (k === "node") return !(VP.isHyp(N[id]) ? document.getElementById("lbl-" + id) : document.getElementById("r-" + id));
    return !document.getElementById("s-" + id);
  });
  check("routes #/node and #/sec of the first version", badR.length === 0, oldRoutes.length + " routes" + (badR.length ? ": " + badR.map((r) => r[1]).join(", ") : ""));

  /* 7. formulas */
  check("no KaTeX error", document.querySelectorAll(".katex-error").length === 0, document.querySelectorAll(".katex").length + " formulas in the text");

  /* 8. hypothesis ranges: Theorem 1 refers to all eight in its statement */
  check("range (H1)–(H8) counted", VP.hypRefs["main-Ggrowth"].stmt.size === 8);

  /* 9. Lean marks agree with the registry */
  const badL = Array.from(doc.querySelectorAll(".stmt[data-node]:not(.syn)")).filter((b) => {
    const st = VP.status(N[b.dataset.node]);
    const mk = b.querySelector(".mg .mk");
    return !VP.isRemark(N[b.dataset.node]) && (!mk || !mk.classList.contains("mk-" + (st || "untracked")));
  });
  check("Lean marks", badL.length === 0, badL.map((b) => b.dataset.node).join(", "));

  /* 10. links to Lean files point to files of the release (relative paths only) */
  const files = new Set();
  Object.values(N).forEach((n) => (n.lean && n.lean.files || []).forEach((f) => files.add(f)));
  check("Lean file links are relative", [...files].every((f) => !/^\/|\.\./.test(f)), files.size + " files");

  console.log(out.join("\n"));
  window.__check = { out, fail };
  return fail;
})();
