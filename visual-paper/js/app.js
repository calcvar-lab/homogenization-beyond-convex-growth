/* Visual Paper — routes, reading depth, reading position, contents, search and keys. */
(function () {
  "use strict";
  const VP = window.VP;
  const { N, esc, KIND, isHyp, isRemark, abbr, sections, secById, store, status, mark } = VP;
  const $ = (s, r) => (r || document).querySelector(s);
  const $$ = (s, r) => Array.from((r || document).querySelectorAll(s));
  const root = document.documentElement;
  const reduce = window.matchMedia("(prefers-reduced-motion: reduce)");

  /* ------------------------------------------------------------ build the text */
  const doc = $("#doc");
  doc.innerHTML = VP.text.buildDoc();
  $("#rail").innerHTML = VP.text.buildRail();
  VP.text.countWords(doc);

  /* displays wider than the column fade at the right edge until scrolled to the end */
  function markWide() {
    $$(".dmath", doc).forEach((d) => {
      if (!d.getClientRects().length) return;
      const w = d.scrollWidth > d.clientWidth + 2;
      d.classList.toggle("wide", w);
      if (w && !d.dataset.sw) { d.dataset.sw = 1; d.addEventListener("scroll", () => d.classList.toggle("end", d.scrollLeft + d.clientWidth >= d.scrollWidth - 2), { passive: true }); }
    });
  }
  let wideQueued = 0;
  const queueWide = () => { clearTimeout(wideQueued); wideQueued = setTimeout(markWide, 120); };
  window.addEventListener("resize", queueWide);
  new MutationObserver(queueWide).observe(doc, { attributes: true, subtree: true, attributeFilter: ["class"] });
  new MutationObserver(queueWide).observe(root, { attributes: true, attributeFilter: ["data-depth", "style"] });

  /* ------------------------------------------------------------ reading depth */
  const DEPTHS = ["statements", "outline", "full"];
  let depth = root.getAttribute("data-depth") || "outline";
  function markDepth() {
    $$("#depth button").forEach((b) => b.setAttribute("aria-pressed", String(b.dataset.depth === depth)));
  }
  /* keep the block at the top of the reading area in place when the depth changes */
  function readingAnchor() {
    const top = $("#mast").getBoundingClientRect().bottom + 24;
    const blocks = $$(".h1, .h2, .blk, .elide, .step, .tp", doc);
    for (const b of blocks) {
      if (!b.offsetParent && b.getClientRects().length === 0) continue;
      const r = b.getBoundingClientRect();
      if (r.bottom > top) return { el: b, off: r.top };
    }
    return null;
  }
  function visibleFrom(el) {
    let e = el;
    while (e && e.getClientRects().length === 0) e = e.nextElementSibling || (e.parentElement !== doc ? e.parentElement : null);
    return e || el;
  }
  function setDepth(d, keep) {
    if (!DEPTHS.includes(d) || d === depth) return;
    const a = keep !== false && $("body").dataset.view === "text" ? readingAnchor() : null;
    depth = d;
    root.setAttribute("data-depth", d);
    store.set("depth", d);
    $$(".open", doc).forEach((x) => x.classList.remove("open"));
    $$("[aria-expanded]", doc).forEach((b) => b.setAttribute("aria-expanded", d === "full" ? "true" : "false"));
    markDepth();
    if (a) {
      const e = visibleFrom(a.el);
      window.scrollBy(0, e.getBoundingClientRect().top - a.off);
    }
    spy();
  }
  $$("#depth button").forEach((b) => { b.onclick = () => setDepth(b.dataset.depth); });
  markDepth();

  /* ------------------------------------------------------------ local disclosure */
  doc.addEventListener("click", (ev) => {
    const st = ev.target.closest(".step-tog");
    if (st) {
      const step = st.closest(".step");
      const on = !isOpenStep(step);
      step.classList.toggle("open", on); step.classList.toggle("shut", !on);
      st.setAttribute("aria-expanded", String(on));
      return;
    }
    const el = ev.target.closest(".elide");
    if (el) {
      const p = el.nextElementSibling;
      const on = !p.classList.contains("open");
      p.classList.toggle("open", on); el.classList.toggle("open", on);
      el.setAttribute("aria-expanded", String(on));
      return;
    }
    const all = ev.target.closest(".pf-all");
    if (all) {
      const pf = all.closest(".proof");
      const steps = $$(".step", pf);
      const on = !steps.every(isOpenStep);
      pf.classList.add("open");
      steps.forEach((s) => { s.classList.toggle("open", on); s.classList.toggle("shut", !on); $(".step-tog", s).setAttribute("aria-expanded", String(on)); });
      all.textContent = on ? "close all steps" : "open all steps";
    }
  });
  const isOpenStep = (s) => s.classList.contains("open") || (depth === "full" && !s.classList.contains("shut"));

  /* make a target visible at the current depth */
  function reveal(el) {
    const prose = el.closest(".prose");
    if (prose && depth !== "full") { prose.classList.add("open"); const e = prose.previousElementSibling; if (e && e.classList.contains("elide")) { e.classList.add("open"); e.setAttribute("aria-expanded", "true"); } }
    const step = el.closest(".step");
    if (step) { step.classList.add("open"); step.classList.remove("shut"); $(".step-tog", step).setAttribute("aria-expanded", "true"); }
    const pf = el.closest(".proof");
    if (pf) pf.classList.add("open");
  }

  /* ------------------------------------------------------------ targets */
  function targetOf(label) {
    if (N[label] && isHyp(N[label]) && depth !== "full") return $("#h-" + CSS.escape(label));
    if (N[label] && !isHyp(N[label])) return document.getElementById("r-" + label);
    if (secById[label]) return document.getElementById("s-" + label);
    return document.getElementById("lbl-" + label) || document.getElementById("pf-" + label);
  }
  function flash(el) {
    const box = el.closest(".stmt, li, .dmath, .proof, h2, h3") || el;
    box.classList.remove("flash"); void box.offsetWidth; box.classList.add("flash");
    setTimeout(() => box.classList.remove("flash"), 2200);
  }
  function scrollToEl(el, smooth) {
    reveal(el);
    const y = el.getBoundingClientRect().top + window.scrollY - $("#mast").offsetHeight - 18;
    window.scrollTo({ top: Math.max(0, y), behavior: smooth && !reduce.matches ? "smooth" : "auto" });
    flash(el);
  }

  /* ------------------------------------------------------------ reading position and return */
  const ret = $("#return");
  /* moving from a place in the text: remember it in the history entry, so that Back returns */
  function remember(from) {
    if ($("body").dataset.view !== "text") return;
    const ctx = from && doc.contains(from) ? VP.peek.context(from) : "";
    history.replaceState({ y: window.scrollY, ctx }, "");
  }
  function jump(label, from) {
    remember(from);
    const h = secById[label] ? "#/s/" + encodeURIComponent(label) : "#/r/" + encodeURIComponent(label);
    if (location.hash === h) route(); else location.hash = h;
    if (from && doc.contains(from)) {
      const ctx = VP.peek.context(from);
      ret.innerHTML = `<span aria-hidden="true">↩</span> Back to ${esc(ctx || "the previous place")}`;
      ret.hidden = false;
    }
  }
  ret.onclick = () => { ret.hidden = true; history.back(); };
  document.addEventListener("click", (ev) => {
    const a = ev.target.closest('a[href^="#/"]');
    if (a && !a.classList.contains("ref") && !ev.metaKey && !ev.ctrlKey) remember(a);
  }, true);

  /* ------------------------------------------------------------ routes */
  let textY = 0;
  function showView(v) {
    const was = document.body.dataset.view;
    if (was === "text" && v !== "text") textY = window.scrollY;
    document.body.dataset.view = v;
    doc.hidden = v !== "text";
    ["atlas", "hypotheses", "lean"].forEach((k) => { $("#v-" + k).hidden = v !== k; });
    $$(".views a").forEach((a) => a.setAttribute("aria-current", a.dataset.v === v ? "page" : "false"));
    if (v !== "text") ret.hidden = true;
    return was;
  }
  function parse() {
    const h = decodeURIComponent(location.hash.replace(/^#\/?/, ""));
    const [path, q] = h.split("?");
    const parts = path.split("/");
    const rest = parts.slice(1).join("/");
    const l = new URLSearchParams(q || "").get("l");
    if (parts[0] === "node") return { v: "text", r: l || rest };        /* routes of the first Visual Paper */
    if (parts[0] === "sec") return { v: "text", s: rest, r: l && l !== rest ? l : null };
    if (parts[0] === "contents") return { v: "text", contents: true };
    if (parts[0] === "r") return { v: "text", r: rest };
    if (parts[0] === "s") return { v: "text", s: rest };
    if (parts[0] === "p") return { v: "text", p: rest };
    if (parts[0] === "atlas") return { v: "atlas", id: rest };
    if (parts[0] === "hypotheses") return { v: "hypotheses" };
    if (parts[0] === "lean") return { v: "lean", id: rest };
    return { v: "text", top: !path };
  }
  let ledgersBuilt = { hypotheses: false, lean: false };
  function route() {
    const r = parse();
    const was = showView(r.v);
    VP.peek.close();
    if (r.v === "atlas") { VP.atlas.show(r.id); window.scrollTo(0, 0); title("Atlas"); return; }
    if (r.v === "hypotheses") { if (!ledgersBuilt.hypotheses) { VP.ledgers.buildHyp(); ledgersBuilt.hypotheses = true; } window.scrollTo(0, 0); title("Hypotheses"); return; }
    if (r.v === "lean") {
      if (!ledgersBuilt.lean) { VP.ledgers.buildLean(); ledgersBuilt.lean = true; }
      const row = r.id && document.getElementById("lean-" + r.id);
      if (row) scrollToEl(row); else window.scrollTo(0, 0);
      title("Lean"); return;
    }
    const st = history.state;
    if (st && typeof st.y === "number") { window.scrollTo(0, st.y); spy(); title(); return; }
    if (r.contents) openRail(true);
    const label = r.r || r.s || null;
    const el = label ? targetOf(label) : r.p ? document.getElementById("pf-" + r.p) : null;
    if (el) { scrollToEl(el, false); title(el); }
    else if (was !== "text" && !r.top) window.scrollTo(0, textY);
    else if (r.top) { window.scrollTo(0, 0); title(); }
    spy();
  }
  function title(x) {
    let t = "Beyond Convex Growth — Visual Paper";
    if (typeof x === "string") t = x + " · " + t;
    document.title = t;
  }
  window.addEventListener("hashchange", route);
  window.addEventListener("popstate", () => { if (!history.state || typeof history.state.y !== "number") ret.hidden = true; });

  /* ------------------------------------------------------------ contents rail and position */
  const rail = $("#rail");
  function openRail(on) {
    document.body.classList.toggle("rail-open", on);
    $("#b-contents").setAttribute("aria-expanded", String(on));
    if (window.matchMedia("(min-width: 1180px)").matches) store.set("rail", on);
  }
  $("#b-contents").onclick = () => openRail(!document.body.classList.contains("rail-open"));
  rail.addEventListener("click", (ev) => { if (ev.target.closest("a") && !window.matchMedia("(min-width: 1180px)").matches) openRail(false); });
  $("#stage").addEventListener("click", () => { if (document.body.classList.contains("rail-open") && !window.matchMedia("(min-width: 1180px)").matches) openRail(false); });
  if (window.matchMedia("(min-width: 1180px)").matches && store.get("rail", true)) openRail(true);

  let spyQueued = false;
  function spy() {
    if (spyQueued) return;
    spyQueued = true;
    requestAnimationFrame(() => {
      spyQueued = false;
      if (document.body.dataset.view !== "text") return;
      const line = $("#mast").getBoundingClientRect().bottom + window.innerHeight * 0.18;
      let sec = null, res = null;
      for (const h of $$("h2[data-sec], h3[data-sec]", doc)) { if (h.getBoundingClientRect().top <= line) sec = h.dataset.sec; else break; }
      for (const b of $$(".stmt[data-node]:not(.syn)", doc)) {
        const r = b.getBoundingClientRect();
        if (r.height === 0) continue;
        if (r.top <= line) res = b.dataset.node; else break;
      }
      $$(".toc li.on", rail).forEach((x) => x.classList.remove("on"));
      $$(".toc .tr.on", rail).forEach((x) => x.classList.remove("on"));
      if (sec) {
        const li = $(`.toc li[data-sec="${CSS.escape(sec)}"]`, rail);
        if (li) {
          li.classList.add("on");
          const top = secById[sec].parent ? $(`.toc li[data-sec="${CSS.escape(secById[sec].parent)}"]`, rail) : null;
          if (top) top.classList.add("on");
          const rr = li.getBoundingClientRect(), cr = rail.getBoundingClientRect();
          if (rr.top < cr.top + 40 || rr.bottom > cr.bottom - 40) rail.scrollTop += rr.top - cr.top - cr.height / 3;
        }
      }
      if (res) { const t = $(`.toc .tr[data-node="${CSS.escape(res)}"]`, rail); if (t) t.classList.add("on"); }
      if (!ret.hidden && history.state && typeof history.state.y !== "number") { /* left the jump target long ago */ }
    });
  }
  window.addEventListener("scroll", spy, { passive: true });
  window.addEventListener("resize", spy);

  /* ------------------------------------------------------------ search */
  const q = $("#q"), list = $("#q-list");
  const index = [];
  Object.values(N).forEach((n) => {
    const one = isHyp(n) ? n.short : KIND[n.kind].one + " " + n.num;
    index.push({ href: "#/r/" + encodeURIComponent(n.id), kind: one, label: n.nick || n.title_plain || "", st: isRemark(n) || isHyp(n) ? undefined : status(n),
      key: [one, abbr(n), n.id, isHyp(n) ? "h" + n.num : ""].join(" ").toLowerCase(),
      hay: [one, abbr(n), n.nick, n.id, n.title_plain, isHyp(n) ? "h" + n.num : "", n.search].join(" ").toLowerCase() });
    const named = n.lean ? [...new Set((n.lean.decls || []).concat(((n.lean.note || "").match(/`[^`\s]+`/g) || []).map((x) => x.slice(1, -1))))] : [];
    named.forEach((d) => index.push({ href: "#/lean/" + encodeURIComponent(n.id), kind: "Lean", label: d + " — " + one, key: d.toLowerCase(), hay: d.toLowerCase(), code: true }));
  });
  sections.forEach((s) => index.push({ href: "#/s/" + encodeURIComponent(s.id), kind: VP.secLabel(s), label: s.title_plain,
    key: ("section " + s.num + " " + s.id).toLowerCase(), hay: ("section " + s.num + " " + s.title_plain + " " + s.id).toLowerCase() }));
  let qsel = -1;
  function search() {
    const t = q.value.trim().toLowerCase();
    if (!t) { list.hidden = true; q.setAttribute("aria-expanded", "false"); return; }
    const terms = t.split(/\s+/);
    const seen = new Set();
    const res = index.map((it) => {
      if (!terms.every((x) => it.hay.includes(x))) return null;
      let sc = 0;
      terms.forEach((x) => { if (it.key.includes(x)) sc += 5; if (it.label.toLowerCase().includes(x)) sc += 3; });
      if (it.key.split(" ").includes(t)) sc += 10;
      if (it.code) sc -= 2;
      return { it, sc };
    }).filter(Boolean).sort((a, b) => b.sc - a.sc).filter((r) => { const k = r.it.href + r.it.label; if (seen.has(k)) return false; seen.add(k); return true; }).slice(0, 12);
    qsel = res.length ? 0 : -1;
    list.innerHTML = res.length ? res.map((r, i) => `<a id="q-${i}" role="option" href="${r.it.href}" aria-selected="${i === 0}" class="${r.it.code ? "code" : ""}">` +
      `<span class="q-k">${r.it.st !== undefined ? mark(r.it.st, false) : ""}${esc(r.it.kind)}</span><span class="q-l">${esc(r.it.label)}</span></a>`).join("")
      : `<p class="q-none">No match</p>`;
    list.hidden = false;
    q.setAttribute("aria-expanded", "true");
    q.setAttribute("aria-activedescendant", res.length ? "q-0" : "");
  }
  q.addEventListener("input", search);
  q.addEventListener("keydown", (ev) => {
    const items = $$("a", list);
    if (ev.key === "ArrowDown" || ev.key === "ArrowUp") {
      ev.preventDefault();
      if (!items.length) return;
      qsel = (qsel + (ev.key === "ArrowDown" ? 1 : -1) + items.length) % items.length;
      items.forEach((a, i) => a.setAttribute("aria-selected", String(i === qsel)));
      q.setAttribute("aria-activedescendant", "q-" + qsel);
      items[qsel].scrollIntoView({ block: "nearest" });
    } else if (ev.key === "Enter") {
      if (items[qsel]) { remember(null); location.hash = items[qsel].getAttribute("href"); closeSearch(); q.blur(); }
    } else if (ev.key === "Escape") { closeSearch(); q.blur(); }
  });
  function closeSearch() { list.hidden = true; q.setAttribute("aria-expanded", "false"); }
  list.addEventListener("click", () => { closeSearch(); });
  document.addEventListener("click", (ev) => { if (!ev.target.closest("#search")) closeSearch(); });

  /* ------------------------------------------------------------ keys */
  function nextResult(dir) {
    const line = $("#mast").getBoundingClientRect().bottom + 30;
    const blocks = $$(".stmt[data-node]", doc).filter((b) => b.getClientRects().length);
    let i = blocks.findIndex((b) => b.getBoundingClientRect().top > line + 2);
    if (i < 0) i = blocks.length;
    const t = dir > 0 ? blocks[i] : blocks[Math.max(0, i - 2)];
    if (t) { scrollToEl(t, true); history.replaceState(null, "", "#/r/" + encodeURIComponent(t.dataset.node)); }
  }
  document.addEventListener("keydown", (ev) => {
    if ((ev.target instanceof Element && ev.target.closest("input, textarea, select, dialog")) || ev.metaKey || ev.ctrlKey) return;
    if (ev.altKey) {
      if (ev.key === "ArrowLeft") history.back();
      if (ev.key === "ArrowRight") history.forward();
      return;
    }
    const k = ev.key;
    if (k === "/") { ev.preventDefault(); q.focus(); q.select(); }
    else if (k === "?") { ev.preventDefault(); $("#help").showModal(); }
    else if (k === "1" || k === "2" || k === "3") { if (document.body.dataset.view !== "text") location.hash = "#/"; setDepth(DEPTHS[+k - 1]); }
    else if (k === "j" || k === "k") { if (document.body.dataset.view === "text") { ev.preventDefault(); nextResult(k === "j" ? 1 : -1); } }
    else if (k === "t") location.hash = "#/";
    else if (k === "a") location.hash = "#/atlas";
    else if (k === "h") location.hash = "#/hypotheses";
    else if (k === "l") location.hash = "#/lean";
    else if (k === "f") { if (document.body.dataset.view === "atlas") VP.atlas.enlarge(); }
    else if (k === "Escape" && VP.atlas.isBig()) VP.atlas.enlarge(false);
    else if (k === "Escape") { openRail(document.body.classList.contains("rail-open") && window.matchMedia("(min-width: 1180px)").matches); ret.hidden = true; }
  });
  $("#b-help").onclick = () => $("#help").showModal();

  /* ------------------------------------------------------------ theme and text size */
  $("#b-theme").onclick = () => {
    const dark = root.getAttribute("data-theme") === "dark" || (!root.getAttribute("data-theme") && matchMedia("(prefers-color-scheme: dark)").matches);
    const t = dark ? "light" : "dark";
    root.setAttribute("data-theme", t);
    store.set("theme", t);
  };
  const SIZES = [16, 17, 18, 19.5, 21];
  $("#b-size").onclick = () => {
    const cur = parseFloat(getComputedStyle(root).getPropertyValue("--fs")) || 18;
    const i = SIZES.findIndex((s) => s > cur + 0.1);
    const v = i < 0 ? SIZES[0] : SIZES[i];
    root.style.setProperty("--fs", v + "px");
    store.set("fs", v);
    $("#b-size").title = "Text size: " + v + " px";
  };

  VP.app = { jump, setDepth, route, reveal };
  route();
  markWide();
})();
