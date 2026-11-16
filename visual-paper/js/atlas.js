/* Visual Paper — the dependency atlas: a layered drawing of the references between results.
   An arrow A → B means that B refers to A (solid: in its statement; dashed: only in its proof).
   Layers: a result is one column to the right of the furthest result it refers to. */
(function () {
  "use strict";
  const { P, N, esc, KIND, isRemark, isHyp, abbr, uses, usedBy, docOrder, status, STATUS_TEXT, mark, store, refLink } = window.VP;
  const $ = (s, r) => (r || document).querySelector(s);
  const SVGNS = "http://www.w3.org/2000/svg";

  const opts = { remarks: store.get("atlas.remarks", false), hyps: store.get("atlas.hyps", false), proof: store.get("atlas.proof", true) };
  let sel = null, chain = false, built = false, geo = null, view = null;

  const NODE_W = 172, COL_GAP = 78, V_GAP = 12, DUMMY_H = 6, LINE = 14;
  const docIdx = Object.fromEntries(docOrder.map((id, i) => [id, i]));

  function wrap(text, max) {
    const out = [];
    let line = "";
    String(text || "").split(/\s+/).forEach((w) => {
      if (!w) return;
      if ((line + " " + w).trim().length > max && line) { out.push(line); line = w; } else line = (line + " " + w).trim();
    });
    if (line) out.push(line);
    return out.slice(0, 3);
  }
  const head = (n) => isHyp(n) ? n.short : KIND[n.kind].one + " " + n.num;

  /* ------------------------------------------------------------ layout */
  function compute() {
    const vis = new Set(Object.keys(N).filter((id) => {
      const n = N[id];
      if (isRemark(n)) return opts.remarks;
      if (isHyp(n)) return opts.hyps;
      return true;
    }));
    const edges = P.edges.filter((e) => vis.has(e.source) && vis.has(e.target) && (opts.proof || e.via !== "proof"));
    /* one edge per pair, solid if one of them is in the statement */
    const pair = new Map();
    edges.forEach((e) => {
      const k = e.source + "\u0000" + e.target;
      const prev = pair.get(k);
      if (!prev || (prev.via === "proof" && e.via !== "proof")) pair.set(k, { s: e.source, t: e.target, via: e.via });
    });
    const E = [...pair.values()];
    const preds = {}, succs = {};
    vis.forEach((v) => { preds[v] = []; succs[v] = []; });
    E.forEach((e) => { preds[e.t].push(e.s); succs[e.s].push(e.t); });

    /* longest path layering (the reference graph has no cycle; a guard stops at depth 64) */
    const layer = {};
    const depth = (v, d) => {
      if (layer[v] !== undefined) return layer[v];
      if (d > 64) return 0;
      layer[v] = 0;
      let L = 0;
      preds[v].forEach((p) => { L = Math.max(L, depth(p, d + 1) + 1); });
      return (layer[v] = L);
    };
    [...vis].forEach((v) => { delete layer[v]; });
    [...vis].forEach((v) => depth(v, 0));
    /* sinks with no successor and a single predecessor are pulled next to it */
    const nL = Math.max(0, ...Object.values(layer)) + 1;

    /* nodes with sizes; dummies for long edges */
    const nodes = {};
    vis.forEach((id) => {
      const n = N[id];
      const lines = wrap(n.nick || n.title_plain || "", 25);
      nodes[id] = { id, real: true, layer: layer[id], h: 22 + LINE * lines.length, lines };
    });
    const chains = [];
    let dk = 0;
    E.forEach((e) => {
      const pts = [e.s];
      for (let l = layer[e.s] + 1; l < layer[e.t]; l++) {
        const d = "~" + (dk++);
        nodes[d] = { id: d, real: false, layer: l, h: DUMMY_H };
        pts.push(d);
      }
      pts.push(e.t);
      chains.push({ e, pts });
    });
    const up = {}, down = {};
    Object.keys(nodes).forEach((v) => { up[v] = []; down[v] = []; });
    chains.forEach((c) => { for (let i = 0; i + 1 < c.pts.length; i++) { down[c.pts[i]].push(c.pts[i + 1]); up[c.pts[i + 1]].push(c.pts[i]); } });

    const layers = Array.from({ length: nL }, () => []);
    Object.values(nodes).forEach((v) => layers[v.layer].push(v.id));
    const key0 = (id) => nodes[id].real ? docIdx[id] ?? 999 : 1000;
    layers.forEach((L) => L.sort((a, b) => key0(a) - key0(b)));

    /* ordering: barycentre sweeps, keeping the order with fewest crossings */
    const pos = {};
    const setPos = () => layers.forEach((L) => L.forEach((v, i) => { pos[v] = i; }));
    const crossings = () => {
      let c = 0;
      for (let l = 0; l + 1 < nL; l++) {
        const segs = [];
        layers[l].forEach((v) => down[v].forEach((w) => segs.push([pos[v], pos[w]])));
        for (let i = 0; i < segs.length; i++) for (let j = i + 1; j < segs.length; j++) {
          if ((segs[i][0] - segs[j][0]) * (segs[i][1] - segs[j][1]) < 0) c++;
        }
      }
      return c;
    };
    setPos();
    let best = crossings(), bestOrder = layers.map((L) => L.slice());
    for (let it = 0; it < 28; it++) {
      const downward = it % 2 === 0;
      const range = downward ? [...Array(nL).keys()].slice(1) : [...Array(nL).keys()].reverse().slice(1);
      range.forEach((l) => {
        const nb = downward ? up : down;
        const bc = {};
        layers[l].forEach((v) => {
          const ns = nb[v];
          bc[v] = ns.length ? ns.reduce((s, w) => s + pos[w], 0) / ns.length : pos[v];
        });
        layers[l].sort((a, b) => bc[a] - bc[b] || pos[a] - pos[b]);
        layers[l].forEach((v, i) => { pos[v] = i; });
      });
      const c = crossings();
      if (c < best) { best = c; bestOrder = layers.map((L) => L.slice()); }
    }
    bestOrder.forEach((L, l) => { layers[l] = L; });
    setPos();

    /* vertical coordinates: each column stacked compactly in the order found above, then moved
       as a block towards the columns it is linked to */
    const y = {};
    const gapOf = (L, i) => nodes[L[i - 1]].h / 2 + V_GAP + nodes[L[i]].h / 2;
    layers.forEach((L) => { let t = 0; L.forEach((v, i) => { t += i ? gapOf(L, i) : nodes[v].h / 2; y[v] = t; }); });
    const H0 = Math.max(...layers.map((L) => L.length ? y[L[L.length - 1]] + nodes[L[L.length - 1]].h / 2 : 0));
    layers.forEach((L) => { if (!L.length) return; const t = y[L[L.length - 1]] + nodes[L[L.length - 1]].h / 2; L.forEach((v) => { y[v] += (H0 - t) / 2; }); });
    for (let it = 0; it < 24; it++) {
      layers.forEach((L) => {
        let s = 0, k = 0;
        L.forEach((v) => { const ns = up[v].concat(down[v]); ns.forEach((w) => { s += y[w] - y[v]; k++; }); });
        if (!k) return;
        let d = 0.5 * s / k;
        const top = y[L[0]] - nodes[L[0]].h / 2, bot = y[L[L.length - 1]] + nodes[L[L.length - 1]].h / 2;
        d = Math.max(-top, Math.min(H0 - bot, d));
        L.forEach((v) => { y[v] += d; });
      });
    }
    let minY = Infinity, maxY = -Infinity;
    Object.values(nodes).forEach((v) => { minY = Math.min(minY, y[v.id] - v.h / 2); maxY = Math.max(maxY, y[v.id] + v.h / 2); });
    Object.keys(y).forEach((v) => { y[v] -= minY; });
    const x = (l) => l * (NODE_W + COL_GAP);
    return { nodes, layers, chains, y, x, width: x(nL - 1) + NODE_W, height: maxY - minY, preds, succs, crossings: best };
  }

  /* ------------------------------------------------------------ drawing */
  function pathOf(c) {
    const g = geo;
    const pts = c.pts.map((id, i) => {
      const v = g.nodes[id];
      const X = g.x(v.layer);
      if (i === 0) return [X + NODE_W, g.y[id]];
      if (i === c.pts.length - 1) return [X - 2, g.y[id]];
      return [X + NODE_W / 2, g.y[id]];
    });
    /* through the dummies: straight across the column, curved between columns */
    let d = `M${pts[0][0].toFixed(1)} ${pts[0][1].toFixed(1)}`;
    for (let i = 1; i < pts.length; i++) {
      const [x0, y0] = pts[i - 1], [x1, y1] = pts[i];
      const xin = i < pts.length - 1 ? x1 - NODE_W / 2 : x1;
      const mx = (x0 + xin) / 2;
      d += ` C${mx.toFixed(1)} ${y0.toFixed(1)} ${mx.toFixed(1)} ${y1.toFixed(1)} ${xin.toFixed(1)} ${y1.toFixed(1)}`;
      if (i < pts.length - 1) d += ` L${(x1 + NODE_W / 2).toFixed(1)} ${y1.toFixed(1)}`;
    }
    return d;
  }

  function draw() {
    geo = compute();
    const svg = $("#atlas-svg");
    const pad = 28;
    const W = geo.width + 2 * pad, H = geo.height + 2 * pad;
    svg.setAttribute("data-w", W); svg.setAttribute("data-h", H);
    let edges = "", nodes = "";
    geo.chains.forEach((c, i) => {
      edges += `<path class="ed ${c.e.via === "proof" ? "pf" : "sm"}" data-s="${esc(c.e.s)}" data-t="${esc(c.e.t)}" d="${pathOf(c)}" marker-end="url(#ah)"/>`;
    });
    geo.layers.forEach((L) => L.forEach((id) => {
      const v = geo.nodes[id];
      if (!v.real) return;
      const n = N[id];
      const X = geo.x(v.layer), Y = geo.y[id] - v.h / 2;
      const st = status(n);
      const cls = ["nd", "k-" + n.kind, n.main ? "main" : "", n.external ? "ext" : "", isRemark(n) ? "rem" : ""].join(" ");
      const label = `${head(n)}${n.nick ? ", " + n.nick : ""}${n.external ? ", result of another paper" : ""}. ${st ? STATUS_TEXT[st] : "Not tracked in the Lean registry"}.`;
      nodes += `<g class="${cls}" data-id="${esc(id)}" transform="translate(${X.toFixed(1)} ${Y.toFixed(1)})" tabindex="0" role="button" aria-label="${esc(label)}">` +
        `<rect width="${NODE_W}" height="${v.h}" rx="1.5"/>` +
        (isHyp(n) || isRemark(n) ? "" : `<g class="nmk" transform="translate(8 7)">${mark(st, false).replace(/^<svg[^>]*>|<\/svg>$/g, "")}</g>`) +
        `<text class="nh" x="${isHyp(n) || isRemark(n) ? 9 : 24}" y="16">${esc(head(n))}${n.external ? '<tspan class="nx" dx="6">cited</tspan>' : ""}</text>` +
        v.lines.map((l, i) => `<text class="nn" x="9" y="${31 + i * LINE}">${esc(l)}</text>`).join("") + `</g>`;
    }));
    svg.innerHTML = `<defs><marker id="ah" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0.8L7 4L0 7.2z" class="ah"/></marker></defs>` +
      `<g id="atlas-world" transform="translate(${pad} ${pad})"><g class="eds">${edges}</g><g class="nds">${nodes}</g></g>`;
    view = null;
    fit();
    applySel();
    $("#atlas-stats").textContent = `${Object.values(geo.nodes).filter((v) => v.real).length} results · ${geo.chains.length} references · ${geo.layers.length} columns`;
  }

  /* ------------------------------------------------------------ view box: pan and zoom */
  function setView(v) {
    const svg = $("#atlas-svg");
    view = v;
    svg.setAttribute("viewBox", `${v.x} ${v.y} ${v.w} ${v.h}`);
  }
  function fit() {
    const svg = $("#atlas-svg");
    const W = +svg.dataset.w, H = +svg.dataset.h;
    const r = svg.getBoundingClientRect();
    const ar = r.width / Math.max(1, r.height);
    let w = W, h = H;
    if (w / h < ar) w = h * ar; else h = w / ar;
    setView({ x: (W - w) / 2, y: (H - h) / 2, w, h });
  }
  function zoomAt(f, cx, cy) {
    if (!view) return;
    const svg = $("#atlas-svg");
    const r = svg.getBoundingClientRect();
    const px = view.x + (cx - r.left) / r.width * view.w, py = view.y + (cy - r.top) / r.height * view.h;
    const W = +svg.dataset.w;
    const w = Math.max(260, Math.min(W * 2.5, view.w * f)), h = w * view.h / view.w;
    setView({ x: px - (px - view.x) * w / view.w, y: py - (py - view.y) * h / view.h, w, h });
  }
  function centerOn(id) {
    if (!geo || !geo.nodes[id] || !view) return;
    const v = geo.nodes[id];
    const cx = 28 + geo.x(v.layer) + NODE_W / 2, cy = 28 + geo.y[id];
    const svg = $("#atlas-svg");
    const r = svg.getBoundingClientRect();
    let w = view.w, h = view.h;
    if (r.width / w < 0.8) { w = r.width / 0.95; h = w * r.height / r.width; }
    setView({ x: cx - w / 2, y: cy - h / 2, w, h });
  }

  /* ------------------------------------------------------------ selection: what a result rests on, what rests on it */
  function cone(id, dir) {
    const out = new Set();
    const nb = dir === "up" ? geo.preds : geo.succs;
    const st = [id];
    while (st.length) { const v = st.pop(); (nb[v] || []).forEach((w) => { if (!out.has(w)) { out.add(w); st.push(w); } }); }
    return out;
  }
  function applySel(hoverId) {
    const svg = $("#atlas-svg");
    const focus = hoverId || sel || (chain ? "main-Ggrowth" : null);
    svg.classList.toggle("focused", !!focus);
    svg.querySelectorAll(".nd").forEach((g) => g.classList.remove("on", "up", "down"));
    svg.querySelectorAll(".ed").forEach((p) => p.classList.remove("up", "down"));
    if (!focus || !geo.nodes[focus]) return;
    const upS = cone(focus, "up"), downS = chain && !hoverId && focus === "main-Ggrowth" ? new Set() : cone(focus, "down");
    svg.querySelectorAll(".nd").forEach((g) => {
      const id = g.dataset.id;
      if (id === focus) g.classList.add("on"); else if (upS.has(id)) g.classList.add("up"); else if (downS.has(id)) g.classList.add("down");
    });
    svg.querySelectorAll(".ed").forEach((p) => {
      const s = p.dataset.s, t = p.dataset.t;
      if (upS.has(s) && (t === focus || upS.has(t))) p.classList.add("up");
      else if (downS.has(t) && (s === focus || downS.has(s))) p.classList.add("down");
    });
  }
  function select(id, center) {
    sel = id && N[id] ? id : null;
    applySel();
    renderPanel();
    if (sel && center) centerOn(sel);
    if (sel) {
      const want = "#/atlas/" + encodeURIComponent(sel);
      if (location.hash !== want) history.replaceState(history.state, "", want);
    }
  }

  function renderPanel() {
    const box = $("#atlas-panel");
    box.closest(".atlas").classList.toggle("has-sel", !!sel);
    if (!sel) {
      box.innerHTML = `<h2 class="sc">Reading the atlas</h2>
        <p>Each box is a numbered result; an arrow from A to B means that B refers to A, in its statement (solid) or only in its proof (dashed). A result stands one column to the right of the furthest result it refers to, so the foundations are on the left.</p>
        <p>Point at a box to see what it rests on (blue) and what rests on it (dark). Click to keep the selection and read the statement here.</p>
        <p class="lg">${mark("proved", false)} proved in Lean &nbsp; ${mark("partial", false)} proved in a restricted form &nbsp; ${mark(null, false)} not tracked</p>
        <p class="lg"><span class="lg-ext"></span> result of another paper, proved in Lean for this project</p>`;
      return;
    }
    const n = N[sel];
    const upS = [...cone(sel, "up")], downS = [...cone(sel, "down")];
    const ord = (a, b) => (docIdx[a] ?? 999) - (docIdx[b] ?? 999);
    const btns = (ids) => ids.sort(ord).map((id) => `<button type="button" class="ab" data-sel="${esc(id)}">${esc(abbr(N[id]))}</button>`).join(" ");
    const direct = [...new Set((uses[sel] || []).map((e) => e.source))].filter((id) => geo.nodes[id]);
    const by = [...new Set((usedBy[sel] || []).map((e) => e.target))].filter((id) => geo.nodes[id]);
    const st = status(n);
    box.innerHTML = `<p class="ap-k sc">${esc(KIND[n.kind].one)}${n.external ? " · result of another paper" : ""}</p>
      <h2 class="ap-t">${esc(head(n))}${n.nick ? ` <span class="ap-n">${esc(n.nick)}</span>` : ""}</h2>
      ${isRemark(n) || isHyp(n) ? "" : `<p class="ap-st">${mark(st)} ${esc(st ? STATUS_TEXT[st] : "Not tracked in the Lean registry")}</p>`}
      <div class="ap-body">${n.body}</div>
      <p class="ap-act"><a class="btn" href="#/r/${encodeURIComponent(sel)}">Read in the text</a> <button type="button" class="btn ghost" data-act="clear">Clear</button></p>
      <dl class="ap-rel">
        <dt>Refers to</dt><dd>${btns(direct) || "—"}</dd>
        <dt>Referred to by</dt><dd>${btns(by) || "—"}</dd>
        <dt>Rests on, through all references <span class="cnt">${upS.length}</span></dt><dd>${btns(upS) || "—"}</dd>
        <dt>Rests on it <span class="cnt">${downS.length}</span></dt><dd>${btns(downS) || "—"}</dd>
      </dl>`;
  }

  /* ------------------------------------------------------------ the view */
  function build() {
    const v = $("#v-atlas");
    v.innerHTML = `<div class="atlas">
      <div class="atlas-bar" role="toolbar" aria-label="Atlas controls">
        <label class="ck"><input type="checkbox" data-opt="hyps"> Hypotheses</label>
        <label class="ck"><input type="checkbox" data-opt="remarks"> Remarks</label>
        <label class="ck"><input type="checkbox" data-opt="proof"> References in proofs</label>
        <button type="button" class="tb" data-act="chain" aria-pressed="false">Theorem 1 and what it rests on</button>
        <span class="grow"></span>
        <span class="stats" id="atlas-stats"></span>
        <button type="button" class="tb" data-act="out" aria-label="Zoom out">−</button>
        <button type="button" class="tb" data-act="in" aria-label="Zoom in">+</button>
        <button type="button" class="tb" data-act="fit">Fit</button>
        <button type="button" class="tb" data-act="big" aria-pressed="false" title="Enlarge to the whole window (f)">Enlarge</button>
      </div>
      <div class="atlas-body">
        <svg id="atlas-svg" class="atlas-svg" role="group" aria-label="Dependency atlas of the results"></svg>
        <aside class="atlas-panel" id="atlas-panel" aria-live="polite"></aside>
      </div></div>`;
    v.querySelectorAll("[data-opt]").forEach((c) => {
      c.checked = opts[c.dataset.opt];
      c.onchange = () => { opts[c.dataset.opt] = c.checked; store.set("atlas." + c.dataset.opt, c.checked); draw(); if (sel && !geo.nodes[sel]) select(null); };
    });
    v.addEventListener("click", (ev) => {
      const b = ev.target.closest("[data-act]");
      if (b) {
        const a = b.dataset.act;
        if (a === "fit") fit();
        else if (a === "big") enlarge();
        else if (a === "in" || a === "out") { const r = $("#atlas-svg").getBoundingClientRect(); zoomAt(a === "in" ? 0.8 : 1.25, r.left + r.width / 2, r.top + r.height / 2); }
        else if (a === "chain") { chain = !chain; b.setAttribute("aria-pressed", String(chain)); if (chain) { select("main-Ggrowth", false); } else select(null); }
        else if (a === "clear") { chain = false; v.querySelector('[data-act="chain"]').setAttribute("aria-pressed", "false"); select(null); }
        return;
      }
      const s = ev.target.closest("[data-sel]");
      if (s) { select(s.dataset.sel, true); return; }
      const g = ev.target.closest(".nd");
      if (g && !moved) { select(g.dataset.id === sel ? null : g.dataset.id, false); return; }
      if (ev.target.closest("#atlas-svg") && !moved && !g) select(null);
    });
    const svg = $("#atlas-svg");
    svg.addEventListener("mouseover", (ev) => { const g = ev.target.closest(".nd"); if (g && !drag) applySel(g.dataset.id); });
    svg.addEventListener("mouseout", (ev) => { const g = ev.target.closest(".nd"); if (g) applySel(); });
    svg.addEventListener("focusin", (ev) => { const g = ev.target.closest(".nd"); if (g) applySel(g.dataset.id); });
    svg.addEventListener("focusout", () => applySel());
    svg.addEventListener("keydown", (ev) => {
      const g = ev.target.closest(".nd");
      if (g && (ev.key === "Enter" || ev.key === " ")) { ev.preventDefault(); select(g.dataset.id, false); }
    });
    svg.addEventListener("wheel", (ev) => {
      ev.preventDefault();
      if (ev.ctrlKey || ev.metaKey) zoomAt(Math.exp(ev.deltaY * 0.01), ev.clientX, ev.clientY);
      else if (view) { const r = svg.getBoundingClientRect(); setView({ x: view.x + ev.deltaX * view.w / r.width, y: view.y + ev.deltaY * view.h / r.height, w: view.w, h: view.h }); }
    }, { passive: false });
    let drag = null, moved = false;
    svg.addEventListener("pointerdown", (ev) => { if (ev.button !== 0) return; drag = { x: ev.clientX, y: ev.clientY, v: Object.assign({}, view) }; moved = false; });
    window.addEventListener("pointermove", (ev) => {
      if (!drag) return;
      const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 4) moved = true;
      if (!moved) return;
      const r = svg.getBoundingClientRect();
      setView({ x: drag.v.x - dx * drag.v.w / r.width, y: drag.v.y - dy * drag.v.h / r.height, w: drag.v.w, h: drag.v.h });
      svg.classList.add("dragging");
    });
    window.addEventListener("pointerup", () => { drag = null; svg.classList.remove("dragging"); setTimeout(() => { moved = false; }, 0); });
    window.addEventListener("resize", () => { if (built && !$("#v-atlas").hidden) fit(); });
    built = true;
  }

  /* enlarged atlas: the drawing takes the whole window; Esc, f or the button bring it back */
  function isBig() { const a = $("#v-atlas .atlas"); return !!a && a.classList.contains("big"); }
  function enlarge(on) {
    const a = $("#v-atlas .atlas");
    if (!a) return;
    if (on === undefined) on = !a.classList.contains("big");
    a.classList.toggle("big", on);
    document.body.classList.toggle("atlas-big", on);
    const b = a.querySelector('[data-act="big"]');
    b.setAttribute("aria-pressed", String(on));
    b.textContent = on ? "Reduce" : "Enlarge";
    b.title = on ? "Back to the page (f or Esc)" : "Enlarge to the whole window (f)";
    if (geo && !$("#v-atlas").hidden) fit();
  }
  window.addEventListener("hashchange", () => { if (isBig() && !/^#\/atlas/.test(location.hash)) enlarge(false); });

  function show(id) {
    if (!built) build();
    if (!geo) draw(); else fit();
    if (id && N[id]) {
      if (!geo.nodes[id]) {
        if (isHyp(N[id])) opts.hyps = true; else if (isRemark(N[id])) opts.remarks = true;
        $("#v-atlas").querySelectorAll("[data-opt]").forEach((c) => { c.checked = opts[c.dataset.opt]; });
        draw();
      }
      select(id, true);
    } else renderPanel();
  }

  window.VP.atlas = { show, select, compute, enlarge, isBig };
})();
