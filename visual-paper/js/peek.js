/* Visual Paper — previews of cross-references and citations, in the margin (wide screens) or in
   a sheet at the bottom (narrow screens). */
(function () {
  "use strict";
  const { P, N, esc, KIND, isHyp, secById, secLabel, status, mark, refLink } = window.VP;
  const $ = (s, r) => (r || document).querySelector(s);
  const peek = $("#peek");
  let current = null;      // { key, pinned, anchor }
  let hoverTimer = null, leaveTimer = null;

  /* ------------------------------------------------------------ where an element sits */
  function context(el) {
    const parts = [];
    const step = el.closest(".step");
    const proof = el.closest(".proof");
    const stmt = el.closest(".stmt");
    if (proof) {
      const o = N[proof.dataset.owner];
      parts.push("proof of " + KIND[o.kind].one + " " + o.num);
      if (step) {
        const sn = step.querySelector(".sn");
        if (sn && !sn.classList.contains("sn-pre")) parts.push(sn.textContent.replace(/\.$/, ""));
      }
    } else if (stmt && stmt.dataset.node) {
      const o = N[stmt.dataset.node];
      parts.push(isHyp(o) ? o.short : KIND[o.kind].one + " " + o.num);
    }
    const sec = sectionOf(el);
    if (sec) parts.push(secLabel(sec));
    return parts.join(" · ");
  }
  function sectionOf(el) {
    /* the last heading before el in document order */
    const doc = $("#doc");
    if (!doc.contains(el)) return null;
    const hs = doc.querySelectorAll("h2[data-sec], h3[data-sec]");
    let found = null;
    for (const h of hs) {
      if (h.compareDocumentPosition(el) & Node.DOCUMENT_POSITION_FOLLOWING) found = h; else break;
    }
    return found ? secById[found.dataset.sec] : null;
  }

  /* ------------------------------------------------------------ the target of a reference */
  function resolve(goto, kind, label) {
    const n = N[label];
    if (n && !isHyp(n)) {
      const box = document.getElementById("r-" + label);
      return { key: label, el: box && box.querySelector(".tx"), node: n, wrap: "stmt",
        title: `${KIND[n.kind].one} ${n.num}`, sub: n.nick, ctx: box ? context(box).split(" · ").pop() : "", target: label };
    }
    if (n && isHyp(n)) {
      const li = document.getElementById("lbl-" + label);
      return { key: label, el: li, node: n, wrap: "li", title: n.short, sub: n.nick, ctx: li ? context(li) : "", target: label };
    }
    if (kind === "section" && secById[label]) {
      const s = secById[label];
      return { key: label, section: s, title: secLabel(s), sub: s.title_plain, target: label };
    }
    const a = document.getElementById("lbl-" + label);
    if (!a) return null;
    if (a.tagName === "FIGURE") return { key: label, el: a, title: a.querySelector(".fig-n").textContent.replace(/\.$/, ""), ctx: context(a), target: label };
    let el = a;
    if (a.classList.contains("anchor")) el = a.closest(".dmath") || a.closest("li") || a.closest("p") || a.parentElement;
    const num = a.matches(".dmath") || a.closest(".dmath") ? numberOf(a.closest(".dmath"), label) : (a.querySelector(":scope > .li-label") || {}).textContent;
    return { key: label, el, wrap: el.tagName === "LI" ? "li" : "", title: num || "", ctx: context(el), target: label };
  }
  function numberOf(dm, label) {
    const tags = dm.querySelectorAll(".tag");
    if (tags.length === 1) return tags[0].textContent;
    const ref = document.querySelector(`a.ref[data-label="${CSS.escape(label)}"]`);
    return ref ? ref.textContent : "";
  }

  /* ------------------------------------------------------------ rendering */
  function cloneOf(el) {
    const c = el.cloneNode(true);
    c.removeAttribute("id");
    c.querySelectorAll("[id]").forEach((x) => x.removeAttribute("id"));
    c.querySelectorAll(".mg, .elide").forEach((x) => x.remove());
    c.classList.remove("highlight");
    return c;
  }
  function render(t) {
    let body = "";
    const holder = document.createElement("div");
    holder.className = "pk-body";
    if (t.section) {
      const items = t.section.pieces.filter((p) => p.t === "stmt").map((p) => `<li>${mark(status(N[p.id]))}${refLink(p.id)}<span class="pk-nick">${esc(N[p.id].nick || "")}</span></li>`).join("");
      holder.innerHTML = items ? `<ul class="pk-list">${items}</ul>` : `<p class="pk-none">No numbered statement in this section.</p>`;
    } else if (t.bib) {
      holder.innerHTML = `<p>${t.bib.html}</p>`;
    } else if (t.el) {
      const c = cloneOf(t.el);
      if (t.wrap === "li") { const ol = document.createElement("ol"); ol.className = "tlist"; ol.appendChild(c); holder.appendChild(ol); }
      else holder.appendChild(c);
    }
    const st = t.node && !isHyp(t.node) ? `<span class="pk-mk">${mark(status(t.node))}</span>` : "";
    peek.innerHTML = `<header class="pk-h"><p class="pk-t">${st}<span class="pk-title">${esc(t.title)}</span>${t.sub ? ` <span class="pk-sub">${esc(t.sub)}</span>` : ""}</p>` +
      `<button type="button" class="pk-x" aria-label="Close the preview" title="Close (Esc)">×</button></header>` +
      (t.ctx ? `<p class="pk-ctx">${esc(t.ctx)}</p>` : "");
    peek.appendChild(holder);
    if (t.target) {
      const f = document.createElement("p");
      f.className = "pk-f";
      f.innerHTML = `<button type="button" class="pk-go" data-go="${esc(t.target)}">Go to ${t.section ? "the section" : "the text"}</button>` +
        (t.node && !isHyp(t.node) ? ` <a class="pk-atlas" href="#/atlas/${encodeURIComponent(t.node.id)}">In the atlas</a>` : "");
      peek.appendChild(f);
    }
  }

  /* ------------------------------------------------------------ placement */
  const wide = () => window.matchMedia("(min-width: 1180px)").matches;
  function place(anchor) {
    peek.classList.toggle("sheet", !wide());
    if (!wide()) { peek.style.top = ""; peek.style.left = ""; return; }
    const lane = $("#stage").getBoundingClientRect();
    const r = anchor.getBoundingClientRect();
    const w = Math.min(360, Math.max(280, window.innerWidth - lane.left - 760));
    peek.style.width = w + "px";
    const left = Math.min(window.innerWidth - w - 16, Math.max(r.right + 24, lane.left + 760));
    peek.style.left = left + "px";
    peek.style.top = "0px";
    const h = peek.offsetHeight;
    const top0 = $("#mast").getBoundingClientRect().bottom + 8;
    peek.style.top = Math.max(top0, Math.min(window.innerHeight - h - 12, r.top - 14)) + "px";
  }

  /* ------------------------------------------------------------ open / close */
  function open(a, pinned) {
    let t;
    if (a.classList.contains("cite")) {
      const b = P.bib[a.dataset.bib];
      if (!b) return;
      t = { key: "bib:" + a.dataset.bib, bib: b, title: "[" + b.alpha + "]", sub: "", ctx: "" };
    } else {
      t = resolve(a.dataset.goto, a.dataset.kind, a.dataset.label);
      if (!t) return;
    }
    if (current && current.key === t.key && current.pinned && pinned) { close(); return; }
    render(t);
    peek.hidden = false;
    place(a);
    peek.classList.toggle("pinned", !!pinned);
    if (current && current.anchor) current.anchor.classList.remove("peeking");
    a.classList.add("peeking");
    current = { key: t.key, pinned: !!pinned, anchor: a };
  }
  function close() {
    peek.hidden = true;
    if (current && current.anchor) current.anchor.classList.remove("peeking");
    current = null;
  }

  document.addEventListener("click", (ev) => {
    const a = ev.target.closest("a.ref, a.cite");
    if (a && !a.closest(".pk-h")) {
      if (ev.metaKey || ev.ctrlKey || ev.shiftKey) return;
      /* a section reference moves to the section; other references open a preview */
      if (a.classList.contains("ref") && a.dataset.kind === "section" && a.dataset.label === a.dataset.goto && !a.closest("#peek")) {
        ev.preventDefault(); close(); window.VP.app.jump(a.dataset.label, a); return;
      }
      ev.preventDefault();
      open(a, true);
      if (ev.detail === 0) { const g = peek.querySelector(".pk-go"); if (g) g.focus(); }
      return;
    }
    if (ev.target.closest(".pk-x")) { close(); return; }
    const go = ev.target.closest(".pk-go");
    if (go) { const from = current && current.anchor; close(); window.VP.app.jump(go.dataset.go, from); return; }
    if (ev.target.closest(".pk-atlas")) { close(); return; }
    if (!ev.target.closest("#peek") && current) close();
  });

  /* hover previews, for a fine pointer only */
  const fine = window.matchMedia("(hover: hover) and (pointer: fine)");
  document.addEventListener("mouseover", (ev) => {
    if (!fine.matches) return;
    const a = ev.target.closest("a.ref, a.cite");
    if (ev.target.closest("#peek")) { clearTimeout(leaveTimer); return; }
    if (!a) return;
    if (a.classList.contains("ref") && a.dataset.kind === "section" && a.dataset.label === a.dataset.goto) return;
    clearTimeout(leaveTimer); clearTimeout(hoverTimer);
    if (current && current.pinned) return;
    hoverTimer = setTimeout(() => open(a, false), 260);
  });
  document.addEventListener("mouseout", (ev) => {
    if (!fine.matches) return;
    const a = ev.target.closest("a.ref, a.cite, #peek");
    if (!a) return;
    clearTimeout(hoverTimer);
    if (current && !current.pinned) leaveTimer = setTimeout(close, 220);
  });
  document.addEventListener("keydown", (ev) => { if (ev.key === "Escape" && current) { close(); ev.stopPropagation(); } }, true);
  window.addEventListener("resize", () => { if (current) place(current.anchor); });
  document.addEventListener("scroll", () => {
    if (!current) return;
    if (!current.pinned || !wide()) { if (!current.pinned) close(); return; }
    const r = current.anchor.getBoundingClientRect();
    if (r.bottom < 0 || r.top > window.innerHeight) close(); else place(current.anchor);
  }, { passive: true, capture: true });

  window.VP.peek = { open, close, resolve, context };
})();
