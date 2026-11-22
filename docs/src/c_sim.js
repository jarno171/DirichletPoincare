/* =====================================================================
   Part C: counterexample simulations, L^q chart, Lean source browser
   ===================================================================== */

/* ------------------------------------------------ region schematic */
(function region() {
  const cv = $('#rg-canvas'); if (!cv) return;
  const KMAX = 12;
  function draw() {
    const lam = +$('#rg-l').value, zoom = +$('#rg-z').value, ex = $('#rg-ex').checked;
    $('#rg-l-v').textContent = lam.toFixed(1); $('#rg-z-v').textContent = zoom.toFixed(2);
    const m = k => Math.pow(lam, k), c = k => 1 / (m(k) * m(k)), r = k => c(k) / 4;
    const hh = k => ex ? 0.07 * c(k) : Math.pow(m(k + 1), -10);
    const k0 = Math.floor(zoom), fr = zoom - k0;
    const cz = Math.exp(Math.log(c(k0)) * (1 - fr) + Math.log(c(k0 + 1)) * fr);
    const { ctx, w, h } = fit(cv, 0.36);
    const xmin = -0.25 * cz, xmax = 1.4 * cz, s = w / (xmax - xmin), X = x => (x - xmin) * s, Y = y => h / 2 - y * s;
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    ctx.strokeStyle = '#ffffff22'; ctx.beginPath(); ctx.moveTo(0, h / 2); ctx.lineTo(w, h / 2); ctx.stroke();
    ctx.fillStyle = '#2b6a7b';
    for (let k = 0; k < KMAX; k++) {
      const a = c(k + 1) + r(k + 1) - 0.01 * c(k + 1), b = c(k) - r(k) + 0.01 * c(k);
      const half = Math.max(hh(k), 0.6 / s);
      ctx.fillRect(X(a), Y(half), (b - a) * s, 2 * half * s);
    }
    for (let k = 0; k <= KMAX; k++) {
      ctx.beginPath(); ctx.arc(X(c(k)), h / 2, Math.max(r(k) * s, 0.6), 0, 7); ctx.fillStyle = '#2b6a7b'; ctx.fill();
      ctx.strokeStyle = COL.mint; ctx.lineWidth = 1.6; ctx.stroke();
      if (r(k) * s > 14) { ctx.fillStyle = COL.ink; ctx.font = '12px Inter, sans-serif'; ctx.textAlign = 'center'; ctx.fillText('D' + k, X(c(k)), h / 2 + 4); ctx.textAlign = 'left'; }
    }
    ctx.fillStyle = COL.coral; ctx.beginPath(); ctx.arc(X(0), h / 2, 4, 0, 7); ctx.fill();
    ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif';
    ctx.fillText(`window: x ∈ [${fmt(xmin, 3)}, ${fmt(xmax, 3)}]   (the origin is the accumulation point)`, 10, h - 10);
    const k = Math.min(KMAX, Math.round(zoom));
    $('#rg-out').innerHTML = [
      `chamber D${k}: m = <span class="hl">${fmt(m(k), 5)}</span>`,
      `centre c = 1/m² = <span class="hl">${fmt(c(k), 4)}</span>, radius c/4 = ${fmt(r(k), 4)}`,
      `neck half-height ≈ m⁻¹⁰ = <span class="hl">${fmt(Math.pow(m(k + 1), -10), 3)}</span>`,
      `neck/chamber ratio = ${fmt(Math.pow(m(k + 1), -10) / r(k), 3)}`].join('<br>');
  }
  ['rg-l', 'rg-z'].forEach(id => bindRange(id, draw)); $('#rg-ex').addEventListener('change', draw);
  REDRAW.push(draw); draw();
})();

/* ------------------------------------------------- g_m plot */
(function gm() {
  const cv = $('#gm-canvas'); if (!cv) return;
  function draw() {
    const m = Math.pow(10, +$('#gm-m').value), K = Math.pow(10, +$('#gm-k').value);
    $('#gm-m-v').textContent = m < 100 ? m.toFixed(1) : m.toExponential(1); $('#gm-k-v').textContent = (+$('#gm-k').value).toFixed(1);
    const { ctx, w, h } = fit(cv, 0.45), pad = 34, X = x => pad + x * (w - 2 * pad), Y = y => h - pad - y * (h - 2 * pad);
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    ctx.strokeStyle = '#ffffff22'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pad, h - pad); ctx.lineTo(w - pad, h - pad); ctx.moveTo(pad, pad / 2); ctx.lineTo(pad, h - pad); ctx.stroke();
    ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif';
    for (const t of [0, 0.25, 0.5, 0.75, 1]) { ctx.fillText(t, X(t) - 6, h - pad + 16); }
    ctx.fillText('x', w - pad + 8, h - pad + 4); ctx.fillText('1', pad - 14, Y(1) + 4);
    const N = 600, dens = x => 4 * m * m * x * x * Math.pow(1 - x * x, 2 * m - 2); let dmax = 0;
    for (let i = 0; i <= N; i++) dmax = Math.max(dmax, dens(i / N));
    ctx.lineWidth = 2.4; ctx.strokeStyle = COL.mint; ctx.beginPath();
    for (let i = 0; i <= N; i++) { const x = i / N, y = Math.pow(1 - x * x, m); i ? ctx.lineTo(X(x), Y(y)) : ctx.moveTo(X(x), Y(y)); } ctx.stroke();
    ctx.strokeStyle = COL.gold; ctx.beginPath();
    for (let i = 0; i <= N; i++) { const x = i / N, y = dens(x) / (dmax || 1); i ? ctx.lineTo(X(x), Y(y)) : ctx.moveTo(X(x), Y(y)); } ctx.stroke();
    const xc = Math.min(1, 1 / (m * m));
    ctx.fillStyle = COL.coral; ctx.beginPath(); ctx.arc(X(xc), Y(Math.pow(1 - xc * xc, m)), 6, 0, 7); ctx.fill();
    ctx.fillStyle = COL.blue; ctx.beginPath(); ctx.arc(X(1), Y(0), 6, 0, 7); ctx.fill();
    const E = 10 / Math.pow(m, 5), low = Math.PI / (1024 * Math.pow(m, 4)), ratio = Math.PI * m / 10240;
    $('#gm-out').innerHTML = [
      `energy ∫|g′|² ≤ <span class="hl">${fmt(E, 3)}</span>   (10/m⁵)`,
      `∫|g − c|² ≥ <span class="hl">${fmt(low, 3)}</span>   (π/1024m⁴)`,
      `ratio ≥ πm/10240 = <span class="${ratio > K ? 'bad' : 'good'}">${fmt(ratio, 3)}</span>`,
      ratio > K ? `K = ${fmt(K, 3)} is <span class="bad">violated</span> by g_m`
        : `K = ${fmt(K, 3)} not yet violated — need m &gt; <span class="hl">${fmt(10240 * K / Math.PI, 3)}</span>`].join('<br>');
  }
  ['gm-m', 'gm-k'].forEach(id => bindRange(id, draw));
  REDRAW.push(draw); draw();
})();

/* ------------------------------------------- boundary length chart */
(function boundary() {
  const cv = $('#bl-canvas'); if (!cv) return;
  function draw() {
    const { ctx, w, h } = fit(cv, 0.38), pad = 36, n = 11, total = 40 / (1 - 0.25);
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    const bw = (w - 2 * pad) / n, Y = v => h - pad - v / (total * 1.08) * (h - 2 * pad);
    let cum = 0; ctx.font = '12px Inter, sans-serif';
    ctx.strokeStyle = COL.gold; ctx.setLineDash([6, 5]); ctx.beginPath(); ctx.moveTo(pad, Y(total)); ctx.lineTo(w - pad, Y(total)); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle = COL.gold; ctx.fillText('Σ 40·4⁻ᵏ = 160/3 ≈ 53.3', w - pad - 150, Y(total) - 6);
    ctx.beginPath(); ctx.strokeStyle = COL.mint; ctx.lineWidth = 2;
    for (let k = 0; k < n; k++) {
      const v = 40 * Math.pow(4, -k); cum += v;
      ctx.fillStyle = '#ff958088'; ctx.fillRect(pad + k * bw + 4, Y(v), bw - 8, h - pad - Y(v));
      ctx.fillStyle = COL.muted; ctx.fillText(k, pad + k * bw + bw / 2 - 3, h - pad + 16);
      const px = pad + k * bw + bw / 2; k ? ctx.lineTo(px, Y(cum)) : ctx.moveTo(px, Y(cum));
    }
    ctx.stroke();
    ctx.fillStyle = COL.coral; ctx.fillText('bars: bound on the length of piece k', pad + 6, 18);
    ctx.fillStyle = COL.mint; ctx.fillText('line: partial sums', pad + 6, 34);
    $('#bl-out').innerHTML = `the bound is a geometric series ⇒ H¹(∂G) ≤ <span class="hl">${fmt(total, 4)}</span> &lt; ∞ — the boundary is rectifiable, yet the Poincaré inequality fails.`;
  }
  REDRAW.push(draw); draw();
})();

/* ---------------------------------- region G* of Theorem 3.21 */
(function regionStar() {
  const cv = $('#rs-canvas'); if (!cv) return;
  const K = 6, c = k => Math.pow(0.5, 2 * k - 0.0), hh = k => 0.16 * Math.pow(0.62, k);
  let ptr = null;
  const rects = []; for (let k = 1; k <= K; k++) rects.push([Math.pow(0.5, k), 1, hh(k)]);
  const inG = (x, y) => Math.hypot(x - 1, y) < 0.25 || rects.some(r => x > r[0] && x < r[1] && Math.abs(y) < r[2]);
  function draw() {
    const { ctx, w, h } = fit(cv, 0.4), s = w / 1.45, X = x => 18 + x * s, Y = y => h / 2 - y * s * 1.4;
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    ctx.fillStyle = '#2b6a7b'; ctx.strokeStyle = COL.mint; ctx.lineWidth = 1.2;
    ctx.beginPath(); ctx.arc(X(1), Y(0), 0.25 * s, 0, 7); ctx.fill(); ctx.stroke();
    rects.forEach(r => { ctx.fillRect(X(r[0]), Y(r[2]), (r[1] - r[0]) * s, 2 * r[2] * s * 1.4); });
    ctx.fillStyle = COL.blue; ctx.beginPath(); ctx.arc(X(1), Y(0), 5, 0, 7); ctx.fill();
    ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif'; ctx.fillText('1', X(1) + 8, Y(0) - 8); ctx.fillText('0', X(0) - 3, Y(0) + 18);
    ctx.fillText('D₀ (disc about 1) ∪ S₁ ∪ S₂ ∪ …  (heights exaggerated)', 10, h - 10);
    let msg = 'move the pointer over the picture';
    if (ptr) {
      const x = (ptr[0] - 18) / s, y = (h / 2 - ptr[1]) / (s * 1.4), ok = inG(x, y);
      ctx.strokeStyle = ok ? COL.gold : COL.coral; ctx.lineWidth = 2.4; ctx.setLineDash(ok ? [] : [5, 4]);
      ctx.beginPath(); ctx.moveTo(X(1), Y(0)); ctx.lineTo(ptr[0], ptr[1]); ctx.stroke(); ctx.setLineDash([]);
      let all = ok; if (ok) for (let t = 0; t <= 200; t++) if (!inG(1 + (x - 1) * t / 200, y * t / 200)) { all = false; break; }
      msg = ok ? `point ∈ G · segment from 1 stays in G: <span class="${all ? 'good' : 'bad'}">${all ? 'yes' : 'no'}</span> (starlike about 1)` : 'point ∉ G';
    }
    $('#rs-out').innerHTML = msg;
  }
  cv.addEventListener('pointermove', e => { ptr = canvasPos(e, cv); draw(); });
  cv.addEventListener('pointerleave', () => { ptr = null; draw(); });
  REDRAW.push(draw); draw();
})();

/* ----------------------------------------------- L^q chart */
(function lq() {
  const cv = $('#lq-canvas'); if (!cv) return;
  function draw() {
    const q = +$('#lq-q').value, lk = +$('#lq-k').value;
    $('#lq-q-v').textContent = q.toFixed(1); $('#lq-k-v').textContent = lk.toFixed(1);
    const l8 = Math.log10(8), lo = L => -l8 - (l8 + 12 * L) / q, up = L => lk + 0.5 - 2.5 * L, Lmax = 6;
    const ys = [lo(0), lo(Lmax), up(0), up(Lmax)], ymin = Math.min(...ys) - 0.5, ymax = Math.max(...ys) + 0.5;
    const { ctx, w, h } = fit(cv, 0.45), pad = 40, X = L => pad + L / Lmax * (w - 2 * pad), Y = y => h - pad - (y - ymin) / (ymax - ymin) * (h - 2 * pad);
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    ctx.strokeStyle = '#ffffff22'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(pad, h - pad); ctx.lineTo(w - pad, h - pad); ctx.moveTo(pad, 8); ctx.lineTo(pad, h - pad); ctx.stroke();
    ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif';
    for (let L = 0; L <= Lmax; L++) ctx.fillText('10^' + L, X(L) - 10, h - pad + 16);
    ctx.fillText('log₁₀ of the norm', pad + 6, 16); ctx.fillText('m', w - pad + 6, h - pad + 4);
    if (ymin < 0 && ymax > 0) { ctx.strokeStyle = '#ffffff18'; ctx.beginPath(); ctx.moveTo(pad, Y(0)); ctx.lineTo(w - pad, Y(0)); ctx.stroke(); }
    const line = (f, col) => { ctx.strokeStyle = col; ctx.lineWidth = 2.6; ctx.beginPath(); ctx.moveTo(X(0), Y(f(0))); ctx.lineTo(X(Lmax), Y(f(Lmax))); ctx.stroke(); };
    line(lo, COL.mint); line(up, COL.coral);
    const slope = 2.5 - 12 / q; let verdict;
    if (slope > 1e-9) {
      const Ls = (lk + 0.5 + l8 + l8 / q) / slope;
      if (Ls > 0 && Ls < Lmax) { ctx.fillStyle = COL.gold; ctx.beginPath(); ctx.arc(X(Ls), Y(lo(Ls)), 6, 0, 7); ctx.fill(); }
      verdict = `violated for m ≥ <span class="hl">${fmt(Math.pow(10, Math.max(0, Ls)), 3)}</span> — <span class="bad">the (${fmt(q, 2)}, 2) inequality fails</span> with constant K = ${fmt(Math.pow(10, lk), 3)}`;
    } else verdict = '<span class="good">this test family does not contradict the inequality</span> (12/q ≥ 5/2)';
    ctx.fillStyle = COL.mint; ctx.fillText('— lower bound for ‖g_m − c‖_q', pad + 10, 36);
    ctx.fillStyle = COL.coral; ctx.fillText('— upper bound K‖g_m′‖₂ ≤ K√(10/m⁵)', pad + 10, 54);
    $('#lq-out').innerHTML = [`slope of the gap: 5/2 − 12/q = <span class="hl">${fmt(slope, 3)}</span>`, verdict, q >= 8 ? 'q ≥ 8 (p ≥ 8/5) is the range proved in Lean' : ''].filter(Boolean).join('<br>');
  }
  ['lq-q', 'lq-k'].forEach(id => bindRange(id, draw));
  REDRAW.push(draw); draw();
})();

/* -------------------------------------------- source browser */
(function source() {
  const filesEl = $('#src-files'), codeEl = $('#src-code'), search = $('#src-search');
  if (!filesEl || typeof SOURCES === 'undefined') return;
  const paths = Object.keys(SOURCES).sort((a, b) => (a.includes('/') - b.includes('/')) || a.localeCompare(b));
  const KW = new Set('theorem lemma def abbrev instance structure class inductive namespace section end open import variable universe noncomputable private protected where deriving extends macro notation example axiom opaque local attribute set_option mutual in at with by fun from have show calc let match then else if do return using only generalizing termination_by decreasing_by'.split(' '));
  const TAC = new Set('intro intros exact apply refine simp simp_all simpa rw rwa nlinarith linarith positivity norm_num omega ring ring_nf field_simp obtain rcases cases rintro constructor use exists left right contradiction exfalso by_contra by_cases induction congr gcongr calc push_neg push_cast norm_cast exact_mod_cast convert filter_upwards refine\' specialize subst rfl trivial decide aesop tauto ext funext unfold change nth_rewrite conv simp_rw fin_cases interval_cases lift choose peel set rename_i skip first repeat all_goals any_goals try assumption classical bound abel linear_combination'.split(' '));
  const esc = s => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  const IDRE = /[\p{L}_][\p{L}\p{N}_'.!?₀-₉]*/uy, NUMRE = /\d+(\.\d+)?/y;
  function highlight(src) {
    const lines = ['']; let i = 0;
    const emit = (cls, text) => {
      const parts = text.split('\n');
      parts.forEach((p, j) => { if (j) lines.push(''); if (p) lines[lines.length - 1] += cls ? `<span class="${cls}">${esc(p)}</span>` : esc(p); });
    };
    while (i < src.length) {
      const ch = src[i];
      if (src.startsWith('/-', i)) {
        const doc = src[i + 2] === '-' || src[i + 2] === '!'; let depth = 1, j = i + 2;
        while (j < src.length && depth > 0) {
          if (src.startsWith('/-', j)) { depth++; j += 2; } else if (src.startsWith('-/', j)) { depth--; j += 2; } else j++;
        }
        emit(doc ? 'c-doc' : 'c-cmt', src.slice(i, j)); i = j; continue;
      }
      if (src.startsWith('--', i)) { let j = src.indexOf('\n', i); if (j < 0) j = src.length; emit('c-cmt', src.slice(i, j)); i = j; continue; }
      if (ch === '"') { let j = i + 1; while (j < src.length && src[j] !== '"') j += src[j] === '\\' ? 2 : 1; emit('s', src.slice(i, j + 1)); i = j + 1; continue; }
      IDRE.lastIndex = i; let mt = IDRE.exec(src);
      if (mt) {
        let id = mt[0]; while (id.length > 1 && /[.!?]$/.test(id)) id = id.slice(0, -1);
        emit(KW.has(id) ? 'k' : (TAC.has(id) ? 'tac' : ''), id); i += id.length; continue;
      }
      NUMRE.lastIndex = i; mt = NUMRE.exec(src);
      if (mt) { emit('num', mt[0]); i += mt[0].length; continue; }
      emit('', ch); i++;
    }
    return lines;
  }
  const DECL = /^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom)\s+([^\s({:\[⦃]+)/;
  const decls = [];
  const cache = {};
  for (const p of paths) {
    SOURCES[p].split('\n').forEach((ln, idx) => { const m = DECL.exec(ln); if (m) decls.push({ file: p, kind: m[1], name: m[2], line: idx + 1 }); });
  }
  const total = paths.reduce((n, p) => n + SOURCES[p].split('\n').length, 0);
  const lb = $('#loc-badge'); if (lb) lb.textContent = total.toLocaleString('en-US').replace(/,/g, ' ');
  const fb = $('#files-badge'); if (fb) fb.textContent = paths.length;
  let curFile = null;
  function show(path, line) {
    if (curFile !== path) {
      if (!cache[path]) cache[path] = highlight(SOURCES[path]);
      const n = decls.filter(d => d.file === path).length;
      codeEl.innerHTML = `<div class="fhead"><b>${path}</b> · ${cache[path].length} lines · ${n} declarations</div><pre>${cache[path].map(l => `<span class="l">${l}</span>`).join('')}</pre>`;
      curFile = path;
      $$('a', filesEl).forEach(a => a.classList.toggle('cur', a.dataset.file === path && !a.dataset.line));
    }
    if (line) {
      const el = $('pre', codeEl).children[line - 1];
      if (el) {
        codeEl.scrollTop = Math.max(0, el.offsetTop - 70);
        el.classList.add('flash'); setTimeout(() => el.classList.remove('flash'), 2200);
      }
    } else codeEl.scrollTop = 0;
  }
  function renderList() {
    const q = search.value.trim().toLowerCase(); let html = '';
    if (q) {
      const hits = decls.filter(d => d.name.toLowerCase().includes(q)).slice(0, 80);
      html = hits.map(d => `<a class="decl" data-file="${d.file}" data-line="${d.line}"><span>${d.kind}</span>${esc(d.name)}<small>${d.file.replace('.lean', '')}</small></a>`).join('') || '<p class="muted small">no match</p>';
    } else {
      let grp = null;
      for (const p of paths) {
        const g = p.includes('/') ? p.split('/')[0] : 'root';
        if (g !== grp) { html += `<div class="grp">${g === 'root' ? 'DirichletPoincare' : g}</div>`; grp = g; }
        html += `<a data-file="${p}">${p.split('/').pop().replace('.lean', '')}<small>${decls.filter(d => d.file === p).length}</small></a>`;
      }
    }
    filesEl.innerHTML = html;
    $$('a', filesEl).forEach(a => a.addEventListener('click', () => show(a.dataset.file, a.dataset.line ? +a.dataset.line : 0)));
    if (curFile) $$('a', filesEl).forEach(a => a.classList.toggle('cur', a.dataset.file === curFile && !a.dataset.line));
  }
  search.addEventListener('input', renderList);
  window.openSource = (file, name) => {
    const d = decls.find(x => x.file === file && x.name.split('.').pop() === name) || decls.find(x => x.name.split('.').pop() === name);
    document.getElementById('source').scrollIntoView({ behavior: 'smooth', block: 'start' });
    if (d) show(d.file, d.line); else show(paths.includes(file) ? file : paths[0], 0);
  };
  renderList();
  show(paths.includes('Section2/Starlike.lean') ? 'Section2/Starlike.lean' : paths[0], 0);
})();

/* ------------------------------------------------ nav highlight */
(function nav() {
  const links = $$('.topbar a[href^="#"]'); if (!links.length) return;
  const secs = links.map(a => $(a.getAttribute('href'))).filter(Boolean);
  const upd = () => {
    let cur = secs[0];
    for (const s of secs) if (s.getBoundingClientRect().top < 140) cur = s;
    links.forEach(a => a.classList.toggle('on', a.getAttribute('href') === '#' + (cur && cur.id)));
  };
  window.addEventListener('scroll', upd, { passive: true }); upd();
})();
