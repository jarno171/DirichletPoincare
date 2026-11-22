/* =====================================================================
   Part A: helpers, dependency graph, quotient explorer, starlike explorer
   ===================================================================== */
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
const COL = { mint: '#8ce0bb', gold: '#ffd27b', coral: '#ff9580', blue: '#9fc5ff', ink: '#edf4ef',
  muted: '#9eb0b2', line: '#334951', panel: '#182630', bg: '#0b1318', violet: '#c9b3ff' };
const REDRAW = [];
window.addEventListener('resize', () => REDRAW.forEach(f => f()));

function fmt(x, d = 4) {
  if (!isFinite(x)) return String(x);
  const a = Math.abs(x);
  if (a !== 0 && (a < 1e-3 || a >= 1e6)) return x.toExponential(2);
  const s = x.toFixed(d);
  return s.indexOf('.') >= 0 ? s.replace(/\.?0+$/, '') || '0' : s;
}
function fit(canvas, aspect) {
  const dpr = window.devicePixelRatio || 1;
  const w = Math.max(200, canvas.clientWidth || (canvas.parentElement && canvas.parentElement.clientWidth) || 400);
  const h = Math.round(w * aspect);
  if (canvas.__w !== w || canvas.__h !== h || canvas.__dpr !== dpr) {
    canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr);
    canvas.style.height = h + 'px';
    canvas.__w = w; canvas.__h = h; canvas.__dpr = dpr;
  }
  const ctx = canvas.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  return { ctx, w, h };
}
function canvasPos(e, canvas) {
  const r = canvas.getBoundingClientRect();
  return [(e.clientX - r.left) * (canvas.__w / r.width), (e.clientY - r.top) * (canvas.__h / r.height)];
}
function heat(t) { // 0..1 -> rgb
  t = Math.max(0, Math.min(1, t));
  const stops = [[18, 40, 52], [30, 98, 104], [140, 224, 187], [255, 210, 123], [255, 149, 128]];
  const p = t * (stops.length - 1), i = Math.min(stops.length - 2, Math.floor(p)), f = p - i;
  const a = stops[i], b = stops[i + 1];
  return `rgb(${Math.round(a[0] + (b[0] - a[0]) * f)},${Math.round(a[1] + (b[1] - a[1]) * f)},${Math.round(a[2] + (b[2] - a[2]) * f)})`;
}
function randn() { // Box–Muller
  let u = 0, v = 0; while (u === 0) u = Math.random(); v = Math.random();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}
function bindRange(id, onchange, fmtfn) {
  const el = $('#' + id), val = $('#' + id + '-v');
  const upd = () => { if (val) val.textContent = fmtfn ? fmtfn(+el.value) : el.value; };
  el.addEventListener('input', () => { upd(); onchange(); });
  upd(); return el;
}

/* ---------------------------------------------------------------- graph */
(function graph() {
  const svg = $('#graph'); if (!svg) return;
  const NS = 'http://www.w3.org/2000/svg', W = 130, H = 46;
  const el = (n, attrs = {}, parent = svg) => { const e = document.createElementNS(NS, n); for (const k in attrs) e.setAttribute(k, attrs[k]); parent.appendChild(e); return e; };
  const defs = el('defs');
  for (const [id, col] of [['arr', '#4b6a73'], ['arrhot', '#ffd27b']]) {
    const m = el('marker', { id, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    el('path', { d: 'M0 0L10 5L0 10z', fill: col }, m);
  }
  for (const b of BANDS) {
    el('rect', { x: 8, y: b.y, width: 984, height: b.h, rx: 14, fill: '#ffffff06' });
    const t = el('text', { x: 22, y: b.y + 18, class: 'bandlabel' }); t.textContent = b.label;
  }
  function clip(n, tx, ty) {
    const dx = tx - n.x, dy = ty - n.y;
    const s = Math.min((W / 2) / Math.abs(dx || 1e-9), (H / 2) / Math.abs(dy || 1e-9));
    return [n.x + dx * s, n.y + dy * s];
  }
  const edgeEls = [];
  for (const [a, b] of EDGES) {
    const A = RESULTS[a], B = RESULTS[b], key = a + '>' + b;
    let d;
    if (EDGE_PATHS[key]) d = EDGE_PATHS[key];
    else { const p = clip(A, B.x, B.y), q = clip(B, A.x, A.y); d = `M${p[0].toFixed(1)} ${p[1].toFixed(1)} L${q[0].toFixed(1)} ${q[1].toFixed(1)}`; }
    const e = el('path', { d, class: 'edge' }); e.dataset.a = a; e.dataset.b = b; edgeEls.push(e);
  }
  const nodeEls = {};
  for (const id in RESULTS) {
    const r = RESULTS[id];
    const g = el('g', { class: `node ${r.kind} ${r.alone ? 'alone' : ''}`, transform: `translate(${r.x - W / 2},${r.y - H / 2})`, tabindex: 0 });
    el('rect', { width: W, height: H }, g);
    el('text', { x: W / 2, y: 20 }, g).textContent = r.title;
    el('text', { x: W / 2, y: 36, class: 'sub' }, g).textContent = r.sub;
    g.addEventListener('click', () => select(id));
    g.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') select(id); });
    nodeEls[id] = g;
  }
  function select(id) {
    const r = RESULTS[id];
    for (const k in nodeEls) nodeEls[k].classList.toggle('sel', k === id);
    for (const e of edgeEls) e.classList.toggle('hot', e.dataset.a === id || e.dataset.b === id);
    const names = r.lean.split(', ').map(n => `<code>${n}</code>`).join(' ');
    const file = r.file, pf = r.proofFile;
    $('#detail').innerHTML = `<h3>${r.title} <span class="muted small">— ${r.sub}</span></h3>
      <div class="row">${r.stmt}</div>
      <div class="row"><b>Lean</b> ${names}<br><span class="muted small">${file}${pf ? ' · proof in ' + pf : ''}</span></div>
      <div class="row"><b>Proof idea</b> ${r.idea}</div>
      ${r.dev ? `<div class="row"><b>Compared to the thesis</b> ${r.dev}</div>` : ''}
      <button class="linkbtn" id="detail-open">Open in source ↓</button>`;
    $('#detail-open').addEventListener('click', () => window.openSource && window.openSource(pf || file, r.lean.split(', ')[0]));
  }
  window.selectResult = select;
  select('t213');
})();

/* ------------------------------------------------- Poincaré quotient */
(function quotient() {
  const cv = $('#qc-canvas'); if (!cv) return;
  const BOX = 1.1;
  const regions = {
    disc: { inside: (x, y) => x * x + y * y < 1, z0: [0, 0], note: 'convex ⇒ starlike (Thm 2.13)' },
    square: { inside: (x, y) => Math.abs(x) < 1 && Math.abs(y) < 1, z0: [0.1, 0.1], note: 'convex ⇒ starlike (Thm 2.13)' },
    lshape: { inside: (x, y) => Math.abs(x) < 1 && Math.abs(y) < 1 && !(x > 0 && y > 0), z0: [-0.5, -0.5], note: 'starlike about points of the lower-left square (Thm 2.13)' },
    annulus: { inside: (x, y) => { const r2 = x * x + y * y; return r2 < 1 && r2 > 0.2025; }, z0: [0.7, 0], note: 'not starlike; three starlike sectors (Thm 2.22)' }
  };
  let coeffs = randomCoeffs(), z0 = regions.disc.z0.slice(), best = null;
  function randomCoeffs() { const c = []; for (let k = 0; k <= 6; k++) c.push([randn() / Math.max(1, k), randn() / Math.max(1, k)]); return c; }
  function funcOf(kind, c) {
    const out = [0, 0, 0, 0];
    if (kind === 'exp') return (x, y) => { const e = Math.exp(3 * x), cs = Math.cos(3 * y), sn = Math.sin(3 * y); out[0] = e * cs; out[1] = e * sn; out[2] = 3 * out[0]; out[3] = 3 * out[1]; return out; };
    let poly = c;
    if (kind === 'z') poly = [[0, 0], [1, 0]];
    if (kind === 'z3') poly = [[0, 0], [0, 0], [0, 0], [1, 0]];
    if (kind === 'z8') poly = [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]];
    return (x, y) => { // Horner for p and p'
      let pr = 0, pi = 0, dr = 0, di = 0;
      for (let k = poly.length - 1; k >= 0; k--) {
        const ndr = dr * x - di * y + pr, ndi = dr * y + di * x + pi; dr = ndr; di = ndi;
        const npr = pr * x - pi * y + poly[k][0], npi = pr * y + pi * x + poly[k][1]; pr = npr; pi = npi;
      }
      out[0] = pr; out[1] = pi; out[2] = dr; out[3] = di; return out;
    };
  }
  function compute(inside, f, N, grid) {
    const h = 2 * BOX / N, o = f(z0[0], z0[1]), f0r = o[0], f0i = o[1];
    let num = 0, den = 0;
    for (let j = 0; j < N; j++) for (let i = 0; i < N; i++) {
      const x = -BOX + (i + 0.5) * h, y = BOX - (j + 0.5) * h;
      if (!inside(x, y)) { if (grid) grid[j * N + i] = -1; continue; }
      const v = f(x, y), a = v[0] - f0r, b = v[1] - f0i, m = a * a + b * b;
      num += m; den += v[2] * v[2] + v[3] * v[3];
      if (grid) grid[j * N + i] = m;
    }
    return { num: num * h * h, den: den * h * h, Q: num / den, area: 0 };
  }
  function draw() {
    const reg = regions[$('#qc-region').value], kind = $('#qc-func').value;
    const f = funcOf(kind, coeffs), { ctx, w, h } = fit(cv, 1);
    const N = 110, grid = new Float64Array(N * N), r = compute(reg.inside, f, N, grid);
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    let mx = 0; for (const v of grid) if (v > mx) mx = v;
    const cell = w / N;
    for (let j = 0; j < N; j++) for (let i = 0; i < N; i++) {
      const v = grid[j * N + i]; if (v < 0) continue;
      ctx.fillStyle = heat(Math.sqrt(v / (mx || 1))); ctx.fillRect(i * cell, j * cell, cell + 0.6, cell + 0.6);
    }
    if ($('#qc-region').value === 'annulus') {
      ctx.strokeStyle = '#ffffff88'; ctx.setLineDash([5, 4]); ctx.lineWidth = 1.2;
      for (const a of [Math.PI / 2, Math.PI / 2 + 2 * Math.PI / 3, Math.PI / 2 + 4 * Math.PI / 3]) {
        const s = w / (2 * BOX);
        ctx.beginPath(); ctx.moveTo(w / 2 + 0.45 * Math.cos(a) * s, h / 2 - 0.45 * Math.sin(a) * s);
        ctx.lineTo(w / 2 + Math.cos(a) * s, h / 2 - Math.sin(a) * s); ctx.stroke();
      }
      ctx.setLineDash([]);
    }
    const s = w / (2 * BOX), px = w / 2 + z0[0] * s, py = h / 2 - z0[1] * s;
    ctx.strokeStyle = COL.gold; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(px, py, 7, 0, 7); ctx.stroke();
    ctx.fillStyle = COL.gold; ctx.font = '12px Inter, sans-serif'; ctx.fillText('z₀', px + 10, py - 8);
    ctx.fillStyle = COL.muted; ctx.fillText('colour: |f − f(z₀)|²   (click to move z₀)', 10, h - 10);
    const rows = [
      `region      <span class="hl">${$('#qc-region').selectedOptions[0].text}</span>`,
      `            ${reg.note}`,
      `∫|f−f(z₀)|² = <span class="hl">${fmt(r.num)}</span>`,
      `∫|f′|²      = <span class="hl">${fmt(r.den)}</span>`,
      `Q(f)        = <span class="good">${fmt(r.Q)}</span>`];
    if (best) rows.push(`largest Q in ${best.n} random f: <span class="good">${fmt(best.Q)}</span>`, `(Poincaré: Q ≤ K for all f — finite)`);
    $('#qc-out').innerHTML = rows.join('<br>');
  }
  function setRegion() { z0 = regions[$('#qc-region').value].z0.slice(); best = null; draw(); }
  $('#qc-region').addEventListener('change', setRegion);
  $('#qc-func').addEventListener('change', () => { best = null; draw(); });
  $('#qc-new').addEventListener('click', () => { coeffs = randomCoeffs(); $('#qc-func').value = 'rand'; draw(); });
  $('#qc-sample').addEventListener('click', () => {
    const reg = regions[$('#qc-region').value]; let mxQ = 0;
    for (let i = 0; i < 400; i++) { const r = compute(reg.inside, funcOf('rand', randomCoeffs()), 48); if (r.Q > mxQ) mxQ = r.Q; }
    best = { Q: mxQ, n: 400 }; draw();
  });
  cv.addEventListener('pointerdown', e => {
    const [x, y] = canvasPos(e, cv), s = cv.__w / (2 * BOX);
    const zx = (x - cv.__w / 2) / s, zy = -(y - cv.__h / 2) / s;
    if (regions[$('#qc-region').value].inside(zx, zy)) { z0 = [zx, zy]; best = null; draw(); }
  });
  REDRAW.push(draw); draw();
})();

/* ------------------------------------------------------- starlike */
(function starlike() {
  const cv = $('#sl-canvas'); if (!cv) return;
  const P = {
    star: (() => { const v = []; for (let k = 0; k < 10; k++) { const a = Math.PI / 2 + k * Math.PI / 5, r = k % 2 ? 0.19 : 0.46; v.push([0.5 + r * Math.cos(a), 0.5 + r * Math.sin(a)]); } return v; })(),
    hex: (() => { const v = []; for (let k = 0; k < 6; k++) { const a = k * Math.PI / 3; v.push([0.5 + 0.42 * Math.cos(a), 0.5 + 0.42 * Math.sin(a)]); } return v; })(),
    ell: [[0.1, 0.1], [0.9, 0.1], [0.9, 0.4], [0.4, 0.4], [0.4, 0.9], [0.1, 0.9]],
    u: [[0.1, 0.1], [0.9, 0.1], [0.9, 0.9], [0.7, 0.9], [0.7, 0.3], [0.3, 0.3], [0.3, 0.9], [0.1, 0.9]],
    comb: [[0.08, 0.1], [0.92, 0.1], [0.92, 0.92], [0.78, 0.92], [0.78, 0.3], [0.64, 0.3], [0.64, 0.92], [0.5, 0.92], [0.5, 0.3], [0.36, 0.3], [0.36, 0.92], [0.22, 0.92], [0.22, 0.3], [0.08, 0.3]]
  };
  let poly, kmask, kArea, inArea, centre = [0.5, 0.5], pt = [0.2, 0.8], drag = null;
  const GN = 90;
  function inside(x, y) {
    let c = false;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
      const [xi, yi] = poly[i], [xj, yj] = poly[j];
      if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c;
    }
    return c;
  }
  function inKernel(x, y) {
    for (let i = 0; i < poly.length; i++) {
      const a = poly[i], b = poly[(i + 1) % poly.length];
      if ((b[0] - a[0]) * (y - a[1]) - (b[1] - a[1]) * (x - a[0]) < -1e-9) return false;
    }
    return true;
  }
  function setPreset() {
    poly = P[$('#sl-preset').value].map(p => p.slice());
    let area = 0; for (let i = 0; i < poly.length; i++) { const a = poly[i], b = poly[(i + 1) % poly.length]; area += a[0] * b[1] - b[0] * a[1]; }
    if (area < 0) poly.reverse();
    kmask = new Uint8Array(GN * GN); kArea = 0; inArea = 0; let sx = 0, sy = 0;
    for (let j = 0; j < GN; j++) for (let i = 0; i < GN; i++) {
      const x = (i + 0.5) / GN, y = (j + 0.5) / GN;
      if (inside(x, y)) { inArea++; if (inKernel(x, y)) { kmask[j * GN + i] = 1; kArea++; sx += x; sy += y; } }
    }
    centre = kArea ? [sx / kArea, sy / kArea] : [0.5, 0.2];
    const c = poly.reduce((s, p) => [s[0] + p[0] / poly.length, s[1] + p[1] / poly.length], [0, 0]);
    pt = [poly[1][0] + 0.15 * (c[0] - poly[1][0]), poly[1][1] + 0.15 * (c[1] - poly[1][1])];
    if ($('#sl-preset').value === 'u' || $('#sl-preset').value === 'comb') { centre = [0.5, 0.2]; pt = [0.2, 0.8]; }
    draw();
  }
  function segOK(a, b) { for (let k = 0; k <= 240; k++) { const t = k / 240; if (!inside(a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)) return false; } return true; }
  function draw() {
    const { ctx, w, h } = fit(cv, 0.82), S = Math.min(w, h / 0.82 * 0.82), ox = (w - S) / 2, oy = 0;
    const X = x => ox + x * S, Y = y => oy + (1 - y) * S * 0.9 + 6;
    const k = S * 0.9;
    const px = x => ox + x * S, py = y => 6 + (1 - y) * k;
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    ctx.beginPath(); poly.forEach((p, i) => i ? ctx.lineTo(px(p[0]), py(p[1])) : ctx.moveTo(px(p[0]), py(p[1]))); ctx.closePath();
    ctx.fillStyle = '#1d3a44'; ctx.fill();
    if ($('#sl-kernel').checked && kArea) {
      ctx.fillStyle = 'rgba(140,224,187,.38)';
      for (let j = 0; j < GN; j++) for (let i = 0; i < GN; i++) if (kmask[j * GN + i]) ctx.fillRect(px(i / GN), py((j + 1) / GN), S / GN + 0.7, k / GN + 0.7);
    }
    ctx.lineWidth = 2; ctx.strokeStyle = '#5d8a95'; ctx.beginPath(); poly.forEach((p, i) => i ? ctx.lineTo(px(p[0]), py(p[1])) : ctx.moveTo(px(p[0]), py(p[1]))); ctx.closePath(); ctx.stroke();
    const cIn = inside(centre[0], centre[1]);
    if ($('#sl-rays').checked && cIn) {
      ctx.strokeStyle = 'rgba(159,197,255,.55)'; ctx.lineWidth = 1;
      for (let a = 0; a < 40; a++) {
        const th = a * 2 * Math.PI / 40; let r = 0;
        while (r < 1.6 && inside(centre[0] + (r + 0.004) * Math.cos(th), centre[1] + (r + 0.004) * Math.sin(th))) r += 0.004;
        ctx.beginPath(); ctx.moveTo(px(centre[0]), py(centre[1])); ctx.lineTo(px(centre[0] + r * Math.cos(th)), py(centre[1] + r * Math.sin(th))); ctx.stroke();
      }
    }
    const ok = cIn && inside(pt[0], pt[1]) && segOK(centre, pt);
    ctx.strokeStyle = ok ? COL.mint : COL.coral; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(px(centre[0]), py(centre[1])); ctx.lineTo(px(pt[0]), py(pt[1])); ctx.stroke();
    ctx.fillStyle = COL.blue; ctx.beginPath(); ctx.arc(px(centre[0]), py(centre[1]), 8, 0, 7); ctx.fill();
    ctx.fillStyle = COL.gold; ctx.beginPath(); ctx.arc(px(pt[0]), py(pt[1]), 7, 0, 7); ctx.fill();
    ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif'; ctx.fillText('drag the blue centre w₀ and the gold point z', 10, h - 8);
    const star = kArea > 0;
    $('#sl-out').innerHTML = [
      `region is starlike: ${star ? '<span class="good">yes</span>' : '<span class="bad">no (kernel empty)</span>'}`,
      `kernel ≈ <span class="hl">${(100 * kArea / inArea).toFixed(1)}%</span> of the region`,
      `centre w₀ in kernel: ${inKernel(centre[0], centre[1]) && cIn ? '<span class="good">yes</span>' : '<span class="bad">no</span>'}`,
      `segment [w₀, z] ⊂ G: ${ok ? '<span class="good">yes</span>' : '<span class="bad">no</span>'}`,
      star ? 'Theorem 2.13 ⇒ Poincaré (2,2) holds' : 'Theorem 2.13 does not apply directly'].join('<br>');
    cv.__map = { px, py, S, k };
  }
  cv.addEventListener('pointerdown', e => {
    const [x, y] = canvasPos(e, cv), m = cv.__map, d = p => Math.hypot(m.px(p[0]) - x, m.py(p[1]) - y);
    drag = d(centre) < 22 && d(centre) <= d(pt) ? centre : (d(pt) < 22 ? pt : null);
    if (drag) cv.setPointerCapture(e.pointerId);
  });
  cv.addEventListener('pointermove', e => {
    if (!drag) return; const [x, y] = canvasPos(e, cv), m = cv.__map;
    drag[0] = Math.max(0, Math.min(1, (x - (cv.__w - m.S) / 2) / m.S)); drag[1] = Math.max(0, Math.min(1, 1 - (y - 6) / m.k)); draw();
  });
  cv.addEventListener('pointerup', () => { drag = null; });
  ['#sl-kernel', '#sl-rays'].forEach(s => $(s).addEventListener('change', draw));
  $('#sl-preset').addEventListener('change', setPreset);
  REDRAW.push(draw); setPreset();
})();
