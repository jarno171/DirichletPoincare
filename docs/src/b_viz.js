/* =====================================================================
   Part B: area mean-value demo, inclusion stepper, Riemann map demo
   ===================================================================== */
const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const cexp = a => { const e = Math.exp(a[0]); return [e * Math.cos(a[1]), e * Math.sin(a[1])]; };
const csin = a => [Math.sin(a[0]) * Math.cosh(a[1]), Math.cos(a[0]) * Math.sinh(a[1])];
const cabs2 = a => a[0] * a[0] + a[1] * a[1];

/* ---------------------------------------------------- mean value */
(function meanvalue() {
  const cv = $('#mv-canvas'); if (!cv) return;
  const F = {
    exp: z => cexp(z),
    cub: z => { const z2 = cmul(z, z), z3 = cmul(z2, z); return [z3[0] - z[0], z3[1] - z[1]]; },
    sin: z => csin(z),
    abs2: z => [cabs2(z), 0]
  };
  const VIEW = 2.2;
  function draw() {
    const f = F[$('#mv-func').value], cx = +$('#mv-cx').value, cy = +$('#mv-cy').value, r = +$('#mv-r').value;
    const { ctx, w, h } = fit(cv, 0.7), s = h / (2 * VIEW);
    const X = x => w / 2 + x * s, Y = y => h / 2 - y * s;
    ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
    const N = 70; let vals = [], mx = 0;
    for (let j = 0; j < N; j++) for (let i = 0; i < N; i++) {
      const v = Math.sqrt(cabs2(f([(i + 0.5) / N * 2 * VIEW * w / h - VIEW * w / h, VIEW - (j + 0.5) / N * 2 * VIEW]))); vals.push(v); if (v > mx) mx = v;
    }
    for (let j = 0; j < N; j++) for (let i = 0; i < N; i++) {
      ctx.fillStyle = heat(Math.log(1 + 4 * vals[j * N + i]) / Math.log(1 + 4 * mx)); ctx.globalAlpha = 0.55;
      ctx.fillRect(i * w / N, j * h / N, w / N + 1, h / N + 1);
    }
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#ffffff22'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(0, h / 2); ctx.lineTo(w, h / 2); ctx.moveTo(w / 2, 0); ctx.lineTo(w / 2, h); ctx.stroke();
    ctx.fillStyle = 'rgba(255,210,123,.15)'; ctx.strokeStyle = COL.gold; ctx.lineWidth = 2.2;
    ctx.beginPath(); ctx.arc(X(cx), Y(cy), r * s, 0, 7); ctx.fill(); ctx.stroke();
    ctx.fillStyle = COL.gold; ctx.beginPath(); ctx.arc(X(cx), Y(cy), 4, 0, 7); ctx.fill();
    ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif'; ctx.fillText('background: |f| (log scale)', 10, h - 10);

    const NT = 240, NR = 60; let ca = [0, 0], aa = [0, 0], sq = 0;
    for (let k = 1; k <= NR; k++) {
      const rho = r * (k - 0.5) / NR; let sr = 0, si = 0, ssq = 0;
      for (let t = 0; t < NT; t++) {
        const a = 2 * Math.PI * t / NT, v = f([cx + rho * Math.cos(a), cy + rho * Math.sin(a)]);
        sr += v[0]; si += v[1]; ssq += cabs2(v);
      }
      sr /= NT; si /= NT; ssq /= NT;
      aa[0] += sr * 2 * rho / (r * r) * (r / NR); aa[1] += si * 2 * rho / (r * r) * (r / NR);
      sq += ssq * 2 * Math.PI * rho * (r / NR);
    }
    for (let t = 0; t < NT; t++) { const a = 2 * Math.PI * t / NT, v = f([cx + r * Math.cos(a), cy + r * Math.sin(a)]); ca[0] += v[0] / NT; ca[1] += v[1] / NT; }
    const fw = f([cx, cy]), z = v => `${fmt(v[0], 5)} ${v[1] < 0 ? '−' : '+'} ${fmt(Math.abs(v[1]), 5)}i`;
    const d1 = Math.hypot(ca[0] - fw[0], ca[1] - fw[1]), d2 = Math.hypot(aa[0] - fw[0], aa[1] - fw[1]);
    const area = Math.PI * r * r, lhs = cabs2(fw) * area, hol = $('#mv-func').value !== 'abs2';
    $('#mv-out').innerHTML = [
      `f(w)            = <span class="hl">${z(fw)}</span>`,
      `circle average  = ${z(ca)}   <span class="${d1 < 1e-3 ? 'good' : 'bad'}">Δ ${fmt(d1, 3)}</span>`,
      `area average    = ${z(aa)}   <span class="${d2 < 1e-3 ? 'good' : 'bad'}">Δ ${fmt(d2, 3)}</span>`,
      `|f(w)|²·area    = <span class="hl">${fmt(lhs)}</span>`,
      `∫_B |f|² dA     = <span class="hl">${fmt(sq)}</span>   ${lhs <= sq + 1e-6 ? '<span class="good">✓ inequality holds</span>' : '<span class="bad">✗ violated</span>'}`,
      hol ? 'holomorphic: averages equal f(w)' : '|z|² is not holomorphic: averages differ from f(w) (inequality can fail)'].join('<br>');
  }
  ['mv-cx', 'mv-cy', 'mv-r'].forEach(id => bindRange(id, draw));
  $('#mv-func').addEventListener('change', draw);
  REDRAW.push(draw); draw();
})();

/* ----------------------------------------------------- stepper */
(function stepper() {
  const body = $('#stepbody'); if (!body) return;
  const steps = [
    { box: ['D', 'X'], arr: ['DX'], t: '1 · Differentiation is injective',
      h: 'On a <i>region</i> a holomorphic f with f(z₀)=0 and f′=0 vanishes identically, so <code>f ↦ f′</code> is injective on D(G). Its image X ⊂ L²(G) is the space of derivatives.' },
    { box: ['D', 'G'], arr: ['DG'], t: '2 · The graph',
      h: 'Assume D(G) ⊂ B(G). Then every f ∈ D(G) also lies in L²(G) and we may form Γ = {([f′],[f])} ⊂ L²(G)×L²(G) (<code>graphSub</code>).' },
    { box: ['G'], arr: [], t: '3 · The graph is closed',
      h: 'The point-evaluation bound <code>ptBound_of_region</code> says |f(x)|² ≤ C<sub>x</sub>·E(f), obtained from <code>sq_norm_sub_le_of_ball</code> on small discs chained across the region. So if f′<sub>k</sub> → h in L², the primitives converge locally uniformly to a primitive F of h (<code>exists_limit_primitive</code>); the L² limit of f<sub>k</sub> is then F.' },
    { box: ['G', 'X'], arr: ['GX'], t: '4 · Projection to the first factor',
      h: 'π₁(f′, f) = f′ is injective on Γ (step 1), bounded, with closed range X ⊂ L²(G) — closedness is exactly the primitive-limit lemma again.' },
    { box: ['G', 'K'], arr: ['GK'], t: '5 · Open mapping',
      h: 'Mathlib’s <code>antilipschitz_of_injective_of_isClosed_range</code> for an injective bounded operator with closed range gives ‖(f′,f)‖ ≤ K‖f′‖, hence <b>‖f‖₂ ≤ K‖f′‖₂</b>: the Poincaré inequality, with an explicit finite constant (<code>inclusion_bounded_aux</code>).' }
  ];
  let cur = 0;
  const dots = $('#step-dots'); steps.forEach(() => dots.appendChild(document.createElement('i')));
  function show() {
    const s = steps[cur];
    ['D', 'X', 'G', 'K'].forEach(b => { const e = $('#b-' + b); e.classList.toggle('on', s.box.includes(b)); e.classList.toggle('dim', !s.box.includes(b)); });
    ['DX', 'DG', 'GX', 'GK'].forEach(a => $('#a-' + a).classList.toggle('on', s.arr.includes(a)));
    body.innerHTML = `<h4 class="steph">${s.t}</h4><p>${s.h}</p>`;
    $$('i', dots).forEach((d, i) => d.classList.toggle('on', i === cur));
    $('#step-prev').disabled = cur === 0; $('#step-next').disabled = cur === steps.length - 1;
  }
  $('#step-prev').addEventListener('click', () => { if (cur > 0) { cur--; show(); } });
  $('#step-next').addEventListener('click', () => { if (cur < steps.length - 1) { cur++; show(); } });
  $$('i', dots).forEach((d, i) => d.addEventListener('click', () => { cur = i; show(); }));
  show();
})();

/* -------------------------------------------------- Riemann map */
(function riemann() {
  const cu = $('#rm-u'), cg = $('#rm-g'); if (!cu || !cg) return;
  const BOUND = { quad: 0.5, cub: 1 / 3, expo: 1 };
  const MAPS = {
    quad: (z, a) => ({ v: [z[0] + a * (z[0] * z[0] - z[1] * z[1]), z[1] + 2 * a * z[0] * z[1]], d: [1 + 2 * a * z[0], 2 * a * z[1]] }),
    cub: (z, a) => { const z2 = cmul(z, z), z3 = cmul(z2, z); return { v: [z[0] + a * z3[0], z[1] + a * z3[1]], d: [1 + 3 * a * z2[0], 3 * a * z2[1]] }; },
    expo: (z, a) => { const e = cexp([a * z[0], a * z[1]]), v = cmul(z, e); return { v, d: cmul(e, [1 + a * z[0], a * z[1]]) }; }
  };
  const FS = {
    w2: w => ({ f: cmul(w, w), d: [2 * w[0], 2 * w[1]] }),
    w3: w => { const w2 = cmul(w, w); return { f: cmul(w2, w), d: [3 * w2[0], 3 * w2[1]] }; },
    e: w => { const e = cexp(w); return { f: e, d: e }; }
  };
  const label = () => { $('#rm-a-v').textContent = fmt(+$('#rm-a').value * BOUND[$('#rm-map').value], 3); };
  function draw() {
    const mk = $('#rm-map').value, phi = MAPS[mk], a = +$('#rm-a').value * BOUND[mk], fk = FS[$('#rm-f').value];
    label();
    const bd = []; for (let t = 0; t < 400; t++) bd.push(phi([Math.cos(2 * Math.PI * t / 400), Math.sin(2 * Math.PI * t / 400)], a).v);
    let ext = 0; for (const p of bd) ext = Math.max(ext, Math.abs(p[0]), Math.abs(p[1])); ext = Math.max(ext * 1.12, 1.2);
    const u = fit(cu, 1), g = fit(cg, 1);
    const NR = 70, NT = 140; let rhs = 0, jmax = 0;
    for (let i = 0; i < NR; i++) for (let j = 0; j < NT; j++) {
      const rho = (i + 0.5) / NR, th = 2 * Math.PI * (j + 0.5) / NT, z = [rho * Math.cos(th), rho * Math.sin(th)];
      const m = phi(z, a), jac = cabs2(m.d), fd = fk(m.v).d;
      rhs += cabs2(fd) * jac * rho / NR * 2 * Math.PI / NT; if (jac > jmax) jmax = jac;
    }
    { // left: disc coloured by |φ'|²
      const { ctx, w, h } = u, s = w / 2.4; ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
      const M = 60; for (let j = 0; j < M; j++) for (let i = 0; i < M; i++) {
        const x = -1.2 + (i + 0.5) / M * 2.4, y = 1.2 - (j + 0.5) / M * 2.4;
        if (x * x + y * y < 1) { ctx.fillStyle = heat(cabs2(phi([x, y], a).d) / jmax); ctx.fillRect(i * w / M, j * h / M, w / M + 1, h / M + 1); }
      }
      ctx.strokeStyle = '#ffffff55'; ctx.lineWidth = 1;
      for (const r of [0.25, 0.5, 0.75, 1]) { ctx.beginPath(); ctx.arc(w / 2, h / 2, r * s, 0, 7); ctx.stroke(); }
      for (let k = 0; k < 12; k++) { ctx.beginPath(); ctx.moveTo(w / 2, h / 2); ctx.lineTo(w / 2 + s * Math.cos(k * Math.PI / 6), h / 2 - s * Math.sin(k * Math.PI / 6)); ctx.stroke(); }
      ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif'; ctx.fillText('U, colour = |φ′|²', 10, h - 10);
    }
    let lhs = 0, area = 0;
    { // right: image
      const { ctx, w, h } = g, s = w / (2 * ext), X = x => w / 2 + x * s, Y = y => h / 2 - y * s;
      ctx.fillStyle = COL.bg; ctx.fillRect(0, 0, w, h);
      ctx.beginPath(); bd.forEach((p, i) => i ? ctx.lineTo(X(p[0]), Y(p[1])) : ctx.moveTo(X(p[0]), Y(p[1]))); ctx.closePath();
      ctx.fillStyle = '#1d3a44'; ctx.fill();
      ctx.strokeStyle = '#8ce0bb99'; ctx.lineWidth = 1;
      for (const r of [0.25, 0.5, 0.75, 1]) { ctx.beginPath(); for (let t = 0; t <= 120; t++) { const p = phi([r * Math.cos(t * Math.PI / 60), r * Math.sin(t * Math.PI / 60)], a).v; t ? ctx.lineTo(X(p[0]), Y(p[1])) : ctx.moveTo(X(p[0]), Y(p[1])); } ctx.stroke(); }
      ctx.strokeStyle = '#9fc5ff99';
      for (let k = 0; k < 12; k++) { ctx.beginPath(); for (let i = 0; i <= 30; i++) { const rr = i / 30, p = phi([rr * Math.cos(k * Math.PI / 6), rr * Math.sin(k * Math.PI / 6)], a).v; i ? ctx.lineTo(X(p[0]), Y(p[1])) : ctx.moveTo(X(p[0]), Y(p[1])); } ctx.stroke(); }
      ctx.strokeStyle = COL.gold; ctx.lineWidth = 2.2; ctx.beginPath(); bd.forEach((p, i) => i ? ctx.lineTo(X(p[0]), Y(p[1])) : ctx.moveTo(X(p[0]), Y(p[1]))); ctx.closePath(); ctx.stroke();
      ctx.fillStyle = COL.muted; ctx.font = '12px Inter, sans-serif'; ctx.fillText('G = φ(U)', 10, g.h - 10);
      const N = 220, cell = 2 * ext / N;
      for (let j = 0; j < N; j++) {
        const y = ext - (j + 0.5) * cell, xs = [];
        for (let k = 0; k < bd.length; k++) {
          const p = bd[k], q = bd[(k + 1) % bd.length];
          if ((p[1] > y) !== (q[1] > y)) xs.push(p[0] + (y - p[1]) / (q[1] - p[1]) * (q[0] - p[0]));
        }
        xs.sort((m, n) => m - n);
        for (let k = 0; k + 1 < xs.length; k += 2) {
          const i0 = Math.ceil((xs[k] + ext) / cell - 0.5), i1 = Math.floor((xs[k + 1] + ext) / cell - 0.5);
          for (let i = i0; i <= i1; i++) { const x = -ext + (i + 0.5) * cell; const d = fk([x, y]).d; lhs += cabs2(d) * cell * cell; area += cell * cell; }
        }
      }
    }
    const rel = Math.abs(lhs - rhs) / Math.max(1e-12, rhs);
    $('#rm-out').innerHTML = [
      `area(G)               = <span class="hl">${fmt(area)}</span>   (π = ${fmt(Math.PI)} for a = 0)`,
      `∫_G |f′|² dA          = <span class="hl">${fmt(lhs)}</span>   <span class="muted">(grid in the image)</span>`,
      `∫_U |(f∘φ)′|² dA      = <span class="hl">${fmt(rhs)}</span>   <span class="muted">(polar grid in the disc)</span>`,
      `relative difference   = <span class="${rel < 0.02 ? 'good' : 'bad'}">${(100 * rel).toFixed(2)} %</span>`].join('<br>');
  }
  ['rm-a'].forEach(id => bindRange(id, draw));
  $('#rm-map').addEventListener('change', draw); $('#rm-f').addEventListener('change', draw);
  REDRAW.push(draw); draw();
})();
