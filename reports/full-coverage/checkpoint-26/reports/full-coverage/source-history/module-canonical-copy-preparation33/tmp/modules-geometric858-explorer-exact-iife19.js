    (function () {
      var el = function (id) { return document.getElementById(id); };
      var mapSel = el('p0-map'), parS = el('p0-par'), x0S = el('p0-x0'), nS = el('p0-n'), gS = el('p0-g'), TS = el('p0-T');
      var TOL = 1e-6, KMAX = 100000, W = 360, H = 300, PL = 46, PR = 10, PT = 12, PB = 34;
      var MAPS = {
        affine: {par: 'slope a', p: [-1.2, 1.2, 0.005, 0.5], x: [-2, 6, 0.01, 0], g: function (x, a) { return a * x + 1; }},
        cos: {x: [-3, 3, 0.01, 1], g: function (x) { return Math.cos(x); }},
        logistic: {par: 'growth r', p: [0.5, 4, 0.01, 2.8], x: [0, 1, 0.005, 0.1], g: function (x, r) { return r * x * (1 - x); }},
        slow: {x: [-2, 2, 0.01, 1], g: function (x) { return x / (1 + x * x); }}
      };
      function f3(v) {
        var a = Math.abs(v);
        if (a !== 0 && (a < 1e-3 || a >= 1e5)) return v.toExponential(2).replace(/e\+?(-?)(\d+)/, function (m, s, d) { return '&middot;10<sup>' + (s ? '&minus;' : '') + d + '</sup>'; });
        return String(Math.round(v * 1e4) / 1e4);
      }
      // One run: iterates, x*, contraction factor L where Banach applies (from index k0), iteration counts, note
      function analyze(key, p, x0, N) {
        var g = function (x) { return MAPS[key].g(x, p); }, xs = [x0], k, x = x0, q, per = null;
        for (k = 0; k < N; k++) { x = g(x); xs.push(x); }
        var R = {xs: xs, xstar: null, L: null, k0: 0, note: '', conv: false, kAct: null, stays: false, kBound: null};
        if (key === 'affine') {
          if (Math.abs(1 - p) < 1e-12) { R.note = 'g(x) = x + 1 has no fixed point (L = 1): x<sub>k</sub> = x₀ + k.'; return R; }
          R.xstar = 1 / (1 - p);
          if (Math.abs(p) < 1) { R.L = Math.abs(p); R.conv = true; R.note = 'A contraction on ℝ with L = |a|.' + (p >= 0 ? ' The bound is exact; from x₀ = 0 the iterates are the sums 1 + a + … + a<sup>k−1</sup>.' : ' For a &lt; 0 the staircase is a spiral and the bound is (1 + |a|)/(1 − |a|) times too large.'); }
          else R.note = Math.abs(p + 1) < 1e-12 ? 'L = 1: the iterates alternate between x₀ and 1 − x₀' + (Math.abs(x0 - R.xstar) < 1e-12 ? ' (here both equal x*).' : '.') : '|a| &gt; 1: x* repels and the iterates run away.';
        } else if (key === 'cos') {
          x = 1; for (k = 0; k < 200; k++) x = Math.cos(x);
          R.xstar = x; R.L = Math.sin(1); R.conv = true; R.k0 = 2;
          for (k = 0; k <= Math.min(2, N); k++) if (xs[k] >= Math.cos(1) - 1e-12 && xs[k] <= 1 + 1e-12) { R.k0 = k; break; }
          R.note = 'cos maps J = [cos 1, 1] into itself with |g′| ≤ sin 1 = 0.841: Banach applies on J from k₀ = ' + R.k0 + '. Near x* the slope is only 0.674, so the bound is pessimistic.';
        } else if (key === 'logistic') {
          if (p <= 1 + 1e-12) {
            R.xstar = 0; R.conv = true;
            if (p < 1 - 1e-12) { R.L = p; R.note = 'For r &lt; 1, g contracts [0, 1] with L = r; fixed point 0.'; }
            else R.note = 'At r = 1, g′(0) = 1: no L &lt; 1, sublinear convergence to 0.';
          } else {
            R.xstar = 1 - 1 / p; q = Math.abs(2 - p);
            R.note = 'max |g′| = r ≥ 1 on [0, 1]: no contraction, Banach does not apply. Local rate at x* = 1 − 1/r: |2 − r| = ' + f3(q) + '. ';
            if (q < 1 - 1e-9) { R.conv = true; R.note += q < 1e-9 ? 'It is 0: quadratic convergence.' : 'Below 1: x* attracts nearby starts.'; }
            else if (q <= 1 + 1e-9) { R.conv = true; R.note += 'Marginal: sublinear convergence.'; }
            else {
              var z = x0, h = [], P, j, ok;
              for (k = 0; k < 4000; k++) { z = p * z * (1 - z); h.push(z); }
              for (P = 1; P <= 64 && per === null; P++) { ok = true; for (j = 0; j < 3 * P && ok; j++) if (Math.abs(h[3999 - j] - h[3999 - j - P]) > 1e-7) ok = false; if (ok) per = P; }
              R.note += 'Above 1: x* repels; ' + (per === 1 ? 'the simulated iterates became constant (at ' + f3(h[3999]) + (Math.abs(h[3999] - R.xstar) <= TOL ? ' = x*' : ', not x*') + ').' : per ? 'an approximate period-' + per + ' pattern was detected.' : 'no approximate cycle of period ≤ 64 was detected in this simulation (this does not by itself establish chaos).');
            }
            if (x0 === 0 || x0 === 1) { R.conv = false; R.note += ' Here x₀ lands on the fixed point 0.'; }
          }
        } else {
          R.xstar = 0; R.conv = true;
          R.note = '|g(x)| &lt; |x|, so x<sub>k</sub> → 0, but g′(0) = 1: no L &lt; 1 near 0; the error decays like 1/√(2k).';
        }
        if (R.xstar !== null) { // first k with |x_k − x*| ≤ TOL by direct simulation, whatever the stability label R.conv says
          x = x0;
          for (k = 0; k <= KMAX; k++) {
            if (Math.abs(x - R.xstar) <= TOL) { R.kAct = k; R.stays = R.conv || g(x) === x; break; }
            x = g(x);
          }
        }
        if (R.L !== null && R.k0 < N) {
          R.d = Math.abs(xs[R.k0 + 1] - xs[R.k0]);
          R.kBound = R.d === 0 ? R.k0 : R.L === 0 ? R.k0 + 1 : R.k0 + Math.max(0, Math.ceil(Math.log(R.d / ((1 - R.L) * TOL)) / Math.log(1 / R.L) - 1e-12));
        }
        return R;
      }
      function step(span, n) { var r = span / n, m = Math.pow(10, Math.floor(Math.log(r) / Math.LN10)); r /= m; return m * (r < 1.5 ? 1 : r < 3 ? 2 : r < 7 ? 5 : 10); }
      function cl(v) { return Math.max(-1e5, Math.min(1e5, v)).toFixed(1); }
      function ln(x1, y1, x2, y2, st, ex) { return '<line x1="' + x1 + '" y1="' + y1 + '" x2="' + x2 + '" y2="' + y2 + '" stroke="' + st + '"' + (ex || '') + '/>'; }
      function ci(x, y, r, ex) { return '<circle cx="' + x + '" cy="' + y + '" r="' + r + '" ' + ex + '/>'; }
      function pl(pts, st, ex) { return '<polyline points="' + pts.join(' ') + '" fill="none" stroke="' + st + '" ' + ex + '/>'; }
      function tx(x, y, t, an, c, fs) { return '<text x="' + x + '" y="' + y + '" font-size="' + (fs || 10) + '" fill="' + (c || '#666') + '" text-anchor="' + (an || 'middle') + '">' + t + '</text>'; }
      function frame(id) {
        var r = 'x="' + PL + '" y="' + PT + '" width="' + (W - PL - PR) + '" height="' + (H - PT - PB) + '"';
        return '<defs><clipPath id="' + id + '"><rect ' + r + '/></clipPath></defs><rect ' + r + ' fill="none" stroke="#bbb"/>';
      }
      function drawCob(R, key, p) {
        var xs = R.xs, lo = Infinity, hi = -Infinity, i, v, s, d, pts = [];
        if (key === 'logistic') { lo = -0.05; hi = 1.05; }
        else {
          for (i = 0; i < xs.length; i++) if (Math.abs(xs[i]) <= 1e4) { lo = Math.min(lo, xs[i]); hi = Math.max(hi, xs[i]); }
          if (R.xstar !== null) { lo = Math.min(lo, R.xstar); hi = Math.max(hi, R.xstar); }
          if (hi - lo < 1) { v = (lo + hi) / 2; lo = v - 0.5; hi = v + 0.5; }
          v = 0.08 * (hi - lo); lo -= v; hi += v;
        }
        var sx = function (u) { return cl(PL + (u - lo) / (hi - lo) * (W - PL - PR)); }, sy = function (u) { return cl(H - PB - (u - lo) / (hi - lo) * (H - PT - PB)); };
        s = frame('p0-cclip'); d = step(hi - lo, 5);
        for (v = Math.ceil(lo / d) * d; v <= hi + 1e-9; v += d) {
          var lb = Math.abs(v) < 1e-9 ? '0' : String(Math.round(v * 1000) / 1000);
          s += ln(sx(v), PT, sx(v), H - PB, '#f0f0f0') + ln(PL, sy(v), W - PR, sy(v), '#f0f0f0') + tx(sx(v), H - PB + 14, lb) + tx(PL - 5, +sy(v) + 3, lb, 'end');
        }
        s += '<g clip-path="url(#p0-cclip)">' + ln(sx(lo), sy(lo), sx(hi), sy(hi), '#9e9e9e');
        for (i = 0; i <= 240; i++) { v = lo + (hi - lo) * i / 240; pts.push(sx(v) + ',' + sy(MAPS[key].g(v, p))); }
        s += pl(pts, '#1565c0', 'stroke-width="1.8"');
        d = 'M' + sx(xs[0]) + ' ' + sy(xs[0]);
        for (i = 0; i < xs.length - 1 && isFinite(xs[i + 1]) && Math.abs(xs[i + 1]) <= 1e6; i++) d += ' L' + sx(xs[i]) + ' ' + sy(xs[i + 1]) + ' L' + sx(xs[i + 1]) + ' ' + sy(xs[i + 1]);
        s += '<path d="' + d + '" fill="none" stroke="#e67e22" stroke-width="1.3"/>' + ci(sx(xs[0]), sy(xs[0]), 3.5, 'fill="#e67e22"');
        if (R.xstar !== null) s += ci(sx(R.xstar), sy(R.xstar), 4.5, 'fill="none" stroke="#2e7d32" stroke-width="2"');
        el('p0-cob').innerHTML = s + '</g>' + tx(W - PR, H - 4, 'x', 'end', '#444', 11) + tx(4, PT + 8, 'g(x)', 'start', '#444', 11);
      }
      function drawErr(R, N) {
        var s = frame('p0-eclip'), i, e, v, pts = [], bnd = [], y0 = Infinity, y1 = -Infinity;
        var add = function (arr, k, val) { if (val > 1e-16 && isFinite(val)) { val = Math.log(val) / Math.LN10; arr.push([k, val]); y0 = Math.min(y0, val); y1 = Math.max(y1, val); } };
        if (R.xstar === null) { el('p0-err').innerHTML = s + tx(W / 2, H / 2, 'no fixed point: nothing to converge to', 'middle', '#c62828', 12); return; }
        for (i = 0; i <= N; i++) add(pts, i, Math.abs(R.xs[i] - R.xstar));
        if (R.L !== null && R.d > 0) for (i = R.k0; i <= N; i++) add(bnd, i, Math.pow(R.L, i - R.k0) * R.d / (1 - R.L));
        if (!pts.length && !bnd.length) { el('p0-err').innerHTML = s + tx(W / 2, H / 2, 'x₀ is already the fixed point', 'middle', '#2e7d32', 12); return; }
        y0 = Math.max(-16, Math.floor(y0)); y1 = Math.max(y0 + 2, Math.ceil(y1));
        var sx = function (u) { return cl(PL + u / N * (W - PL - PR)); }, sy = function (u) { return cl(H - PB - (u - y0) / (y1 - y0) * (H - PT - PB)); };
        for (v = y0; v <= y1; v += Math.max(1, Math.ceil((y1 - y0) / 6))) s += ln(PL, sy(v), W - PR, sy(v), '#f0f0f0') + tx(PL - 5, +sy(v) + 3, '10<tspan dy="-4" font-size="8">' + String(v).replace('-', '&minus;') + '</tspan>', 'end');
        for (v = 0, e = Math.max(1, step(N, 5)); v <= N; v += e) s += tx(sx(v), H - PB + 14, v);
        s += '<g clip-path="url(#p0-eclip)">';
        if (bnd.length) s += pl(bnd.map(function (b) { return sx(b[0]) + ',' + sy(b[1]); }), '#e67e22', 'stroke-width="1.6" stroke-dasharray="5,4"');
        pts.forEach(function (q) { s += ci(sx(q[0]), sy(q[1]), 2.4, 'fill="#1565c0"'); });
        el('p0-err').innerHTML = s + '</g>' + tx(W - PR, H - 4, 'k', 'end', '#444', 11) + tx(W - PR - 4, PT + 13, '|x<tspan dy="3" font-size="8">k</tspan><tspan dy="-3"> − x*|</tspan>', 'end', '#444', 11);
      }
      function setMap(key) {
        var M = MAPS[key];
        parS.disabled = !M.par; el('p0-par-name').textContent = M.par || 'no parameter';
        if (M.par) { parS.min = M.p[0]; parS.max = M.p[1]; parS.step = M.p[2]; parS.value = M.p[3]; }
        x0S.min = M.x[0]; x0S.max = M.x[1]; x0S.step = M.x[2]; x0S.value = M.x[3];
      }
      function update() {
        var key = mapSel.value, M = MAPS[key], p = M.par ? +parS.value : 0, x0 = +x0S.value, N = +nS.value, R, h;
        el('p0-par-val').textContent = M.par ? p.toFixed(M.p[2] < 0.01 ? 3 : 2) : '–';
        el('p0-x0-val').textContent = x0.toFixed(M.x[2] < 0.01 ? 3 : 2);
        el('p0-n-val').textContent = N;
        R = analyze(key, p, x0, N);
        if (R.xstar === null) h = 'Fixed point: <b>none</b>.';
        else {
          h = 'Fixed point x* = <b>' + f3(R.xstar) + '</b>; x<sub>' + N + '</sub> = ' + f3(R.xs[N]) + ', error <b>' + f3(Math.abs(R.xs[N] - R.xstar)) + '</b>.';
          if (R.d !== undefined) h += ' L = ' + f3(R.L) + ', a priori bound ' + f3(Math.pow(R.L, N - R.k0) * R.d / (1 - R.L)) + '.';
          h += '<br>Iterations to error ≤ 10<sup>−6</sup>: ' + (R.kAct === null ? (R.conv ? 'over ' + KMAX + (key === 'slow' ? ' (about 5·10<sup>11</sup>)' : '') : '<b>not reached</b> within ' + KMAX) : '<b>' + R.kAct + '</b>' + (R.conv ? ' needed' : R.stays ? ' (then the orbit stays put)' : ' to come that close once (x* repels, so the orbit leaves again)'));
          if (R.kBound !== null) h += ', <b>' + R.kBound + '</b> guaranteed by the bound';
          h += '.';
        }
        el('p0-info').innerHTML = h + '<br><span style="color:#555;">' + R.note + '</span>';
        drawCob(R, key, p); drawErr(R, N);
      }
      function drawGeo() {
        var gm = +gS.value, T = +TS.value, gT = Math.pow(gm, T), lim = 1 / (1 - gm), W2 = 560, H2 = 240, L2 = 40, R2 = 12, T2 = 12, B2 = 32, t, v, a = [], b = [];
        var T99 = gm === 0 ? 1 : Math.ceil(Math.log(0.01) / Math.log(gm) - 1e-12), Ts = Math.ceil(Math.log(100) / (1 - gm) - 1e-12), Xm = Math.min(300, Math.max(20, T + 5, T99 + 5));
        el('p0-g-val').textContent = gm.toFixed(3); el('p0-T-val').textContent = T;
        el('p0-ginfo').innerHTML = 'Limit 1/(1 − γ) = <b>' + f3(lim) + '</b>. S<sub>T</sub> = (1 − γ<sup>T</sup>)/(1 − γ) = <b>' + f3((1 - gT) * lim) + '</b> (' + (100 * (1 - gT)).toFixed(1) + '% of the limit), tail γ<sup>T</sup>/(1 − γ) = ' + f3(gT * lim) + '. 99% needs T ≥ <b>' + T99 + '</b>; the rule T ≥ ln(100)/(1 − γ) gives ' + Ts + '.';
        var sx = function (u) { return (L2 + u / Xm * (W2 - L2 - R2)).toFixed(1); }, sy = function (u) { return (H2 - B2 - u / 1.05 * (H2 - T2 - B2)).toFixed(1); };
        var s = '<rect x="' + L2 + '" y="' + T2 + '" width="' + (W2 - L2 - R2) + '" height="' + (H2 - T2 - B2) + '" fill="none" stroke="#bbb"/>';
        [0, 0.25, 0.5, 0.75, 1].forEach(function (u) { s += ln(L2, sy(u), W2 - R2, sy(u), '#f0f0f0') + tx(L2 - 5, +sy(u) + 3, u, 'end'); });
        for (v = 0, t = step(Xm, 7); v <= Xm; v += t) s += tx(sx(v), H2 - B2 + 14, v);
        for (t = 0; t <= Xm; t++) { a.push(sx(t) + ',' + sy(1 - Math.pow(gm, t))); b.push(sx(t) + ',' + sy(Math.pow(gm, t))); }
        s += pl(a, '#1565c0', 'stroke-width="2"') + pl(b, '#00838f', 'stroke-width="2"');
        s += ln(sx(T), T2, sx(T), H2 - B2, '#e67e22', ' stroke-width="1.6"') + ci(sx(T), sy(1 - gT), 3.5, 'fill="#e67e22"') + tx(+sx(T) + 4, T2 + 12, 'T', 'start', '#e67e22', 11);
        s += T99 <= Xm ? ln(sx(T99), T2, sx(T99), H2 - B2, '#7b1fa2', ' stroke-width="1.4" stroke-dasharray="5,4"') + tx(+sx(T99) + 4, T2 + 26, '99%', 'start', '#7b1fa2', 11) : tx(W2 - R2 - 6, H2 - B2 - 8, '99% only at T = ' + T99 + ' (off the plot)', 'end', '#7b1fa2', 11);
        el('p0-geo').innerHTML = s + tx(W2 - R2, H2 - 4, 't', 'end', '#444', 11);
      }
      mapSel.addEventListener('change', function () { setMap(mapSel.value); update(); });
      [parS, x0S, nS].forEach(function (s) { s.addEventListener('input', update); });
      [gS, TS].forEach(function (s) { s.addEventListener('input', drawGeo); });
      el('p0-sync').addEventListener('click', function () {
        mapSel.value = 'affine'; setMap('affine');
        parS.value = gS.value; x0S.value = 0; nS.value = Math.max(3, Math.min(80, +TS.value));
        update();
      });
      setMap('affine'); update(); drawGeo();
    })();