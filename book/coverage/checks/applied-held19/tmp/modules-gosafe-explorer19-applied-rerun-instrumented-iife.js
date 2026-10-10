    (function () {
      'use strict';
      var svg = document.getElementById('gs-svg');
      if (!svg) return;
      // toy system: x_{k+1} = x_k + dt [-(1+kappa) x_k + kappa rho + w], walls at |x| = 1, start at x0 = 0
      var N = 25, P = N * N, DT = 0.0025, K = 1200, W = 0.6, X0 = 0.0, ELL = 0.12, SN = 0.02;
      var EPS = 0.2, NMAX = 160, NGE = 6, BSTRIDE = 30, TIE = 1e-3;
      var grid = [];
      for (var i = 0; i < N; i++) for (var j = 0; j < N; j++) grid.push({ a1: i / (N - 1), a2: j / (N - 1) });
      function sq(v) { return v * v; }
      function rho(a1) { return 0.8 * (1 + Math.cos(4 * Math.PI * a1)); }
      function kap(a2) { return 3 + 5 * a2; }
      function stepX(x, p) { var g = grid[p]; return x + DT * (-(1 + kap(g.a2)) * x + kap(g.a2) * rho(g.a1) + W); }
      function gbar(x) { return 1 - Math.abs(x); }

      // --- true objective and trajectory-minimum constraint on the grid (closed form) ---
      // From x0 = 0 the state rises monotonically to x_eq > 0, so the infimum of gbar along the
      // infinite-horizon trajectory is g(a) = 1 - max(|x0|, x_eq(a)) (the 1200-step rollouts differ by < 1e-5).
      var gTrue = new Float64Array(P), fTrue = new Float64Array(P);
      for (var p = 0; p < P; p++) {
        var a = grid[p], xeq = (kap(a.a2) * rho(a.a1) + W) / (1 + kap(a.a2));
        gTrue[p] = 1 - Math.max(Math.abs(X0), xeq);
        fTrue[p] = Math.exp(-(sq(a.a1 - 0.75) + sq(a.a2 - 0.60)) / (2 * sq(0.13))) + 0.6 * Math.exp(-(sq(a.a1 - 0.25) + sq(a.a2 - 0.40)) / (2 * sq(0.13))) + 0.1 * a.a2;
      }
      var dist = new Float32Array(P * P);
      for (p = 0; p < P; p++) for (var q = 0; q < P; q++) dist[p * P + q] = Math.sqrt(sq(grid[p].a1 - grid[q].a1) + sq(grid[p].a2 - grid[q].a2));
      var LA_TRUE = 0;
      for (p = 0; p < P; p++) for (q = p + 1; q < P; q++) { var r = Math.abs(gTrue[p] - gTrue[q]) / dist[p * P + q]; if (r > LA_TRUE) LA_TRUE = r; }
      var XI_TRUE = 0; // largest one-step motion over the grid for |x| <= 1.2
      for (p = 0; p < P; p++) { var kk = kap(grid[p].a2), rr = rho(grid[p].a1); var mv = DT * ((1 + kk) * 1.2 + Math.abs(kk * rr + W)); if (mv > XI_TRUE) XI_TRUE = mv; }
      var SEED_P = 6 * N + 12; // a = (0.25, 0.5), centre of island A
      var OPT_P = -1, fOpt = -Infinity;
      for (p = 0; p < P; p++) if (gTrue[p] >= 0 && fTrue[p] > fOpt) { fOpt = fTrue[p]; OPT_P = p; }
      function kern(p, q) { var d = dist[p * P + q]; return Math.exp(-d * d / (2 * ELL * ELL)); }

      // --- controls ---
      var el = function (id) { return document.getElementById(id); };
      var ctrl = { mode: 'gosafeopt', beta: 3, la: Math.ceil(LA_TRUE * 2) / 2, lx: 1, xi: 1, bc: true };
      el('gs-la').value = ctrl.la;
      function fmt(v, d) { return Number(v).toFixed(d === undefined ? 2 : d); }
      function readControls() {
        ctrl.mode = el('gs-mode').value;
        ctrl.beta = parseFloat(el('gs-beta').value);
        ctrl.la = parseFloat(el('gs-la').value);
        ctrl.lx = parseFloat(el('gs-lx').value);
        ctrl.xi = parseFloat(el('gs-xi').value);
        ctrl.bc = el('gs-bc').checked;
        el('gs-mode-val').textContent = ctrl.mode === 'safeopt' ? 'SafeOpt' : 'GoSafeOpt';
        el('gs-beta-val').textContent = fmt(ctrl.beta, 1);
        el('gs-la-val').textContent = fmt(ctrl.la, 1) + ' (true ' + fmt(LA_TRUE, 1) + ')';
        el('gs-lx-val').textContent = fmt(ctrl.lx, 1);
        el('gs-xi-val').textContent = fmt(ctrl.xi, 1) + ' (= ' + fmt(ctrl.xi * XI_TRUE, 3) + ')';
      }

      // --- seeded noise ---
      var seedVal = 12345, rng;
      function mulberry32(s) { return function () { s |= 0; s = s + 0x6D2B79F5 | 0; var t = Math.imul(s ^ s >>> 15, 1 | s); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
      function gauss() { var u = 1 - rng(), v = rng(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); }

      // --- algorithm state ---
      var Xd, yf, yg, lf, uf, lg, ug, S, E, isG, isM, Xfail, B, n, phase, lseCount, geCount, nLSE, done, violations, backups, evals, lastRoll, logLines, converged;

      function gpUpdate() { // exact GP posterior (Cholesky) for f and g; monotone (contained) confidence bounds
        var nd = Xd.length, L = new Float64Array(nd * nd), beta = ctrl.beta;
        for (var i = 0; i < nd; i++) for (var j = 0; j <= i; j++) {
          var s = kern(Xd[i], Xd[j]) + (i === j ? SN * SN + 1e-8 : 0);
          for (var m = 0; m < j; m++) s -= L[i * nd + m] * L[j * nd + m];
          L[i * nd + j] = (i === j) ? Math.sqrt(Math.max(s, 1e-12)) : s / L[j * nd + j];
        }
        function solveL(b) { var z = new Float64Array(nd); for (var i = 0; i < nd; i++) { var s = b[i]; for (var m = 0; m < i; m++) s -= L[i * nd + m] * z[m]; z[i] = s / L[i * nd + i]; } return z; }
        function solveLT(z) { var x = new Float64Array(nd); for (var i = nd - 1; i >= 0; i--) { var s = z[i]; for (var m = i + 1; m < nd; m++) s -= L[m * nd + i] * x[m]; x[i] = s / L[i * nd + i]; } return x; }
        var af = solveLT(solveL(yf)), ag = solveLT(solveL(yg)), kv = new Float64Array(nd);
        for (var p = 0; p < P; p++) {
          for (i = 0; i < nd; i++) kv[i] = kern(p, Xd[i]);
          var mf = 0, mg = 0; for (i = 0; i < nd; i++) { mf += kv[i] * af[i]; mg += kv[i] * ag[i]; }
          var v = solveL(kv), vv = 0; for (i = 0; i < nd; i++) vv += v[i] * v[i];
          var sd = Math.sqrt(Math.max(1 - vv, 0));
          lf[p] = Math.max(lf[p], mf - beta * sd); uf[p] = Math.min(uf[p], mf + beta * sd);
          lg[p] = Math.max(lg[p], mg - beta * sd); ug[p] = Math.min(ug[p], mg + beta * sd);
        }
      }
      function updateSafe() { // eq. 8: Lipschitz expansion from certified points
        var newS = new Uint8Array(P), changed = false;
        for (var q = 0; q < P; q++) {
          if (!S[q]) continue; newS[q] = 1; var l = lg[q]; if (!(l >= 0)) continue;
          var reach = l / ctrl.la;
          for (var p = 0; p < P; p++) if (!newS[p] && dist[q * P + p] <= reach) newS[p] = 1;
        }
        for (p = 0; p < P; p++) if (newS[p] !== S[p]) { changed = true; break; }
        S = newS; return changed;
      }
      function updateGM() { // expanders (Def. D.1) and maximisers (Def. D.2)
        isG = new Uint8Array(P); isM = new Uint8Array(P);
        var maxLf = -Infinity; for (var p = 0; p < P; p++) if (S[p] && lf[p] > maxLf) maxLf = lf[p];
        for (p = 0; p < P; p++) {
          if (!S[p]) continue;
          if (uf[p] >= maxLf) isM[p] = 1;
          var u = ug[p]; if (!(u >= 0)) continue; var reach = u / ctrl.la;
          for (var q = 0; q < P; q++) if (!S[q] && dist[p * P + q] <= reach) { isG[p] = 1; break; }
        }
      }
      function boundary(x) { // Algorithm 3 and eq. 12
        var Lx = ctrl.lx, Xi = ctrl.xi * XI_TRUE, best = -Infinity, bp = -1, ok = false;
        for (var b = 0; b < B.length; b++) {
          var l = lg[B[b].p]; if (!isFinite(l)) continue;
          var d = Math.abs(x - B[b].x);
          if (l >= Lx * (d + Xi)) ok = true;
          var margin = l - Lx * d; if (margin > best) { best = margin; bp = B[b].p; }
        }
        return { trigger: !ok, p: bp, margin: best };
      }
      function rollout(p, useBC) {
        var xs = [X0], x = X0, cur = p, trig = -1, pb = -1, viol = false;
        for (var k = 0; k < K; k++) {
          if (useBC && ctrl.bc && trig < 0) { var bc = boundary(x); if (bc.trigger && bc.p >= 0) { trig = k; pb = bc.p; cur = pb; } }
          if (gbar(x) < 0) viol = true;
          x = stepX(x, cur); xs.push(x);
        }
        if (gbar(x) < 0) viol = true;
        return { p: p, xs: xs, trig: trig, pb: pb, viol: viol };
      }
      function addBackups(roll) { for (var k = 0; k < roll.xs.length; k += BSTRIDE) B.push({ p: roll.p, x: roll.xs[k] }); B.push({ p: roll.p, x: roll.xs[roll.xs.length - 1] }); }
      function observe(p) { Xd.push(p); yf.push(fTrue[p] + SN * gauss()); yg.push(gTrue[p] + SN * gauss()); }
      function addLog(s) { logLines.push('n = ' + n + ': ' + s); if (logLines.length > 6) logLines.shift(); }
      function label(p) { return '(' + fmt(grid[p].a1) + ', ' + fmt(grid[p].a2) + ')'; }
      function pickMax(score) { // argmax; scores within TIE of the maximum count as ties and are broken by the seeded generator
        var best = -Infinity, vals = new Float64Array(P);
        for (var p = 0; p < P; p++) { var s = score(p); vals[p] = (s === null) ? -Infinity : s; if (vals[p] > best) best = vals[p]; }
        if (best === -Infinity) return -1;
        var cands = []; for (p = 0; p < P; p++) if (vals[p] >= best - TIE) cands.push(p);
        return cands[Math.floor(rng() * cands.length) % cands.length];
      }
      function hasGE() { for (var p = 0; p < P; p++) if (!S[p] && !E[p]) return true; return false; }
      function recheckFail() { // Algorithm 4: re-evaluate the fail set against the current backups before choosing or ruling out GE
        for (var i = Xfail.length - 1; i >= 0; i--) { if (!boundary(Xfail[i].x).trigger) { E[Xfail[i].p] = 0; Xfail.splice(i, 1); } }
      }

      function lseStep() { // Algorithm 1 with eq. 9 and the convergence test eq. 10
        var bp = pickMax(function (p) { return (isG[p] || isM[p]) ? Math.max(uf[p] - lf[p], ug[p] - lg[p]) : null; });
        if (bp < 0) { converged = true; return; }
        var roll = rollout(bp, false);
        if (roll.viol) violations++;
        addBackups(roll); observe(bp); evals.push({ p: bp, kind: 'lse' });
        n++; lseCount++; lastRoll = roll; lastRoll.kind = 'LSE';
        gpUpdate(); var changed = updateSafe(); updateGM();
        var wmax = -Infinity;
        for (var p = 0; p < P; p++) if (isG[p] || isM[p]) wmax = Math.max(wmax, Math.max(uf[p] - lf[p], ug[p] - lg[p]));
        converged = (wmax < EPS) && !changed;
        addLog('LSE at a = ' + label(bp) + ', true g = ' + fmt(gTrue[bp]) + (roll.viol ? ' &mdash; VIOLATION (wall hit)' : '') + '; |S| = ' + count(S) + (converged ? '; LSE converged' : ''));
      }
      function geStep() { // Algorithm 2 with eq. 11; fail-set re-evaluation as in Algorithm 4
        recheckFail();
        var bp = pickMax(function (p) { return (!S[p] && !E[p]) ? ug[p] - lg[p] : null; });
        if (bp < 0) return false;
        var roll = rollout(bp, true);
        if (roll.viol) violations++;
        n++; geCount++; lastRoll = roll; lastRoll.kind = 'GE';
        if (roll.trig >= 0) {
          backups++; E[bp] = 1; Xfail.push({ p: bp, x: roll.xs[roll.trig] }); evals.push({ p: bp, kind: 'gefail' });
          addLog('GE at a = ' + label(bp) + ': backup ' + label(roll.pb) + ' triggered at k = ' + roll.trig + ' (x = ' + fmt(roll.xs[roll.trig]) + '); a added to the fail set E');
          return false;
        }
        observe(bp); evals.push({ p: bp, kind: 'geok' });
        if (ctrl.bc) { addBackups(roll); S[bp] = 1; gpUpdate(); lg[bp] = Math.max(lg[bp], 0); }
        else { gpUpdate(); if (yg[yg.length - 1] >= 0) { S[bp] = 1; addBackups(roll); } }
        updateSafe(); updateGM(); converged = false;
        addLog('GE at a = ' + label(bp) + ' completed without trigger' + (ctrl.bc ? '' : ' (boundary condition OFF: unsafe evaluation)') + ', true g = ' + fmt(gTrue[bp]) + (roll.viol ? ' &mdash; VIOLATION (wall hit)' : '') + '; new region added, back to LSE');
        return true;
      }
      function count(arr) { var c = 0; for (var p = 0; p < P; p++) c += arr[p]; return c; }

      function experiment() {
        if (done) return;
        readControls();
        if (ctrl.mode === 'safeopt') {
          if (converged) { done = true; addLog('SafeOpt converged: the safe set stopped growing and all widths are below &epsilon;.'); }
          else lseStep();
        } else {
          if (phase === 'LSE' && (converged || lseCount >= nLSE)) {
            recheckFail();
            if (hasGE()) { phase = 'GE'; geCount = 0; }
            else if (converged) { done = true; addLog('Done: LSE converged and no untested parameter is left outside S &cup; E.'); }
            else lseCount = 0;
          }
          if (!done) {
            if (phase === 'LSE') lseStep();
            else {
              var ok = geStep();
              if (ok) { phase = 'LSE'; lseCount = 0; nLSE = 8; }
              else if (geCount >= NGE || !hasGE()) { phase = 'LSE'; lseCount = 0; nLSE = Math.max(3, Math.floor(nLSE / 2)); }
            }
          }
        }
        if (n >= NMAX && !done) { done = true; addLog('Budget of ' + NMAX + ' experiments exhausted.'); }
        draw();
      }

      function reset() {
        readControls();
        rng = mulberry32(seedVal);
        Xd = []; yf = []; yg = [];
        lf = new Float64Array(P).fill(-Infinity); uf = new Float64Array(P).fill(Infinity);
        lg = new Float64Array(P).fill(-Infinity); ug = new Float64Array(P).fill(Infinity);
        lg[SEED_P] = 0;
        S = new Uint8Array(P); S[SEED_P] = 1; E = new Uint8Array(P); Xfail = []; B = [{ p: SEED_P, x: X0 }];
        n = 0; phase = 'LSE'; lseCount = 0; geCount = 0; nLSE = 8; done = false; violations = 0; backups = 0; evals = []; logLines = []; converged = false;
        var roll = rollout(SEED_P, false); addBackups(roll); observe(SEED_P); evals.push({ p: SEED_P, kind: 'lse' }); lastRoll = roll; lastRoll.kind = 'seed';
        gpUpdate(); updateSafe(); updateGM();
        addLog('Reset. Seed a&#8320; = ' + label(SEED_P) + ' evaluated; true L<sub>a</sub> = ' + fmt(LA_TRUE, 2) + ', &Xi; = ' + fmt(XI_TRUE, 3) + ', L<sub>x</sub> = 1.');
        draw();
      }

      // --- drawing ---
      function draw() {
        var s = '', CS = 12, OX = 30, OY = 22;
        for (var p = 0; p < P; p++) {
          var i = Math.floor(p / N), j = p % N, x = OX + i * CS, y = OY + (N - 1 - j) * CS, g = gTrue[p];
          var col = g >= 0 ? 'rgba(46,125,50,' + fmt(0.12 + 0.7 * Math.min(1, g / 0.9)) + ')' : 'rgba(198,40,40,' + fmt(0.18 + 0.6 * Math.min(1, -g / 0.5)) + ')';
          s += '<rect x="' + x + '" y="' + y + '" width="' + CS + '" height="' + CS + '" fill="' + col + '"/>';
          if (S[p]) s += '<rect x="' + (x + 1) + '" y="' + (y + 1) + '" width="' + (CS - 2) + '" height="' + (CS - 2) + '" fill="rgba(21,101,192,0.5)"/>';
        }
        function cx(p) { return OX + Math.floor(p / N) * CS + CS / 2; }
        function cy(p) { return OY + (N - 1 - (p % N)) * CS + CS / 2; }
        evals.forEach(function (e) {
          if (e.kind === 'lse') s += '<circle cx="' + cx(e.p) + '" cy="' + cy(e.p) + '" r="2.4" fill="#0d3c7a"/>';
          else if (e.kind === 'geok') s += '<circle cx="' + cx(e.p) + '" cy="' + cy(e.p) + '" r="3.6" fill="#7b1fa2" stroke="#fff" stroke-width="0.8"/>';
          else s += '<path d="M' + (cx(e.p) - 3) + ',' + (cy(e.p) - 3) + ' l6,6 m0,-6 l-6,6" stroke="#e67e22" stroke-width="1.8" fill="none"/>';
        });
        s += '<circle cx="' + cx(SEED_P) + '" cy="' + cy(SEED_P) + '" r="4.5" fill="#fff" stroke="#000" stroke-width="1.2"/>';
        var ox = cx(OPT_P), oy = cy(OPT_P);
        s += '<polygon points="' + [0, -6, 1.8, -1.8, 6, -1.8, 2.5, 1.2, 4, 6, 0, 3, -4, 6, -2.5, 1.2, -6, -1.8, -1.8, -1.8].map(function (v, idx) { return (idx % 2 ? oy : ox) + v; }).join(',') + '" fill="#f9a825" stroke="#000" stroke-width="0.8"/>';
        var bestP = -1, bestL = -Infinity;
        for (p = 0; p < P; p++) if (S[p] && lf[p] > bestL) { bestL = lf[p]; bestP = p; }
        if (bestP >= 0) s += '<circle cx="' + cx(bestP) + '" cy="' + cy(bestP) + '" r="6" fill="none" stroke="#000" stroke-width="1.6"/>';
        if (lastRoll && lastRoll.kind !== 'seed') s += '<rect x="' + (cx(lastRoll.p) - 6) + '" y="' + (cy(lastRoll.p) - 6) + '" width="12" height="12" fill="none" stroke="' + (lastRoll.kind === 'GE' ? '#7b1fa2' : '#0d3c7a') + '" stroke-width="1.5"/>';
        s += '<rect x="' + OX + '" y="' + OY + '" width="' + (N * CS) + '" height="' + (N * CS) + '" fill="none" stroke="#888"/>';
        s += '<text x="' + (OX + N * CS / 2) + '" y="' + (OY + N * CS + 14) + '" text-anchor="middle" font-size="10" fill="#555">a&#8321; (reference)  0 &rarr; 1</text>';
        s += '<text x="12" y="' + (OY + N * CS / 2) + '" text-anchor="middle" font-size="10" fill="#555" transform="rotate(-90,12,' + (OY + N * CS / 2) + ')">a&#8322; (gain)  0 &rarr; 1</text>';
        var ly = OY + N * CS + 30;
        s += '<circle cx="' + (OX + 6) + '" cy="' + ly + '" r="2.4" fill="#0d3c7a"/><text x="' + (OX + 12) + '" y="' + (ly + 3) + '" font-size="9" fill="#444">LSE</text>';
        s += '<circle cx="' + (OX + 46) + '" cy="' + ly + '" r="3.4" fill="#7b1fa2"/><text x="' + (OX + 52) + '" y="' + (ly + 3) + '" font-size="9" fill="#444">GE success</text>';
        s += '<path d="M' + (OX + 114) + ',' + (ly - 3) + ' l6,6 m0,-6 l-6,6" stroke="#e67e22" stroke-width="1.6" fill="none"/><text x="' + (OX + 124) + '" y="' + (ly + 3) + '" font-size="9" fill="#444">GE interrupted</text>';
        s += '<rect x="' + (OX + 196) + '" y="' + (ly - 5) + '" width="10" height="10" fill="rgba(21,101,192,0.5)"/><text x="' + (OX + 210) + '" y="' + (ly + 3) + '" font-size="9" fill="#444">safe set S&#8345;</text>';
        s += '<circle cx="' + (OX + 270) + '" cy="' + ly + '" r="5" fill="none" stroke="#000" stroke-width="1.4"/><text x="' + (OX + 278) + '" y="' + (ly + 3) + '" font-size="9" fill="#444">best guess</text>';

        // trajectory panel: state x over the samples of the last rollout, with the certified safe-state set
        var TX = 380, TW = 300, TY = 30, TH = 290, YLO = -1.05, YHI = 1.5;
        function tx(k) { return TX + TW * k / K; }
        function ty(v) { return TY + TH * (YHI - v) / (YHI - YLO); }
        s += '<rect x="' + TX + '" y="' + TY + '" width="' + TW + '" height="' + TH + '" fill="#fff" stroke="#888"/>';
        var ivs = [], Lx = ctrl.lx, Xi = ctrl.xi * XI_TRUE;
        for (var b = 0; b < B.length; b++) { var l = lg[B[b].p]; if (!isFinite(l)) continue; var rad = l / Lx - Xi; if (rad > 0) ivs.push([B[b].x - rad, B[b].x + rad]); }
        ivs.sort(function (u, v) { return u[0] - v[0]; });
        var merged = [];
        ivs.forEach(function (iv) { if (merged.length && iv[0] <= merged[merged.length - 1][1]) merged[merged.length - 1][1] = Math.max(merged[merged.length - 1][1], iv[1]); else merged.push([iv[0], iv[1]]); });
        merged.forEach(function (iv) { var lo = Math.max(YLO, iv[0]), hi = Math.min(YHI, iv[1]); if (hi > lo) s += '<rect x="' + TX + '" y="' + ty(hi) + '" width="' + TW + '" height="' + (ty(lo) - ty(hi)) + '" fill="rgba(46,125,50,0.16)"/>'; });
        [-1, 1].forEach(function (v) { s += '<line x1="' + TX + '" y1="' + ty(v) + '" x2="' + (TX + TW) + '" y2="' + ty(v) + '" stroke="#c62828" stroke-width="1.5" stroke-dasharray="6,3"/>'; });
        [-1, -0.5, 0, 0.5, 1, 1.5].forEach(function (v) { s += '<text x="' + (TX - 4) + '" y="' + (ty(v) + 3) + '" text-anchor="end" font-size="9" fill="#666">' + v + '</text>'; });
        [0, K / 3, 2 * K / 3, K].forEach(function (kk) { s += '<text x="' + tx(kk) + '" y="' + (TY + TH + 12) + '" text-anchor="middle" font-size="9" fill="#666">' + kk + '</text>'; });
        s += '<text x="' + (TX + TW / 2) + '" y="' + (TY + TH + 24) + '" text-anchor="middle" font-size="10" fill="#555">sample k (&Delta;t = 0.0025)</text>';
        s += '<text x="' + (TX + 4) + '" y="' + (ty(1) - 4) + '" font-size="9" fill="#c62828">wall x = +1</text>';
        s += '<text x="' + (TX + 4) + '" y="' + (ty(-1) - 4) + '" font-size="9" fill="#c62828">wall x = &minus;1</text>';
        if (lastRoll) {
          var xs = lastRoll.xs, t = lastRoll.trig, pre = '', post = '';
          for (var kk2 = 0; kk2 < xs.length; kk2++) { var pt = fmt(tx(kk2), 1) + ',' + fmt(ty(Math.max(YLO, Math.min(YHI, xs[kk2]))), 1); if (t < 0 || kk2 <= t) pre += pt + ' '; if (t >= 0 && kk2 >= t) post += pt + ' '; }
          s += '<polyline points="' + pre + '" fill="none" stroke="' + (lastRoll.kind === 'GE' ? '#7b1fa2' : '#1565c0') + '" stroke-width="2"/>';
          if (t >= 0) {
            s += '<polyline points="' + post + '" fill="none" stroke="#00838f" stroke-width="2"/>';
            s += '<line x1="' + tx(t) + '" y1="' + TY + '" x2="' + tx(t) + '" y2="' + (TY + TH) + '" stroke="#e67e22" stroke-width="1" stroke-dasharray="3,3"/>';
            s += '<circle cx="' + tx(t) + '" cy="' + ty(xs[t]) + '" r="4" fill="#e67e22"/>';
            s += '<text x="' + Math.min(tx(t) + 6, TX + TW - 90) + '" y="' + (TY + 12) + '" font-size="9" fill="#e67e22">backup at k = ' + t + '</text>';
          }
          var ttl = (lastRoll.kind === 'seed' ? 'seed' : lastRoll.kind) + ' rollout of a = ' + label(lastRoll.p) + (t >= 0 ? ' &rarr; a&#8347; = ' + label(lastRoll.pb) : '');
          s += '<text x="' + (TX + TW / 2) + '" y="' + (TY - 8) + '" text-anchor="middle" font-size="10" fill="#333">' + ttl + '</text>';
        }
        s += '<rect x="' + (TX + TW - 118) + '" y="' + (TY + TH - 16) + '" width="10" height="10" fill="rgba(46,125,50,0.35)"/><text x="' + (TX + TW - 104) + '" y="' + (TY + TH - 7) + '" font-size="9" fill="#444">certified states X&#8347;&#8345;</text>';
        svg.innerHTML = s;

        var regret = (bestP >= 0) ? fOpt - fTrue[bestP] : NaN;
        el('gs-info').innerHTML =
          '<span>experiments n = <strong>' + n + '</strong></span>' +
          '<span>phase: <strong>' + (done ? 'finished' : (ctrl.mode === 'safeopt' ? 'LSE' : phase)) + '</strong></span>' +
          '<span>|S| = <strong>' + count(S) + '</strong> of ' + P + '</span>' +
          '<span>|E| = <strong>' + count(E) + '</strong></span>' +
          '<span>backups stored: <strong>' + B.length + '</strong></span>' +
          '<span>backups triggered: <strong>' + backups + '</strong></span>' +
          '<span style="color:' + (violations > 0 ? '#c62828' : '#2e7d32') + '">violations: <strong>' + violations + '</strong></span>' +
          '<span>best guess f(&acirc;) = <strong>' + (bestP >= 0 ? fmt(fTrue[bestP]) : '&ndash;') + '</strong>, f* = ' + fmt(fOpt) + ', regret = <strong>' + (isNaN(regret) ? '&ndash;' : fmt(regret)) + '</strong></span>';
        el('gs-log').innerHTML = logLines.map(function (t) { return '<div>' + t + '</div>'; }).join('');
      }

      // --- wiring ---
      ['gs-beta', 'gs-la', 'gs-lx', 'gs-xi', 'gs-bc'].forEach(function (id) { el(id).addEventListener('input', function () { readControls(); if (lf) draw(); }); });
      el('gs-mode').addEventListener('change', function () { reset(); });
      el('gs-step').addEventListener('click', function () { experiment(); });
      el('gs-run10').addEventListener('click', function () { for (var i = 0; i < 10 && !done; i++) experiment(); });
      var runTimer = null;
      el('gs-runall').addEventListener('click', function () {
        if (runTimer) return;
        function chunk() { for (var i = 0; i < 4 && !done; i++) experiment(); if (!done) runTimer = setTimeout(chunk, 30); else runTimer = null; }
        chunk();
      });
      el('gs-reset').addEventListener('click', function () { if (runTimer) { clearTimeout(runTimer); runTimer = null; } reset(); });
      el('gs-reseed').addEventListener('click', function () { if (runTimer) { clearTimeout(runTimer); runTimer = null; } seedVal = (seedVal * 1103515245 + 12345) % 2147483647; reset(); });
      reset();

      globalThis.__explorerAudit={
        reset:reset,experiment:experiment,rollout:rollout,pickMax:pickMax,kern:kern,boundary:boundary,
        state:function(){return {settings:{N:N,P:P,DT:DT,K:K,W:W,X0:X0,ELL:ELL,SN:SN,EPS:EPS,NMAX:NMAX,NGE:NGE,BSTRIDE:BSTRIDE,TIE:TIE},
          ctrl:Object.assign({},ctrl),grid:grid.map(function(a){return Object.assign({},a)}),
          gTrue:Array.from(gTrue),fTrue:Array.from(fTrue),dist:Array.from(dist),LA_TRUE:LA_TRUE,XI_TRUE:XI_TRUE,
          SEED_P:SEED_P,OPT_P:OPT_P,fOpt:fOpt,Xd:Xd.slice(),yf:yf.slice(),yg:yg.slice(),
          lf:Array.from(lf),uf:Array.from(uf),lg:Array.from(lg),ug:Array.from(ug),S:Array.from(S),E:Array.from(E),
          B:B.map(function(a){return Object.assign({},a)}),n:n,phase:phase,lseCount:lseCount,geCount:geCount,nLSE:nLSE,
          done:done,violations:violations,backups:backups,evals:evals.map(function(a){return Object.assign({},a)}),
          lastRoll:lastRoll,logLines:logLines.slice(),converged:converged}}
      };
    })();