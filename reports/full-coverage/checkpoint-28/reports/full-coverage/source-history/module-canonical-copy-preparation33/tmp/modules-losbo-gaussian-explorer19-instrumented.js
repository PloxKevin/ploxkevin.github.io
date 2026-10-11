    // ---- shared numerics: SE kernel, Cholesky, GP posterior on a grid, seeded PRNG ----
    var STL = (function() {
      function mulberry32(a) { return function() { a |= 0; a = a + 0x6D2B79F5 | 0; var t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
      function chol(A) { var n = A.length, L = [], i, j, m, s; for (i = 0; i < n; i++) { L.push(new Array(n).fill(0)); }
        for (i = 0; i < n; i++) { for (j = 0; j <= i; j++) { s = A[i][j]; for (m = 0; m < j; m++) s -= L[i][m] * L[j][m];
          if (i === j) { L[i][i] = Math.sqrt(Math.max(s, 1e-12)); } else { L[i][j] = s / L[j][j]; } } } return L; }
      function fwd(L, b) { var n = L.length, y = new Array(n), i, m, s; for (i = 0; i < n; i++) { s = b[i]; for (m = 0; m < i; m++) s -= L[i][m] * y[m]; y[i] = s / L[i][i]; } return y; }
      function solve(L, b) { var n = L.length, y = fwd(L, b), x = new Array(n), i, m, s; for (i = n - 1; i >= 0; i--) { s = y[i]; for (m = i + 1; m < n; m++) s -= L[m][i] * x[m]; x[i] = s / L[i][i]; } return x; }
      // posterior mean/sd on grid for data (X,Y), SE kernel with length scale ell, nominal noise lam; also log det(I + K/lam)
      function posterior(grid, X, Y, ell, lam) {
        var t = X.length, N = grid.length, mu = new Array(N).fill(0), sd = new Array(N).fill(1), i, j, g;
        if (t === 0) return { mu: mu, sd: sd, logdet: 0 };
        var k = function(a, b) { var d = (a - b) / ell; return Math.exp(-0.5 * d * d); };
        var A = []; for (i = 0; i < t; i++) { A.push([]); for (j = 0; j < t; j++) A[i].push(k(X[i], X[j]) + (i === j ? lam : 0)); }
        var L = chol(A), alpha = solve(L, Y), ld = 0;
        for (i = 0; i < t; i++) ld += 2 * Math.log(L[i][i]); ld -= t * Math.log(lam);
        for (g = 0; g < N; g++) { var kv = new Array(t), m = 0; for (i = 0; i < t; i++) { kv[i] = k(grid[g], X[i]); m += kv[i] * alpha[i]; }
          var v = fwd(L, kv), q = 0; for (i = 0; i < t; i++) q += v[i] * v[i]; mu[g] = m; sd[g] = Math.sqrt(Math.max(1 - q, 1e-12)); }
        return { mu: mu, sd: sd, logdet: ld };
      }
      return { rng: mulberry32, posterior: posterior };
    })();

    // ---- Explorer B: break SafeOpt, not LoSBO (Monte-Carlo, real GP) ----
    (function() {
      var N = 40, grid = [], i; for (i = 0; i < N; i++) grid.push(i / (N - 1));
      var ELL = 0.2, M = 12, T = 25, DELTA = 0.01, seed = 11;
      function k(x, y) { var d = (x - y) / ELL; return Math.exp(-0.5 * d * d); }
      function kd(x, y) { return -(x - y) / (ELL * ELL) * k(x, y); }
      function sampleRKHS(rng, B) { var xs = [], al = [], i, j, q = 0; for (i = 0; i < M; i++) { xs.push(rng()); al.push(rng() * 2 - 1); }
        for (i = 0; i < M; i++) for (j = 0; j < M; j++) q += al[i] * al[j] * k(xs[i], xs[j]);
        var sc = B / Math.sqrt(q); for (i = 0; i < M; i++) al[i] *= sc;
        return { f: function(x) { var s = 0, i; for (i = 0; i < M; i++) s += al[i] * k(x, xs[i]); return s; },
                 fp: function(x) { var s = 0, i; for (i = 0; i < M; i++) s += al[i] * kd(x, xs[i]); return s; } }; }
      function runOne(fv, h, s0, o, rng) {
        var X = [], Y = [], lo = new Array(N).fill(-Infinity), up = new Array(N).fill(Infinity), safe = new Array(N).fill(false);
        safe[s0] = true; lo[s0] = h; var unsafe = 0, restarts = 0, lastX = null, lastY = null, beta = o.beta, t, g, g2, post = null, queries = [];
        for (t = 1; t <= T; t++) {
          post = STL.posterior(grid, X, Y, ELL, o.lam);
          if (o.alg === 'realbeta') beta = o.B + o.R / Math.sqrt(o.lam) * Math.sqrt(Math.max(post.logdet - 2 * Math.log(DELTA), 0));
          if (t > 1) {
            // C_t = C_{t-1} intersected with the band Q. If the data contradict an earlier band, the intersection is empty
            // (for a valid beta this happens with probability <= delta) and Algorithms 2-3 are undefined there: restart C_t(x)
            // from the current band and count the event. This keeps l_t <= u_t at every point.
            for (g = 0; g < N; g++) { var ql = post.mu[g] - beta * post.sd[g], qu = post.mu[g] + beta * post.sd[g], nl = Math.max(lo[g], ql), nu = Math.min(up[g], qu);
              if (nl > nu) { nl = ql; nu = qu; restarts++; } lo[g] = nl; up[g] = nu; }
            if (o.alg === 'losbo') { for (g = 0; g < N; g++) if (!safe[g] && lastY - o.E - o.L * Math.abs(grid[g] - lastX) >= h) safe[g] = true; }
            else { var prev = safe.slice(); for (g = 0; g < N; g++) { if (!prev[g]) continue; for (g2 = 0; g2 < N; g2++) if (!safe[g2] && lo[g] - o.L * Math.abs(grid[g] - grid[g2]) >= h) safe[g2] = true; } }
          }
          var maxLo = -Infinity; for (g = 0; g < N; g++) if (safe[g]) maxLo = Math.max(maxLo, lo[g]);
          var best = -1, bw = -Infinity;
          for (g = 0; g < N; g++) { if (!safe[g]) continue; var isM = up[g] >= maxLo, isG = false;
            if (!isM) for (g2 = 0; g2 < N; g2++) if (!safe[g2] && up[g] - o.L * Math.abs(grid[g] - grid[g2]) >= h) { isG = true; break; }
            if (isM || isG) { var w = up[g] - lo[g]; if (w > bw) { bw = w; best = g; } } }
          // no fallback is needed: since l_t <= u_t everywhere, the maximizer of l_t over S_t is in M_t, so G_t u M_t is never empty
          var eps; if (o.noise === 'gauss') { var u1 = rng() || 1e-12, u2 = rng(); eps = o.Beps * Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2); } else { eps = (2 * rng() - 1) * o.Beps; }
          var y = fv[best] + eps; if (fv[best] < h) unsafe++;
          queries.push({ x: grid[best], y: y, bad: fv[best] < h }); X.push(grid[best]); Y.push(y); lastX = grid[best]; lastY = y;
        }
        post = STL.posterior(grid, X, Y, ELL, o.lam);
        // beta_T after the last update (Algorithm 2, line 17), so the plotted band mu +- beta*sd is eq. (7) for the posterior it is drawn with
        if (o.alg === 'realbeta') beta = o.B + o.R / Math.sqrt(o.lam) * Math.sqrt(Math.max(post.logdet - 2 * Math.log(DELTA), 0));
        var bg = -1, bm = -Infinity, expanded = false, nSafe = 0, nCert = 0;
        for (g = 0; g < N; g++) { if (fv[g] >= h) { nSafe++; if (safe[g]) nCert++; } if (safe[g] && g !== s0) expanded = true; if (safe[g] && post.mu[g] > bm) { bm = post.mu[g]; bg = g; } }
        var fstar = Math.max.apply(null, fv);
        return { unsafe: unsafe, restarts: restarts, expanded: expanded, cover: nSafe > 0 ? nCert / nSafe : 0, perf: (fv[bg] - h) / (fstar - h), beta: beta, safe: safe, mu: post.mu, sd: post.sd, queries: queries };
      }
      var cfgIds = ['norm', 'beta', 'bfac', 'lfac', 'efac', 'beps', 'K', 'show'], dec = { norm: 0, beta: 2, bfac: 2, lfac: 2, efac: 1, beps: 2, K: 0, show: 0 };
      function v(id) { return parseFloat(document.getElementById('st-mc-' + id).value); }
      var results = null;
      function simulate() {
        var B = v('norm'), K = v('K'), Beps = v('beps'), E = v('efac') * Beps, noise = document.getElementById('st-mc-noise').value;
        var rng = STL.rng(seed), funcs = [], f;
        results = { safeopt: [], realbeta: [], losbo: [], funcs: funcs };
        for (f = 0; f < K; f++) {
          var fn = sampleRKHS(rng, B), fv = grid.map(fn.f), mean = fv.reduce(function(a, b) { return a + b; }, 0) / N;
          var sdv = Math.sqrt(fv.reduce(function(a, b) { return a + (b - mean) * (b - mean); }, 0) / N), h = mean - 0.2 * sdv, Lt = 0, i, j2;
          var fine = []; for (i = 0; i <= 400; i++) { fine.push(fn.f(i / 400)); Lt = Math.max(Lt, Math.abs(fn.fp(i / 400))); }
          // L_true: max |f'| on the fine grid, raised if needed to the exact Lipschitz constant of f on the 40 query points,
          // so that factor >= 1 is a valid bound for every certificate the explorer can issue
          for (i = 0; i < N; i++) for (j2 = i + 1; j2 < N; j2++) Lt = Math.max(Lt, Math.abs(fv[j2] - fv[i]) / (grid[j2] - grid[i]));
          var am = 0, g; for (g = 1; g < N; g++) if (fv[g] > fv[am]) am = g;
          var a = am, b = am; while (a > 0 && fv[a - 1] >= h + E) a--; while (b < N - 1 && fv[b + 1] >= h + E) b++;
          var s0 = a + Math.floor(rng() * (b - a + 1));
          var base = { lam: Beps, R: Beps, Beps: Beps, noise: noise, L: v('lfac') * Lt, E: E };
          var rs = STL.rng(seed * 7919 + f), r1 = STL.rng(rs() * 1e9 | 0), r2 = STL.rng(rs() * 1e9 | 0), r3 = STL.rng(rs() * 1e9 | 0);
          funcs.push({ fine: fine, fv: fv, h: h, s0: s0, Lt: Lt });
          results.safeopt.push(runOne(fv, h, s0, Object.assign({ alg: 'safeopt', beta: v('beta') }, base), r1));
          results.realbeta.push(runOne(fv, h, s0, Object.assign({ alg: 'realbeta', B: v('bfac') * B }, base), r2));
          results.losbo.push(runOne(fv, h, s0, Object.assign({ alg: 'losbo', beta: v('beta') }, base), r3));
        }
      }
      function stats(r) { var n = r.length; return { viol: 100 * r.filter(function(x) { return x.unsafe > 0; }).length / n, per: r.reduce(function(s, x) { return s + x.unsafe; }, 0) / n,
        stuck: 100 * r.filter(function(x) { return !x.expanded; }).length / n, cover: 100 * r.reduce(function(s, x) { return s + x.cover; }, 0) / n,
        perf: 100 * r.reduce(function(s, x) { return s + x.perf; }, 0) / n, beta: r.reduce(function(s, x) { return s + x.beta; }, 0) / n,
        empty: 100 * r.filter(function(x) { return x.restarts > 0; }).length / n }; }
      function readouts() { cfgIds.forEach(function(id) { document.getElementById('st-mc-' + id + '-val').textContent = v(id).toFixed(dec[id]); }); }
      function draw(recompute) {
        var showEl = document.getElementById('st-mc-show'); showEl.max = v('K'); if (v('show') > v('K')) showEl.value = v('K');
        readouts();
        if (recompute || !results) simulate();
        var names = { safeopt: 'SafeOpt, heuristic &beta; = ' + v('beta').toFixed(2), realbeta: 'Real-&beta;-SafeOpt, B = ' + (v('bfac') * v('norm')).toFixed(1), losbo: 'LoSBO, L = ' + v('lfac').toFixed(2) + ' L<sub>true</sub>, E = ' + v('efac').toFixed(2) + ' B<sub>&epsilon;</sub>' };
        var cols = { safeopt: '#1565c0', realbeta: '#7b1fa2', losbo: '#2e7d32' };
        var tb = '<table style="font-size:12px;"><thead><tr><th>Algorithm</th><th>runs with &ge; 1 unsafe query</th><th>unsafe queries per run</th><th>never expanded</th><th>safe grid points certified</th><th>final performance</th><th>&beta; after t = 25 (mean over runs)</th><th>runs with an empty C<sub>t</sub> (restarted)</th></tr></thead><tbody>';
        ['safeopt', 'realbeta', 'losbo'].forEach(function(a) { var s = stats(results[a]);
          tb += '<tr><td style="color:' + cols[a] + ';font-weight:600;">' + names[a] + '</td><td style="font-weight:600;color:' + (s.viol > 0 ? '#c62828' : '#2e7d32') + ';">' + s.viol.toFixed(1) + '%</td><td>' + s.per.toFixed(2) + '</td><td>' + s.stuck.toFixed(1) + '%</td><td>' + s.cover.toFixed(1) + '%</td><td>' + s.perf.toFixed(1) + '%</td><td>' + s.beta.toFixed(2) + '</td><td>' + s.empty.toFixed(1) + '%</td></tr>'; });
        document.getElementById('st-mc-table').innerHTML = tb + '</tbody></table>';
        // plot the selected function
        var fi = v('show') - 1, F = results.funcs[fi], model = document.getElementById('st-mc-model').value, R = results[model][fi];
        var W = 760, H = 360, ML = 50, MR = 16, MT = 16, PH = 220, PW = W - ML - MR, yTop = MT, yBot = MT + PH;
        var ymin = Infinity, ymax = -Infinity, g; F.fine.forEach(function(y) { ymin = Math.min(ymin, y); ymax = Math.max(ymax, y); });
        for (g = 0; g < N; g++) { ymin = Math.min(ymin, R.mu[g] - R.beta * R.sd[g]); ymax = Math.max(ymax, R.mu[g] + R.beta * R.sd[g]); }
        ymin = Math.min(ymin, F.h); var pad = 0.08 * (ymax - ymin); ymin -= pad; ymax += pad;
        function sx(x) { return ML + x * PW; } function sy(y) { return yBot - (y - ymin) / (ymax - ymin) * PH; }
        var s = '';
        [0, 0.25, 0.5, 0.75, 1].forEach(function(x) { s += '<line x1="' + sx(x) + '" y1="' + yTop + '" x2="' + sx(x) + '" y2="' + yBot + '" stroke="#eee"/><text x="' + sx(x) + '" y="' + (yBot + 14) + '" font-size="11" fill="#888" text-anchor="middle">' + x + '</text>'; });
        var yt, step = Math.pow(10, Math.floor(Math.log10(ymax - ymin))) / 2; for (yt = Math.ceil(ymin / step) * step; yt <= ymax; yt += step) { s += '<line x1="' + ML + '" y1="' + sy(yt).toFixed(1) + '" x2="' + (ML + PW) + '" y2="' + sy(yt).toFixed(1) + '" stroke="#eee"/><text x="' + (ML - 6) + '" y="' + (sy(yt) + 4).toFixed(1) + '" font-size="11" fill="#888" text-anchor="end">' + yt.toFixed(1) + '</text>'; }
        // band of the selected model at the end of the run
        var d = ''; for (g = 0; g < N; g++) d += (g === 0 ? 'M' : 'L') + sx(grid[g]).toFixed(1) + ' ' + sy(Math.min(R.mu[g] + R.beta * R.sd[g], ymax)).toFixed(1) + ' ';
        for (g = N - 1; g >= 0; g--) d += 'L' + sx(grid[g]).toFixed(1) + ' ' + sy(Math.max(R.mu[g] - R.beta * R.sd[g], ymin)).toFixed(1) + ' ';
        s += '<path d="' + d + 'Z" fill="' + cols[model] + '" opacity="0.13" stroke="none"/>';
        d = ''; for (g = 0; g < N; g++) d += (g === 0 ? 'M' : 'L') + sx(grid[g]).toFixed(1) + ' ' + sy(R.mu[g]).toFixed(1) + ' ';
        s += '<path d="' + d + '" fill="none" stroke="' + cols[model] + '" stroke-width="1.5" stroke-dasharray="4,3"/>';
        d = ''; F.fine.forEach(function(y, j) { d += (j === 0 ? 'M' : 'L') + sx(j / 400).toFixed(1) + ' ' + sy(y).toFixed(1) + ' '; });
        s += '<path d="' + d + '" fill="none" stroke="#222" stroke-width="2"/>';
        s += '<line x1="' + ML + '" y1="' + sy(F.h).toFixed(1) + '" x2="' + (ML + PW) + '" y2="' + sy(F.h).toFixed(1) + '" stroke="#c62828" stroke-width="1.5" stroke-dasharray="6,4"/><text x="' + (ML + PW - 4) + '" y="' + (sy(F.h) - 5).toFixed(1) + '" font-size="11" fill="#c62828" text-anchor="end">threshold h</text>';
        R.queries.forEach(function(q) { s += '<circle cx="' + sx(q.x).toFixed(1) + '" cy="' + sy(Math.min(Math.max(q.y, ymin), ymax)).toFixed(1) + '" r="4" fill="' + (q.bad ? '#c62828' : cols[model]) + '" stroke="#fff" stroke-width="1"/>'; });
        s += '<circle cx="' + sx(grid[F.s0]).toFixed(1) + '" cy="' + sy(F.fv[F.s0]).toFixed(1) + '" r="6" fill="none" stroke="#e67e22" stroke-width="2"/>';
        s += '<line x1="' + ML + '" y1="' + yTop + '" x2="' + ML + '" y2="' + yBot + '" stroke="#333" stroke-width="1.5"/><line x1="' + ML + '" y1="' + yBot + '" x2="' + (ML + PW) + '" y2="' + yBot + '" stroke="#333" stroke-width="1.5"/>';
        // safe-set bars
        var rows = [['safeopt', 'SafeOpt'], ['realbeta', 'Real-&beta;'], ['losbo', 'LoSBO']], cell = PW / N;
        rows.forEach(function(r, j) { var y0 = yBot + 30 + j * 24, Rr = results[r[0]][fi];
          s += '<text x="' + (ML - 6) + '" y="' + (y0 + 12) + '" font-size="11" fill="' + cols[r[0]] + '" text-anchor="end">' + r[1] + '</text>';
          for (g = 0; g < N; g++) { var badPt = F.fv[g] < F.h; s += '<rect x="' + (ML + g * cell).toFixed(1) + '" y="' + y0 + '" width="' + (cell - 0.5).toFixed(1) + '" height="16" fill="' + (Rr.safe[g] ? (badPt ? '#c62828' : cols[r[0]]) : '#e6e6e6') + '"/>'; } });
        s += '<text x="' + (ML + PW) + '" y="' + (yBot + 30 + 3 * 24 + 8) + '" font-size="11" fill="#666" text-anchor="end">safe sets used for query 25 (red = certified but unsafe)</text>';
        var lx = ML + 8, ly = yTop + 12;
        s += '<line x1="' + lx + '" y1="' + ly + '" x2="' + (lx + 18) + '" y2="' + ly + '" stroke="#222" stroke-width="2"/><text x="' + (lx + 24) + '" y="' + (ly + 4) + '" font-size="11" fill="#333">true f</text>';
        s += '<line x1="' + (lx + 70) + '" y1="' + ly + '" x2="' + (lx + 88) + '" y2="' + ly + '" stroke="' + cols[model] + '" stroke-width="1.5" stroke-dasharray="4,3"/><text x="' + (lx + 94) + '" y="' + (ly + 4) + '" font-size="11" fill="#333">GP mean and band at t = 25 (' + { safeopt: 'SafeOpt', realbeta: 'Real-&beta;', losbo: 'LoSBO' }[model] + ')</text>';
        s += '<circle cx="' + (lx + 330) + '" cy="' + ly + '" r="4" fill="' + cols[model] + '"/><text x="' + (lx + 338) + '" y="' + (ly + 4) + '" font-size="11" fill="#333">query</text><circle cx="' + (lx + 385) + '" cy="' + ly + '" r="4" fill="#c62828"/><text x="' + (lx + 393) + '" y="' + (ly + 4) + '" font-size="11" fill="#333">unsafe query</text><circle cx="' + (lx + 485) + '" cy="' + ly + '" r="5" fill="none" stroke="#e67e22" stroke-width="2"/><text x="' + (lx + 494) + '" y="' + (ly + 4) + '" font-size="11" fill="#333">seed</text>';
        document.getElementById('st-mc-svg').innerHTML = s;
        var tot = 0; ['safeopt', 'realbeta', 'losbo'].forEach(function(a) { tot += results[a][fi].unsafe; });
        document.getElementById('st-mc-note').innerHTML = 'Function ' + (fi + 1) + ' of ' + v('K') + ' (seed ' + seed + '): norm ' + v('norm').toFixed(0) + ', h = ' + F.h.toFixed(2) + ', L<sub>true</sub> = ' + F.Lt.toFixed(1) + ' (L used = ' + (v('lfac') * F.Lt).toFixed(1) + '), E = ' + (v('efac') * v('beps')).toFixed(3) + ', noise ' + (document.getElementById('st-mc-noise').value === 'gauss' ? 'Gaussian with sigma = B<sub>&epsilon;</sub>' : 'uniform on [-B<sub>&epsilon;</sub>, B<sub>&epsilon;</sub>]') + '. Unsafe queries on this function: SafeOpt ' + results.safeopt[fi].unsafe + ', Real-&beta; ' + results.realbeta[fi].unsafe + ', LoSBO ' + results.losbo[fi].unsafe + '. Real-&beta; ended with &beta; = ' + results.realbeta[fi].beta.toFixed(2) + '.';
      }
      globalThis.__readonlyTheoryMonteCarlo = {
        snapshot: function() { return {results: results, seed: seed, grid: grid, N: N, M: M, T: T, ELL: ELL, DELTA: DELTA}; },
        summarize: function() { return {safeopt: stats(results.safeopt), realbeta: stats(results.realbeta), losbo: stats(results.losbo)}; }
      };
      // readouts follow the drag; the Monte-Carlo run starts when a slider is released ('change'); "function shown" and the band selector only redraw
      cfgIds.forEach(function(id) { var el = document.getElementById('st-mc-' + id); el.addEventListener('input', readouts); el.addEventListener('change', function() { draw(id !== 'show'); }); });
      document.getElementById('st-mc-noise').addEventListener('change', function() { draw(true); });
      document.getElementById('st-mc-model').addEventListener('change', function() { draw(false); });
      document.getElementById('st-mc-resample').addEventListener('click', function() { seed += 1; draw(true); });
      draw(true);
    })();
