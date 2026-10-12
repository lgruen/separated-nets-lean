/* NetCore: exact constructions of the nets of the explainer pages (pure functions, no DOM). Loaded by anatomy.html,
   shifts.html and beyond.html with <script src="netcore.js">.
   Conventions of the paper (sec:conv): index digit v_l, least significant first, is the coefficient of t^l;
   output digit 0 is the most significant; the integer coordinate of a point is sum_j d_j q^(m-1-j) in [0, q^m).
   The node cross-check (check/run_core.mjs, check/run_core23.mjs) evaluates exactly this file. */
var NetCore = (function () {
  'use strict';
  function binom(a, b) {
    if (a < 0 || b < 0 || b > a) return 0;
    var r = 1;
    for (var i = 1; i <= b; i++) r = (r * (a - b + i)) / i;
    return r;
  }
  function zeros(r, c) { var A = []; for (var i = 0; i < r; i++) { var row = []; for (var j = 0; j < c; j++) row.push(0); A.push(row); } return A; }
  function eye(n) { var A = zeros(n, n); for (var i = 0; i < n; i++) A[i][i] = 1; return A; }
  function mul(A, B) {
    var n = A.length, l = B.length, c = B[0].length, R = zeros(n, c);
    for (var i = 0; i < n; i++) for (var t = 0; t < l; t++) { var a = A[i][t]; if (a) for (var j = 0; j < c; j++) R[i][j] += a * B[t][j]; }
    return R;
  }
  function isEye(A) { for (var i = 0; i < A.length; i++) for (var j = 0; j < A.length; j++) if (A[i][j] !== (i === j ? 1 : 0)) return false; return true; }
  function mod(a, q) { var r = a % q; return r < 0 ? r + q : r + 0; }
  function ipow(b, e) { var r = 1; for (var i = 0; i < e; i++) r *= b; return r; }

  /* 2D: the Hammersley net (frame of the places infinity, 0) in graph form with depths (k, k).
     Index v = (n_x levels 0..k-1, n_y levels 0..k-1). Offset rows: Phi_xy = s*J, Phi_yx = J.
     'frame':   Phi_xx = Phi_yy = 0, s = +1: geometric layer [[0,1],[1,0]] (the Hammersley net itself).
     'rotated': gauge moves of lem:box: (a) row 0 of the diagonal blocks = -1 on the last level, (c) L_x = -I,
                so the layer is M = -I + R_90 = [[-1,-1],[1,-1]], the xy-block of M in prop:cell. */
  function hammersley2D(k, variant) {
    var m = 2 * k, Cx = zeros(m, m), Cy = zeros(m, m), i, j;
    for (i = 0; i < k; i++) { Cx[i][i] = 1; Cy[i][k + i] = 1; }
    var sxy = variant === 'rotated' ? -1 : 1;
    for (j = 0; j < k; j++) { Cx[k + j][k + (k - 1 - j)] = sxy; Cy[k + j][k - 1 - j] = 1; }
    if (variant === 'rotated') { Cx[k][k - 1] = -1; Cy[k][2 * k - 1] = -1; }
    var M = variant === 'rotated' ? [[-1, -1], [1, -1]] : [[0, 1], [1, 0]];
    return { kind: '2D', variant: variant, s: 2, m: m, k: k, C: [Cx, Cy], M: M };
  }

  /* 3D: P_{k,q} of def:net. tau column l = coefficients of (1-t)^(m-1-l); T = s_k tau, s_k = (-1)^(k+1);
     K_ij = binom(i-j+k-1, k-1); E = identity except rows k-2, k-1, k; L = E K; generators (L T^2, L, L T). */
  function pNet(k) {
    var m = 3 * k, sk = k % 2 === 1 ? 1 : -1, i, j, l;
    var tau = zeros(m, m);
    for (l = 0; l < m; l++) for (i = 0; i < m; i++) tau[i][l] = (i % 2 ? -1 : 1) * binom(m - 1 - l, i) + 0;
    var T = tau.map(function (r) { return r.map(function (x) { return sk * x + 0; }); });
    var T2 = mul(T, T);
    if (!isEye(mul(T2, T))) throw new Error('T^3 != I');
    var K = zeros(m, m);
    for (i = 0; i < m; i++) for (j = 0; j <= i; j++) K[i][j] = binom(i - j + k - 1, k - 1);
    var E = eye(m);
    if (k >= 2) for (j = 0; j < m; j++) E[k - 2][j] = j <= k - 2 ? 1 : 0;
    for (j = 0; j < m; j++) E[k - 1][j] = j === k - 1 ? -1 : 0;
    for (j = 0; j < m; j++) E[k][j] = (j === k - 1 || j === k) ? 1 : 0;
    var L = mul(E, K);
    return { kind: 'P', s: 3, m: m, k: k, C: [mul(L, T2), L, mul(L, T)],
             M: [[-1, -1, 1], [1, -1, -1], [-1, 1, -1]], J: [[0, 0, -1], [-1, 0, 0], [0, -1, 0]] };
  }

  /* 3D: the column net C_q of def:col: every coordinate c has the digits n_c, a.n, l.n with
     w = (-2,1,1) (q = 2 mod 3) or (-1,-1,2) (q = 1 mod 3), a = (q 1 + w)/3, l = (-1, 1, 0). */
  function colW(q) { return q % 3 === 2 ? [-2, 1, 1] : [-1, -1, 2]; }
  function colNet(q) {
    if (q < 5 || q % 2 === 0 || q % 3 === 0) throw new Error('column nets need q >= 5 coprime to 6');
    var w = colW(q), a = w.map(function (x) { return (q + x) / 3; }), ell = [-1, 1, 0];
    var C = [0, 1, 2].map(function (c) { return [[0, 1, 2].map(function (j) { return j === c ? 1 : 0; }), a.slice(), ell.slice()]; });
    return { kind: 'C', s: 3, m: 3, k: 1, C: C, w: w, a: a, ell: ell };
  }

  /* all N = q^m points as integer coordinates; the cell of a point = first k digits of each coordinate. */
  function build(net, q) {
    var s = net.s, m = net.m, k = net.k, N = ipow(q, m), cw = ipow(q, m - k), G = ipow(q, k);
    var C = net.C.map(function (Cc) { return Cc.map(function (r) { return r.map(function (x) { return mod(x, q); }); }); });
    var X = [], c, j, l;
    for (c = 0; c < s; c++) X.push(new Int32Array(N));
    var v = new Int32Array(m);
    for (var i = 0; i < N; i++) {
      for (c = 0; c < s; c++) {
        var x = 0, Cc = C[c];
        for (j = 0; j < m; j++) { var t = 0, row = Cc[j]; for (l = 0; l < m; l++) t += row[l] * v[l]; x = x * q + (t % q); }
        X[c][i] = x;
      }
      for (l = 0; l < m; l++) { if (++v[l] < q) break; v[l] = 0; }
    }
    var cells = ipow(G, s), cell = new Int32Array(cells).fill(-1), ok = true;
    for (i = 0; i < N; i++) {
      var idx = 0, mg = 1;
      for (c = 0; c < s; c++) { idx += Math.floor(X[c][i] / cw) * mg; mg *= G; }
      if (cell[idx] !== -1) ok = false;
      cell[idx] = i;
    }
    return { net: net, q: q, s: s, m: m, k: k, N: N, W: N, cw: cw, G: G, X: X, Cq: C, cell: cell, onePerCell: ok };
  }

  /* the same net with every coordinate cut after its first `keep` digits (keep = k+1: the lattice image). */
  function truncate(B, keep) {
    var u = ipow(B.q, B.m - keep), out = Object.assign({}, B);
    out.X = B.X.map(function (Xc) { var Y = new Int32Array(Xc.length); for (var i = 0; i < Xc.length; i++) Y[i] = Xc[i] - (Xc[i] % u); return Y; });
    return out;
  }

  function digit(B, c, i, j) { return Math.floor(B.X[c][i] / ipow(B.q, B.m - 1 - j)) % B.q; }
  function cellCoords(B, idx) { var n = []; for (var c = 0; c < B.s; c++) { n.push(idx % B.G); idx = (idx - n[c]) / B.G; } return n; }
  function cellIndex(B, n) { var idx = 0, mg = 1; for (var c = 0; c < B.s; c++) { idx += n[c] * mg; mg *= B.G; } return idx; }

  function offsets(s, R) {
    var out = [], e = [], c;
    for (c = 0; c < s; c++) e.push(-R);
    for (;;) {
      var f = 0;
      for (c = 0; c < s; c++) if (e[c] !== 0) { f = e[c]; break; }
      if (f > 0) out.push(e.slice());
      c = 0;
      while (c < s && e[c] === R) { e[c] = -R; c++; }
      if (c === s) break;
      e[c]++;
    }
    return out;
  }

  /* exact minimum distance by a cell list. Two points whose cells differ by more than R in some coordinate
     are more than R cells apart in that coordinate, so the scan over |e| <= R is exact once best <= (R cells)^2.
     toroidal: differences reduced modulo q^m (the paper's delta). Returns d2 at integer scale q^m and
     c = delta N^(1/s) = sqrt(d2)/cw (N^(1/s) = q^k when m = sk). */
  function minDist(B, toroidal) {
    var s = B.s, G = B.G, cw = B.cw, W = B.W, X = B.X, cell = B.cell, N = B.N, half = W / 2, c;
    for (var R = 1; ; R++) {
      var offs = offsets(s, R), best = Infinity, rep = null, plain = null, keys = new Set();
      var n = new Array(s), D = new Array(s);
      for (var idx = 0; idx < cell.length; idx++) {
        var t = idx;
        for (c = 0; c < s; c++) { n[c] = t % G; t = (t - n[c]) / G; }
        var i = cell[idx];
        for (var o = 0; o < offs.length; o++) {
          var e = offs[o], idx2 = 0, mg = 1, inside = true;
          for (c = 0; c < s; c++) {
            var vv = n[c] + e[c];
            if (toroidal) vv = mod(vv, G); else if (vv < 0 || vv >= G) { inside = false; break; }
            idx2 += vv * mg; mg *= G;
          }
          if (!inside || idx2 === idx) continue;
          var j = cell[idx2], d2 = 0, wrapped = false;
          for (c = 0; c < s; c++) {
            var d = X[c][j] - X[c][i];
            if (toroidal) { var dd = mod(d, W); if (dd > half) dd -= W; if (dd !== d) wrapped = true; d = dd; }
            D[c] = d; d2 += d * d;
          }
          if (d2 > best) continue;
          if (d2 < best) { best = d2; keys = new Set(); rep = null; plain = null; }
          keys.add(i < j ? i * N + j : j * N + i);
          if (!rep) rep = { i: i, j: j, D: D.slice() };
          if (!wrapped && !plain) plain = { i: i, j: j, D: D.slice() };
        }
      }
      var done = best <= (R * cw) * (R * cw) || (toroidal ? 2 * R + 1 >= G : R >= G - 1);
      if (done) return { d2: best, c: Math.sqrt(best) / cw, pair: plain || rep, count: keys.size, radius: R };
    }
  }

  /* t = 0 by definition: for every composition d of m, every elementary box with d_c digits in coordinate c holds
     exactly one point (valid over any Z/qZ). */
  function compositions(m, s) {
    var out = [];
    (function rec(c, rem, acc) {
      if (c === s - 1) { out.push(acc.concat([rem])); return; }
      for (var d = 0; d <= rem; d++) rec(c + 1, rem - d, acc.concat([d]));
    })(0, m, []);
    return out;
  }
  function boxCheck(B) {
    var s = B.s, m = B.m, q = B.q, N = B.N, X = B.X, comps = compositions(m, s), seen = new Uint8Array(N);
    for (var a = 0; a < comps.length; a++) {
      var d = comps[a], div = [], mult = [], mm = 1, c;
      for (c = 0; c < s; c++) { div.push(ipow(q, m - d[c])); mult.push(mm); mm *= ipow(q, d[c]); }
      seen.fill(0);
      for (var i = 0; i < N; i++) {
        var b = 0;
        for (c = 0; c < s; c++) b += Math.floor(X[c][i] / div[c]) * mult[c];
        if (seen[b]) return { ok: false, shapes: comps.length, bad: d };
        seen[b] = 1;
      }
    }
    return { ok: true, shapes: comps.length };
  }

  /* shortest nonzero vector of (I + M/q) Z^s, by enumeration over |v_i| <= 3 (enough for these layers). */
  function latticeMin(M, q) {
    var s = M.length, best = Infinity, v = [], c;
    for (c = 0; c < s; c++) v.push(-3);
    for (;;) {
      var nz = false; for (c = 0; c < s; c++) if (v[c]) nz = true;
      if (nz) {
        var n2 = 0;
        for (var r = 0; r < s; r++) { var x = v[r]; for (c = 0; c < s; c++) x += M[r][c] * v[c] / q; n2 += x * x; }
        if (n2 < best) best = n2;
      }
      c = 0; while (c < s && v[c] === 3) { v[c] = -3; c++; }
      if (c === s) break;
      v[c]++;
    }
    return Math.sqrt(best);
  }

  /* thm:main: c(q)^2 = min{(1-1/q)^2, (1-2/q)^2 + (1-4/q)^2, 3(1-3/q)^2}. */
  function cMain(q) {
    var b = function (j) { return 1 - j / q; };
    return Math.sqrt(Math.min(b(1) * b(1), b(2) * b(2) + b(4) * b(4), 3 * b(3) * b(3)));
  }

  /* thm:col and lem:drift: exact d^2 = (2 q^4 + tau^2)/3 at integer scale q^3; excesses eps_i = q w_i/3 + r_i, r = (q-1,1,0). */
  function colTheory(q) {
    var w = colW(q), r = [q - 1, 1, 0], tau = q % 3 === 2 ? q * q - q - 3 : q * q - 2 * q;
    var d2 = (2 * q * q * q * q + tau * tau) / 3;
    var eps3 = w.map(function (wi, i) { return q * wi + 3 * r[i]; });          /* 3 eps_i, an integer */
    var eta3 = Math.max.apply(null, eps3);
    return { w: w, r: r, tau: tau, d2: d2, c: Math.sqrt(d2) / (q * q), eps3: eps3, eta3: eta3 };
  }

  /* heights along the cycle of q steps in direction e_dir through the column of the cell 0: each step value
     phi([n+e]) - phi([n]) taken modulo q^2 in the window (-q^2/6, 5q^2/6] (as in fig:drift). */
  function colPhi(q, a, n) { return q * mod(a[0] * n[0] + a[1] * n[1] + a[2] * n[2], q) + mod(n[1] - n[0], q); }
  function cycle(q, dir) {
    var net = colNet(q), a = net.a, qq = q * q, n = [0, 0, 0], xs = [], H = [0];
    for (var t = 0; t < q; t++) {
      var n2 = n.slice(); n2[dir] = mod(n2[dir] + 1, q);
      var dl = mod(colPhi(q, a, n2) - colPhi(q, a, n), qq);
      var x = 6 * dl > 5 * qq ? dl - qq : dl;
      xs.push(x); H.push(H[H.length - 1] + x); n = n2;
    }
    return { xs: xs, H: H };
  }

  /* ---------------------------------------------------------------- the worked example of section 0 */
  /* the geometric layer used by digit k (index k) of each coordinate: r = M l + J h (mod q), l = last cell digits,
     h = second-last cell digits. 2D: M = layer of hammersley2D. P: prop:cell (J only for k >= 2).
     C_q: digit 2 of every coordinate is a.n, so M = 1 a^T. */
  function layer(net) {
    if (net.kind === 'C') return { M: [net.a.slice(), net.a.slice(), net.a.slice()], J: null };
    return { M: net.M, J: net.kind === 'P' && net.k >= 2 ? net.J : null };
  }
  function dot(a, b) { var t = 0; for (var i = 0; i < a.length; i++) t += a[i] * b[i]; return t; }
  /* one point, every intermediate number. Units: cell units for n; numerators over q for lattice quantities. */
  function explain(net, q, i) {
    var s = net.s, m = net.m, k = net.k, c, d, j, l;
    var C = net.C.map(function (Cc) { return Cc.map(function (r) { return r.map(function (x) { return mod(x, q); }); }); });
    var v = [], t = i;
    for (l = 0; l < m; l++) { v.push(t % q); t = (t - (t % q)) / q; }
    var coords = [];
    for (c = 0; c < s; c++) {
      var rows = [], dig = [], X = 0;
      for (j = 0; j < m; j++) {
        var terms = [], sum = 0;
        for (l = 0; l < m; l++) { terms.push(C[c][j][l] * v[l]); sum += C[c][j][l] * v[l]; }
        rows.push({ terms: terms, sum: sum, d: sum % q }); dig.push(sum % q); X = X * q + (sum % q);
      }
      coords.push({ C: C[c], rows: rows, d: dig, X: X });
    }
    var cw = ipow(q, m - k);
    var n = coords.map(function (o) { return Math.floor(o.X / cw); });
    var ell = n.map(function (x) { return x % q; });
    var blk = n.map(function (x) { return Math.floor(x / q); });
    var h = blk.map(function (x) { return x % q; });
    var r = coords.map(function (o) { return o.d[k]; });
    var Ly = layer(net), M = Ly.M, J = Ly.J;
    var pre = [], rPred = [], kappa = [], latNum = [], shiftNum = [], imgNum = [], ok = true;
    for (c = 0; c < s; c++) {
      var Jh = J ? dot(J[c], h) : 0, p = dot(M[c], ell) + Jh;
      pre.push(p); rPred.push(mod(p, q)); kappa.push(Math.floor(p / q));
      latNum.push(q * n[c] + dot(M[c], n));                         /* q (I + M/q) n           */
      shiftNum.push(-q * dot(M[c], blk) + Jh);                      /* q (-M floor(n/q) + Jh/q) */
      imgNum.push(q * n[c] + r[c]);                                 /* q (n + r/q)             */
      if (rPred[c] !== r[c] || imgNum[c] !== latNum[c] + shiftNum[c] - q * kappa[c]) ok = false;
    }
    var out = { net: net.kind, q: q, i: i, s: s, m: m, k: k, N: ipow(q, m), v: v, coords: coords, n: n, ell: ell,
                blk: blk, h: h, r: r, M: M, J: J, pre: pre, rPred: rPred, kappa: kappa, latNum: latNum,
                shiftNum: shiftNum, imgNum: imgNum, ok: ok };
    if (net.kind === 'C') {                 /* the common height phi(n) = q h(n) + j(n), def:col */
      var an = dot(net.a, n), jn = n[1] - n[0];
      var col = { an: an, hn: mod(an, q), k2: Math.floor(an / q), jn: jn, jv: mod(jn, q), k3: Math.floor(jn / q) };
      col.phi = q * col.hn + col.jv;
      col.lin = q * an + jn;                                        /* (q a + l) . n, l = (-1, 1, 0) */
      if (col.phi !== col.lin - q * q * col.k2 - q * col.k3) ok = false;
      for (c = 0; c < 3; c++) if (coords[c].X !== q * q * n[c] + col.phi) ok = false;
      out.col = col; out.ok = ok;
    }
    return out;
  }

  /* the reference implementation printed in step 6: the same digit-by-digit algorithm as build() */
  var PY_LISTING = [
    'def net_points(C, q):',
    '    """All q**m points of the digital net with generator matrices C[c] (m x m integers).',
    '    Returns integer coordinates X in [0, q**m); the point itself is X / q**m."""',
    '    m = len(C[0])',
    '    points = []',
    '    for i in range(q ** m):',
    '        v = [(i // q ** l) % q for l in range(m)]  # index digits, least significant first',
    '        point = []',
    '        for Cc in C:                                # one generator matrix per coordinate',
    '            X = 0',
    '            for row in Cc:                          # output digit j, most significant first',
    '                d = sum(a * b for a, b in zip(row, v)) % q',
    '                X = X * q + d',
    '            point.append(X)',
    '        points.append(tuple(point))',
    '    return points'].join('\n');
  function pyProgram(net, q, i, X) {
    var names = net.s === 2 ? ['x', 'y'] : ['x', 'y', 'z'];
    var mats = net.C.map(function (Cc, c) {
      return '    ' + JSON.stringify(Cc.map(function (r) { return r.map(function (x) { return mod(x, q); }); })).replace(/,/g, ', ') +
             ',  # C_' + names[c];
    }).join('\n');
    return PY_LISTING + '\n\n\nq = ' + q + '\nC = [\n' + mats + '\n]\npoints = net_points(C, q)\nprint(points[' + i + '])  # ' +
           '(' + X.join(', ') + ')';
  }

  /* ================================================================ pages 2 and 3 (shifts.html, beyond.html) */
  function isPrime(n) { if (n < 2) return false; for (var d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; }
  function primesIn(a, b) { var o = []; for (var n = a; n <= b; n++) if (isPrime(n)) o.push(n); return o; }
  function torDiff(d, W) { var x = mod(d, W); return x > W / 2 ? x - W : x; }

  /* graph form with the depths (1,...,1): coordinate c has the digits n_c, (O_1 n)_c, (O_2 n)_c, ... for the offset
     row matrices O_j (s x s integers). The index digits are the cell digits, v = n. */
  function graphNet(offs, kind, extra) {
    var s = offs[0].length, m = offs.length + 1, C = [];
    for (var c = 0; c < s; c++) {
      var Cc = [[]];
      for (var d = 0; d < s; d++) Cc[0].push(d === c ? 1 : 0);
      for (var j = 0; j < offs.length; j++) Cc.push(offs[j][c].slice());
      C.push(Cc);
    }
    var net = { kind: kind, s: s, m: m, k: 1, C: C, offs: offs };
    for (var key in extra) net[key] = extra[key];
    return net;
  }

  /* prop:twocoset: T_p, p >= 5 prime, h = (p-1)/2, r = nearest integer to p/8, theta = 8r - p.
     C_x: e_x, (0,h,h), (0,1,2);  C_y: e_y, (r,-1,1), (3,0,1);  C_z: e_z, (r,-1,1), (1,5,0). */
  function twoCoset(p) {
    var h = (p - 1) / 2, r = Math.round(p / 8);
    return graphNet([[[0, h, h], [r, -1, 1], [r, -1, 1]], [[0, 1, 2], [3, 0, 1], [1, 5, 0]]], 'T', { p: p, h: h, r: r, theta: 8 * r - p });
  }
  /* prop:wnet: W_p, h = (p-1)/2, r = floor(p/48), rho = 2r+1, eps = rho/(2p); z reads zeta = u.n, u = (h-r,h-r,rho),
     x and y read 2 zeta mod p.  C_x: e_x, rho(-1,-1,2), (0,1,2); C_y: e_y, rho(-1,-1,2), (1,0,1); C_z: e_z, u, (0,1,0). */
  function wNet(p) {
    var h = (p - 1) / 2, r = Math.floor(p / 48), rho = 2 * r + 1;
    return graphNet([[[-rho, -rho, 2 * rho], [-rho, -rho, 2 * rho], [h - r, h - r, rho]], [[0, 1, 2], [1, 0, 1], [0, 1, 0]]], 'W',
                    { p: p, h: h, r: r, rho: rho, eps: rho / (2 * p), u: [h - r, h - r, rho] });
  }
  /* prop:half5: Q*_p, s = 5, m = 5: digits n_c, (F0* n)_c, (D1 n)_c, (D2 n)_c, (D3 n)_c with 1/2 = (p+1)/2 mod p. */
  var HALF5 = {
    H: [[-3, -3, -3, -1, -1], [3, -3, -1, -3, 1], [3, 1, -3, 1, -1], [1, 3, -1, -3, -1], [1, -1, 1, 1, -1]],   /* 2 F0* */
    D1: [[-2, 0, -1, -1, 1], [0, -1, -1, -1, -1], [2, -1, -3, 1, 0], [-1, 2, -1, -2, 0], [-1, -1, 3, 2, -5]],
    D2: [[0, -1, -1, 0, 0], [-1, 0, 0, 0, -1], [-1, -1, 0, 0, 0], [-1, -1, 0, 0, 0], [-1, -1, 0, 0, 0]],
    D3: [[0, -1, 0, 0, 0], [-1, 0, 0, 0, 0], [-1, 0, 0, 0, 0], [-1, 0, 0, 0, 0], [-1, 0, 0, 0, 0]]
  };
  function half5(p) {
    var half = (p + 1) / 2;
    var F = HALF5.H.map(function (r) { return r.map(function (x) { return mod(x * half, p); }); });
    return graphNet([F, HALF5.D1, HALF5.D2, HALF5.D3], 'Q', { p: p });
  }

  /* def:dshift: add tau_c (m digits, most significant first) to the digits of coordinate c, digit by digit mod q,
     without carries. Returns a new built net (one point per cell again, lem:shift). */
  function shiftCoord(X, t, q, m) {
    var out = 0;
    for (var j = 0; j < m; j++) { var w = ipow(q, m - 1 - j), d = Math.floor(X / w) % q; out = out * q + (d + t[j]) % q; }
    return out;
  }
  function shiftNet(B, tau) {
    var q = B.q, m = B.m, s = B.s, N = B.N, cw = B.cw, G = B.G, c, i, w = [];
    for (var j = 0; j < m; j++) w.push(ipow(q, m - 1 - j));
    var X = [];
    for (c = 0; c < s; c++) {
      var Y = new Int32Array(N), Xc = B.X[c], t = tau[c].map(function (x) { return mod(x, q); });
      for (i = 0; i < N; i++) {
        var x = Xc[i], o = 0;
        for (j = 0; j < m; j++) { var d = Math.floor(x / w[j]) % q; o += ((d + t[j]) % q) * w[j]; }
        Y[i] = o;
      }
      X.push(Y);
    }
    var cell = new Int32Array(B.cell.length).fill(-1), ok = true;
    for (i = 0; i < N; i++) {
      var idx = 0, mg = 1;
      for (c = 0; c < s; c++) { idx += Math.floor(X[c][i] / cw) * mg; mg *= G; }
      if (cell[idx] !== -1) ok = false;
      cell[idx] = i;
    }
    var out = Object.assign({}, B);
    out.X = X; out.cell = cell; out.onePerCell = ok; out.tau = tau.map(function (r) { return r.map(function (x) { return mod(x, q); }); });
    return out;
  }
  function zeroShift(s, m) { var t = []; for (var c = 0; c < s; c++) { var r = []; for (var j = 0; j < m; j++) r.push(0); t.push(r); } return t; }

  /* lem:shift: for the cells n and n+E (torus), the digit j of each coordinate changes by an integer in (-q,q) whose
     residue mod q is the same for every digital shift; the shift only decides which of its two representatives
     (sigma and sigma - q, or 0 alone) occurs. Returns, per coordinate: the residue, the options, the value. */
  function stepDigits(B, n, E, j) {
    var s = B.s, G = B.G, q = B.q, n2 = [], c;
    for (c = 0; c < s; c++) n2.push(mod(n[c] + E[c], G));
    var a = B.cell[cellIndex(B, n)], b = B.cell[cellIndex(B, n2)], out = [];
    for (c = 0; c < s; c++) {
      var dv = digit(B, c, b, j) - digit(B, c, a, j), sig = mod(dv, q);
      out.push({ value: dv, residue: sig, options: sig === 0 ? [0] : [sig, sig - q] });
    }
    return { n: n.slice(), n2: n2, i: a, j: b, coords: out };
  }

  /* prop:colshift: the bounds for a digital shift tau (tau[c] = (first, second, third) digit) of the column net C_q. */
  function colShiftBounds(q, tau) {
    var th = colTheory(q), w = th.w, W = q % 3 === 2 ? 2 : 4, wmax = Math.max.apply(null, w), r3 = Math.sqrt(3);
    var eq2 = mod(tau[0][1], q) === mod(tau[1][1], q) && mod(tau[1][1], q) === mod(tau[2][1], q);
    var eq3 = mod(tau[0][2], q) === mod(tau[1][2], q) && mod(tau[1][2], q) === mod(tau[2][2], q);
    var out = { W: W, wmax: wmax, eq2: eq2, eq3: eq3, exact: th.c, lbEvery: (1 - (W + 3) / q + 3 / (q * q)) / r3 };
    out.part = eq2 && eq3 ? 1 : (eq2 ? 2 : 3);
    if (eq2) out.lbEq2 = 1 - (7 * q - 3) / (r3 * q * q);
    else out.ub = (1 + (3 + wmax) / q - 3 / (q * q)) / r3;
    return out;
  }

  /* rem:wshift: second shift digits (t, t, t') of W_p keep the bound of prop:wnet(2) if t = 2t' or 2t'+1 (mod p). */
  function wShiftKeeps(p, t, tz) { var d = mod(t - 2 * tz, p); return d === 0 || d === 1; }

  /* proven bounds and explicit pairs of prop:twocoset and prop:wnet (integer scale p^3 for d*^2) */
  function twoCosetBounds(p) {
    var r = Math.round(p / 8), out = { limit: Math.sqrt(66) / 8 };
    if (p >= 41) out.lb = Math.sqrt(33 / 32 - 41 / (16 * p)) - Math.sqrt(3) / p;
    if (p >= 7) { var a = p * p - 2 * p + 3, b = (r - 1) * p + 4, c = (r - 1) * p + 6; out.dstar2 = a * a + b * b + c * c; out.ub = Math.sqrt(out.dstar2) / (p * p); }
    return out;
  }
  function wBounds(p) {
    var h = (p - 1) / 2, r = Math.floor(p / 48), out = { limit: Math.sqrt(281) / 16, muStar: Math.sqrt((72 - 8 * Math.sqrt(31)) / 25) };
    if (p >= 53) {
      out.lb = Math.sqrt(281 / 256 - 345 / (128 * p)) - Math.sqrt(3) / p;
      var a = p * p - (6 * r + 2) * p - 2, b = (6 * r + 3) * p, c = (h + 3 * r + 2) * p;
      out.dstar2 = a * a + b * b + c * c; out.ub = Math.sqrt(out.dstar2) / (p * p);
    }
    return out;
  }
  /* the two contacts of W_p in the limit (Table tab:wcontacts rows (a), (b)) and the family optimum (prop:wfamily) */
  function qa(e) { return 5 / 4 - 9 * e + 81 * e * e; }
  function qb(e) { return 1 + 4 * e + 36 * e * e; }
  /* prop:wfamily(1), (2): for 0 < eps <= 3/100 the squared value of W_p without its third digits is min(q_a, q_b)(eps),
     eps = rho/(2p) (p >= 53); delta N^(1/3) differs from its square root by less than sqrt3/p. */
  function wNoJitter(p) { var e = wNet(p).eps; return e > 0.03 ? null : Math.sqrt(Math.min(qa(e), qb(e))); }
  var EPS_STAR = (13 - 2 * Math.sqrt(31)) / 90, MU_STAR = Math.sqrt((72 - 8 * Math.sqrt(31)) / 25);

  /* the step along the axis `ax` from the cell n (graph forms with depths (1,...,1)): the difference vector D of the two
     points (toroidal representative, integer scale q^m; D/cw in cell units) and the wrap pattern of the second digit:
     coordinate c wraps if its second digit goes down although the step raises it modulo q (residue > 0). */
  function axisStep(B, n, ax) {
    var s = B.s, E = [], c, D = [], len2 = 0, key = '';
    for (c = 0; c < s; c++) E.push(c === ax ? 1 : 0);
    var st = stepDigits(B, n, E, 1);
    for (c = 0; c < s; c++) {
      var d = torDiff(B.X[c][st.j] - B.X[c][st.i], B.W); D.push(d); len2 += d * d;
      key += st.coords[c].value < 0 && st.coords[c].residue > 0 ? '1' : '0';
    }
    return { n: st.n, n2: st.n2, i: st.i, j: st.j, D: D, len: Math.sqrt(len2) / B.cw, len2: len2, key: key, digits: st.coords };
  }
  /* all steps along `ax`, grouped by wrap pattern: number of cells, shortest step (cell units) and where it occurs */
  function axisSteps(B, ax) {
    var s = B.s, G = B.G, q = B.q, W = B.W, cw = B.cw, m = B.m, wd = ipow(q, m - 2), groups = {}, c, n = new Int32Array(s), stride = 1;
    for (c = 0; c < ax; c++) stride *= G;
    for (var idx = 0; idx < B.cell.length; idx++) {
      var idx2 = n[ax] === G - 1 ? idx - (G - 1) * stride : idx + stride, i = B.cell[idx], j = B.cell[idx2], len2 = 0, key = '';
      for (c = 0; c < s; c++) {
        var xi = B.X[c][i], xj = B.X[c][j], d = torDiff(xj - xi, W);
        len2 += d * d;
        var dv = Math.floor(xj / wd) % q - Math.floor(xi / wd) % q;
        key += dv < 0 && mod(dv, q) > 0 ? '1' : '0';
      }
      var g = groups[key] || (groups[key] = { key: key, count: 0, minLen2: Infinity, n: null });
      g.count++;
      if (len2 < g.minLen2) { g.minLen2 = len2; g.n = Array.from(n); }
      for (c = 0; c < s; c++) { if (++n[c] < G) break; n[c] = 0; }
    }
    return Object.keys(groups).sort().map(function (k) { var g = groups[k]; g.minLen = Math.sqrt(g.minLen2) / cw; return g; });
  }

  /* cor:colceil, thm:colmin: the three steps [n] -> [n+e_x] -> [n+e_x+e_y] -> [n+1] = [n] of a column point set.
     Given the residues (mod 1, in periods q^2) of the first two height steps, the third is forced by the closing
     condition; g = least distance of the three from 2/3 + Z. Returns g (<= 1/3 always, cor:colceil). */
  function colCeil(a, b) {
    var r = [mod1(a), mod1(b), mod1(-a - b)], g = Infinity;
    r.forEach(function (x) { var d = Math.abs(x - 2 / 3); d = Math.min(d, 1 - d); if (d < g) g = d; });
    return { r: r, sum: r[0] + r[1] + r[2], g: g, c: Math.sqrt(2 / 3 + 3 * g * g) };
  }
  function mod1(x) { var y = x - Math.floor(x); return y >= 1 ? 0 : y; }
  /* the same for C_q itself: step values Delta_i([n]) of the heights phi, the triangle through the column [n], and
     g over all columns and directions (thm:colmin: d^2 = (2 q^4 + 9 g^2)/3 at integer scale q^3; 3g is an integer). */
  function colTriangle(q, n) {
    var a = colNet(q).a, qq = q * q;
    function phi(v) { return colPhi(q, a, v); }
    var m1 = [n[0] + 1, n[1], n[2]], m2 = [n[0] + 1, n[1] + 1, n[2]], m3 = [n[0] + 1, n[1] + 1, n[2] + 1];
    var st = [mod(phi(m1) - phi(n), qq), mod(phi(m2) - phi(m1), qq), mod(phi(m3) - phi(m2), qq)];
    var g3 = Infinity, v = [0, 0, 0];
    for (v[0] = 0; v[0] < q; v[0]++) for (v[1] = 0; v[1] < q; v[1]++) for (v[2] = 0; v[2] < q; v[2]++) for (var i = 0; i < 3; i++) {
      var w = v.slice(); w[i] += 1;
      var D3 = 3 * mod(phi(w) - phi(v), qq), d = Math.abs(D3 - 2 * qq) % (3 * qq); d = Math.min(d, 3 * qq - d);
      if (d < g3) g3 = d;
    }
    return { steps: st, sum: st[0] + st[1] + st[2], g3: g3, d2: (2 * qq * qq + g3 * g3) / 3 };
  }

  /* exact toroidal minimum distance, faster cell scan for the larger nets of pages 2 and 3 (same result as minDist).
     Coordinates are stored by cell; the offsets e in {-R..R}^s (one of each pair +-e) are scanned for R = 1, then
     R = 2 with the lower bound sum_c ((|e_c| - 1) cw)^2 (two points whose cells differ by |e_c| >= 2 differ by more
     than (|e_c| - 1) cw in that coordinate). Exact once best <= (R cw)^2. Needs G > 2R (else falls back to minDist). */
  function minDistFast(B) {
    var s = B.s, G = B.G, cw = B.cw, W = B.W, half = W / 2, cells = B.cell.length, c, idx;
    if (G <= 4) return minDist(B, true);
    var Y = [];
    for (c = 0; c < s; c++) { var y = new Float64Array(cells), Xc = B.X[c]; for (idx = 0; idx < cells; idx++) y[idx] = Xc[B.cell[idx]]; Y.push(y); }
    var strides = []; for (c = 0, idx = 1; c < s; c++, idx *= G) strides.push(idx);
    var best = Infinity, count = 0, pair = null, n = new Int32Array(s);
    for (var R = 1; R <= 2; R++) {
      var offs = offsets(s, R).filter(function (e) { return R === 1 || e.some(function (x) { return Math.abs(x) === 2; }); });
      for (var o = 0; o < offs.length; o++) {
        var e = offs[o], lb = 0;
        for (c = 0; c < s; c++) { var a = Math.max(0, Math.abs(e[c]) - 1) * cw; lb += a * a; }
        if (lb > best) continue;
        /* per coordinate and cell digit value: index increment of the wrapped neighbour */
        var add = [];
        for (c = 0; c < s; c++) { var t = new Float64Array(G); for (var v = 0; v < G; v++) t[v] = (mod(v + e[c], G) - v) * strides[c]; add.push(t); }
        n.fill(0);
        for (idx = 0; idx < cells; idx++) {
          var idx2 = idx;
          for (c = 0; c < s; c++) idx2 += add[c][n[c]];
          var d2 = 0;
          for (c = 0; c < s; c++) {
            var d = Y[c][idx2] - Y[c][idx];
            if (d > half) d -= W; else if (d < -half) d += W;
            d2 += d * d;
            if (d2 > best) break;
          }
          if (d2 <= best) {
            if (d2 < best) { best = d2; count = 0; pair = { a: idx, b: idx2 }; }
            count++;
          }
          for (c = 0; c < s; c++) { if (++n[c] < G) break; n[c] = 0; }
        }
      }
      if (best <= (R * cw) * (R * cw)) break;
    }
    var D = [];
    for (c = 0; c < s; c++) D.push(torDiff(Y[c][pair.b] - Y[c][pair.a], W));
    return { d2: best, c: Math.sqrt(best) / cw, count: count, pair: { i: B.cell[pair.a], j: B.cell[pair.b], D: D }, exact: best <= 4 * cw * cw };
  }

  /* lem:shiftcert: mu_n(d) = least toroidal |X' - X| over X in [0, b^n), X' = X plus d digitwise (d most significant
     first). Each nonzero digit of weight b^k contributes d_k b^k or (d_k - b) b^k, so mu is the distance mod b^n from D
     to the nearest sum of b^(k+1) over a subset of the support (greedy in the paper; here all subsets). */
  function muDigits(d, b) {
    var n = d.length, Wn = ipow(b, n), D = 0, sup = [];
    for (var j = 0; j < n; j++) { var k = n - 1 - j; D += d[j] * ipow(b, k); if (d[j]) sup.push(ipow(b, k + 1)); }
    var best = Infinity;
    for (var S = 0; S < (1 << sup.length); S++) {
      var t = D;
      for (var i = 0; i < sup.length; i++) if (S >> i & 1) t -= sup[i];
      var x = Math.abs(torDiff(t, Wn));
      if (x < best) best = x;
    }
    return best;
  }
  function muBrute(d, b) {
    var n = d.length, Wn = ipow(b, n), best = Infinity;
    for (var X = 0; X < Wn; X++) { var x = Math.abs(torDiff(shiftCoord(X, d, b, n) - X, Wn)); if (x < best) best = x; }
    return best;
  }
  function digitsOf(X, b, n) { var o = []; for (var j = 0; j < n; j++) o.push(Math.floor(X / ipow(b, n - 1 - j)) % b); return o; }
  /* lem:shiftcert(b) for a digital (unshifted) net over F_b: the digit differences of two points are the digit vectors
     of the points themselves (the net is linear), so min over all shifts of delta^2 = min over the nonzero points of
     sum_c mu_m(digits of X_c)^2 (integer scale b^m). Also returns a shift that attains it. */
  function everyShiftMin(B) {
    var b = B.q, m = B.m, s = B.s, best = Infinity, arg = -1, mus = null, c;
    var zero = -1;
    for (var i = 0; i < B.N; i++) { var z = true; for (c = 0; c < s; c++) if (B.X[c][i]) z = false; if (z) { zero = i; break; } }
    for (i = 0; i < B.N; i++) {
      if (i === zero) continue;
      var tot = 0, mm = [];
      for (c = 0; c < s; c++) { var mu = muDigits(digitsOf(B.X[c][i], b, m), b); mm.push(mu); tot += mu * mu; if (tot >= best) break; }
      if (tot < best) { best = tot; arg = i; mus = mm; }
    }
    /* a shift that realizes it: in each coordinate pick X with |X' - X| = mu, and shift the point 0 onto X */
    var tau = [];
    for (c = 0; c < s; c++) {
      var dd = digitsOf(B.X[c][arg], b, m), Wn = ipow(b, m), pick = 0;
      for (var X = 0; X < Wn; X++) if (Math.abs(torDiff(shiftCoord(X, dd, b, m) - X, Wn)) === mus[c]) { pick = X; break; }
      tau.push(digitsOf(pick, b, m));
    }
    return { d2: best, c: Math.sqrt(best) / B.cw, point: arg, delta: B.X.map(function (Xc) { return digitsOf(Xc[arg], b, m); }), mus: mus, tau: tau };
  }
  /* every shift tried (tiny nets only): min over all tau of the exact toroidal minimum distance */
  function bruteEveryShift(B) {
    var b = B.q, m = B.m, s = B.s, Wn = ipow(b, m), N = B.N, best = Infinity, c, i, j;
    var tables = [];             /* per coordinate: shifted value of every X under every shift t (t as an integer) */
    for (var t = 0; t < Wn; t++) { var row = new Int32Array(Wn), td = digitsOf(t, b, m); for (var X = 0; X < Wn; X++) row[X] = shiftCoord(X, td, b, m); tables.push(row); }
    /* every shift tau = (t_x, t_y, t_z), each t_c one of the b^m digit vectors; the lemma is not used */
    var tt = new Array(s).fill(0);
    for (;;) {
      var mn = Infinity;
      for (i = 0; i < N; i++) for (j = i + 1; j < N; j++) {
        var d2 = 0;
        for (c = 0; c < s; c++) { var d = torDiff(tables[tt[c]][B.X[c][j]] - tables[tt[c]][B.X[c][i]], Wn); d2 += d * d; }
        if (d2 < mn) mn = d2;
      }
      if (mn < best) best = mn;
      c = 0; while (c < s && tt[c] === Wn - 1) { tt[c] = 0; c++; }
      if (c === s) break;
      tt[c]++;
    }
    return { d2: best, c: Math.sqrt(best) / B.cw, shifts: Math.pow(Wn, s) };
  }

  /* lem:R2 for Q*_p: LB_2(p) = min(2, min_E |b| / p^2) over 0 != E in {-2..2}^5, with b_c = min over the options
     t (geometric digit, prop:Hk(1)) and u (second digit) of max(0, |p^2 E_c + p t + u| - 1). Valid for p >= 29. */
  var HALF5_STEPS = null;
  function half5Steps() {
    if (HALF5_STEPS) return HALF5_STEPS;
    var out = [], E = [-2, -2, -2, -2, -2], c;
    for (;;) {
      if (E.some(function (x) { return x; })) {
        var h = [], v = [], sm = 0;
        for (c = 0; c < 5; c++) { var a = 0, b = 0; for (var d = 0; d < 5; d++) { a += HALF5.H[c][d] * E[d]; b += HALF5.D1[c][d] * E[d]; } h.push(a); v.push(b); sm += E[c]; }
        out.push({ E: E.slice(), odd: mod(sm, 2) === 1, h: h, v: v });
      }
      c = 0; while (c < 5 && E[c] === 2) { E[c] = -2; c++; }
      if (c === 5) break;
      E[c]++;
    }
    HALF5_STEPS = out;
    return out;
  }
  function sgn(x) { return x > 0 ? 1 : (x < 0 ? -1 : 0); }
  function half5LB2(p) {
    var st = half5Steps(), pp = p * p, best = Infinity, arg = null;
    for (var e = 0; e < st.length; e++) {
      var S = st[e], tot = 0;
      for (var c = 0; c < 5 && tot < best; c++) {
        var h = S.h[c], T, U, v = S.v[c];
        if (S.odd) T = [(h + p) / 2, (h - p) / 2];
        else { var b0 = h / 2; T = b0 === 0 ? [0] : [b0, b0 - p * sgn(b0)]; }
        U = v === 0 ? [0] : [v, v - p * sgn(v)];
        var bc = Infinity;
        for (var a = 0; a < T.length; a++) for (var u = 0; u < U.length; u++) { var x = Math.abs(pp * S.E[c] + p * T[a] + U[u]); if (x < bc) bc = x; }
        bc -= 1;
        if (bc > 0) tot += bc * bc;
      }
      if (tot < best) { best = tot; arg = S.E; }
    }
    return { sq: best, lb: Math.min(2, Math.sqrt(best) / pp), E: arg };
  }
  /* prop:half5(2): the upper bound sqrt5/2 + 4 sqrt5/p for p > 32, and the limit sqrt5/2 */
  function half5Upper(p) { return p > 32 ? Math.sqrt(5) / 2 + 4 * Math.sqrt(5) / p : null; }

  /* def:dshift for one coordinate, every intermediate number: the digits of X and of the shift t, their digitwise sum
     mod q (no carries), and for contrast the ordinary sum X + T mod q^m with its carries. */
  function explainShift(X, t, q, m) {
    var Wm = ipow(q, m), T = 0, j;
    for (j = 0; j < m; j++) T = T * q + mod(t[j], q);
    var xd = digitsOf(X, q, m), td = digitsOf(T, q, m), sd = [], carries = [], carry = 0;
    for (j = 0; j < m; j++) sd.push((xd[j] + td[j]) % q);
    for (j = m - 1; j >= 0; j--) { var v = xd[j] + td[j] + carry; carry = v >= q ? 1 : 0; carries.unshift(carry); }
    var S = 0; for (j = 0; j < m; j++) S = S * q + sd[j];
    return { X: X, T: T, xd: xd, td: td, sd: sd, S: S, plain: (X + T) % Wm, plainDigits: digitsOf((X + T) % Wm, q, m), carries: carries };
  }

  /* rem:shiftshared, proof of prop:colshift(3): for the step along e_c of a (shifted) column net, which coordinates'
     second digits wrap, as a function of the shared digit value theta = a.n mod q of the starting cell (cells with
     n_c < q-1, so the cell digits do not carry). wraps[theta][d] = 1 if coordinate d wraps; consistent = the pattern
     depends on theta alone. */
  function colWrapWindows(B, c) {
    var q = B.q, a = B.net.a, wraps = [], seen = [], ok = true, E = [0, 0, 0], n = [0, 0, 0];
    E[c] = 1;
    for (n[0] = 0; n[0] < q; n[0]++) for (n[1] = 0; n[1] < q; n[1]++) for (n[2] = 0; n[2] < q; n[2]++) {
      if (n[c] === q - 1) continue;
      /* the shifted net is indexed by its own cells; theta is read off the unshifted rows: a.(n - tau_1) */
      var t1 = B.tau ? [B.tau[0][0], B.tau[1][0], B.tau[2][0]] : [0, 0, 0];
      var th = mod(a[0] * (n[0] - t1[0]) + a[1] * (n[1] - t1[1]) + a[2] * (n[2] - t1[2]), q);
      var st = stepDigits(B, n, E, 1), w = st.coords.map(function (o) { return o.value < 0 && o.residue > 0 ? 1 : 0; });
      if (!seen[th]) { seen[th] = true; wraps[th] = w; }
      else if (wraps[th].join() !== w.join()) ok = false;
    }
    return { wraps: wraps, consistent: ok };
  }

  /* summary of the grid of second-digit shifts (t, t, t') of W_p: how many keep delta N^(1/3) above `thr`, and whether
     they are exactly the shifts with t = 2t' or 2t'+1 (mod p); the extreme values on and off these two lines. */
  function wHeatSummary(p, grid, thr) {
    var cw = p * p, kept = 0, keptOff = 0, onMin = Infinity, offMax = 0;
    grid.forEach(function (e) {
      var c = Math.sqrt(e.d2) / cw, on = wShiftKeeps(p, e.t, e.tz);
      if (c > thr) { kept++; if (!on) keptOff++; }
      if (on) onMin = Math.min(onMin, c); else offMax = Math.max(offMax, c);
    });
    return { total: grid.length, kept: kept, keptOff: keptOff, onLines: 2 * p, onMin: onMin, offMax: offMax };
  }

  /* ================================================================ page 1: the frame, boxes and scrambles */
  /* the 3D frame of the places infinity, 0, 1 (the Moebius frame of sec:frames): generators (T^2, I, T), unscrambled.
     P_{k,q} of def:net is this frame with the lower-triangular scramble L applied to every coordinate. */
  function frame3(k) {
    var P = pNet(k), m = 3 * k, sk = k % 2 === 1 ? 1 : -1, tau = zeros(m, m), i, l;
    for (l = 0; l < m; l++) for (i = 0; i < m; i++) tau[i][l] = (i % 2 ? -1 : 1) * binom(m - 1 - l, i) + 0;
    var T = tau.map(function (r) { return r.map(function (x) { return sk * x + 0; }); });
    return { kind: 'F', s: 3, m: m, k: k, C: [mul(T, T), eye(m), T], L: mul(P.C[1], eye(m)) };
  }
  /* exact integer determinant (Bareiss, fraction-free) */
  function detInt(A) {
    var n = A.length; if (!n) return 1;
    var M = A.map(function (r) { return r.slice(); }), sign = 1, prev = 1, i, j, k;
    for (k = 0; k < n - 1; k++) {
      if (M[k][k] === 0) {
        for (i = k + 1; i < n && M[i][k] === 0; i++);
        if (i === n) return 0;
        var t = M[k]; M[k] = M[i]; M[i] = t; sign = -sign;
      }
      for (i = k + 1; i < n; i++) for (j = k + 1; j < n; j++) M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) / prev;
      prev = M[k][k];
    }
    return sign * M[n - 1][n - 1];
  }
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  /* lem:nie: the box matrix of the shape d stacks the first d_c rows of each (integer) generator matrix; every box of
     that shape holds exactly one point iff its determinant is a unit mod q. keep: rows with index >= keep are zero
     (keep = k+1: the net without its deeper digits). */
  function boxMatrix(C, d, q, keep) {
    var A = [];
    for (var c = 0; c < C.length; c++) for (var j = 0; j < d[c]; j++) A.push(C[c][j].map(function (x) { return keep !== undefined && j >= keep ? 0 : x + 0; }));
    return A;
  }
  function boxDet(C, d, q, keep) {
    var A = boxMatrix(C, d, q, keep), D = detInt(A), r = mod(D, q);
    return { d: d.slice(), A: A, det: D, mod: r, unit: gcd(r, q) === 1 };
  }
  function boxTable(net, q, keep) {
    return compositions(net.m, net.s).map(function (d) { return boxDet(net.C, d, q, keep); });
  }
  /* the number of points in every elementary box of the shape d (a built, possibly truncated, net) */
  function boxOccupancy(B, d) {
    var s = B.s, m = B.m, q = B.q, div = [], mult = [], mm = 1, c;
    for (c = 0; c < s; c++) { div.push(ipow(q, m - d[c])); mult.push(mm); mm *= ipow(q, d[c]); }
    var counts = new Int32Array(mm);
    for (var i = 0; i < B.N; i++) { var b = 0; for (c = 0; c < s; c++) b += Math.floor(B.X[c][i] / div[c]) * mult[c]; counts[b]++; }
    var empty = 0, one = 0, many = 0;
    for (var j = 0; j < mm; j++) { if (counts[j] === 0) empty++; else if (counts[j] === 1) one++; else many++; }
    return { d: d.slice(), counts: counts, empty: empty, one: one, many: many, dims: d.map(function (x) { return ipow(q, x); }) };
  }
  /* inverse of an integer matrix mod q (Gauss-Jordan with unit pivots); null if not invertible */
  function invMod(A, q) {
    var n = A.length, M = A.map(function (r, i) { return r.map(function (x) { return mod(x, q); }).concat(eye(n)[i]); }), i, j, k;
    function inv(a) { for (var x = 1; x < q; x++) if (mod(a * x, q) === 1) return x; return 0; }
    for (k = 0; k < n; k++) {
      for (i = k; i < n && gcd(M[i][k], q) !== 1; i++);
      if (i === n) return null;
      var t = M[k]; M[k] = M[i]; M[i] = t;
      var iv = inv(M[k][k]);
      M[k] = M[k].map(function (x) { return mod(x * iv, q); });
      for (i = 0; i < n; i++) if (i !== k && M[i][k]) { var f = M[i][k]; M[i] = M[i].map(function (x, j2) { return mod(x - f * M[k][j2], q); }); }
    }
    return M.map(function (r) { return r.slice(n); });
  }
  /* the scramble that turns the generator matrix Cf into Ct (both mod q): L = Ct Cf^(-1); lower: L is lower
     triangular with unit diagonal, i.e. each digit of the coordinate gets a combination of its earlier digits. */
  function scrambleBetween(Cf, Ct, q) {
    var Li = invMod(Cf, q); if (!Li) return null;
    var L = mul(Ct.map(function (r) { return r.map(function (x) { return mod(x, q); }); }), Li).map(function (r) { return r.map(function (x) { return mod(x, q); }); });
    var lower = true;
    for (var i = 0; i < L.length; i++) for (var j = 0; j < L.length; j++) {
      if (j > i && L[i][j] !== 0) lower = false;
      if (j === i && gcd(L[i][i], q) !== 1) lower = false;
    }
    return { L: L, lower: lower };
  }

  /* two points in the cells n and n+E (torus): their difference D (toroidal representative, integer scale q^m) and the
     change of the digit j of every coordinate (stepDigits). */
  function cellStep(B, n, E, j) {
    var st = stepDigits(B, n, E, j), D = [];
    for (var c = 0; c < B.s; c++) D.push(torDiff(B.X[c][st.j] - B.X[c][st.i], B.W));
    var len2 = 0; D.forEach(function (x) { len2 += x * x; });
    return { n: st.n, n2: st.n2, D: D, len: Math.sqrt(len2) / B.cw, digits: st.coords };
  }
  /* rows below the geometric digit of a scramble L (rows k+1, ...): 'same' if the row is e_j, 'negated' if -e_j */
  function deeperRows(L, k, q) {
    var out = [];
    for (var i = k + 1; i < L.length; i++) {
      var r = L[i], other = r.some(function (x, j) { return j !== i && x !== 0; });
      out.push(other ? 'mixed' : (r[i] === 1 ? 'same' : (r[i] === q - 1 ? 'negated' : 'scaled')));
    }
    return out;
  }

  return { binom: binom, mul: mul, mod: mod, ipow: ipow, hammersley2D: hammersley2D, pNet: pNet, colNet: colNet,
           colW: colW, build: build, truncate: truncate, digit: digit, cellCoords: cellCoords, cellIndex: cellIndex,
           minDist: minDist, boxCheck: boxCheck, compositions: compositions, latticeMin: latticeMin, cMain: cMain,
           colTheory: colTheory, cycle: cycle, layer: layer, explain: explain, PY_LISTING: PY_LISTING,
           pyProgram: pyProgram,
           isPrime: isPrime, primesIn: primesIn, torDiff: torDiff, graphNet: graphNet, twoCoset: twoCoset, wNet: wNet,
           HALF5: HALF5, half5: half5, shiftCoord: shiftCoord, shiftNet: shiftNet, zeroShift: zeroShift,
           stepDigits: stepDigits, colShiftBounds: colShiftBounds, wShiftKeeps: wShiftKeeps,
           twoCosetBounds: twoCosetBounds, wBounds: wBounds, qa: qa, qb: qb, EPS_STAR: EPS_STAR, MU_STAR: MU_STAR,
           axisStep: axisStep, axisSteps: axisSteps, colCeil: colCeil, colTriangle: colTriangle, colPhi: colPhi, muDigits: muDigits,
           muBrute: muBrute, digitsOf: digitsOf, everyShiftMin: everyShiftMin, bruteEveryShift: bruteEveryShift,
           half5LB2: half5LB2, half5Upper: half5Upper, minDistFast: minDistFast,
           explainShift: explainShift, colWrapWindows: colWrapWindows, wHeatSummary: wHeatSummary, wNoJitter: wNoJitter,
           frame3: frame3, detInt: detInt, boxMatrix: boxMatrix, boxDet: boxDet, boxTable: boxTable,
           boxOccupancy: boxOccupancy, invMod: invMod, scrambleBetween: scrambleBetween, cellStep: cellStep, deeperRows: deeperRows };
})();
