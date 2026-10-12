// run_core23.mjs -- evaluate explainers/netcore.js under node and dump what shifts.html (page 2) and beyond.html
// (page 3) show: shifted nets and their exact minimum distances, the bounds printed next to them, the two-coset and
// rank-one nets T_p, W_p, the s = 5 net Q*_p and its certified relaxation, the base-2/3 every-shift minima.
//   node run_core23.mjs <netcore.js> <out.json> [a|b]
import fs from 'fs';
import vm from 'vm';

const [, , corePath, outPath, PART] = process.argv;
const want = (part) => !PART || PART === part;     // 'a': page 2, 'b': page 3 (run in parallel by crosscheck23.py)
const ctx = {};
vm.createContext(ctx);
vm.runInContext(fs.readFileSync(corePath, 'utf8') + '\n;this.NetCore = NetCore;', ctx);
const NC = ctx.NetCore;
const t0 = Date.now();
const lap = (w) => { if (process.env.LAPS) console.log(w, (Date.now() - t0) / 1000); };
let seed = 20261012;
const rnd = (n) => { seed = (seed * 1103515245 + 12345) % 2147483648; return Math.floor(seed / 65536) % n; };
const randTau = (s, m, q) => Array.from({ length: s }, () => Array.from({ length: m }, () => rnd(q)));
const arr = (B) => B.X.map((a) => Array.from(a));
const out = { shifted: [], col: [], wshift: [], wheat: [], tw: [], steps: [], tri: [], ceil: [], every: [], mu: [], half5: {}, bounds: {} };

// ---- page 2, section 1: the small nets of the shift demo (2D turned layer, column nets), with shifts
function dumpShift(name, net, q, tau, withPts) {
  const B = NC.build(net, q), S = NC.shiftNet(B, tau), md = NC.minDistFast(S);
  const rec = { name, q, s: B.s, m: B.m, k: B.k, C: B.Cq, tau: S.tau, d2: md.d2, count: md.count, onePerCell: S.onePerCell,
                d2un: NC.minDistFast(B).d2 };
  if (withPts) { rec.X = arr(S); rec.box = NC.boxCheck(S).ok; }
  // lem:shift: digit-difference residues at the closest pair's cells, unshifted and shifted
  const ncell = (BB, i) => BB.X.map((x) => Math.floor(x[i] / BB.cw));
  const n = ncell(S, md.pair.i), n2 = ncell(S, md.pair.j);
  const E = n.map((x, c) => NC.torDiff(n2[c] - x, S.G));
  rec.step = { n, E, sh: NC.stepDigits(S, n, E, B.k), un: NC.stepDigits(B, n, E, B.k) };
  return rec;
}
if (want('a')) {
for (const q of [3, 5, 7]) for (const k of [1, 2]) {
  if (q ** k > 64) continue;
  for (let r = 0; r < 4; r++) out.shifted.push(dumpShift(`H2-q${q}-k${k}`, NC.hammersley2D(k, 'rotated'), q, randTau(2, 2 * k, q), true));
}
for (const q of [4, 5, 6, 7]) for (let r = 0; r < 6; r++) out.shifted.push(dumpShift(`P-q${q}-k2`, NC.pNet(2), q, randTau(3, 6, q), q <= 5));
}
lap('// ---- page 2, section 3');
if (want('a')) {
// ---- page 2, section 3: column nets under shifts of the three kinds of prop:colshift
for (let q = 5; q <= 43; q++) {
  if (!(q % 2 && q % 3)) continue;
  for (let r = 0; r < 6; r++) {
    const tau = randTau(3, 3, q);
    if (r < 2) { tau[1][1] = tau[2][1] = tau[0][1]; tau[1][2] = tau[2][2] = tau[0][2]; }
    else if (r < 4) { tau[1][1] = tau[2][1] = tau[0][1]; }
    else if (tau[0][1] === tau[1][1] && tau[1][1] === tau[2][1]) tau[2][1] = (tau[2][1] + 1) % q;
    const rec = dumpShift(`C-q${q}`, NC.colNet(q), q, tau, q <= 13);
    rec.bounds = NC.colShiftBounds(q, tau);
    if (q <= 19) { const S = NC.shiftNet(NC.build(NC.colNet(q), q), tau); rec.windows = [0, 1, 2].map((c) => NC.colWrapWindows(S, c)); }
    out.col.push(rec);
  }
}
}
lap('// ---- page 2, section 4');
if (want('a')) {
// ---- page 2, section 4: W_p under shifts of the second digits; full grids at small p, the paper's shifts at 53, 101
for (const p of [11, 13]) {
  const B = NC.build(NC.wNet(p), p), grid = [];
  for (let t = 0; t < p; t++) for (let tz = 0; tz < p; tz++) {
    const S = NC.shiftNet(B, [[0, t, 0], [0, t, 0], [0, tz, 0]]);
    grid.push({ t, tz, d2: NC.minDistFast(S).d2, keeps: NC.wShiftKeeps(p, t, tz) });
  }
  out.wheat.push({ p, grid, summary: NC.wHeatSummary(p, grid, 0.5) });
}
for (const p of [53, 101]) {
  const B = NC.build(NC.wNet(p), p);
  const shs = p === 101 ? [[7, 7, 7], [1, 1, 0]]
                        : [[0, 0, 1], [7, 7, 7], [1, 1, 0], [3, 3, 1], [5, 5, 2], [2, 2, 0], [10, 10, 5], [21, 21, 10]];
  for (const sh of shs) {
    const third = [rnd(p), rnd(p), rnd(p)];
    for (const th of p === 101 ? [[0, 0, 0]] : [[0, 0, 0], third]) {
      const tau = [[0, sh[0], th[0]], [0, sh[1], th[1]], [0, sh[2], th[2]]];
      const S = NC.shiftNet(B, tau);
      out.wshift.push({ p, tau, d2: NC.minDistFast(S).d2, keeps: NC.wShiftKeeps(p, sh[0], sh[2]), bounds: NC.wBounds(p) });
    }
  }
}
}
lap('// ---- page 3: T_p');
if (want('b')) {
// ---- page 3: T_p and W_p, every prime 5..101 (exact), bounds; points of the small ones
for (const p of NC.primesIn(5, 101)) for (const kind of ['T', 'W']) {
  const net = kind === 'T' ? NC.twoCoset(p) : NC.wNet(p), B = NC.build(net, p), md = NC.minDistFast(B);
  const rec = { kind, p, C: B.Cq, d2: md.d2, count: md.count, onePerCell: B.onePerCell,
                bounds: kind === 'T' ? NC.twoCosetBounds(p) : NC.wBounds(p), eps: net.eps, rho: net.rho, r: net.r };
  if (p <= 41) { rec.X = arr(B); rec.box = NC.boxCheck(B).ok; }
  out.tw.push(rec);
}
}
lap('for (const [kind, p, ax, tau]');
if (want('b')) {
for (const [kind, p, ax, tau] of [['W', 101, 2, null], ['W', 101, 2, [[0, 0, 0], [0, 0, 0], [0, 1, 0]]], ['T', 101, 0, null],
                                  ['W', 29, 2, null], ['W', 29, 2, [[0, 0, 0], [0, 0, 0], [0, 1, 0]]], ['T', 29, 0, null], ['W', 37, 2, [[0, 3, 0], [0, 3, 0], [0, 0, 0]]]]) {
  let B = NC.build(kind === 'T' ? NC.twoCoset(p) : NC.wNet(p), p);
  if (tau) B = NC.shiftNet(B, tau);
  const g = NC.axisSteps(B, ax);
  const one = [];
  for (let r = 0; r < 30; r++) { const n = [rnd(p), rnd(p), rnd(p)]; const a = NC.axisStep(B, n, ax); one.push({ n, D: a.D, key: a.key }); }
  out.steps.push({ kind, p, ax, tau, groups: g, one, d2: p <= 29 ? NC.minDistFast(B).d2 : null });
}
}
lap('// ---- page 3, section 1');
if (want('b')) {
// ---- page 3, section 1: the column ceiling
for (let q = 5; q <= 61; q++) if (q % 2 && q % 3) out.tri.push({ q, n: [rnd(q), rnd(q), rnd(q)], tri: null, d2: NC.colTheory(q).d2 });
out.tri.forEach((t) => { t.tri = NC.colTriangle(t.q, t.n); });
for (let a = 0; a < 120; a++) for (let b = 0; b < 120; b++) { const r = NC.colCeil(a / 120, b / 120); out.ceil.push([a, b, r.g, r.sum]); }
}
lap('// ---- page 2, section 5');
if (want('a')) {
// ---- page 2, section 5: bases two and three
for (const [k, b] of [[1, 2], [2, 2], [3, 2], [1, 3], [2, 3]]) {
  const B = NC.build(NC.pNet(k), b), ev = NC.everyShiftMin(B), S = NC.shiftNet(B, ev.tau);
  const rec = { k, b, m: B.m, X: arr(B), C: B.Cq, box: NC.boxCheck(B).ok, d2un: NC.minDist(B, true).d2, every: ev,
                atTau: NC.minDist(S, true).d2, random: [] };
  for (let r = 0; r < 25; r++) { const tau = randTau(3, B.m, b); rec.random.push({ tau, d2: NC.minDist(NC.shiftNet(B, tau), true).d2 }); }
  if (B.N <= 27) rec.brute = NC.bruteEveryShift(B);
  out.every.push(rec);
}
for (const b of [2, 3]) for (let n = 1; n <= (b === 2 ? 7 : 5); n++) {
  for (let D = 0; D < b ** n; D++) { const d = NC.digitsOf(D, b, n); out.mu.push({ b, d, mu: NC.muDigits(d, b), brute: NC.muBrute(d, b) }); }
}
}
lap('// ---- page 3, section 4');
if (want('b')) {
// ---- page 3, section 4: Q*_p
const h5 = out.half5;
h5.nets = [];
for (const p of [7, 11, 13]) {
  const B = NC.build(NC.half5(p), p), md = NC.minDistFast(B);
  h5.nets.push({ p, C: B.Cq, d2: md.d2, count: md.count, X: p <= 11 ? arr(B) : null, box: p === 7 ? NC.boxCheck(B).ok : null, onePerCell: B.onePerCell });
}
h5.lb2 = NC.primesIn(29, 199).map((p) => ({ p, ...NC.half5LB2(p), ub: NC.half5Upper(p) }));
out.wnoj = [53, 59, 61, 97, 101, 199, 401].map((p) => [p, NC.wNoJitter(p)]);
{ const B = NC.build(NC.half5(17), 17), md = NC.minDistFast(B); h5.nets.push({ p: 17, C: B.Cq, d2: md.d2, count: md.count, X: null, box: null, onePerCell: B.onePerCell }); }
out.ceilC = [[0.1, 0.2], [0.3, 0.3], [0.5, 0.9], [0, 0]].map(([a, b]) => [a, b, NC.colCeil(a, b)]);
}
if (want('a')) {
out.explainShift = [];
for (const [q, m] of [[2, 5], [3, 4], [5, 2], [5, 4], [7, 3], [13, 2]]) for (let r = 0; r < 40; r++) {
  const X = rnd(q ** m), t = Array.from({ length: m }, () => rnd(q));
  out.explainShift.push({ q, m, X, t, ex: NC.explainShift(X, t, q, m) });
}
}
lap('// ---- constants');
out.bounds = { qa: [0, 0.01, 1 / 48, 0.03].map((e) => [e, NC.qa(e), NC.qb(e)]), EPS_STAR: NC.EPS_STAR, MU_STAR: NC.MU_STAR,
               cMain: [4, 5, 6, 7].map((q) => [q, NC.cMain(q)]) };
out.seconds = (Date.now() - t0) / 1000;
fs.writeFileSync(outPath, JSON.stringify(out));
console.log(`run_core23: ${out.shifted.length} shifted nets, ${out.col.length} shifted column nets, ${out.tw.length} T/W nets, ${out.seconds}s`);
