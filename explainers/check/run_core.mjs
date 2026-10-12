// run_core.mjs -- evaluate explainers/netcore.js under node and dump the nets of anatomy.html (page 1).
//   node run_core.mjs <netcore.js> <out.json>
// The pages' math lives in netcore.js (loaded by every page with <script src="netcore.js">); this script runs exactly
// that file (vm sandbox, no DOM) and
// writes, for each net shown on the page, the generator matrices mod q, all points (integer coordinates), the exact
// toroidal and Euclidean minimum distances, the elementary-box check, and the holonomy cycles of section 3.
import fs from 'fs';
import vm from 'vm';

const [, , corePath, outPath] = process.argv;
const src = fs.readFileSync(corePath, 'utf8');
const ctx = {};
vm.createContext(ctx);
vm.runInContext(src + '\n;this.NetCore = NetCore;', ctx);
const NC = ctx.NetCore;

const t0 = Date.now();
const out = { nets: [], cycles: {}, cmain: {}, coltheory: {} };
function dump(name, net, q) {
  const B = NC.build(net, q);
  const tor = NC.minDist(B, true);
  const euc = NC.minDist(B, false);
  const rec = {
    name, q, s: B.s, m: B.m, k: B.k, N: B.N, onePerCell: B.onePerCell,
    C: B.Cq,
    X: B.X.map((a) => Array.from(a)),
    tor: { d2: tor.d2, count: tor.count, pair: tor.pair },
    euc: { d2: euc.d2, count: euc.count },
    box: NC.boxCheck(B),
  };
  if (net.kind === '2D' && B.k + 1 < B.m) {
    const lat = NC.minDist(NC.truncate(B, B.k + 1), true);
    rec.lat = { d2: lat.d2, count: lat.count };
    rec.lam = NC.latticeMin(net.M, q);
  }
  out.nets.push(rec);
}
// section 1: every (q, k, layer) the sliders allow (q = 2..13, q^k <= 64)
for (let q = 2; q <= 13; q++) {
  for (let k = 1; k <= 3; k++) {
    if (k > 1 && q ** k > 64) continue;
    for (const v of ['rotated', 'frame']) dump(`H2-${v}-q${q}-k${k}`, NC.hammersley2D(k, v), q);
  }
}
// section 2: P_{2,q}, q = 4..7, and every column net with q^3 <= 1e5
for (const q of [4, 5, 6, 7]) dump(`P-q${q}-k2`, NC.pNet(2), q);
for (const q of [3, 5]) dump(`P-q${q}-k1`, NC.pNet(1), q);
for (let q = 5; q ** 3 <= 100000; q++) if (q % 2 && q % 3) dump(`C-q${q}`, NC.colNet(q), q);
// section 3: cycles for every q on the slider
for (let q = 5; q <= 97; q++) {
  if (!(q % 2 && q % 3)) continue;
  out.cycles[q] = [0, 1, 2].map((i) => NC.cycle(q, i).xs);
  out.coltheory[q] = NC.colTheory(q);
}
for (let q = 4; q <= 16; q++) out.cmain[q] = NC.cMain(q);
// section 0: the worked example, NetCore.explain for every net/q/k the selectors allow (sampled indices) and the
// Python reference listing printed in step 6.
out.explain = [];
out.pyListing = NC.PY_LISTING;
out.programs = [];
let seed = 12345;
const rnd = (N) => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % N; };
const exNets = [];
for (const v of ['rotated', 'frame']) for (let q = 2; q <= 13; q++) for (const k of [1, 2]) exNets.push([`H2-${v}-q${q}-k${k}`, NC.hammersley2D(k, v), q]);
for (let q = 2; q <= 13; q++) for (const k of [1, 2]) if (k === 1 || q <= 7) exNets.push([`P-q${q}-k${k}`, NC.pNet(k), q]);
for (const q of [5, 7, 11, 13]) exNets.push([`C-q${q}`, NC.colNet(q), q]);
for (const [name, net, q] of exNets) {
  const N = q ** net.m;
  const idx = N <= 1500 ? [...Array(N).keys()] : [0, N - 1, ...Array.from({ length: 120 }, () => rnd(N))];
  for (const i of idx) out.explain.push({ name, q, k: net.k, i, ex: NC.explain(net, q, i) });
}
for (const [name, net, q, i] of [['H2-rotated-q5-k2', NC.hammersley2D(2, 'rotated'), 5, 312], ['H2-frame-q3-k2', NC.hammersley2D(2, 'frame'), 3, 50],
                                 ['P-q5-k1', NC.pNet(1), 5, 77], ['P-q3-k2', NC.pNet(2), 3, 500], ['C-q7', NC.colNet(7), 7, 200]]) {
  const ex = NC.explain(net, q, i);
  out.programs.push({ name, q, i, X: ex.coords.map((o) => o.X), text: NC.pyProgram(net, q, i, ex.coords.map((o) => o.X)) });
}
// sections 1-4 and 8 (page 1, rev 2): box minors and box counts, the scrambles from the frame to the turned layer,
// the frame's wrap step, the 3D frame of the places infinity, 0, 1, and the nets that are not frame scrambles
const occSum = (o) => ({ empty: o.empty, one: o.one, many: o.many, n: o.counts.length });
out.boxes2d = [];
for (let q = 2; q <= 13; q++) for (let k = 1; k <= 3; k++) {
  if (q ** k > 64) continue;
  for (const v of ['frame', 'rotated']) {
    const net = NC.hammersley2D(k, v), B = NC.build(net, q), T = NC.truncate(B, k + 1), m = 2 * k;
    const rec = { name: `H2-${v}-q${q}-k${k}`, q, k, full: NC.boxTable(net, q).map((b) => ({ d: b.d, det: b.det, mod: b.mod, unit: b.unit, A: b.A })),
                  trunc: NC.boxTable(net, q, k + 1).map((b) => ({ d: b.d, det: b.det, mod: b.mod, unit: b.unit })), occ: [], occT: [] };
    for (let dx = 0; dx <= m; dx++) { rec.occ.push(occSum(NC.boxOccupancy(B, [dx, m - dx]))); rec.occT.push(occSum(NC.boxOccupancy(T, [dx, m - dx]))); }
    if (v === 'frame') {
      const R = NC.hammersley2D(k, 'rotated');
      rec.scr = [0, 1].map((c) => { const Cf = net.C[c].map((r) => r.map((x) => NC.mod(x, q))), Cr = R.C[c].map((r) => r.map((x) => NC.mod(x, q)));
        const sc = NC.scrambleBetween(Cf, Cr, q); return { L: sc.L, lower: sc.lower, deep: NC.deeperRows(sc.L, k, q) }; });
      rec.step = NC.cellStep(B, [q - 1, q - 1], [1, 1], k);
    }
    out.boxes2d.push(rec);
  }
}
out.frame3 = [];
for (const [k, q] of [[1, 3], [1, 5], [1, 7], [2, 4], [2, 5], [2, 6], [2, 7]]) {
  const net = NC.frame3(k), B = NC.build(net, q), md = NC.minDist(B, true);
  out.frame3.push({ k, q, C: B.Cq, X: q ** (3 * k) <= 20000 ? B.X.map((a) => Array.from(a)) : null, d2: md.d2, box: NC.boxCheck(B).ok,
                    dets: NC.boxTable(net, q).map((b) => b.det) });
}
out.direct = [];
for (const [kind, qs] of [['C', [5, 7, 11, 13]], ['T', [7, 11, 13, 17, 19, 23, 29]], ['W', [5, 7, 11, 13, 17]]]) for (const q of qs) {
  const net = kind === 'C' ? NC.colNet(q) : (kind === 'T' ? NC.twoCoset(q) : NC.wNet(q)), B = NC.build(net, q), T = NC.truncate(B, 2);
  const rec = { kind, q, C: B.Cq, full: NC.boxTable(net, q).map((b) => ({ d: b.d, mod: b.mod, unit: b.unit })),
                trunc: NC.boxTable(net, q, 2).map((b) => ({ d: b.d, mod: b.mod, unit: b.unit })), occ: [], occT: [] };
  for (const b of rec.full) { rec.occ.push(occSum(NC.boxOccupancy(B, b.d))); rec.occT.push(occSum(NC.boxOccupancy(T, b.d))); }
  out.direct.push(rec);
}
out.seconds = (Date.now() - t0) / 1000;
fs.writeFileSync(outPath, JSON.stringify(out));
console.log(`run_core: ${out.nets.length} nets, ${Object.keys(out.cycles).length} cycle sets, ${out.seconds}s`);
