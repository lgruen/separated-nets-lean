// colmind.cpp -- exact toroidal minimum distances for the column nets C_q of the paper (m = 3, depths (1,1,1),
// integer scale q^3), with optional digital shifts; Theorem C cross-checks; box counting; class maximum.
// Written for colnets.py. Build: g++ -O3 -std=c++17 -o scripts/bin/colmind scripts/colmind.cpp
//
// A "column digital net" is given by q, a = (a0,a1,a2) and l = (l0,l1,l2) in (Z/q)^3 and a shift tau[c][k]
// (coordinate c, digit k = 0,1,2).  The point of index n in (Z/q)^3 has in coordinate c the digits
//     (n_c + tau[c][0],  a.n + tau[c][1],  l.n + tau[c][2])   (each mod q, no carries),
// i.e. X_c = q^2 d0 + q d1 + d2 in [0, q^3).  C_q itself is l = (-1,1,0), tau = 0.
//
// Kernels (all distances exact int64, toroidal on [0,q^3)^3):
//   brute(X)  all N(N-1)/2 pairs.
//   nbr(X)    one point per cell (cells = first digits; checked), pairs in the 26 neighbour cells only
//             (13 half-offsets).  Exact whenever the result is < (q^2+1)^2: a pair whose toroidal cell
//             difference has a component of size >= 2 differs by >= q^2+1 in that coordinate.  Prints cert=0
//             otherwise (and the caller must not trust it).
// Modes:
//   thmC <seed> <reps>   random column point sets X(n) = q^2 n + phi([n]) 1 at q = 2..13: arbitrary phi (with
//                        repeats), random bijections, random Lemma-B nets (odd q); brute vs Theorem C formula vs nbr.
//   dist                 stdin lines "q a0 a1 a2 l0 l1 l2 t00 t01 t02 t10 t11 t12 t20 t21 t22"; prints per line
//                        "d2 cert" (nbr kernel; brute instead when q <= 13 -- then cert=2).
//   shiftall q a0 a1 a2 l0 l1 l2 [dylo dyhi]   all shifts up to isometry: tau[0][*] = 0, tau[c][0] = 0, tau[c][1], tau[c][2]
//                        (c = 1,2) over (Z/q)^4; prints "dy dz ey ez d2 cert" per shift.
//   box                  stdin lines "q a0 a1 a2 l0 l1 l2": counts all 10 box shapes (d0+d1+d2 = 3); prints
//                        "1" iff every box holds exactly one point.
//   graph                cellmin's stdin format (p, 3 rows B, 3 rows R); exact d2 by brute force (small p only).
//   classmax <qlo> <qhi> Theorem C over all t=0 digital column nets (a, r) with units a_i, sum a = sum r = 0 mod q,
//                        unit minor a0 r1 - a1 r0, for q coprime to 6; prints q, max d2, #maximizers.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <climits>
#include <cmath>
#include <vector>
#include <array>
#include <string>
#include <random>
#include <numeric>
#include <algorithm>
using namespace std;
typedef long long ll;
typedef array<ll, 3> P3;

static ll Q, Q2, Q3;
static void setq(ll q) { Q = q; Q2 = q * q; Q3 = Q2 * q; }
static inline ll tor(ll x, ll y) { ll d = llabs(x - y) % Q3; return min(d, Q3 - d); }
static inline ll dist2(const P3& x, const P3& y) {
  ll s = 0; for (int c = 0; c < 3; c++) { ll d = tor(x[c], y[c]); s += d * d; } return s; }
static inline ll md(ll x) { x %= Q; return x < 0 ? x + Q : x; }

ll brute(const vector<P3>& X) {
  ll best = LLONG_MAX; size_t N = X.size();
  for (size_t i = 0; i < N; i++) for (size_t j = i + 1; j < N; j++) { ll d = dist2(X[i], X[j]); if (d < best) best = d; }
  return best;
}
// X indexed by cell (first digits): X[(c0*q+c1)*q+c2]; returns -1 if a cell is empty / hit twice
bool byCell(const vector<P3>& pts, vector<P3>& X) {
  int q = (int)Q; X.assign(q * q * q, P3{-1, -1, -1}); vector<char> seen(q * q * q, 0);
  for (auto& x : pts) { ll id = ((x[0] / Q2) * Q + x[1] / Q2) * Q + x[2] / Q2; if (seen[id]) return false; seen[id] = 1; X[id] = x; }
  return true;
}
ll nbr(const vector<P3>& pts, int* cert) {
  int q = (int)Q; vector<P3> X; if (!byCell(pts, X)) { *cert = -1; return -1; }
  static const int H[13][3] = {{1,-1,-1},{1,-1,0},{1,-1,1},{1,0,-1},{1,0,0},{1,0,1},{1,1,-1},{1,1,0},{1,1,1},
                               {0,1,-1},{0,1,0},{0,1,1},{0,0,1}};
  ll best = LLONG_MAX;
  for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) {
    const P3& x = X[(a * q + b) * q + c];
    for (auto& e : H) {
      int a2 = (a + e[0] + q) % q, b2 = (b + e[1] + q) % q, c2 = (c + e[2] + q) % q;
      if (a2 == a && b2 == b && c2 == c) continue;
      ll d = dist2(x, X[(a2 * q + b2) * q + c2]); if (d < best) best = d;
    }
  }
  *cert = best < (Q2 + 1) * (Q2 + 1) ? 1 : 0;
  return best;
}
vector<P3> colnet(const ll a[3], const ll l[3], const ll t[3][3]) {
  int q = (int)Q; vector<P3> X; X.reserve(q * q * q);
  for (ll n0 = 0; n0 < q; n0++) for (ll n1 = 0; n1 < q; n1++) for (ll n2 = 0; n2 < q; n2++) {
    ll h = md(a[0] * n0 + a[1] * n1 + a[2] * n2), j = md(l[0] * n0 + l[1] * n1 + l[2] * n2), n[3] = {n0, n1, n2};
    P3 p; for (int c = 0; c < 3; c++) p[c] = Q2 * md(n[c] + t[c][0]) + Q * md(h + t[c][1]) + md(j + t[c][2]);
    X.push_back(p);
  }
  return X;
}
// column point set from phi on T = (Z/q)^3/<1>, class coordinates (x,y) = (n0-n2, n1-n2) mod q
vector<P3> columnSet(const vector<ll>& phi) {
  int q = (int)Q; vector<P3> X; X.reserve(q * q * q);
  for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) {
    ll f = phi[md(a - c) * q + md(b - c)];
    X.push_back({(a * Q2 + f) % Q3, (b * Q2 + f) % Q3, (c * Q2 + f) % Q3});
  }
  return X;
}
// Theorem C: d2 = 2q^4/3 + 3 g^2, g = min_{i,c} dist(phi(c+[e_i]) - phi(c), 2q^2/3 + q^2 Z).
// Integer form: T = min dist(3*Delta, 2q^2 + 3q^2 Z) = 3g, d2 = (2q^4 + T^2)/3.
ll thmC(const vector<ll>& phi) {
  int q = (int)Q; ll T = LLONG_MAX; const int dx[3] = {1, 0, -1}, dy[3] = {0, 1, -1};
  for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) for (int i = 0; i < 3; i++) {
    ll D = phi[md(x + dx[i]) * q + md(y + dy[i])] - phi[x * q + y];
    ll m3 = 3 * Q2, r = ((3 * D - 2 * Q2) % m3 + m3) % m3; T = min(T, min(r, m3 - r));
  }
  ll num = 2 * Q2 * Q2 + T * T;
  if (num % 3) { fprintf(stderr, "thmC: non-integral\n"); exit(3); }
  return num / 3;
}
bool isNet(const vector<P3>& X) {
  int q = (int)Q;
  for (int d0 = 0; d0 <= 3; d0++) for (int d1 = 0; d1 <= 3 - d0; d1++) {
    int d[3] = {d0, d1, 3 - d0 - d1}; vector<int> cnt(q * q * q, 0);
    for (auto& x : X) {
      ll key = 0;
      for (int c = 0; c < 3; c++) { ll lead = x[c], base = 1; for (int k = 0; k < 3 - d[c]; k++) lead /= Q; for (int k = 0; k < d[c]; k++) base *= Q; key = key * base + lead; }
      if (++cnt[key] > 1) return false;
    }
  }
  return true;
}
static ll gcdll(ll a, ll b) { return b ? gcdll(b, a % b) : llabs(a); }
static bool unit(ll a) { return gcdll(md(a), Q) == 1; }

int main(int argc, char** argv) {
  if (argc < 2) { fprintf(stderr, "mode?\n"); return 1; }
  string mode = argv[1];
  if (mode == "thmC") {
    mt19937_64 rng(atoll(argv[2])); int reps = atoi(argv[3]);
    long tot = 0, bad = 0, nbad = 0, over = 0, cnt[3] = {0, 0, 0};
    for (int q = 2; q <= 13; q++) {
      setq(q);
      auto rnd = [&](ll m) { return (ll)(rng() % (unsigned long long)m); };
      for (int t = 0; t < 3; t++) for (int rep = 0; rep < reps; rep++) {
        vector<ll> phi(q * q);
        if (t == 0) for (auto& f : phi) f = rnd(Q2);                       // arbitrary, repeats allowed
        else if (t == 1) { iota(phi.begin(), phi.end(), 0); shuffle(phi.begin(), phi.end(), rng); }   // bijection
        else {                                                             // random Lemma-B net (odd q only)
          if (q % 2 == 0) continue;
          ll al, be; do { al = rnd(Q); be = rnd(Q); } while (!unit(al) || !unit(be) || !unit(al + be));
          vector<int> pi(q); iota(pi.begin(), pi.end(), 0); shuffle(pi.begin(), pi.end(), rng);
          vector<vector<int>> js(q); vector<int> used(q, 0);
          for (int h = 0; h < q; h++) { js[h].resize(q); iota(js[h].begin(), js[h].end(), 0); shuffle(js[h].begin(), js[h].end(), rng); }
          for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { int h = pi[md(al * x + be * y)]; phi[x * q + y] = (ll)h * q + js[h][used[h]++]; }
        }
        auto X = columnSet(phi); ll b = brute(X), f = thmC(phi); int ce; ll nb = nbr(X, &ce);
        tot++; cnt[t]++;
        if (b != f) { bad++; printf("MISMATCH q=%d type=%d brute=%lld formula=%lld\n", q, t, b, f); }
        if (nb != b || ce != 1) { nbad++; printf("NBR-MISMATCH q=%d type=%d brute=%lld nbr=%lld cert=%d\n", q, t, b, nb, ce); }
        if (b > Q2 * Q2) { over++; printf("ABOVE-q^4 q=%d d2=%lld\n", q, b); }
      }
    }
    printf("thmC sets=%ld arbitrary=%ld bijection=%ld lemmaB=%ld formula_mismatch=%ld nbr_mismatch=%ld above_q4=%ld\n",
           tot, cnt[0], cnt[1], cnt[2], bad, nbad, over);
  } else if (mode == "dist") {
    ll q, a[3], l[3], t[3][3];
    while (scanf("%lld", &q) == 1) {
      setq(q);
      for (int i = 0; i < 3; i++) { scanf("%lld", &a[i]); a[i] = md(a[i]); }
      for (int i = 0; i < 3; i++) { scanf("%lld", &l[i]); l[i] = md(l[i]); }
      for (int c = 0; c < 3; c++) for (int k = 0; k < 3; k++) { scanf("%lld", &t[c][k]); t[c][k] = md(t[c][k]); }
      auto X = colnet(a, l, t); int ce; ll d;
      if (q <= 13) { d = brute(X); ce = 2; } else d = nbr(X, &ce);
      printf("%lld %d\n", d, ce); fflush(stdout);
    }
  } else if (mode == "shiftall") {
    ll q = atoll(argv[2]); setq(q); ll a[3], l[3];
    for (int i = 0; i < 3; i++) { a[i] = md(atoll(argv[3 + i])); l[i] = md(atoll(argv[6 + i])); }
    ll dylo = argc > 9 ? atoll(argv[9]) : 0, dyhi = argc > 10 ? atoll(argv[10]) : q;
    for (ll dy = dylo; dy < dyhi; dy++) for (ll dz = 0; dz < q; dz++) for (ll ey = 0; ey < q; ey++) for (ll ez = 0; ez < q; ez++) {
      ll t[3][3] = {{0, 0, 0}, {0, dy, ey}, {0, dz, ez}};
      int ce; ll d = nbr(colnet(a, l, t), &ce);
      printf("%lld %lld %lld %lld %lld %d\n", dy, dz, ey, ez, d, ce);
    }
  } else if (mode == "box") {
    ll q, a[3], l[3]; ll t[3][3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
    while (scanf("%lld", &q) == 1) {
      setq(q);
      for (int i = 0; i < 3; i++) { scanf("%lld", &a[i]); a[i] = md(a[i]); }
      for (int i = 0; i < 3; i++) { scanf("%lld", &l[i]); l[i] = md(l[i]); }
      printf("%d\n", (int)isNet(colnet(a, l, t))); fflush(stdout);
    }
  } else if (mode == "graph") {
    ll p, B[3][3], R[3][3]; if (scanf("%lld", &p) != 1) return 1; setq(p);
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { scanf("%lld", &B[i][j]); B[i][j] = md(B[i][j]); }
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { scanf("%lld", &R[i][j]); R[i][j] = md(R[i][j]); }
    vector<P3> X;
    for (ll n0 = 0; n0 < p; n0++) for (ll n1 = 0; n1 < p; n1++) for (ll n2 = 0; n2 < p; n2++) {
      ll n[3] = {n0, n1, n2}; P3 x;
      for (int c = 0; c < 3; c++) x[c] = Q2 * n[c] + Q * md(B[c][0] * n0 + B[c][1] * n1 + B[c][2] * n2) + md(R[c][0] * n0 + R[c][1] * n1 + R[c][2] * n2);
      X.push_back(x);
    }
    printf("%lld\n", brute(X));
  } else if (mode == "classmax") {
    for (ll q = atoll(argv[2]); q <= atoll(argv[3]); q++) {
      if (gcdll(q, 6) != 1) continue; setq(q);
      vector<ll> T(q * q);   // tau(a, r) = min |3U + q^2| over U in qa + r + {0, -q if r != 0} + q^2 Z
      for (ll a = 0; a < q; a++) for (ll r = 0; r < q; r++) {
        ll best = LLONG_MAX;
        for (int li = 0; li < (r ? 2 : 1); li++) {
          ll v = 3 * (q * a + r - li * q) + Q2, m3 = 3 * Q2, x = ((v % m3) + m3) % m3; best = min(best, min(x, m3 - x));
        }
        T[a * q + r] = best;
      }
      vector<char> u(q); for (ll x = 0; x < q; x++) u[x] = gcdll(x, q) == 1;
      ll bt = -1, cnt = 0;
      for (ll a0 = 1; a0 < q; a0++) if (u[a0]) for (ll a1 = 1; a1 < q; a1++) if (u[a1]) {
        ll a2 = md(-a0 - a1); if (!u[a2]) continue;
        for (ll r0 = 0; r0 < q; r0++) {
          ll t0 = T[a0 * q + r0];
          for (ll r1 = 0; r1 < q; r1++) {
            if (!u[md(a0 * r1 - a1 * r0)]) continue;
            ll t = min(t0, min(T[a1 * q + r1], T[a2 * q + md(-r0 - r1)]));
            if (t > bt) { bt = t; cnt = 0; }
            if (t == bt) cnt++;
          }
        }
      }
      printf("%lld %lld %lld\n", q, (2 * Q2 * Q2 + bt * bt) / 3, cnt); fflush(stdout);
    }
  } else { fprintf(stderr, "unknown mode\n"); return 1; }
  return 0;
}
