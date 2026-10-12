// shiftmin.cpp -- rev 15.1: exact toroidal minimum distance of a digitally shifted m = 3 graph form over Z/p.
// Same scan as cellmin.cpp (whose output format it shares), with constants added to the second and third digits:
//   coordinate c of the point of cell n in [0,p)^3:  X_c(n) = p^2 n_c + p ((B_c.n + G2_c) mod p) + ((R_c.n + G3_c) mod p).
// (A digital shift of the first digits only re-indexes the cells and changes these constants, Lemma lem:shift.)
// Exactness: two points whose cells differ by >= 3 in some coordinate (toroidally) are > 2 p^2 apart, so it suffices
// to scan the cell steps E in {-2..2}^3; the per-E lower bound below (every wrap option of the second digit, jitter
// |.| < p) does not depend on the constants, which cancel in every digit difference modulo p.
// stdin: p, then the 3x3 rows B, the 3x3 rows R, then G2x G2y G2z G3x G3y G3z.   Output: d2 c E=(..) n=(..) scannedE=..
#include <cstdio>
#include <cmath>
#include <vector>
#include <algorithm>
typedef long long ll;
int main() {
  ll p, B[3][3], R[3][3], G2[3], G3[3];
  if (scanf("%lld", &p) != 1) return 1;
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { if (scanf("%lld", &B[i][j]) != 1) return 1; B[i][j] = ((B[i][j] % p) + p) % p; }
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { if (scanf("%lld", &R[i][j]) != 1) return 1; R[i][j] = ((R[i][j] % p) + p) % p; }
  for (int i = 0; i < 3; i++) { if (scanf("%lld", &G2[i]) != 1) return 1; G2[i] = ((G2[i] % p) + p) % p; }
  for (int i = 0; i < 3; i++) { if (scanf("%lld", &G3[i]) != 1) return 1; G3[i] = ((G3[i] % p) + p) % p; }
  ll N = p * p * p, p2 = p * p;
  struct EE { int e[3]; double lb; };
  std::vector<EE> Es;
  for (int a = -2; a <= 2; a++) for (int b = -2; b <= 2; b++) for (int c = -2; c <= 2; c++) {
    if (!a && !b && !c) continue;
    int e[3] = {a, b, c}; double lb = 0;
    for (int k = 0; k < 3; k++) {
      ll beta = ((B[k][0] * a + B[k][1] * b + B[k][2] * c) % p + p) % p; double best = 1e300;
      for (int kap = 0; kap <= 1; kap++) {
        if (kap && beta == 0) continue;
        double L = fabs((double)(e[k] * p2 + (beta - kap * p) * p)); double v = std::max(0.0, L - (double)(p - 1));
        best = std::min(best, v * v);
      }
      lb += best;
    }
    EE x; x.e[0] = a; x.e[1] = b; x.e[2] = c; x.lb = lb; Es.push_back(x);
  }
  std::sort(Es.begin(), Es.end(), [](const EE& x, const EE& y) { return x.lb < y.lb; });
  ll best = 4 * p2 * p2; int bestE[3] = {0, 0, 0}; ll bestn[3] = {0, 0, 0}; int scanned = 0;
  auto tor = [&](ll d) -> ll { d %= N; if (d < 0) d += N; if (d > N - d) d = N - d; return d; };
  auto X = [&](int k, const ll* n) -> ll {
    ll g = (B[k][0] * n[0] + B[k][1] * n[1] + B[k][2] * n[2] + G2[k]) % p, f = (R[k][0] * n[0] + R[k][1] * n[1] + R[k][2] * n[2] + G3[k]) % p;
    return n[k] * p2 + g * p + f;
  };
  for (auto& E : Es) {
    if (E.lb >= (double)best) break;
    scanned++;
    for (ll n0 = 0; n0 < p; n0++) for (ll n1 = 0; n1 < p; n1++) for (ll n2 = 0; n2 < p; n2++) {
      ll n[3] = {n0, n1, n2}, m[3] = {(n0 + E.e[0] + p) % p, (n1 + E.e[1] + p) % p, (n2 + E.e[2] + p) % p}; ll s = 0;
      for (int k = 0; k < 3; k++) { ll d = tor(X(k, m) - X(k, n)); s += d * d; if (s >= best) break; }
      if (s < best) { best = s; for (int k = 0; k < 3; k++) { bestE[k] = E.e[k]; bestn[k] = n[k]; } }
    }
  }
  printf("%lld %.6f E=(%d,%d,%d) n=(%lld,%lld,%lld) scannedE=%d\n", best, sqrt((double)best) / (double)p2, bestE[0], bestE[1],
         bestE[2], bestn[0], bestn[1], bestn[2], scanned);
}
