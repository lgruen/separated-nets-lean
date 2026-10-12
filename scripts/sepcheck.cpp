// Exact toroidal min D2 over neighbour cells; checks the Lean integer forms of P_sep / Q_sep.
#include "../../cpp/genz3net.h"  // build: g++ -O3 -std=c++17 -o sepcheck sepcheck.cpp ; run: sepcheck q k [two]
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
typedef __int128 i128;
int main(int argc, char** argv) {
  unsigned q = atoi(argv[1]), k = atoi(argv[2]); bool two = argc > 3 && !strcmp(argv[3], "two");
  GenZ3Net g(q, 3 * k, two ? GenZ3Net::TwoDigit : GenZ3Net::EK);
  uint64_t N = g.n, G = 1; for (unsigned i = 0; i < k; ++i) G *= q;   // cells per axis
  uint64_t W = N / G;                                                 // cell width
  std::vector<uint64_t> X(N), Y(N), Z(N); std::vector<int64_t> cell(G * G * G, -1);
  for (uint64_t i = 0; i < N; ++i) { g.get(i, X[i], Y[i], Z[i]);
    uint64_t c = (X[i] / W) * G * G + (Y[i] / W) * G + Z[i] / W; if (cell[c] >= 0) { puts("DUP CELL"); return 1; } cell[c] = i; }
  auto cr = [&](int64_t u) { int64_t r = ((u % (int64_t)N) + N) % N; return std::min<int64_t>(r, N - r); };
  i128 best = -1;
  for (uint64_t i = 0; i < N; ++i) {
    uint64_t cx = X[i] / W, cy = Y[i] / W, cz = Z[i] / W;
    for (int ex = -1; ex <= 1; ++ex) for (int ey = -1; ey <= 1; ++ey) for (int ez = -1; ez <= 1; ++ez) {
      if (!ex && !ey && !ez) continue;
      uint64_t j = cell[((cx + G + ex) % G) * G * G + ((cy + G + ey) % G) * G + (cz + G + ez) % G];
      i128 a = cr((int64_t)X[i] - (int64_t)X[j]), b = cr((int64_t)Y[i] - (int64_t)Y[j]), c = cr((int64_t)Z[i] - (int64_t)Z[j]);
      i128 d2 = a * a + b * b + c * c; if (best < 0 || d2 < best) best = d2; } }
  i128 q4k = 1; for (unsigned i = 0; i < 4 * k; ++i) q4k *= q;
  i128 Q = q; bool ok; double cexact = std::sqrt((double)best) / (double)W;
  if (!two) { i128 a = (Q-1)*(Q-1), b = (Q-2)*(Q-2)+(Q-4)*(Q-4), c = 3*(Q-3)*(Q-3); i128 mn = std::min(a, std::min(b, c));
    ok = q4k * mn <= Q * Q * best; printf("P q=%u k=%u  c_exact=%.4f  c(q)=%.4f  lean_ineq=%s\n", q, k, cexact, std::sqrt((double)mn) / q, ok ? "OK" : "FAIL"); }
  else { i128 T = Q*Q*(Q-1)*(Q-1) + (Q-1)*(Q-1) + (Q-2)*(Q-2);
    ok = q4k * T <= Q*Q*Q*Q * best; printf("Q p=%u k=%u  c_exact=%.4f  c*(p)=%.4f  lean_ineq=%s\n", q, k, cexact, std::sqrt((double)T) / (q * q), ok ? "OK" : "FAIL"); }
  return !ok;
}
