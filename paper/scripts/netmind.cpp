// netmind.cpp -- exact toroidal minimum distance of a digital net in dimension 3 with m = 3k and one point in each
// of the q^{3k} cells of side q^{-k} (the (k,k,k) elementary boxes), e.g. P_{k,q} and Q_{k,p} of core.tex.
//
// build:  g++ -O3 -std=c++17 -o scripts/bin/netmind scripts/netmind.cpp
// stdin:  "q m 3" + 3 lines of m*m entries (row-major; row j = output digit j, most significant first; column l =
//         index digit v_l, least significant first) -- written by netdefs.write_mats / tab_c_two.py.
// stdout: "d2=<int> W=<int> c=<float> pair=<x,y,z>-<x,y,z>"   (integer coordinates in [0, q^m)),
//         d2 = minimum squared toroidal distance at integer scale q^m, c = delta N^{1/3} = sqrt(d2)/q^{2k}.
// Method: all q^m points are generated from the matrices (index odometer), each is filed in its cell (the program
// stops if a cell is hit twice: then the net does not have one point per cell); every pair of points in cyclically
// adjacent cells (the 13 forward offsets of {-1,0,1}^3) is scanned.  Two points whose cells differ by >= 2 in some
// coordinate are more than W = q^{2k} apart, so the scan is exact as soon as its minimum is below W^2, which is
// checked (exit status 2 otherwise).
#include <cstdio>
#include <cstdint>
#include <climits>
#include <cstdlib>
#include <cmath>
#include <vector>
using namespace std;
typedef long long ll;

int main() {
    unsigned q, m, s;
    if (scanf("%u %u %u", &q, &m, &s) != 3 || s != 3 || m % 3 || q < 2) { fprintf(stderr, "bad header\n"); return 1; }
    vector<ll> C[3];
    for (int c = 0; c < 3; c++) {
        C[c].resize((size_t)m * m);
        for (auto& x : C[c]) if (scanf("%lld", &x) != 1) { fprintf(stderr, "bad matrix\n"); return 1; }
    }
    const unsigned k = m / 3;
    ll N = 1, G = 1, W = 1;
    for (unsigned i = 0; i < m; i++) N *= q;
    for (unsigned i = 0; i < k; i++) G *= q;
    W = N / G;                                     // q^{2k}: cell side at integer scale
    if (N > (1ll << 32) || G < 3) { fprintf(stderr, "q^m too large or q^k < 3\n"); return 1; }
    vector<uint32_t> P[3];
    for (int c = 0; c < 3; c++) P[c].assign((size_t)N, UINT32_MAX);
    // odometer over the index digits; d[c][j] = (C_c v)_j (not reduced) updated incrementally
    vector<unsigned> v(m, 0);
    vector<ll> d[3];
    for (int c = 0; c < 3; c++) d[c].assign(m, 0);
    for (ll i = 0; i < N; i++) {
        ll X[3];
        for (int c = 0; c < 3; c++) {
            ll x = 0;
            for (unsigned j = 0; j < m; j++) x = x * q + ((d[c][j] % q) + q) % q;
            X[c] = x;
        }
        ll cell = ((X[0] / W) * G + X[1] / W) * G + X[2] / W;
        if (P[0][cell] != UINT32_MAX) { fprintf(stderr, "two points in cell %lld: not one point per cell\n", cell); return 1; }
        for (int c = 0; c < 3; c++) P[c][cell] = (uint32_t)X[c];
        unsigned l = 0;
        while (l < m && v[l] == q - 1) {
            v[l] = 0;
            for (int c = 0; c < 3; c++) for (unsigned j = 0; j < m; j++) d[c][j] -= (ll)(q - 1) * C[c][(size_t)j * m + l];
            l++;
        }
        if (l < m) { v[l]++; for (int c = 0; c < 3; c++) for (unsigned j = 0; j < m; j++) d[c][j] += C[c][(size_t)j * m + l]; }
    }
    int off[13][3], no = 0;
    for (int a = -1; a <= 1; a++) for (int b = -1; b <= 1; b++) for (int e = -1; e <= 1; e++)
        if (a > 0 || (a == 0 && (b > 0 || (b == 0 && e > 0)))) { off[no][0] = a; off[no][1] = b; off[no][2] = e; no++; }
    ll best = LLONG_MAX, bi = -1, bj = -1;
    auto tor = [&](ll t) { t = t < 0 ? -t : t; return t > N - t ? N - t : t; };
    for (ll a = 0; a < G; a++) for (ll b = 0; b < G; b++) for (ll e = 0; e < G; e++) {
        ll i = (a * G + b) * G + e;
        ll x0 = P[0][i], y0 = P[1][i], z0 = P[2][i];
        for (int o = 0; o < 13; o++) {
            ll a2 = (a + off[o][0] + G) % G, b2 = (b + off[o][1] + G) % G, e2 = (e + off[o][2] + G) % G;
            ll j = (a2 * G + b2) * G + e2;
            ll dx = tor((ll)P[0][j] - x0), dy = tor((ll)P[1][j] - y0), dz = tor((ll)P[2][j] - z0);
            ll s2 = dx * dx + dy * dy + dz * dz;
            if (s2 < best) { best = s2; bi = i; bj = j; }
        }
    }
    if (!(best < W * W)) { fprintf(stderr, "minimum %lld not below W^2 = %lld: scan not certified exact\n", best, W * W); return 2; }
    printf("d2=%lld W=%lld c=%.9f pair=%u,%u,%u-%u,%u,%u\n", best, W, sqrt((double)best) / (double)W,
           P[0][bi], P[1][bi], P[2][bi], P[0][bj], P[1][bj], P[2][bj]);
    return 0;
}
