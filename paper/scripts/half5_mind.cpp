// half5_mind.cpp -- EXACT toroidal minimum distance of a digital (0,5,5)-net over F_p at k = 1 (one resolution,
// N = p^5, 5 digits per coordinate); used by half5_exact.py for the net Q*_p of the s = 5 one-resolution section.
// Adapted from the HOLONOMY_S5 audit kernel (aud_mind.cpp), which was validated bit-for-bit against
// `algs_mind2.cpp` (research repository) at p = 7, 11, 13 (d2 = 1720717, 121318230, 542292439).
//
// STDIN: p 5 5, then 5 generator matrices G_c (5x5, row j = output digit j, most significant first) mod p.
// Coordinate c of index n: X_c = sum_j (G_c n)_j p^(4-j) in [0, p^5) (integer units p^-5); row 0 of G_c must be
// e_c (checked), so the cell of coordinate c is n_c.
//
// Exactness:
//  * a pair whose torus cell difference E has some |E_c| >= 3 is > 2 cells apart in that coordinate, and the
//    output is < 2 cells whenever p >= 7 (checked: the answer is compared with 4 p^8);
//  * for every other E (one per +- pair) the coordinate difference is determined by the 4 deep-digit wrap bits
//    (Delta_j = rho_j - p w_j, rho_j = (G_c E)_j mod p), so LB_E = sum_c min over the possible wrap patterns is a
//    valid lower bound for the step E; steps are taken in increasing LB_E, steps with LB_E >= best are skipped,
//    and every other step is scanned over ALL p^5 cells n.
// Output (one line): p=.. d2=.. (units p^-10) c=sqrt(d2)/p^4 c>1:0/1 (exact integer test d2 > p^8)
//                    argE=(..) scanned=../..
// build: g++ -O3 -std=c++17 -o scripts/bin/half5_mind scripts/half5_mind.cpp   (std::thread; on Linux add -pthread)
// optional argv[1] = number of threads (default: hardware concurrency)
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <vector>
#include <algorithm>
#include <thread>
#include <atomic>
#include <mutex>
typedef long long ll;
typedef unsigned long long u64;
int p; long long P5;
int G[5][5][5];  // G[c][j][d]

static ll tor(ll x) {  // centred representative modulo p^5
    ll m = (ll)P5;
    x %= m;
    if (x < 0) x += m;
    if (2 * x > m) x -= m;
    return x;
}

int main(int argc, char** argv) {
    int m, s;
    if (scanf("%d %d %d", &p, &m, &s) != 3 || m != 5 || s != 5) { fprintf(stderr, "need p 5 5\n"); return 1; }
    for (int c = 0; c < 5; c++)
        for (int j = 0; j < 5; j++)
            for (int d = 0; d < 5; d++) { int x; if (scanf("%d", &x) != 1) return 1; G[c][j][d] = ((x % p) + p) % p; }
    for (int c = 0; c < 5; c++)
        for (int d = 0; d < 5; d++)
            if (G[c][0][d] != (c == d)) { fprintf(stderr, "row 0 of G_c must be e_c\n"); return 1; }
    P5 = 1; for (int i = 0; i < 5; i++) P5 *= (long long)p;
    int nthreads = std::max(1u, std::thread::hardware_concurrency());
    if (argc > 1) nthreads = atoi(argv[1]);
    ll pw[5] = {1, p, (ll)p * p, (ll)p * p * p, (ll)p * p * p * p};

    struct Step { int E[5]; u64 lb; u64 tab[5][16]; int rho[5][5]; };
    std::vector<Step> steps;
    for (int code = 0; code < 3125; code++) {
        int E[5], t = code; bool nz = false;
        for (int d = 0; d < 5; d++) { E[d] = t % 5 - 2; t /= 5; if (E[d]) nz = true; }
        if (!nz) continue;
        int f = 0; while (E[f] == 0) f++;
        if (E[f] < 0) continue;  // one per +- pair
        Step st; for (int d = 0; d < 5; d++) st.E[d] = E[d];
        u64 lb = 0;
        for (int c = 0; c < 5; c++) {
            for (int j = 0; j < 5; j++) {
                ll v = 0; for (int d = 0; d < 5; d++) v += (ll)G[c][j][d] * ((E[d] % p + p) % p);
                st.rho[c][j] = (int)(v % p);
            }
            u64 mn = ~0ULL;
            for (int w = 0; w < 16; w++) {
                ll X = (ll)E[c] * pw[4];
                for (int j = 1; j < 5; j++) {
                    ll dj = st.rho[c][j] - (((w >> (j - 1)) & 1) ? p : 0);
                    X += dj * pw[4 - j];
                }
                ll y = tor(X);
                u64 sq = (u64)(y < 0 ? -y : y) * (u64)(y < 0 ? -y : y);
                st.tab[c][w] = sq;
                // a wrap with rho == 0 is impossible; keep the entry but it is never selected (w bit set only if wrapped)
                bool possible = true;
                for (int j = 1; j < 5; j++) if (((w >> (j - 1)) & 1) && st.rho[c][j] == 0) possible = false;
                if (possible) mn = std::min(mn, sq);
            }
            lb += mn;
        }
        st.lb = lb;
        steps.push_back(st);
    }
    std::sort(steps.begin(), steps.end(), [](const Step& a, const Step& b) { return a.lb < b.lb; });
    u64 best = ~0ULL; int bestE[5] = {0, 0, 0, 0, 0}; int scanned = 0;
    for (auto& st : steps) {
        if (st.lb >= best) break;
        scanned++;
        std::atomic<u64> gbest(best);
        std::vector<std::thread> th;
        for (int tid = 0; tid < nthreads; tid++) {
            th.emplace_back([&, tid]() {
                u64 lbest = gbest.load();
                for (int n0 = tid; n0 < p; n0 += nthreads) {
                    int n[5]; n[0] = n0;
                    for (n[1] = 0; n[1] < p; n[1]++)
                    for (n[2] = 0; n[2] < p; n[2]++)
                    for (n[3] = 0; n[3] < p; n[3]++) {
                        int dig[5][5];
                        for (int c = 0; c < 5; c++) for (int j = 1; j < 5; j++) {
                            ll v = 0; for (int d = 0; d < 4; d++) v += (ll)G[c][j][d] * n[d];
                            dig[c][j] = (int)(v % p);
                        }
                        for (n[4] = 0; n[4] < p; n[4]++) {
                            u64 tot = 0;
                            for (int c = 0; c < 5 && tot < lbest; c++) {
                                int w = 0;
                                for (int j = 1; j < 5; j++) if (dig[c][j] + st.rho[c][j] >= p) w |= 1 << (j - 1);
                                tot += st.tab[c][w];
                            }
                            if (tot < lbest) lbest = tot;
                            for (int c = 0; c < 5; c++) for (int j = 1; j < 5; j++) {
                                int v = dig[c][j] + G[c][j][4]; if (v >= p) v -= p; dig[c][j] = v;
                            }
                        }
                    }
                }
                u64 cur = gbest.load();
                while (lbest < cur && !gbest.compare_exchange_weak(cur, lbest)) {}
            });
        }
        for (auto& t : th) t.join();
        if (gbest.load() < best) { best = gbest.load(); for (int d = 0; d < 5; d++) bestE[d] = st.E[d]; }
    }
    double c = std::sqrt((double)best) / ((double)p * p * p * p);
    // exact rational check c > 1  <=>  best > p^8
    __int128 p8 = (__int128)pw[4] * pw[4];
    if ((__int128)best >= 4 * p8) { fprintf(stderr, "minimum >= 2 cells: the |E_c|<=2 reduction is not conclusive\n"); return 1; }
    printf("p=%d d2=%llu c=%.6f c>1:%d argE=(%d,%d,%d,%d,%d) scanned=%d/%zu\n", p, best, c,
           (int)((__int128)best > p8), bestE[0], bestE[1], bestE[2], bestE[3], bestE[4], scanned, steps.size());
    return 0;
}
