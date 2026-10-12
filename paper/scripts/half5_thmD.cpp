// half5_thmD.cpp -- the computer-assisted part of Theorem D (drift optimum of half-integer one-resolution layers at
// s = 5) and the structure of the skew optimum.  Adapted from the HOLONOMY_S5 audit (aud_thmD.cpp); like it, it does
// NOT use a "pairwise distinct" pre-filter: every heavy row has 240 candidates and the disjoint minors are checked
// generically as rows are added (and once more on the complete layer).
//
// H = 2*F0 (odd integers).  2*dr(H) = max over binding steps E (E in {-1,0,1}^5, sum odd) of
//   sum_{E_c=0} |(HE)_c| - sum_{E_c!=0} E_c (HE)_c.
// (MIN): every off-diagonal entry nonzero, and every 2x2 minor on rows {a,b} and two columns not in {a,b} nonzero.
// Part A (Sigma alpha = 13/2, normalized): light row 4 = (1,1,1,1,-1)/2; heavy rows 0..3 have diagonal -3/2 and
//   off-diagonal entries in {+-1/2, +-3/2} with at least one +-3/2 (minimal diagonal 3/2).  Asserted: 1,004,544
//   admissible layers, min dr = 17/2, no layer with dr <= 15/2, 84 minimizers (48 skew, 36 non-skew).
// Part B (skew, entries in {+-1/2, +-3/2}, minimal diagonal): all 2^20 layers.  Asserted: 39,168 (MIN)-admissible,
//   histogram of dr 17/2: 3840, 19/2: 2304, 21/2: 11520, 23/2: 21504.
// Part C: the 3840 skew minimizers form 2 orbits of 1920 under S5 x sign conjugation; each orbit representative has
//   exactly one light row and its |entry| = 3/2 graph is a path P4 on the four heavy rows.
// Scope: a complete enumeration of the finite families above (the reduction of Theorem D to Part A is by hand).
// build: g++ -O3 -std=c++17 -o scripts/bin/half5_thmD scripts/half5_thmD.cpp      (no input; ~1 s)
// Exit status 0 iff every assertion holds; last line "half5_thmD: ALL OK".
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <map>
#include <set>
#include <array>
#include <algorithm>
typedef std::array<int, 25> Mat;
static int nfail = 0;
#define CHECK(cond, ...) do { bool ok_ = (cond); printf(ok_ ? "  OK    " : "  FAIL  "); printf(__VA_ARGS__); printf("\n"); if (!ok_) nfail++; } while (0)
static int BIND[122][5]; static int nb = 0;
static int H[5][5];

static void init_bind() {
    for (int code = 0; code < 243; code++) {
        int E[5], t = code, s = 0;
        for (int d = 0; d < 5; d++) { E[d] = t % 3 - 1; t /= 3; s += E[d]; }
        if (s % 2 != 0) { for (int d = 0; d < 5; d++) BIND[nb][d] = E[d]; nb++; }
    }
}
static int drift2(int (*A)[5], const int* E) {
    int tot = 0;
    for (int c = 0; c < 5; c++) {
        int h = 0; for (int d = 0; d < 5; d++) h += A[c][d] * E[d];
        tot += E[c] == 0 ? abs(h) : -E[c] * h;
    }
    return tot;
}
static int K2(int (*A)[5]) { int m = -1000000; for (int i = 0; i < nb; i++) m = std::max(m, drift2(A, BIND[i])); return m; }
// check all disjoint 2x2 minors among rows in 'rows' set (bitmask) that involve row r
static bool minors_ok_row(int (*A)[5], int r, int rowmask) {
    for (int b = 0; b < 5; b++) {
        if (b == r || !((rowmask >> b) & 1)) continue;
        int cols[3], k = 0; for (int c = 0; c < 5; c++) if (c != r && c != b) cols[k++] = c;
        for (int i = 0; i < 3; i++) for (int j = i + 1; j < 3; j++) {
            int c = cols[i], d = cols[j];
            if (A[r][c] * A[b][d] - A[r][d] * A[b][c] == 0) return false;
        }
    }
    return true;
}
static bool all_minors_ok(int (*A)[5]) {
    for (int r = 0; r < 5; r++) for (int c = 0; c < 5; c++) if (r != c && A[r][c] == 0) return false;
    for (int r = 0; r < 5; r++) if (!minors_ok_row(A, r, 31)) return false;
    return true;
}
static bool is_skew(int (*A)[5]) {
    for (int c = 0; c < 5; c++) for (int d = c + 1; d < 5; d++) if (A[c][d] != -A[d][c]) return false;
    return true;
}

int main() {
    init_bind();
    const int vals[4] = {-3, -1, 1, 3};
    // ---------------- Part A ----------------
    std::vector<std::array<int, 4>> rowopts;  // off-diagonal entries (in column order skipping the diagonal)
    for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = 0; c < 4; c++) for (int d = 0; d < 4; d++) {
        std::array<int, 4> r = {vals[a], vals[b], vals[c], vals[d]};
        bool heavy = false; for (int x : r) if (abs(x) == 3) heavy = true;
        if (heavy) rowopts.push_back(r);
    }
    printf("Part A: heavy-row options per row = %zu\n", rowopts.size());
    for (int d = 0; d < 4; d++) H[4][d] = 1; H[4][4] = -1;
    long long admissible = 0, cntK[64] = {0}, minK = 1 << 30, atMin = 0, atMinSkew = 0, skewAdm = 0;
    std::vector<Mat> minimizers;
    auto setrow = [&](int r, const std::array<int, 4>& o) { int k = 0; for (int d = 0; d < 5; d++) H[r][d] = (d == r) ? -3 : o[k++]; };
    for (auto& o0 : rowopts) { setrow(0, o0); if (!minors_ok_row(H, 0, 1 << 4)) continue;
    for (auto& o1 : rowopts) { setrow(1, o1); if (!minors_ok_row(H, 1, (1 << 4) | 1)) continue;
    for (auto& o2 : rowopts) { setrow(2, o2); if (!minors_ok_row(H, 2, (1 << 4) | 3)) continue;
    for (auto& o3 : rowopts) { setrow(3, o3); if (!minors_ok_row(H, 3, (1 << 4) | 7)) continue;
        if (!all_minors_ok(H)) { fprintf(stderr, "inconsistent minor check\n"); return 1; }
        admissible++;
        int k = K2(H);
        cntK[std::min(k, 63)]++;
        bool sk = is_skew(H); if (sk) skewAdm++;
        if (k < minK) { minK = k; atMin = 0; atMinSkew = 0; minimizers.clear(); }
        if (k == minK) { atMin++; if (sk) atMinSkew++; Mat M; for (int i = 0; i < 25; i++) M[i] = H[i / 5][i % 5]; minimizers.push_back(M); }
    }}}}
    printf("Part A: admissible normalized layers = %lld (skew: %lld)\n", admissible, skewAdm);
    printf("Part A: min K_drift = %lld/2, #at min = %lld (skew %lld, non-skew %lld)\n", minK, atMin, atMinSkew, atMin - atMinSkew);
    printf("Part A: histogram 2K: "); for (int i = 0; i < 64; i++) if (cntK[i]) printf("%d:%lld ", i, cntK[i]); printf("\n");
    long long le15 = 0; for (int i = 0; i <= 15; i++) le15 += cntK[i];
    printf("Part A: #layers with K_drift <= 15/2 = %lld\n", le15);
    CHECK(rowopts.size() == 240, "Part A: 240 candidate heavy rows (no distinctness pre-filter)");
    CHECK(admissible == 1004544, "Part A: %lld admissible normalized Sigma alpha = 13/2 layers (expected 1,004,544)", admissible);
    CHECK(minK == 17, "Part A: min dr = %lld/2 (expected 17/2)", minK);
    CHECK(le15 == 0, "Part A: %lld layers with dr <= 15/2 (expected 0)", le15);
    CHECK(atMin == 84 && atMinSkew == 48, "Part A: %lld minimizers, %lld skew, %lld non-skew (expected 84 = 48 + 36)",
          atMin, atMinSkew, atMin - atMinSkew);
    // ---------------- Part B ----------------
    std::vector<std::pair<int, int>> prs; for (int c = 0; c < 5; c++) for (int d = c + 1; d < 5; d++) prs.push_back({c, d});
    long long adm = 0, hist[64] = {0};
    std::vector<Mat> skmin; int skminK = 1 << 30;
    for (int code = 0; code < (1 << 20); code++) {
        int t = code;
        for (int i = 0; i < 10; i++) { int v = vals[t & 3]; t >>= 2; H[prs[i].first][prs[i].second] = v; H[prs[i].second][prs[i].first] = -v; }
        for (int c = 0; c < 5; c++) { int m = 0; for (int d = 0; d < 5; d++) if (d != c) m = std::max(m, abs(H[c][d])); H[c][c] = -m; }
        if (!all_minors_ok(H)) continue;
        adm++;
        int k = K2(H); hist[k]++;
        if (k < skminK) { skminK = k; skmin.clear(); }
        if (k == skminK) { Mat M; for (int i = 0; i < 25; i++) M[i] = H[i / 5][i % 5]; skmin.push_back(M); }
    }
    printf("Part B: skew admissible = %lld; histogram 2K: ", adm); for (int i = 0; i < 64; i++) if (hist[i]) printf("%d:%lld ", i, hist[i]); printf("\n");
    {   long long other = 0; for (int i = 0; i < 64; i++) if (i != 17 && i != 19 && i != 21 && i != 23) other += hist[i];
        CHECK(adm == 39168, "Part B: %lld (MIN)-admissible skew layers of 2^20 (expected 39,168)", adm);
        CHECK(hist[17] == 3840 && hist[19] == 2304 && hist[21] == 11520 && hist[23] == 21504 && other == 0,
              "Part B: dr histogram 17/2:%lld 19/2:%lld 21/2:%lld 23/2:%lld other:%lld (expected 3840, 2304, 11520, 21504, 0)",
              hist[17], hist[19], hist[21], hist[23], other); }
    // ---------------- Part C ----------------
    std::vector<std::array<int, 5>> perms; std::array<int, 5> pm = {0, 1, 2, 3, 4};
    do perms.push_back(pm); while (std::next_permutation(pm.begin(), pm.end()));
    auto canon = [&](const Mat& M) {
        Mat best; bool first = true;
        for (auto& P : perms) for (int sg = 0; sg < 32; sg++) {
            Mat X;
            for (int c = 0; c < 5; c++) for (int d = 0; d < 5; d++) {
                int ec = ((sg >> c) & 1) ? -1 : 1, ed = ((sg >> d) & 1) ? -1 : 1;
                X[c * 5 + d] = ec * ed * M[P[c] * 5 + P[d]];
            }
            if (first || X < best) { best = X; first = false; }
        }
        return best;
    };
    std::map<Mat, int> orb;
    for (auto& M : skmin) orb[canon(M)]++;
    printf("Part C: skew minimizers = %zu at 2K=%d, orbits = %zu, sizes:", skmin.size(), skminK, orb.size());
    for (auto& kv : orb) printf(" %d", kv.second); printf("\n");
    CHECK(skminK == 17 && skmin.size() == 3840 && orb.size() == 2, "Part C: %zu skew minimizers (dr = %d/2) in %zu orbits under S5 x signs",
          skmin.size(), skminK, orb.size());
    for (auto& kv : orb) {
        const Mat& M = kv.first; int deg[5] = {0}, light = 0, edges = 0, lightv = -1;
        for (int c = 0; c < 5; c++) for (int d = 0; d < 5; d++) if (c != d && abs(M[c * 5 + d]) == 3) deg[c]++;
        for (int c = 0; c < 5; c++) { if (-M[c * 5 + c] == 1) { light++; lightv = c; } edges += deg[c]; }
        // full orbit size (number of distinct images under the 120 * 32 group elements)
        std::set<Mat> imgs;
        for (auto& P : perms) for (int sg = 0; sg < 32; sg++) {
            Mat X;
            for (int c = 0; c < 5; c++) for (int d = 0; d < 5; d++) {
                int ec = ((sg >> c) & 1) ? -1 : 1, ed = ((sg >> d) & 1) ? -1 : 1;
                X[c * 5 + d] = ec * ed * M[P[c] * 5 + P[d]];
            }
            imgs.insert(X);
        }
        // path P4 on the heavy rows: 3 edges, light row isolated, heavy degrees {1,1,2,2}, connected
        int hd[4], k = 0; for (int c = 0; c < 5; c++) if (c != lightv) hd[k++] = deg[c];
        std::sort(hd, hd + 4);
        int comp = 0; { int seen[5] = {0}; int st[5], sp = 0; for (int c = 0; c < 5; c++) if (c != lightv) { st[sp++] = c; seen[c] = 1; break; }
            while (sp) { int x = st[--sp]; comp++; for (int y = 0; y < 5; y++) if (!seen[y] && y != x && abs(M[x * 5 + y]) == 3) { seen[y] = 1; st[sp++] = y; } } }
        bool p4 = light == 1 && edges / 2 == 3 && deg[lightv] == 0 && hd[0] == 1 && hd[1] == 1 && hd[2] == 2 && hd[3] == 2 && comp == 4;
        int A[5][5]; for (int i = 0; i < 25; i++) A[i / 5][i % 5] = M[i];
        int nbind = 0; int kk = K2(A);
        for (int i = 0; i < nb; i++) if (drift2(A, BIND[i]) == kk) nbind++;
        CHECK(kv.second == 1920 && imgs.size() == 1920 && p4,
              "Part C: orbit of size %d (%zu distinct images): light rows = %d, |entry|=3/2 graph %d edges, degrees %d%d%d%d%d -> P4: %s; "
              "#binding steps attaining dr (up to sign) = %d", kv.second, imgs.size(), light, edges / 2,
              deg[0], deg[1], deg[2], deg[3], deg[4], p4 ? "yes" : "no", nbind / 2);
    }
    // non-skew minimizers of Part A: orbit classes (under S4 on heavy indices only after normalization -> use full canon)
    std::map<Mat, int> orbA; for (auto& M : minimizers) orbA[canon(M)]++;
    CHECK(orbA.size() == 5, "Part A: the 84 minimizers fall into %zu classes under S5 x signs (audit: 5)", orbA.size());
    if (nfail) { printf("half5_thmD: %d FAILURE(S)\n", nfail); return 1; }
    printf("half5_thmD: ALL OK\n");
    return 0;
}
