// gk2d_rescr.cpp -- rem:gk2d(iii) (rev 15.4): the phases of the two-dimensional Gruenschloss-Keller nets.
// Even m = 2r, R = 2^r, N = R^2.  Line c in [0,R) with phase pi(c) holds the points
//     Y = pi(c) + j R,   X = (c R + floor(pi(c)/4) + (R/4)(j+1)) mod N,      0 <= j < R,
// which is the net of rem:gk2d for pi = rev_r (van der Corput) and line c = rev_r(k).
// A nested scrambling of the van der Corput phases: bit i from the top of pi(c) is bit i of c xor s_i(c mod 2^i).
// The re-scramble of rem:gk2d(iii): pi(c) = rev(c) xor (R/8) [bit r-2 of rev(c)], i.e. the third binary digit of
// the phase is flipped on the lines c = 2,3 mod 4 (s_2(c mod 4) = bit 1 of c).
// Modes (all exact integer arithmetic):
//   mind r            d^2 (integer scale N) of GK and of the re-scramble, standard torus and tiling <(N,0),(N/4,N)>,
//                     and the number of elementary boxes (all m+1 shapes) not holding exactly one point
//   census r          all phase maps pi in Sym(R) on these lines (DFS over the lines, box counts): number keeping
//                     t = 0 and how many of them are nested scramblings of rev_r
//   jitter r          over all 2^(R-1) nested scramblings: the set of values 2R*J(pi), where
//                     J(pi) = min_{A in Z/R, beta} max_c || pi(c)/R - A c/R - beta ||  (distance from lattice phases)
// Build: g++ -O3 -std=c++17 -o scripts/bin/gk2d_rescr scripts/gk2d_rescr.cpp
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <set>
#include <vector>
using namespace std;
typedef long long ll;

static int r, m;
static ll R, N;

static ll rev(ll x) { ll y = 0; for (int i = 0; i < r; i++) y |= ((x >> i) & 1) << (r - 1 - i); return y; }

static void build(const vector<ll>& pi, vector<ll>& XofY) {
  XofY.assign(N, -1);
  for (ll c = 0; c < R; c++)
    for (ll j = 0; j < R; j++) {
      ll Y = pi[c] + j * R, X = (c * R + pi[c] / 4 + (R / 4) * (j + 1)) % N;
      XofY[Y] = X;
    }
}

static ll badboxes(const vector<ll>& XofY) {
  ll bad = 0; vector<int> cnt(N);
  for (int h = 0; h <= m; h++) {
    fill(cnt.begin(), cnt.end(), 0);
    for (ll Y = 0; Y < N; Y++) cnt[((XofY[Y] >> (m - h)) << (m - h)) | (Y >> h)]++;
    for (ll i = 0; i < N; i++) bad += cnt[i] != 1;
  }
  return bad;
}

// exact minimum squared toroidal distance; every Y holds exactly one point (pi is a permutation)
static ll mind(const vector<ll>& XofY, bool tiling) {
  ll best = N * N;
  for (ll dy = 1; dy < N && dy * dy < best; dy++)
    for (ll Y = 0; Y < N; Y++) {
      ll Y2 = Y + dy, sh = 0;
      if (Y2 >= N) { Y2 -= N; sh = tiling ? N / 4 : 0; }
      ll dx = ((XofY[Y2] + sh - XofY[Y]) % N + N) % N;
      dx = min(dx, N - dx);
      ll d2 = dx * dx + dy * dy;
      if (d2 < best) best = d2;
    }
  return best;
}

// nested scrambling from the bits s (index (1<<i)-1 + (c mod 2^i) for level i)
static vector<ll> nestedpi(const vector<int>& s) {
  vector<ll> pi(R);
  for (ll c = 0; c < R; c++) {
    ll v = 0;
    for (int i = 0; i < r; i++) v |= (ll)(((c >> i) & 1) ^ s[(1 << i) - 1 + (c & ((1 << i) - 1))]) << (r - 1 - i);
    pi[c] = v;
  }
  return pi;
}

static bool isnested(const vector<ll>& pi) {
  for (int i = 0; i < r; i++) {
    vector<int> val(1 << i, -1);
    for (ll c = 0; c < R; c++) {
      int v = (int)(((pi[c] >> (r - 1 - i)) & 1) ^ ((c >> i) & 1)), key = (int)(c & ((1 << i) - 1));
      if (val[key] < 0) val[key] = v; else if (val[key] != v) return false;
    }
  }
  return true;
}

// census: DFS over lines with incremental box counts
static vector<vector<unsigned char>> cnt;
static vector<ll> cpi; static vector<char> used; static ll nsol, nnest;
static bool addline(ll c, ll ph, int sg) {
  bool ok = true;
  for (ll j = 0; j < R; j++) {
    ll Y = ph + j * R, X = (c * R + ph / 4 + (R / 4) * (j + 1)) % N;
    for (int h = 0; h <= m; h++) {
      ll id = ((X >> (m - h)) << (m - h)) | (Y >> h);
      cnt[h][id] += sg; if (cnt[h][id] > 1) ok = false;
    }
  }
  return ok;
}
static void dfs(ll c) {
  if (c == R) { nsol++; if (isnested(cpi)) nnest++; return; }
  for (ll ph = 0; ph < R; ph++) {
    if (used[ph]) continue;
    used[ph] = 1; cpi[c] = ph;
    if (addline(c, ph, +1)) dfs(c + 1);
    addline(c, ph, -1); used[ph] = 0;
  }
}

int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage: gk2d_rescr mind|census|jitter r\n"); return 2; }
  r = atoi(argv[2]); m = 2 * r; R = 1LL << r; N = R * R;
  if (!strcmp(argv[1], "mind")) {
    vector<ll> vdc(R), res(R), XofY;
    for (ll c = 0; c < R; c++) { vdc[c] = rev(c); res[c] = vdc[c] ^ ((R / 8) * ((vdc[c] >> (r - 2)) & 1)); }
    for (int v = 0; v < 2; v++) {
      build(v ? res : vdc, XofY);
      printf("%s m=%d bad=%lld std=%lld tiling=%lld nested=%d\n", v ? "rescramble" : "GK", m, badboxes(XofY),
             mind(XofY, false), mind(XofY, true), (int)isnested(v ? res : vdc));
    }
  } else if (!strcmp(argv[1], "census")) {
    cnt.assign(m + 1, vector<unsigned char>(N, 0)); cpi.assign(R, -1); used.assign(R, 0); nsol = nnest = 0;
    dfs(0);
    printf("census m=%d solutions=%lld nested=%lld\n", m, nsol, nnest);
  } else if (!strcmp(argv[1], "jitter")) {
    set<ll> vals; ll nsc = 1LL << (R - 1);
    for (ll S = 0; S < nsc; S++) {
      vector<int> s(R - 1); for (ll b = 0; b < R - 1; b++) s[b] = (S >> b) & 1;
      vector<ll> pi = nestedpi(s);
      ll bestJ = -1;
      for (ll A = 0; A < R; A++) {
        vector<ll> pts(R);
        for (ll c = 0; c < R; c++) pts[c] = ((pi[c] - A * c) % R + R) % R;
        sort(pts.begin(), pts.end());
        ll gap = pts[0] + R - pts[R - 1];
        for (ll i = 0; i + 1 < R; i++) gap = max(gap, pts[i + 1] - pts[i]);
        ll J2R = R - gap;  // 2R*J, J = (1 - maxgap/R)/2
        if (bestJ < 0 || J2R < bestJ) bestJ = J2R;
      }
      vals.insert(bestJ);
    }
    printf("jitter m=%d scramblings=%lld values2RJ=", m, nsc);
    for (ll v : vals) printf("%lld,", v);
    printf("\n");
  }
  return 0;
}
