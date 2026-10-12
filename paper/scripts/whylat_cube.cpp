// whylat_cube.cpp -- Remark rem:cubecost of core.tex: one-point-per-cube lattices.
// Build: g++ -O3 -std=c++17 -o scripts/bin/whylat_cube scripts/whylat_cube.cpp
//
// "lat s e [T]" (s = 2 or 3): enumerate ALL lattices L = L'/e, L' in Z^s of index e^s (column Hermite normal form),
//   i.e. every lattice of covolume 1 contained in (1/e)Z^s.  For each: the exact minimum lambda (squared, units 1/e^2;
//   the candidate vectors reach norm 1.13 > 2^(1/6), the Hermite bound for s = 3) and, when lambda > 0.9, the exact
//   one-point-per-cube test (no unit cube n+[0,1)^s holds two points; density 1 => exactly one).  Prints the number of
//   lattices, the largest minimum over all of them and over the one-per-cube ones (as lambda^2 = a/e^2), up to four
//   one-per-cube maximizers with lambda > T (default 1), and how many one-per-cube lattices have a full phase grid.
//   Driver: cubecost.py (e = 1..11, s = 3).
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <climits>
#include <vector>
#include <array>
#include <set>
#include <map>
#include <string>
#include <algorithm>
#include <chrono>
using namespace std;
typedef long long ll;

static ll mod(ll a, ll m){ a%=m; return a<0?a+m:a; }

// ---------------- lattice mode ----------------
int S, E_;
struct HNF { ll h[3][3]; };
static bool member(const HNF& H, const ll* u){
  // columns basis, upper triangular: H = [[h00,h01,h02],[0,h11,h12],[0,0,h22]]
  if(S==3){
    if(u[2]%H.h[2][2]) return false; ll x2=u[2]/H.h[2][2];
    ll r1=u[1]-H.h[1][2]*x2; if(r1%H.h[1][1]) return false; ll x1=r1/H.h[1][1];
    ll r0=u[0]-H.h[0][1]*x1-H.h[0][2]*x2; return r0%H.h[0][0]==0;
  } else {
    if(u[1]%H.h[1][1]) return false; ll x1=u[1]/H.h[1][1];
    ll r0=u[0]-H.h[0][1]*x1; return r0%H.h[0][0]==0;
  }
}
int run_lat(int s, int e, double T){
  S=s; E_=e; ll N=1; for(int i=0;i<s;i++) N*=e;
  // candidate vectors, half space, sorted by norm, norm^2 <= (1.13 e)^2
  double R = (s==3?1.13:1.08)*e; ll R2=(ll)floor(R*R);
  vector<array<ll,4>> cand; // u0,u1,u2,norm
  int B=(int)ceil(R);
  for(int a=-B;a<=B;a++)for(int b=-B;b<=B;b++)for(int c=(s==3?-B:0);c<=(s==3?B:0);c++){
    ll n2=(ll)a*a+(ll)b*b+(ll)c*c; if(n2==0||n2>R2) continue;
    // half space: first nonzero coord positive
    int f = a?a:(b?b:c); if(f<0) continue;
    cand.push_back({a,b,c,n2});
  }
  sort(cand.begin(),cand.end(),[](auto&x,auto&y){return x[3]<y[3];});
  // box vectors for one-per-cube test: |u_c| < e
  ll thr2=(ll)floor(T*T*e*e+1e-9); // lambda^2 must exceed thr2 to be reported
  map<ll,ll> hist_opc, hist_all; ll nlat=0, nopc=0, nopc_full=0, nopc_full_gt1=0;
  vector<pair<ll,HNF>> best; ll bestv=0;
  auto process=[&](const HNF& H){
    nlat++;
    ll lam2=-1; for(auto&c:cand){ ll u[3]={c[0],c[1],c[2]}; if(member(H,u)){lam2=c[3];break;} }
    if(lam2<0) lam2=R2+1;
    // one-per-cube test only needed when lam2 > e^2 ... but we want stats: do it for lam2 > (0.9e)^2 to bound cost
    bool want = lam2 > (ll)(0.81*e*e);
    if(!want){ hist_all[lam2]++; return; }
    hist_all[lam2]++;
    // phase group Y = L' mod e
    vector<array<int,3>> cols(s);
    for(int j=0;j<s;j++) for(int i=0;i<3;i++) cols[j][i]= (i<s)? (int)mod(H.h[i][j],e):0;
    set<array<int,3>> Y;
    vector<int> x(s,0);
    int tot=1; for(int j=0;j<s;j++) tot*=e;
    for(int idx=0;idx<tot;idx++){ int t=idx; array<int,3> y={0,0,0};
      for(int j=0;j<s;j++){ int xj=t%e; t/=e; for(int i=0;i<s;i++) y[i]=(y[i]+xj*cols[j][i])%e; }
      Y.insert(y);}
    // short box vectors
    bool ok=true;
    int Bx=e-1;
    for(int a=-Bx;a<=Bx && ok;a++)for(int b=-Bx;b<=Bx && ok;b++)for(int c=(s==3?-Bx:0);c<=(s==3?Bx:0) && ok;c++){
      if(!a&&!b&&!c) continue; ll u[3]={a,b,c}; if(!member(H,u)) continue;
      int v[3]={a,b,c};
      for(auto& y:Y){ bool in=true; for(int i=0;i<s;i++){ int z=y[i]+v[i]; if(z<0||z>=e){in=false;break;} } if(in){ok=false;break;} }
    }
    if(!ok) return;
    nopc++; hist_opc[lam2]++;
    // full grid?
    ll prodp=1; for(int i=0;i<s;i++){ set<int> P; for(auto&y:Y) P.insert(y[i]); prodp*=P.size(); }
    bool full = (ll)Y.size()==prodp; if(full){ nopc_full++; if(lam2>(ll)e*e) nopc_full_gt1++; }
    if(lam2>thr2){ best.push_back({lam2,H}); if(lam2>bestv) bestv=lam2; }
  };
  if(s==2){
    for(ll a=1;a<=N;a++) if(N%a==0){ ll d=N/a; for(ll b=0;b<a;b++){ HNF H{}; H.h[0][0]=a;H.h[0][1]=b;H.h[1][1]=d; process(H);} }
  } else {
    for(ll a=1;a<=N;a++) if(N%a==0) for(ll d=1;d<=N/a;d++) if((N/a)%d==0){ ll g=N/a/d;
      for(ll b=0;b<a;b++)for(ll c=0;c<a;c++)for(ll f=0;f<d;f++){ HNF H{}; H.h[0][0]=a;H.h[0][1]=b;H.h[0][2]=c;H.h[1][1]=d;H.h[1][2]=f;H.h[2][2]=g; process(H);} }
  }
  printf("lat s=%d e=%d: lattices=%lld  one-per-cube(among lambda>0.9)=%lld  of which full-grid=%lld (full-grid with lambda>1: %lld)\n",
    s,e,nlat,nopc,nopc_full,nopc_full_gt1);
  double maxall=0; for(auto&kv:hist_all) maxall=max(maxall,sqrt((double)kv.first)/e);
  printf("  max lambda over ALL covolume-1 lattices in (1/e)Z^s: %.6f\n", maxall);
  double maxo=0; ll maxo2=0; for(auto&kv:hist_opc){ if(sqrt((double)kv.first)/e>maxo){maxo=sqrt((double)kv.first)/e; maxo2=kv.first;} }
  printf("  max lambda over one-per-cube lattices: %.6f (lambda^2 = %lld/%d)\n", maxo, maxo2, e*e);
  sort(best.begin(),best.end(),[](auto&x,auto&y){return x.first>y.first;});
  int shown=0; for(auto& b:best){ if(shown>=4) break; shown++; const HNF&H=b.second;
    if(s==3) printf("  lam=%.6f H=[[%lld,%lld,%lld],[0,%lld,%lld],[0,0,%lld]]/%d\n", sqrt((double)b.first)/e,
      H.h[0][0],H.h[0][1],H.h[0][2],H.h[1][1],H.h[1][2],H.h[2][2],e);
    else printf("  lam=%.6f H=[[%lld,%lld],[0,%lld]]/%d\n", sqrt((double)b.first)/e,H.h[0][0],H.h[0][1],H.h[1][1],e); }
  return 0;
}

int main(int argc, char** argv){
  if(argc<4 || string(argv[1])!="lat"){ fprintf(stderr,"usage: lat s e [T]\n"); return 1; }
  auto t0=chrono::steady_clock::now();
  int rc=run_lat(atoi(argv[2]),atoi(argv[3]),argc>4?atof(argv[4]):1.0);
  double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
  fprintf(stderr,"[%.2fs]\n",el);
  return rc;
}
