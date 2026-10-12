// es.cpp -- EVERY-DIGITAL-SHIFT analysis of the base-2/3 deep-shift-lift nets (the research notes).
// Written from the mathematics; shares no code with ba.cpp / r1_* / g3_* (reads the same NET file format).
//
// NET format: "NET b M" / M lines (generator i: 3M digits, coord c depth d at c*M+d, depth 0 = most significant) /
//             1 line shift (3M digits).  Point set {C n (+) sh : n in F_b^M}.
//
// KEY IDENTITY (proved in the research notes).  For a pair of points with digit difference Delta = (Delta_x,Delta_y,
// Delta_z) (a nonzero codeword of the generator code), a digital shift tau acts on the three coordinates independently,
// and the integer difference of coordinate c after the shift is int(X_c (+) Delta_c) - int(X_c) with X_c = (first point
// (+) tau)_c ranging over ALL digit strings as tau_c does.  Hence
//     min_tau  F(P (+) tau) = min_{Delta in code, Delta != 0}  sum_c  w(Delta_c),     w(delta) = min_X f(int(X(+)delta)-int(X))
// for every pair metric F = sum_c f(coordinate difference).  With mu(delta) = min_X |int(X(+)delta)-int(X)|  (toroidal
// mod b^n, or not) we get   v*_unif = min sum_c max(0,mu_H(Delta_c)-1)^2  (top-H-digit code)   and
//                           d2_unif = min sum_c mu_m(Delta_c)^2           (full code)
// mu itself: int(X(+)delta)-int(X) = sum_k e_k b^k with e_k in {delta_k, delta_k-b} chosen freely (delta_k != 0), i.e.
// = int(delta) - s with s in S = { sum_{k in B} b^{k+1} : B subset supp(delta) }; S is super-increasing, so the
// nearest elements of S to a target are found greedily (pred) and by a binary increment (succ).
//
// modes:
//   selftest                      mu (greedy) == brute force over all X, b=2,3, n<=7, toroidal and not
//   vunif NET [H]                 v*_unif = min over ALL digital shifts of the certificate v* (top H=floor(M/2) digits);
//                                 exact, by threshold enumeration of low-weight codewords (syndrome meet-in-the-middle);
//                                 prints a witness shift tau' (top-H digits) and re-checks it by brute force over pairs
//                                 when b^M <= 2^22. Also prints Z = #nonzero codewords with weight 0 (adjacent pattern).
//   vfull NET [H]                 same quantity by enumerating ALL b^M codewords (cross-check, small M)
//   cunif NET                     exact min over ALL depth-M digital shifts of the toroidal min distance d2 (units b^-M)
//                                 and of the non-toroidal one (d2nt) -- full codeword enumeration; witness shift printed
//   freeze NET_L NET_m            linear-algebra check that P_m (m=L+3j) has the frozen structure of lem:liftsep relative
//                                 to P_L: rank Sigma = 3j, K(F^m) subset V_L, dim K(ker Sigma) = L, shift_K - shift_L in V_L
//   effD NET_l NET_l3             effective depth parameter of the lift P_l -> P_{l+3}: the largest D such that the
//                                 level-(l+3) code is the lift of P_l with shifts vanishing on the top D block digits
//   witshift NET tau_file OUT     write NET with its shift replaced (for cross-checks with ba vstar / ba mind)
// build: g++-16 -O3 -fopenmp -std=c++17 -o es es.cpp
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <climits>
#include <vector>
#include <string>
#include <algorithm>
#include <unordered_map>
#include <map>
#include <array>
#include <chrono>
#ifdef _OPENMP
#include <omp.h>
#endif
using namespace std;
typedef long long ll; typedef unsigned long long u64; typedef vector<int> VI;
#define DIE(...) do{ fprintf(stderr,"es: "); fprintf(stderr,__VA_ARGS__); fprintf(stderr,"\n"); exit(3);}while(0)

static int B=0;
static inline int md(int a){ a%=B; return a<0? a+B : a; }
static int inv(int a){ for(int x=1;x<B;x++) if(md(a*x)==1) return x; DIE("inv(0)"); }
static ll PW[40];
static void initPW(){ PW[0]=1; for(int i=1;i<40;i++) PW[i]=PW[i-1]*B; }

struct Net{ int M=0; vector<VI> g; VI sh; };
static Net readNet(const char* fn){
    FILE* f=fopen(fn,"r"); if(!f) DIE("open %s",fn); char tag[8]; int b,M;
    if(fscanf(f,"%7s %d %d",tag,&b,&M)!=3||strcmp(tag,"NET")) DIE("header %s",fn);
    if(B && B!=b) DIE("mixed bases"); B=b; initPW(); Net n; n.M=M; n.g.assign(M,VI(3*M)); n.sh.assign(3*M,0);
    for(int i=0;i<M;i++) for(int t=0;t<3*M;t++){ if(fscanf(f,"%d",&n.g[i][t])!=1) DIE("short"); n.g[i][t]=md(n.g[i][t]); }
    for(int t=0;t<3*M;t++){ if(fscanf(f,"%d",&n.sh[t])!=1) DIE("short shift"); n.sh[t]=md(n.sh[t]); }
    fclose(f); return n; }
static void writeNet(const Net& n,const char* fn){ FILE* f=fopen(fn,"w"); fprintf(f,"NET %d %d\n",B,n.M);
    for(auto& g:n.g) for(int t=0;t<3*n.M;t++) fprintf(f,"%d%c",g[t],t+1<3*n.M?' ':'\n');
    for(int t=0;t<3*n.M;t++) fprintf(f,"%d%c",n.sh[t],t+1<3*n.M?' ':'\n'); fclose(f); }

// ------------------------------------------------------------------ RREF over F_b
struct Ech{ vector<VI> R; VI piv; int nc=0; };
static Ech echelon(vector<VI> A,int nc){ Ech E; E.nc=nc; int r=0;
    for(int c=0;c<nc && r<(int)A.size();c++){ int p=-1; for(int i=r;i<(int)A.size();i++) if(A[i][c]){p=i;break;} if(p<0) continue;
        swap(A[p],A[r]); int iv=inv(A[r][c]); for(auto& x:A[r]) x=md(x*iv);
        for(int i=0;i<(int)A.size();i++) if(i!=r && A[i][c]){ int f=A[i][c]; for(int t=0;t<nc;t++) A[i][t]=md(A[i][t]-f*A[r][t]); }
        E.piv.push_back(c); r++; }
    A.resize(r); E.R=A; return E; }
static VI reduceBy(const Ech& E, VI v){ for(size_t k=0;k<E.R.size();k++){ int f=v[E.piv[k]]; if(f) for(int t=0;t<E.nc;t++) v[t]=md(v[t]-f*E.R[k][t]); } return v; }
static bool inSpan(const Ech& E,const VI& v){ VI r=reduceBy(E,v); for(int x:r) if(x) return false; return true; }

// ------------------------------------------------------------------ digit vectors of one coordinate, packed
// bit k <-> weight b^k (k=0 least significant). b=2: plane p only. b=3: digit 1 -> p, digit 2 -> q.
struct DV{ u64 p=0,q=0; };
static inline DV dadd(DV a, DV b){
    if(B==2) return {a.p^b.p,0};
    u64 z1=~(a.p|a.q), z2=~(b.p|b.q);
    DV r; r.p=(a.p&z2)|(z1&b.p)|(a.q&b.q); r.q=(a.q&z2)|(z1&b.q)|(a.p&b.p); return r; }
static inline DV dneg(DV a){ if(B==2) return a; return {a.q,a.p}; }
static inline DV dscale(DV a,int s){ s=md(s); if(s==0) return {0,0}; if(s==1) return a; return dneg(a); }
static DV packDigits(const int* dig,int n){ DV v; for(int d=0;d<n;d++){ int k=n-1-d; if(dig[d]==1) v.p|=1ULL<<k; else if(dig[d]==2) v.q|=1ULL<<k; } return v; }
static inline int digitAt(DV v,int k){ return (v.p>>k&1)? 1 : ((v.q>>k&1)? 2 : 0); }
static ll T3[65536];
static void initT3(){ for(int x=0;x<65536;x++){ ll v=0,w=1; for(int k=0;k<16;k++){ if(x>>k&1) v+=w; w*=3; } T3[x]=v; } }
static inline ll v3(u64 m){ ll r=0, w=1; while(m){ r+=w*T3[m&0xFFFF]; m>>=16; w*=43046721LL; } return r; }
static inline ll ival(DV v){ if(B==2) return (ll)v.p; return v3(v.p)+2*v3(v.q); }

// mu(delta): minimal |int(X(+)delta)-int(X)| over X (toroidal mod b^n if tor). Also returns the minimising subset Bm
// (bits k where e_k = delta_k - b), from which X is X_k = b-delta_k (k in Bm), 0 otherwise.
static inline ll muDV(DV v,int n,bool tor,u64* Bm=nullptr){
    u64 supp=v.p|v.q; if(!supp){ if(Bm)*Bm=0; return 0; }
    ll I=ival(v); ll best=LLONG_MAX; u64 bestB=0;
    int ts= tor? 3:1;
    for(int ti=0;ti<ts;ti++){ int t= ti==0?0:(ti==1?1:-1); ll T=I-(ll)t*PW[n];
        // pred: largest s<=T in S (greedy, bits of supp descending, value b^{k+1})
        u64 ch=0; ll cur=0;
        if(T>=0){ for(u64 m=supp;m;){ int k=63-__builtin_clzll(m); m&=~(1ULL<<k); if(cur+PW[k+1]<=T){ cur+=PW[k+1]; ch|=1ULL<<k; } }
            ll d=T-cur; ll cand= tor? d : d; if(cand<best){best=cand;bestB=ch;} if(d==0) continue; }
        // succ: binary increment of ch over the positions supp (or 0 if T<0)
        u64 s2; ll val2;
        if(T<0){ s2=0; val2=0; }
        else { u64 free=supp&~ch; if(!free) continue; int k=__builtin_ctzll(free); s2=(ch&~((1ULL<<k)-1))|(1ULL<<k);
               // clear chosen bits below k (they are in supp, lower than k)
               s2&=~(((1ULL<<k)-1)); val2=0; for(u64 m=s2;m;){ int kk=__builtin_ctzll(m); m&=m-1; val2+=PW[kk+1]; } }
        ll d=val2-T; if(d<best){best=d;bestB=s2;} }
    if(tor){ ll Bn=PW[n]; if(best> Bn) DIE("mu internal"); }
    if(Bm) *Bm=bestB; return best; }
static ll muBrute(DV v,int n,bool tor){ ll best=LLONG_MAX; ll N=PW[n];
    for(ll X=0;X<N;X++){ // digits of X
        ll x=X, y=0, w=1; DV vv=v; for(int k=0;k<n;k++){ int xd=x%B; x/=B; int dd=digitAt(vv,k); y+=(ll)md(xd+dd)*w; w*=B; }
        ll d=y-X; if(d<0) d=-d; if(tor) d=min(d,N-d); best=min(best,d); }
    return best; }

// ------------------------------------------------------------------ code helpers
// top-H window of coordinate c of a generator, packed
static DV winDV(const VI& g,int M,int c,int d0,int H){ VI dg(H); for(int d=0;d<H;d++) dg[d]=g[c*M+d0+d]; return packDigits(dg.data(),H); }

typedef __int128 i128; static const i128 I128MAX=(((i128)1)<<126);
static double cOf(i128 d2,int M){ return sqrtl((long double)d2)*powl((long double)B,-2.0L*M/3); }
static string s128(i128 x){ if(x==0) return "0"; bool neg=x<0; if(neg) x=-x; string r; while(x>0){ r+=char('0'+(int)(x%10)); x/=10; } if(neg) r+='-'; reverse(r.begin(),r.end()); return r; }

// ------------------------------------------------------------------ vunif (threshold enumeration)
struct WRes{ ll v=LLONG_MAX; array<DV,3> D; ll zeroCnt=0; ll T=0; };
static ll hOf(ll mu){ ll t=mu>1? mu-1:0; return t*t; }

struct WinCode{ int H=0; bool inj=true; vector<pair<ll,DV>> all; vector<array<DV,64>> unitSyn; };
static WinCode buildWin(const Net& n,int H){
    int M=n.M; int nd=3*H; WinCode W; W.H=H;
    vector<VI> img; for(int i=0;i<M;i++){ VI v(nd); for(int c=0;c<3;c++) for(int d=0;d<H;d++) v[c*H+d]=n.g[i][c*M+d]; img.push_back(v); }
    Ech E=echelon(img,nd); if((int)E.R.size()<M){ W.inj=false; return W; }
    VI np; { vector<char> isp(nd,0); for(int c:E.piv) isp[c]=1; for(int t=0;t<nd;t++) if(!isp[t]) np.push_back(t); }
    if(np.size()>64) DIE("syndrome too long");
    W.unitSyn.resize(3);
    for(int c=0;c<3;c++) for(int d=0;d<H;d++){ VI v(nd,0); v[c*H+d]=1; VI rr=reduceBy(E,v); DV x; for(size_t i=0;i<np.size();i++){ int s=rr[np[i]]; if(s==1) x.p|=1ULL<<i; else if(s==2) x.q|=1ULL<<i; } W.unitSyn[c][H-1-d]=x; }
    ll NH=PW[H]; W.all.reserve(NH);
    for(ll x=0;x<NH;x++){ DV v; ll t=x; for(int k=0;k<H;k++){ int dg=t%B; t/=B; if(dg==1) v.p|=1ULL<<k; else if(dg==2) v.q|=1ULL<<k; }
        W.all.push_back({hOf(muDV(v,H,true)),v}); }
    sort(W.all.begin(),W.all.end(),[](const pair<ll,DV>& a,const pair<ll,DV>& b){ return a.first<b.first; });
    return W; }
// every nonzero window codeword (x,y,z) with sum_c h(.) <= T, exactly once; callback(weight, x,y,z)
template<class F> static void lowWindow(const WinCode& W,ll T,F f){
    int H=W.H; auto syn=[&](int c,DV v){ DV s; for(int k=0;k<H;k++){ int dg=digitAt(v,k); if(dg) s=dadd(s,dscale(W.unitSyn[c][k],dg)); } return s; };
    auto key=[](DV s){ return s.p*0x9E3779B97F4A7C15ULL ^ (s.q+0x632BE59BD9B4E019ULL)*0xC2B2AE3D27D4EB4FULL; };
    size_t ns=0; while(ns<W.all.size() && W.all[ns].first<=T) ns++;
    unordered_map<u64,vector<int>> hz; hz.reserve(ns*2+1); vector<DV> sx(ns),sy(ns),sz(ns);
    for(size_t i=0;i<ns;i++){ sx[i]=syn(0,W.all[i].second); sy[i]=syn(1,W.all[i].second); sz[i]=syn(2,W.all[i].second); hz[key(sz[i])].push_back(i); }
    for(size_t i=0;i<ns;i++) for(size_t j=0;j<ns;j++){ ll hx=W.all[i].first, hy=W.all[j].first; if(hx+hy>T) break;
        DV t=dneg(dadd(sx[i],sy[j])); auto it=hz.find(key(t)); if(it==hz.end()) continue;
        for(int k:it->second){ if(sz[k].p!=t.p||sz[k].q!=t.q) continue; ll w=hx+hy+W.all[k].first; if(w>T) continue;
            DV a=W.all[i].second,b=W.all[j].second,cc=W.all[k].second; if(!(a.p|a.q|b.p|b.q|cc.p|cc.q)) continue;
            f(w,a,b,cc); } }
}
static WRes vunifThreshold(const Net& n,int H){
    WRes R; WinCode W=buildWin(n,H); if(!W.inj){ R.v=0; R.zeroCnt=-1; return R; }
    for(ll T=0;;T=(T==0?1:2*T)){
        ll best=LLONG_MAX, zc=0; array<DV,3> bw;
        lowWindow(W,T,[&](ll w,DV a,DV b,DV c){ if(w==0) zc++; if(w<best){ best=w; bw={a,b,c}; } });
        if(best<=T){ R.v=best; R.D=bw; R.zeroCnt=zc; R.T=T; return R; }
        if(T>(ll)1e7) DIE("threshold runaway"); }
}

// generic codeword enumeration over F_b^M (odometer), parallel over chunks; callback per thread
template<class F> static void enumCode(const vector<array<DV,3>>& col,int M,F f){
    int rr=0; while(rr<M && PW[rr]<256) rr++; // outer digits: the LAST rr generators
    int inner=M-rr; ll NO=PW[rr], NI=PW[inner];
    #pragma omp parallel for schedule(dynamic,1)
    for(ll o=0;o<NO;o++){ array<DV,3> cur; ll t=o; for(int i=inner;i<M;i++){ int dg=t%B; t/=B; for(int c=0;c<3;c++) cur[c]=dadd(cur[c],dscale(col[i][c],dg)); }
        VI v(inner,0); int tid=0;
#ifdef _OPENMP
        tid=omp_get_thread_num();
#endif
        for(ll it=0;it<NI;it++){ if(o!=0||it!=0) f(cur,tid);
            for(int i=0;i<inner;i++){ v[i]++; for(int c=0;c<3;c++) cur[c]=dadd(cur[c],col[i][c]); if(v[i]<B) break; v[i]=0; } } }
}

// recover the index n (coefficients) of a codeword given its packed coordinates over the top-H window
static VI solveIndex(const Net& n,int H,const array<DV,3>& D){ int M=n.M, nd=3*H;
    // unknown n in F_b^M: sum_i n_i g_i|window = D
    vector<VI> A(nd,VI(M+1));
    for(int c=0;c<3;c++) for(int d=0;d<H;d++){ int row=c*H+d; for(int i=0;i<M;i++) A[row][i]=n.g[i][c*M+d]; A[row][M]=digitAt(D[c],H-1-d); }
    Ech E=echelon(A,M+1); for(size_t k=0;k<E.R.size();k++) if(E.piv[k]==M) DIE("solveIndex: inconsistent");
    VI x(M,0); for(size_t k=0;k<E.R.size();k++) x[E.piv[k]]=E.R[k][M]; return x; }

// optimal X digits (top-H window, MSB-first) realising mu for delta
static VI optX(DV v,int H,bool tor){ u64 Bm; muDV(v,H,tor,&Bm); VI X(H,0); for(int d=0;d<H;d++){ int k=H-1-d; if(Bm>>k&1) X[d]=B-digitAt(v,k); } return X; }

int main(int argc,char** argv){
    if(argc<2) DIE("see header");
    string mode=argv[1]; initT3();
    if(mode=="selftest"){ ll nchk=0;
        for(int b: {2,3}){ B=b; initPW(); for(int n=1;n<=7;n++){ ll N=PW[n]; for(ll x=0;x<N;x++){ DV v; ll t=x; for(int k=0;k<n;k++){ int dg=t%B; t/=B; if(dg==1) v.p|=1ULL<<k; else if(dg==2) v.q|=1ULL<<k; }
            for(int tor=0;tor<2;tor++){ ll a=muDV(v,n,tor), c=muBrute(v,n,tor); if(a!=c) DIE("selftest FAIL b=%d n=%d x=%lld tor=%d greedy=%lld brute=%lld",b,n,x,tor,a,c);
                // the minimiser X realises it
                u64 Bm; muDV(v,n,tor,&Bm); ll X=0,Y=0,w=1; for(int k=0;k<n;k++){ int dk=digitAt(v,k); int xk=(Bm>>k&1)? B-dk:0; X+=xk*w; Y+=md(xk+dk)*w; w*=B; }
                ll d=llabs(Y-X); if(tor) d=min(d,PW[n]-d); if(d!=a) DIE("selftest minimiser FAIL"); nchk++; } } } }
        B=0; printf("selftest OK: %lld (b,n,delta,tor) cases, greedy mu == brute force, minimiser realises it\n",nchk); return 0; }
    if(mode=="witshift"){ Net n=readNet(argv[2]); FILE* f=fopen(argv[3],"r"); for(int t=0;t<3*n.M;t++) if(fscanf(f,"%d",&n.sh[t])!=1) DIE("tau file"); fclose(f); writeNet(n,argv[4]); return 0; }
    Net n=readNet(argv[2]); int M=n.M;
    if(mode=="vunif"||mode=="vfull"){
        int H= argc>3? atoi(argv[3]) : M/2; ll K=PW[H]; auto t0=chrono::steady_clock::now();
        WRes R;
        if(mode=="vunif") R=vunifThreshold(n,H);
        else { vector<array<DV,3>> col(M); for(int i=0;i<M;i++) for(int c=0;c<3;c++) col[i][c]=winDV(n.g[i],M,c,0,H);
            int nt=1;
#ifdef _OPENMP
            nt=omp_get_max_threads();
#endif
            vector<ll> tb(nt,LLONG_MAX), tz(nt,0); vector<array<DV,3>> tw(nt);
            enumCode(col,M,[&](const array<DV,3>& cw,int tid){ ll w=0; for(int c=0;c<3;c++) w+=hOf(muDV(cw[c],H,true)); if(w==0) tz[tid]++; if(w<tb[tid]){tb[tid]=w; tw[tid]=cw;} });
            R.v=LLONG_MAX; R.zeroCnt=0; for(int t=0;t<nt;t++){ R.zeroCnt+=tz[t]; if(tb[t]<R.v){R.v=tb[t]; R.D=tw[t];} } }
        double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
        int W=M-H; double g=pow((double)B,W)*sqrt((double)R.v)*pow((double)B,-2.0*M/3);
        printf("%s L=%d H=%d: v*_unif=%lld gsep_unif=%.6f zeroweight_codewords=%lld [%.2fs]",mode.c_str(),M,H,R.v,g,R.zeroCnt,el);
        if(R.zeroCnt==-1){ printf(" (coarse map not injective)\n"); return 0; }
        // witness: index, shift tau' (top-H digits), explicit pair re-check
        VI idx=solveIndex(n,H,R.D); VI tau(3*M,0);
        // first point p = shift (index 0); X_c = optimal digits; tau_c = X_c - top(p)_c
        for(int c=0;c<3;c++){ VI X=optX(R.D[c],H,true); for(int d=0;d<H;d++) tau[c*M+d]=md(X[d]-n.sh[c*M+d]); }
        // re-evaluate the pair (p, p + Delta) under tau directly
        ll vv=0; for(int c=0;c<3;c++){ ll a=0,bq=0; for(int d=0;d<H;d++){ int pd=md(n.sh[c*M+d]+tau[c*M+d]); int dd=0; for(int i=0;i<M;i++) dd+=idx[i]*n.g[i][c*M+d]; int qd=md(pd+dd); a=a*B+pd; bq=bq*B+qd; }
            ll dk=llabs(bq-a)%K; dk=min(dk,K-dk); ll t=dk>1?dk-1:0; vv+=t*t; }
        printf(" witness_pair_recheck=%lld %s\n",vv, vv==R.v?"OK":"MISMATCH");
        if(vv!=R.v) return 4;
        if(argc>4){ FILE* f=fopen(argv[4],"w"); for(int t=0;t<3*M;t++) fprintf(f,"%d ",md(n.sh[t]+tau[t])); fprintf(f,"\n"); fclose(f); }
        return 0; }
    if(mode=="cunif"){ auto t0=chrono::steady_clock::now();
        vector<array<DV,3>> col(M); for(int i=0;i<M;i++) for(int c=0;c<3;c++) col[i][c]=winDV(n.g[i],M,c,0,M);
        int nt=1;
#ifdef _OPENMP
        nt=omp_get_max_threads();
#endif
        vector<i128> bt(nt,I128MAX), bn(nt,I128MAX); vector<array<DV,3>> wt(nt), wn(nt);
        enumCode(col,M,[&](const array<DV,3>& cw,int tid){
            i128 s=0; for(int c=0;c<3;c++){ i128 m=muDV(cw[c],M,true); s+=m*m; if(s>=bt[tid] && s>=bn[tid]) return; }
            if(s<bt[tid]){ bt[tid]=s; wt[tid]=cw; }
            i128 s2=0; for(int c=0;c<3;c++){ i128 m=muDV(cw[c],M,false); s2+=m*m; if(s2>=bn[tid]) return; }
            if(s2<bn[tid]){ bn[tid]=s2; wn[tid]=cw; } });
        i128 dT=I128MAX, dN=I128MAX; array<DV,3> WT,WN; for(int t=0;t<nt;t++){ if(bt[t]<dT){dT=bt[t];WT=wt[t];} if(bn[t]<dN){dN=bn[t];WN=wn[t];} }
        double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
        printf("cunif M=%d: toroidal d2_unif=%s c_unif=%.6f | non-toroidal d2nt_unif=%s cnt_unif=%.6f [%.2fs]\n",M,s128(dT).c_str(),cOf(dT,M),s128(dN).c_str(),cOf(dN,M),el);
        if(argc>3){ // witness shift for the toroidal minimum: full-depth tau with first point = shift
            FILE* f=fopen(argv[3],"w"); for(int c=0;c<3;c++){ VI X=optX(WT[c],M,true); for(int d=0;d<M;d++) fprintf(f,"%d ",X[d]); } fprintf(f,"\n"); fclose(f); }
        return 0; }
    if(mode=="cunif2"){ // exact min over all shifts of toroidal d2 (and non-toroidal d2nt), pruned by the top-H window:
        // mu_M(delta) >= b^(M-H) * max(0, mu_H(top_H delta) - 1)  (both toroidal; non-toroidal mu >= toroidal mu), so every
        // codeword with sum mu_M^2 <= U has window weight <= U / b^(2(M-H)); the window map is injective (3H >= M, t=0).
        auto t0=chrono::steady_clock::now();
        int H= argc>3? atoi(argv[3]) : (M+2)/3; WinCode W=buildWin(n,H); if(!W.inj) DIE("cunif2: window map not injective (H too small or not a net)");
        i128 W2=(i128)PW[M-H]*PW[M-H];
        // window -> full codeword: precompute map from window digits to index via solveIndex per candidate
        auto fullOf=[&](DV a,DV b,DV c){ array<DV,3> D={a,b,c}; VI idx=solveIndex(n,H,D); array<DV,3> F;
            for(int cc=0;cc<3;cc++){ VI dg(M); for(int d=0;d<M;d++){ int s=0; for(int i=0;i<M;i++) s+=idx[i]*n.g[i][cc*M+d]; dg[d]=md(s); } F[cc]=packDigits(dg.data(),M); }
            return F; };
        i128 UT=I128MAX, UN=I128MAX; array<DV,3> WT,WN; ll T=0; ll ncand=0; int passes=0;
        while(true){ passes++;
            lowWindow(W,T,[&](ll w,DV a,DV b,DV c){ ncand++; array<DV,3> F=fullOf(a,b,c);
                i128 s=0,s2=0; for(int cc=0;cc<3;cc++){ i128 m1=muDV(F[cc],M,true), m2=muDV(F[cc],M,false); s+=m1*m1; s2+=m2*m2; }
                if(s<UT){UT=s;WT=F;} if(s2<UN){UN=s2;WN=F;} });
            ll need = (UN==I128MAX)? -1 : (ll)(UN/W2);   // UN >= UT, so this threshold covers both minima
            if(need>=0 && need<=T) break;
            T = (need<0)? (T==0?1:2*T) : need; if(T>(ll)1e8) DIE("cunif2 threshold runaway"); }
        double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
        printf("cunif2 M=%d H=%d: toroidal d2_unif=%s c_unif=%.6f | non-toroidal d2nt_unif=%s cnt_unif=%.6f (final window threshold %lld, %lld candidates, %d passes) [%.2fs]\n",
               M,H,s128(UT).c_str(),cOf(UT,M),s128(UN).c_str(),cOf(UN,M),T,ncand,passes,el);
        if(argc>4){ FILE* f=fopen(argv[4],"w"); for(int c=0;c<3;c++){ VI X=optX(WT[c],M,true); for(int d=0;d<M;d++) fprintf(f,"%d ",X[d]); } fprintf(f,"\n"); fclose(f); }
        return 0; }
    if(mode=="freeze"){ Net m2=readNet(argv[3]); int L=M, Mm=m2.M; if((Mm-L)%3) DIE("levels"); int j=(Mm-L)/3, H=L/2;
        // V_L
        vector<VI> img; for(int i=0;i<L;i++){ VI v(3*H); for(int c=0;c<3;c++) for(int d=0;d<H;d++) v[c*H+d]=n.g[i][c*L+d]; img.push_back(v); }
        Ech EV=echelon(img,3*H); bool ok=true; string why;
        if((int)EV.R.size()!=L){ ok=false; why+=" dimV<L"; }
        // Sigma rows (top j digits of each coordinate of P_m) and K rows (digits j..j+H-1)
        vector<VI> Sg; for(int c=0;c<3;c++) for(int d=0;d<j;d++){ VI r(Mm); for(int i=0;i<Mm;i++) r[i]=m2.g[i][c*Mm+d]; Sg.push_back(r); }
        int rs = j? (int)echelon(Sg,Mm).R.size() : 0; if(rs!=3*j){ ok=false; why+=" rankSigma"; }
        auto Kof=[&](const VI& g){ VI v(3*H); for(int c=0;c<3;c++) for(int d=0;d<H;d++) v[c*H+d]=g[c*Mm+j+d]; return v; };
        for(int i=0;i<Mm;i++) if(!inSpan(EV,Kof(m2.g[i]))){ ok=false; why+=" K(gen)notinV"; break; }
        // dim K(ker Sigma): kernel of Sigma via echelon of [Sigma^T]... compute rank of [Sigma;K] - rank Sigma
        vector<VI> SK=Sg; for(int c=0;c<3;c++) for(int d=0;d<H;d++){ VI r(Mm); for(int i=0;i<Mm;i++) r[i]=m2.g[i][c*Mm+j+d]; SK.push_back(r); }
        int rsk=echelon(SK,Mm).R.size(); if(rsk-rs!=L){ ok=false; why+=" dimK(kerSigma)!=L"; }
        VI ds(3*H); for(int c=0;c<3;c++) for(int d=0;d<H;d++) ds[c*H+d]=md(m2.sh[c*Mm+j+d]-n.sh[c*L+d]);
        if(!inSpan(EV,ds)){ ok=false; why+=" shift"; }
        printf("freeze L=%d -> m=%d (j=%d, H=%d): %s%s\n",L,Mm,j,H,ok?"FROZEN (hypothesis of the reduction lemma holds)":"NOT FROZEN:",why.c_str()); return ok?0:2; }
    if(mode=="effD"){ Net q=readNet(argv[3]); int Mq=q.M; if(Mq!=M+3) DIE("effD: need levels l, l+3");
        // the level-(l+3) code must contain the embedded level-l code (block digits 1..M, top and jitter 0); the
        // remaining 3 directions carry the shifts s_A, s_B on the block digits. D_eff = number of leading block digits
        // on which EVERY codeword of the level-(l+3) code agrees with an embedded level-l codeword ... computed as:
        // largest D such that (block digits 1..D) of every generator of q lie in the top-D code of P_l.
        vector<VI> emb; for(int i=0;i<M;i++){ VI v(3*Mq,0); for(int c=0;c<3;c++) for(int d=0;d<M;d++) v[c*Mq+1+d]=n.g[i][c*M+d]; emb.push_back(v); }
        vector<VI> qg=q.g; Ech EQ=echelon(qg,3*Mq); bool contains=true; for(auto& v:emb) if(!inSpan(EQ,v)) contains=false;
        int Deff=-1;
        for(int D=0; D<=M; D++){ // top-D block digits of every q generator, minus the part explained by top/jitter? use: project
            // codewords of q with top digit 0 in all coords (kernel of the top map) must have block top-D digits in top-D code of P_l
            // simpler sufficient+necessary for the lift form: for every generator g of q, its block top-D digits lie in the
            // span of {top-D block digits of P_l generators}.
            vector<VI> base; for(int i=0;i<M;i++){ VI v(3*D); for(int c=0;c<3;c++) for(int d=0;d<D;d++) v[c*D+d]=n.g[i][c*M+d]; base.push_back(v); }
            Ech EB=echelon(base,3*D); bool ok=true;
            for(int i=0;i<Mq && ok;i++){ VI v(3*D); for(int c=0;c<3;c++) for(int d=0;d<D;d++) v[c*D+d]=q.g[i][c*Mq+1+d]; if(!inSpan(EB,v)) ok=false; }
            VI ds(3*D); for(int c=0;c<3;c++) for(int d=0;d<D;d++) ds[c*D+d]=md(q.sh[c*Mq+1+d]-n.sh[c*M+d]); if(!inSpan(EB,ds)) ok=false;
            if(ok) Deff=D; else break; }
        printf("effD l=%d: embedded P_l contained=%d, D_eff=%d (floor(l/2)=%d)\n",M,contains?1:0,Deff,M/2); return 0; }
    DIE("unknown mode");
}
