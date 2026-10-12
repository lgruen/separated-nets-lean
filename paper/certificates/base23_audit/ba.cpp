// ba.cpp -- BASE23 audit toolkit (written from the mathematics; shares no code with a6_*, g3_*, r1_*, r3_*).
// Digital (0,M,3)-nets over F_b, b in {2,3}: point set { C n (+) sigma : n in F_b^M }, digits MSB first,
// integer coordinate X = sum_d digit_d b^(M-1-d) in [0,b^M), torus period b^M.
//
// NET file format:  "NET b M" / M lines (generator i: 3M digits, coord c depth d at c*M+d) / 1 line shift (3M digits).
//
// modes:
//   frompts PTS OUT.net        point file ("b m" + b^m lines "x y z") -> verify it is an affine F_b-space, write NET
//   info NET                   M, t=0 check (all compositions), shift==0?
//   tpexport NET               print "b M 3" + 3 MxM matrices (rows = output digits) for explainers/check/net_tparam.py
//   mind NET                   materialise; exact toroidal d2 (integer units b^-M), c = sqrt(d2) b^(-2M/3)
//   vstar NET                  materialise; certificate v* = min_{p!=q} sum_i max(0,|dk_i|_tor(K)-1)^2, k = top floor(M/2) digits
//   block NET trunc|exact j    generic block evaluator (any digital net; partition by the top j digits of each coordinate)
//   lift NET D_off mode seed OUT.net   one deep-shift lift (mode: part = particular solution, rand = random admissible)
//   setshift NET zero|rand seed OUT.net
//   cmpsets NET1 NET2          same point set?
//   freeze NET_L NET_m         every sigma-block of P_m carries exactly the top-floor(L/2)-digit triples of P_L
//   ushift NET                 min of the certificate v* over ALL digital shifts (enumerated modulo the coarse image)
//   uallc NET                  min of the exact c over ALL digital shifts (modulo the image of the generator map)
// build: g++-16 -O3 -fopenmp -std=c++17 -o ba ba.cpp
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <climits>
#include <vector>
#include <string>
#include <algorithm>
#include <random>
#include <unordered_map>
#include <array>
#include <map>
#include <chrono>
#ifdef _OPENMP
#include <omp.h>
#include <parallel/algorithm>
#endif
using namespace std;
typedef long long ll; typedef unsigned long long u64; typedef vector<int> VI;

static int B = 0;
static inline int md(int a){ a %= B; return a < 0 ? a + B : a; }
static int inv(int a){ for(int x=1;x<B;x++) if(md(a*x)==1) return x; fprintf(stderr,"inv(0)\n"); exit(9); }
static ll ipow(ll b, int e){ ll r=1; for(int i=0;i<e;i++){ if(r > (ll)4e18/b){ fprintf(stderr,"ipow overflow\n"); exit(9);} r*=b; } return r; }
#define DIE(...) do{ fprintf(stderr, __VA_ARGS__); fprintf(stderr,"\n"); exit(3);}while(0)

struct Net { int M=0; vector<VI> g; VI sh; };

static Net readNet(const char* fn){
    FILE* f=fopen(fn,"r"); if(!f) DIE("cannot open %s",fn);
    char tag[8]; int b,M; if(fscanf(f,"%7s %d %d",tag,&b,&M)!=3 || strcmp(tag,"NET")) DIE("bad NET header %s",fn);
    B=b; Net n; n.M=M; n.g.assign(M,VI(3*M)); n.sh.assign(3*M,0);
    for(int i=0;i<M;i++) for(int t=0;t<3*M;t++){ if(fscanf(f,"%d",&n.g[i][t])!=1) DIE("short NET"); n.g[i][t]=md(n.g[i][t]); }
    for(int t=0;t<3*M;t++){ if(fscanf(f,"%d",&n.sh[t])!=1) DIE("short NET shift"); n.sh[t]=md(n.sh[t]); }
    fclose(f); return n;
}
static void writeNet(const Net& n, const char* fn){
    FILE* f=fopen(fn,"w"); fprintf(f,"NET %d %d\n",B,n.M);
    for(auto& g:n.g){ for(int t=0;t<3*n.M;t++) fprintf(f,"%d%c",g[t],t+1<3*n.M?' ':'\n'); }
    for(int t=0;t<3*n.M;t++) fprintf(f,"%d%c",n.sh[t],t+1<3*n.M?' ':'\n'); fclose(f);
}

// ---------------------------------------------------------------- linear algebra over F_b
static int rankOf(vector<VI> A, int nc){
    int r=0, ne=A.size();
    for(int c=0;c<nc && r<ne;c++){ int p=-1; for(int i=r;i<ne;i++) if(A[i][c]){p=i;break;} if(p<0) continue;
        swap(A[p],A[r]); int iv=inv(A[r][c]); for(int t=c;t<nc;t++) A[r][t]=md(A[r][t]*iv);
        for(int i=r+1;i<ne;i++) if(A[i][c]){ int f=A[i][c]; for(int t=c;t<nc;t++) A[i][t]=md(A[i][t]-f*A[r][t]); }
        r++; }
    return r;
}
// RREF solve A x = rhs ; returns false if inconsistent. part: free vars = 0. nulls: basis of kernel.
static bool solveSys(vector<VI> A, VI rhs, int nv, VI& part, vector<VI>& nulls){
    int ne=A.size(), r=0; vector<int> pc;
    for(int c=0;c<nv && r<ne;c++){ int p=-1; for(int i=r;i<ne;i++) if(A[i][c]){p=i;break;} if(p<0) continue;
        swap(A[p],A[r]); swap(rhs[p],rhs[r]); int iv=inv(A[r][c]);
        for(int t=0;t<nv;t++) A[r][t]=md(A[r][t]*iv); rhs[r]=md(rhs[r]*iv);
        for(int i=0;i<ne;i++) if(i!=r && A[i][c]){ int f=A[i][c]; for(int t=0;t<nv;t++) A[i][t]=md(A[i][t]-f*A[r][t]); rhs[i]=md(rhs[i]-f*rhs[r]); }
        pc.push_back(c); r++; }
    for(int i=r;i<ne;i++) if(rhs[i]) return false;
    part.assign(nv,0); for(int i=0;i<r;i++) part[pc[i]]=rhs[i];
    vector<char> isp(nv,0); for(int c:pc) isp[c]=1; nulls.clear();
    for(int fcol=0; fcol<nv; fcol++) if(!isp[fcol]){ VI v(nv,0); v[fcol]=1; for(int i=0;i<r;i++) v[pc[i]]=md(-A[i][fcol]); nulls.push_back(v); }
    return true;
}

// ---------------------------------------------------------------- t = 0 check (direct from the definition)
// (0,M,3)-net iff for every (d0,d1,d2), d0+d1+d2=M, the M x M matrix [top d_c rows of C_c] is nonsingular.
static bool isT0(const Net& n, int* bad=nullptr){
    int M=n.M;
    for(int d0=0; d0<=M; d0++) for(int d1=0; d0+d1<=M; d1++){ int d2=M-d0-d1; int dd[3]={d0,d1,d2};
        vector<VI> A; for(int c=0;c<3;c++) for(int d=0; d<dd[c]; d++){ VI r(M); for(int i=0;i<M;i++) r[i]=n.g[i][c*M+d]; A.push_back(r); }
        if(rankOf(A,M)!=M){ if(bad){bad[0]=d0;bad[1]=d1;bad[2]=d2;} return false; } }
    return true;
}

// ---------------------------------------------------------------- packed digits (digitwise F_b addition)
// b=2: the packed word IS the integer (bit k = weight 2^k); add = XOR.
// b=3: 4-bit lanes, lane k = digit of weight 3^k (<=16 digits/word); add = SWAR mod 3; value via table.
static uint32_t T3[65536];
static void initPack(){ if(B==3) for(int x=0;x<65536;x++){ uint32_t v=0,w=1; bool ok=true; for(int k=0;k<4;k++){ int dg=(x>>(4*k))&15; if(dg>2) ok=false; v+=dg*w; w*=3; } T3[x]= ok? v : 0xFFFFFFFFu; } }
static inline u64 padd(u64 a, u64 b){
    if(B==2) return a^b;
    const u64 ONE=0x1111111111111111ULL; u64 s=a+b; u64 m=((s+ONE)>>2)&ONE; return s-3*m;
}
static inline u64 pval(u64 a){
    if(B==2) return a;
    return (u64)T3[a&0xFFFF] + 81ULL*T3[(a>>16)&0xFFFF] + 6561ULL*T3[(a>>32)&0xFFFF] + 531441ULL*T3[(a>>48)&0xFFFF];
}
// pack digits dig[0..nd-1] (MSB first) of one coordinate
static u64 packDigits(const int* dig, int nd){
    if(B==2){ if(nd>63) DIE("pack b2 nd>63"); u64 v=0; for(int d=0;d<nd;d++) v=(v<<1)|(u64)dig[d]; return v; }
    if(nd>16) DIE("pack b3 nd>16 (%d)",nd); u64 v=0; for(int d=0;d<nd;d++) v|=(u64)dig[d] << (4*(nd-1-d)); return v;
}

// ---------------------------------------------------------------- materialise
static void materialise(const Net& n, vector<u64>* XYZ){
    int M=n.M; ll N=ipow(B,M);
    for(int c=0;c<3;c++) XYZ[c].resize(N);
    vector<array<u64,3>> col(M); for(int i=0;i<M;i++) for(int c=0;c<3;c++) col[i][c]=packDigits(&n.g[i][c*M],M);
    u64 cur[3]; for(int c=0;c<3;c++) cur[c]=packDigits(&n.sh[c*M],M);
    VI v(M,0);
    for(ll idx=0; idx<N; idx++){
        for(int c=0;c<3;c++) XYZ[c][idx]=pval(cur[c]);
        for(int i=0;i<M;i++){ v[i]++; for(int c=0;c<3;c++) cur[c]=padd(cur[c],col[i][c]); if(v[i]<B) break; v[i]=0; }
    }
}

// metric: exact -> sum t_i^2 ; trunc -> sum max(0,t_i-1)^2 ; t_i toroidal |delta| mod K
static inline ll tor(ll d, ll K){ d%=K; if(d<0) d+=K; return d < K-d ? d : K-d; }
static inline ll term(ll t, bool trunc){ if(trunc){ t = t>0? t-1 : 0; } return t*t; }

// grid min over a materialised set (coordinates in [0,K)); returns min metric and count of unordered pairs at min.
// cells of width w=b^(e-g), G=b^g per axis (exact torus tiling). Non-adjacent pairs have some t >= w+1, i.e. metric >= w^2 (trunc) / (w+1)^2.
static pair<ll,ll> gridMin(const vector<u64>* P, int e /* K=b^e */, bool trunc, int g){
    ll N=P[0].size(); ll K=ipow(B,e);
    auto pairm=[&](ll a, ll b){ ll s=0; for(int c=0;c<3;c++) s+=term(tor((ll)P[c][a]-(ll)P[c][b],K),trunc); return s; };
    ll G=ipow(B,g);
    if(G<3){ ll best=LLONG_MAX, cnt=0; for(ll a=0;a<N;a++) for(ll b=a+1;b<N;b++){ ll v=pairm(a,b); if(v<best){best=v;cnt=1;} else if(v==best) cnt++; } return {best,cnt}; }
    ll w=ipow(B,e-g); ll G3=G*G*G; if(G3>(ll)4e9) DIE("grid too big");
    vector<uint32_t> st(G3+1,0); vector<uint32_t> ord(N);
    auto cellOf=[&](ll i){ return ((ll)(P[0][i]/w)*G + (ll)(P[1][i]/w))*G + (ll)(P[2][i]/w); };
    for(ll i=0;i<N;i++) st[cellOf(i)+1]++;
    for(ll c=0;c<G3;c++) st[c+1]+=st[c];
    { vector<uint32_t> pos(st.begin(),st.end()-1); for(ll i=0;i<N;i++) ord[pos[cellOf(i)]++]=i; }
    ll best=LLONG_MAX, cnt=0;
    #pragma omp parallel
    { ll lb=LLONG_MAX, lc=0;
      #pragma omp for schedule(dynamic,256)
      for(ll c0=0;c0<G3;c0++){ ll cx=c0/(G*G), cy=(c0/G)%G, cz=c0%G;
        for(int dx=-1;dx<=1;dx++) for(int dy=-1;dy<=1;dy++) for(int dz=-1;dz<=1;dz++){
            ll c1=(((cx+dx+G)%G)*G+((cy+dy+G)%G))*G+((cz+dz+G)%G); if(c1<c0) continue;
            for(uint32_t a=st[c0];a<st[c0+1];a++) for(uint32_t b=(c1==c0?a+1:st[c1]); b<st[c1+1]; b++){ ll v=pairm(ord[a],ord[b]); if(v<lb){lb=v;lc=1;} else if(v==lb) lc++; } } }
      #pragma omp critical
      { if(lb<best){best=lb;cnt=lc;} else if(lb==best) cnt+=lc; } }
    ll guard = trunc? w*w : (w+1)*(w+1);
    if(!(best < guard)) return {-1,-1};   // inconclusive: caller retries with coarser grid
    return {best,cnt};
}

// ---------------------------------------------------------------- the deep-shift lift (own implementation)
// lambda_e for plane (ca,cb), e=1..M : functional on (a digits 0..M-1, b digits 0..M-1), kernel = P_ab + Z_e,
// Z_e = {a-depth index >= e, b-depth index >= M+1-e}. Support: a idx < e, b idx <= M-e  (M+1 unknowns).
static vector<VI> lambdas(const Net& n, int ca, int cb){
    int M=n.M; vector<VI> out;
    for(int e=1;e<=M;e++){
        int nv=M+1; vector<VI> A; VI r;
        for(int i=0;i<M;i++){ VI row(nv); for(int d=0;d<e;d++) row[d]=n.g[i][ca*M+d]; for(int d=0;d<=M-e;d++) row[e+d]=n.g[i][cb*M+d]; A.push_back(row); r.push_back(0); }
        VI part; vector<VI> nul; solveSys(A,r,nv,part,nul);
        if(nul.size()!=1) DIE("lambda: nullity %zu at e=%d plane %d%d (shadow not (0,M,2))",nul.size(),e,ca,cb);
        VI lam(2*M,0); for(int d=0;d<e;d++) lam[d]=nul[0][d]; for(int d=0;d<=M-e;d++) lam[M+d]=nul[0][e+d];
        // the two coefficient facts of the existence lemma
        if(lam[e-1]==0) DIE("lambda_%d has zero coefficient on a[e]",e);
        if(lam[M+M-e]==0) DIE("lambda_%d has zero coefficient on b[M+1-e]",e);
        out.push_back(lam);
    }
    return out;
}
// solve lambda_e(u)=r_e, u supported on deep digits (index >= D) of a and b. Returns u as 2M vector.
static VI deepSolve(const vector<VI>& lam, int M, int D, mt19937_64* rng){
    int nd=M-D, nv=2*nd; vector<VI> A; VI r;
    for(int e=0;e<M;e++){ VI row(nv); for(int k=0;k<nd;k++){ row[k]=lam[e][D+k]; row[nd+k]=lam[e][M+D+k]; } A.push_back(row);
        r.push_back(rng && B==3 ? 1+(int)((*rng)()%2) : 1); }
    VI part; vector<VI> nul;
    if(!solveSys(A,r,nv,part,nul)) DIE("deep system inconsistent M=%d D=%d",M,D);
    if(rankOf(A,nv)!=M) DIE("deep restrictions dependent M=%d D=%d",M,D);
    if(rng) for(auto& v:nul){ int c=(*rng)()%B; for(int t=0;t<nv;t++) part[t]=md(part[t]+c*v[t]); }
    VI u(2*M,0); for(int k=0;k<nd;k++){ u[D+k]=part[k]; u[M+D+k]=part[nd+k]; }
    for(int e=0;e<M;e++){ int s=0; for(int t=0;t<2*M;t++) s+=lam[e][t]*u[t]; if(md(s)==0) DIE("lambda_e(u)=0"); }
    return u;
}
static Net liftOnce(const Net& n, int D, mt19937_64* rng){
    int M=n.M; if(2*D>M) DIE("need 2D<=M");
    // planes: yz -> sA ; xy -> sB ; xz -> sB - sA
    auto Lyz=lambdas(n,1,2), Lxy=lambdas(n,0,1), Lxz=lambdas(n,0,2);
    VI uyz=deepSolve(Lyz,M,D,rng), uxy=deepSolve(Lxy,M,D,rng), uxz=deepSolve(Lxz,M,D,rng);
    VI sA(3*M,0), sB(3*M,0);
    for(int d=0;d<M;d++){ sA[1*M+d]=uyz[d]; sA[2*M+d]=uyz[M+d]; sB[0*M+d]=uxy[d]; sB[1*M+d]=uxy[M+d]; }
    for(int d=0;d<M;d++){ sA[0*M+d]=md(sB[0*M+d]-uxz[d]); sB[2*M+d]=md(sA[2*M+d]+uxz[M+d]); }
    for(int c=0;c<3;c++) for(int d=0;d<D;d++) if(sA[c*M+d]||sB[c*M+d]) DIE("shift not deep");
    int M2=M+3; Net q; q.M=M2;
    auto emb=[&](const VI& v){ VI h(3*M2,0); for(int c=0;c<3;c++) for(int d=0;d<M;d++) h[c*M2+1+d]=v[c*M+d]; return h; };
    for(auto& g:n.g) q.g.push_back(emb(g));
    VI ga(3*M2,0); for(int c=0;c<3;c++) ga[c*M2]=1;                      // a: top digits (1,1,1)
    VI g1=emb(sA); g1[0*M2]=0; g1[1*M2]=1; g1[2*M2]=1;                    // delta1: top (0,1,1)
    VI g2=emb(sB); g2[0*M2]=0; g2[1*M2]=0; g2[2*M2]=1;                    // delta2: top (0,0,1)
    // jitter (hi,lo): x=(d2,d1), y=(d1+d2,d1), z=(d1,d2)
    int hi=M+1, lo=M+2;
    g1[0*M2+hi]=0; g1[0*M2+lo]=1;  g1[1*M2+hi]=1; g1[1*M2+lo]=1;  g1[2*M2+hi]=1; g1[2*M2+lo]=0;
    g2[0*M2+hi]=1; g2[0*M2+lo]=0;  g2[1*M2+hi]=1; g2[1*M2+lo]=0;  g2[2*M2+hi]=0; g2[2*M2+lo]=1;
    q.g.push_back(ga); q.g.push_back(g1); q.g.push_back(g2);
    q.sh=emb(n.sh);
    return q;
}

// ---------------------------------------------------------------- generic block evaluator
// Partition the net by the top j digits of every coordinate (sigma, b^(3j) blocks; needs rank 3j).
// Inside a block, keep the next nb=T-j digits (T = floor(L/2) for trunc, L for exact). The block's local point set
// is S (+) off(sigma), S = image of ker(Sigma) under the block rows (common to all blocks), off affine in sigma;
// two sigmas with off congruent mod S give the SAME local set (class). Pairs: within a block, or between toroidally
// adjacent blocks (b^j >= 3); non-adjacent pairs have a coordinate t >= side+1.
struct BRes { ll best=LLONG_MAX; double cnt=0; ll ncls=0, ncomb=0; ll U0=0; };
static BRes blockEval(const Net& n, bool trunc, int j){
    int L=n.M; int T = trunc? L/2 : L; int nb=T-j, l0=L-3*j; ll Bj=ipow(B,j);
    if(nb<1 || l0<1 || Bj<3) DIE("block: bad j (nb=%d l0=%d b^j=%lld)",nb,l0,Bj);
    if(B==3 && nb>16) DIE("block: b3 nb>16");
    ll side=ipow(B,nb), K=Bj*side; if(side > (1LL<<32)-1) DIE("side too big");
    auto rowv=[&](int c,int d){ VI r(L); for(int i=0;i<L;i++) r[i]=n.g[i][c*L+d]; return r; };
    vector<VI> S; VI shS; for(int c=0;c<3;c++) for(int d=0;d<j;d++){ S.push_back(rowv(c,d)); shS.push_back(n.sh[c*L+d]); }
    if(rankOf(S,L)!=3*j) DIE("Sigma rank deficient");
    // right inverse w_r (S w_r = e_r) and kernel basis
    vector<VI> W(3*j); vector<VI> Ker;
    for(int r=0;r<3*j;r++){ VI rhs(3*j,0); rhs[r]=1; VI part; vector<VI> nul; if(!solveSys(S,rhs,L,part,nul)) DIE("right inverse"); W[r]=part; if(r==0) Ker=nul; }
    if((int)Ker.size()!=l0) DIE("kernel dim");
    vector<VI> Brows; VI shB; for(int c=0;c<3;c++) for(int d=j;d<T;d++){ Brows.push_back(rowv(c,d)); shB.push_back(n.sh[c*L+d]); }
    int nbr=3*nb;
    auto apply=[&](const VI& x){ VI y(nbr,0); for(int r=0;r<nbr;r++){ int s=0; for(int i=0;i<L;i++) s+=Brows[r][i]*x[i]; y[r]=md(s);} return y; };
    vector<VI> gK; for(auto& k:Ker) gK.push_back(apply(k));
    vector<VI> gW; for(auto& w:W) gW.push_back(apply(w));
    // echelon of span(gK) for canonical reduction
    vector<VI> E=gK; vector<int> piv; { int r=0; for(int c=0;c<nbr && r<(int)E.size();c++){ int p=-1; for(int i=r;i<(int)E.size();i++) if(E[i][c]){p=i;break;} if(p<0) continue;
            swap(E[p],E[r]); int iv=inv(E[r][c]); for(auto& x:E[r]) x=md(x*iv);
            for(int i=0;i<(int)E.size();i++) if(i!=r && E[i][c]){ int f=E[i][c]; for(int t=0;t<nbr;t++) E[i][t]=md(E[i][t]-f*E[r][t]); }
            piv.push_back(c); r++; } E.resize(r); }
    BRes R;
    if((int)E.size()<l0){ if(!trunc) DIE("exact: block map not injective (impossible for a net)"); R.best=0; R.cnt=-1; return R; } // two points share a coarse cell
    auto reduce=[&](VI v){ for(size_t k=0;k<E.size();k++){ int f=v[piv[k]]; if(f) for(int t=0;t<nbr;t++) v[t]=md(v[t]-f*E[k][t]); } return v; };
    auto pack3=[&](const VI& v){ array<u64,3> a; for(int c=0;c<3;c++) a[c]=packDigits(&v[c*nb],nb); return a; };
    VI off0=shB; for(int r=0;r<3*j;r++) if(shS[r]) for(int t=0;t<nbr;t++) off0[t]=md(off0[t]-shS[r]*gW[r][t]);
    array<u64,3> r0=pack3(reduce(off0)); vector<array<u64,3>> rW; for(int r=0;r<3*j;r++) rW.push_back(pack3(reduce(gW[r])));
    // enumerate sigma digit vectors
    ll NS=ipow(B,3*j); vector<int32_t> cls(NS); vector<array<u64,3>> reps; vector<ll> cmult;
    { struct H{ size_t operator()(const array<u64,3>& a) const { return a[0]*0x9E3779B97F4A7C15ULL ^ (a[1]+0x7F4A7C15ULL)*0xC2B2AE3D27D4EB4FULL ^ (a[2]+0x165667B1ULL)*0x27D4EB2F165667C5ULL; } };
      unordered_map<array<u64,3>,int,H> mp; VI v(3*j,0); array<u64,3> cur=r0;
      for(ll it=0; it<NS; it++){
          ll sidx=0; for(int c=0;c<3;c++){ ll s=0; for(int d=0;d<j;d++) s=s*B+v[c*j+d]; sidx=sidx*Bj+s; }
          auto f=mp.find(cur); int id; if(f==mp.end()){ id=reps.size(); mp[cur]=id; reps.push_back(cur); cmult.push_back(0);} else id=f->second;
          cls[sidx]=id; cmult[id]++;
          for(int r=0;r<3*j;r++){ v[r]++; for(int c=0;c<3;c++) cur[c]=padd(cur[c],rW[r][c]); if(v[r]<B) break; v[r]=0; } } }
    ll nc=reps.size(); R.ncls=nc;
    vector<array<u64,3>> pK; for(auto& k:gK) pK.push_back(pack3(k));
    ll NP=ipow(B,l0);
    auto genPts=[&](int id, vector<array<uint32_t,3>>& pts){ pts.resize(NP); array<u64,3> cur=reps[id]; VI v(l0,0);
        for(ll i=0;i<NP;i++){ for(int c=0;c<3;c++) pts[i][c]=(uint32_t)pval(cur[c]);
            for(int t=0;t<l0;t++){ v[t]++; for(int c=0;c<3;c++) cur[c]=padd(cur[c],pK[t][c]); if(v[t]<B) break; v[t]=0; } } };
    auto pm=[&](const array<uint32_t,3>& p, const array<uint32_t,3>& q, const ll* eo){ ll s=0; for(int c=0;c<3;c++) s+=term(tor(eo[c]+(ll)q[c]-(ll)p[c],K),trunc); return s; };
    // within-block min with grid of cell width >= Rs+1 (finds every pair with metric <= U)
    auto withinMin=[&](const vector<array<uint32_t,3>>& pts, ll U, ll& cnt)->ll{
        ll Rs = (ll)floor(sqrt((double)U)) + (trunc?2:1);
        ll G = side/(Rs+1); ll Gc=(ll)cbrt((double)pts.size())+1; if(G>Gc) G=Gc; if(G<1) G=1; ll w=(side+G-1)/G;
        ll G3=G*G*G; vector<uint32_t> st(G3+1,0), ord(pts.size());
        auto cellOf=[&](const array<uint32_t,3>& p){ return ((ll)(p[0]/w)*G+(ll)(p[1]/w))*G+(ll)(p[2]/w); };
        for(auto& p:pts) st[cellOf(p)+1]++; for(ll c=0;c<G3;c++) st[c+1]+=st[c];
        { vector<uint32_t> pos(st.begin(),st.end()-1); for(size_t i=0;i<pts.size();i++) ord[pos[cellOf(pts[i])]++]=i; }
        ll best=LLONG_MAX; cnt=0; ll z[3]={0,0,0};
        for(ll c0=0;c0<G3;c0++){ ll cx=c0/(G*G), cy=(c0/G)%G, cz=c0%G;
            for(int dx=-1;dx<=1;dx++) for(int dy=-1;dy<=1;dy++) for(int dz=-1;dz<=1;dz++){
                ll x=cx+dx,y=cy+dy,zz=cz+dz; if(x<0||y<0||zz<0||x>=G||y>=G||zz>=G) continue; ll c1=(x*G+y)*G+zz; if(c1<c0) continue;
                for(uint32_t a=st[c0];a<st[c0+1];a++) for(uint32_t b=(c1==c0?a+1:st[c1]); b<st[c1+1]; b++){ ll v=pm(pts[ord[a]],pts[ord[b]],z); if(v<best){best=v;cnt=1;} else if(v==best) cnt++; } } }
        return best; };
    // U0: an upper bound on the global minimum (an actual within-block pair of class 0)
    { vector<array<uint32_t,3>> pts; genPts(0,pts); ll cnt;
      double sp = (double)side / cbrt((double)NP); ll Ug = (ll)(4.0*sp*sp) + 4; ll U=LLONG_MAX;
      while(true){ U=withinMin(pts,Ug,cnt); if(U<=Ug) break; if(Ug > (ll)side*side) DIE("U0 search failed"); Ug*=4; }
      R.U0=U; }
    ll U=R.U0; ll Rs=(ll)floor(sqrt((double)U)) + (trunc?2:1); if(Rs>=side) DIE("U0 too large for slab method (Rs=%lld side=%lld)",Rs,side);
    // per class: within min/count, face lists (coord c, hi/lo)
    vector<ll> wmin(nc), wcnt(nc); vector<array<vector<array<uint32_t,3>>,6>> face(nc);
    #pragma omp parallel
    { vector<array<uint32_t,3>> pts;
      #pragma omp for schedule(dynamic,1)
      for(ll id=0; id<nc; id++){ genPts(id,pts); ll cnt; wmin[id]=withinMin(pts,U,cnt); wcnt[id]=cnt;
          for(auto& p:pts) for(int c=0;c<3;c++){ if((ll)p[c] < Rs) face[id][2*c].push_back(p); if((ll)p[c] >= side-Rs) face[id][2*c+1].push_back(p); } } }
    // combos: (cls(sigma), cls(sigma+e), e) over 13 forward steps
    static const int E13[13][3]={{1,0,0},{0,1,0},{0,0,1},{1,1,0},{1,-1,0},{1,0,1},{1,0,-1},{0,1,1},{0,1,-1},{1,1,1},{1,1,-1},{1,-1,1},{1,-1,-1}};
    if(nc >= (1LL<<30)) DIE("too many classes");
    vector<u64> keys((size_t)NS*13);
    #pragma omp parallel for schedule(static)
    for(ll s=0;s<NS;s++){ ll sz=s%Bj, sy=(s/Bj)%Bj, sx=s/(Bj*Bj);
        for(int w=0;w<13;w++){ ll tx=(sx+E13[w][0]+Bj)%Bj, ty=(sy+E13[w][1]+Bj)%Bj, tz=(sz+E13[w][2]+Bj)%Bj; ll t=(tx*Bj+ty)*Bj+tz;
            keys[(size_t)s*13+w]=((u64)cls[s]<<34)|((u64)cls[t]<<4)|(u64)w; } }
#ifdef _OPENMP
    __gnu_parallel::sort(keys.begin(),keys.end());
#else
    sort(keys.begin(),keys.end());
#endif
    vector<pair<u64,ll>> combos; for(size_t i=0;i<keys.size();){ size_t k=i; while(k<keys.size() && keys[k]==keys[i]) k++; combos.push_back({keys[i],(ll)(k-i)}); i=k; }
    vector<u64>().swap(keys); R.ncomb=combos.size();
    vector<ll> cmin(combos.size()), ccnt(combos.size());
    #pragma omp parallel
    { vector<array<uint32_t,3>> A, Bv;
      #pragma omp for schedule(dynamic,64)
      for(size_t k=0;k<combos.size();k++){ u64 key=combos[k].first; int a=key>>34, b=(key>>4)&((1ULL<<30)-1), w=key&15; const int* e=E13[w];
        ll eo[3]; for(int c=0;c<3;c++) eo[c]=(ll)e[c]*side;
        int i0=-1; for(int c=0;c<3;c++) if(e[c]){ i0=c; break; }
        auto inSlabA=[&](const array<uint32_t,3>& p){ for(int c=0;c<3;c++){ if(e[c]==1 && (ll)p[c]<side-Rs) return false; if(e[c]==-1 && (ll)p[c]>=Rs) return false; } return true; };
        auto inSlabB=[&](const array<uint32_t,3>& q){ for(int c=0;c<3;c++){ if(e[c]==1 && (ll)q[c]>=Rs) return false; if(e[c]==-1 && (ll)q[c]<side-Rs) return false; } return true; };
        A.clear(); Bv.clear();
        for(auto& p: face[a][2*i0+(e[i0]==1?1:0)]) if(inSlabA(p)) A.push_back(p);
        for(auto& q: face[b][2*i0+(e[i0]==1?0:1)]) if(inSlabB(q)) Bv.push_back(q);
        int f=-1; for(int c=0;c<3;c++) if(!e[c]){ f=c; break; }
        ll best=LLONG_MAX, cnt=0;
        if(f<0){ for(auto& p:A) for(auto& q:Bv){ ll v=pm(p,q,eo); if(v<best){best=v;cnt=1;} else if(v==best) cnt++; } }
        else { sort(Bv.begin(),Bv.end(),[&](const array<uint32_t,3>& x,const array<uint32_t,3>& y){ return x[f]<y[f]; });
            for(auto& p:A){ ll lo=(ll)p[f]-Rs, hi=(ll)p[f]+Rs;
                auto it=lower_bound(Bv.begin(),Bv.end(),lo,[&](const array<uint32_t,3>& x, ll val){ return (ll)x[f]<val; });
                for(; it!=Bv.end() && (ll)(*it)[f]<=hi; ++it){ ll v=pm(p,*it,eo); if(v<best){best=v;cnt=1;} else if(v==best) cnt++; } } }
        cmin[k]=best; ccnt[k]=cnt; } }
    // combine
    for(ll id=0;id<nc;id++) if(wmin[id]<R.best) R.best=wmin[id];
    for(size_t k=0;k<combos.size();k++) if(cmin[k]<R.best) R.best=cmin[k];
    if(R.best>U) DIE("internal: best > U0");
    for(ll id=0;id<nc;id++) if(wmin[id]==R.best) R.cnt+=(double)wcnt[id]*cmult[id];
    for(size_t k=0;k<combos.size();k++) if(cmin[k]==R.best) R.cnt+=(double)ccnt[k]*combos[k].second;
    ll guard = trunc? side*side : (side+1)*(side+1);
    if(!(R.best<guard)) DIE("non-adjacent blocks not excluded");
    return R;
}

// ---------------------------------------------------------------- main
static void readPts(const char* fn, int& b, int& m, vector<VI>& P){
    FILE* f=fopen(fn,"r"); if(!f) DIE("open %s",fn); if(fscanf(f,"%d %d",&b,&m)!=2) DIE("hdr"); B=b; ll N=ipow(b,m); P.assign(N,VI(3*m));
    for(ll i=0;i<N;i++) for(int c=0;c<3;c++){ ll v; if(fscanf(f,"%lld",&v)!=1) DIE("short pts"); if(v<0||v>=N) DIE("coord range"); for(int d=m-1;d>=0;d--){ P[i][c*m+d]=v%b; v/=b; } }
    fclose(f);
}
int main(int argc,char** argv){
    if(argc<3){ fprintf(stderr,"see header\n"); return 1; }
    string mode=argv[1];
    if(mode=="frompts"){
        int b,m; vector<VI> P; readPts(argv[2],b,m,P); ll N=P.size(); int D3=3*m;
        // distinct points
        vector<VI> S=P; sort(S.begin(),S.end()); for(ll i=1;i<N;i++) if(S[i]==S[i-1]) DIE("duplicate points");
        Net n; n.M=m; n.sh=P[0]; vector<VI> E; vector<int> pv;
        for(ll i=1;i<N;i++){ VI d(D3); for(int t=0;t<D3;t++) d[t]=md(P[i][t]-P[0][t]);
            for(size_t k=0;k<E.size();k++){ int f=d[pv[k]]; if(f) for(int t=0;t<D3;t++) d[t]=md(d[t]-f*E[k][t]); }
            int p=-1; for(int t=0;t<D3;t++) if(d[t]){p=t;break;}
            if(p<0) continue;
            if((int)E.size()==m) DIE("NOT AFFINE: difference outside an m-dim space (point %lld)",i);
            int iv=inv(d[p]); for(auto& x:d) x=md(x*iv); for(size_t k=0;k<E.size();k++){ int f=E[k][p]; if(f) for(int t=0;t<D3;t++) E[k][t]=md(E[k][t]-f*d[t]); }
            E.push_back(d); pv.push_back(p); }
        if((int)E.size()!=m) DIE("rank %zu != m",E.size());
        n.g=E; writeNet(n,argv[3]);
        printf("frompts %s: b=%d m=%d N=%lld distinct, all differences in an %d-dim F_b space -> affine digital net (shift %s)\n",argv[2],b,m,N,m,
               all_of(n.sh.begin(),n.sh.end(),[](int x){return x==0;})?"0":"nonzero"); return 0; }
    Net n=readNet(argv[2]); initPack(); int M=n.M;
    bool sh0=all_of(n.sh.begin(),n.sh.end(),[](int x){return x==0;});
    if(mode=="info"){ int bad[3]; bool t0=isT0(n,bad); printf("b=%d M=%d t0=%d%s shift=%s\n",B,M,t0?1:0, t0?"":(" FAIL at ("+to_string(bad[0])+","+to_string(bad[1])+","+to_string(bad[2])+")").c_str(), sh0?"zero":"nonzero"); return t0?0:2; }
    if(mode=="tpexport"){ printf("%d %d 3\n",B,M); for(int c=0;c<3;c++) for(int d=0;d<M;d++){ for(int i=0;i<M;i++) printf("%d ",n.g[i][c*M+d]); printf("\n"); } return 0; }
    if(mode=="mind" || mode=="vstar"){
        bool trunc = mode=="vstar"; auto t0=chrono::steady_clock::now();
        vector<u64> P[3]; materialise(n,P); int e=M;
        if(trunc){ int H=M/2; u64 Wd=ipow(B,M-H); for(int c=0;c<3;c++) for(auto& x:P[c]) x/=Wd; e=H; }
        pair<ll,ll> r={-1,-1}; for(int g=min(M/3,e); g>=0; g--){ r=gridMin(P,e,trunc,g); if(r.first>=0) break; }
        double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
        if(!trunc) printf("mind M=%d N=%lld d2=%lld c=%.6f pairs=%lld shift=%s [%.2fs]\n",M,(ll)P[0].size(),r.first,sqrt((double)r.first)*pow((double)B,-2.0*M/3),r.second,sh0?"0":"nz",el);
        else { int H=M/2; printf("vstar L=%d H=%d v*=%lld gsep=%.6f pairs=%lld shift=%s [%.2fs]\n",M,H,r.first,pow((double)B,M-H)*sqrt((double)r.first)*pow((double)B,-2.0*M/3),r.second,sh0?"0":"nz",el); }
        return 0; }
    if(mode=="block"){
        bool trunc = string(argv[3])=="trunc"; int j=atoi(argv[4]); auto t0=chrono::steady_clock::now();
        BRes r=blockEval(n,trunc,j); double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
        int H=M/2;
        if(trunc) printf("block-trunc L=%d j=%d v*=%lld gsep=%.6f pairs=%.0f classes=%lld combos=%lld U0=%lld shift=%s [%.2fs]\n",M,j,r.best,pow((double)B,M-H)*sqrt((double)r.best)*pow((double)B,-2.0*M/3),r.cnt,r.ncls,r.ncomb,r.U0,sh0?"0":"nz",el);
        else printf("block-exact M=%d j=%d d2=%lld c=%.6f pairs=%.0f classes=%lld combos=%lld U0=%lld shift=%s [%.2fs]\n",M,j,r.best,sqrt((double)r.best)*pow((double)B,-2.0*M/3),r.cnt,r.ncls,r.ncomb,r.U0,sh0?"0":"nz",el);
        return 0; }
    if(mode=="lift"){
        int doff=atoi(argv[3]); string lm=argv[4]; mt19937_64 rng(atoll(argv[5])); Net q=liftOnce(n, M/2-doff, lm=="rand"? &rng : nullptr); writeNet(q,argv[6]);
        int bad[3]; bool t0=isT0(q,bad); printf("lift M=%d -> %d D=%d (%s) t0=%d\n",M,q.M,M/2-doff,lm.c_str(),t0?1:0); return t0?0:2; }
    if(mode=="freeze"){ // freeze NET_L NET_m : every sigma-block of P_m carries exactly the multiset of top-floor(L/2)-digit triples of P_L
        Net m2=readNet(argv[3]); int L=M, Mm=m2.M; if((Mm-L)%3) DIE("levels not congruent"); int j=(Mm-L)/3, H=L/2;
        vector<u64> P[3],Q[3]; materialise(n,P); materialise(m2,Q); ll NL=P[0].size(), NM=Q[0].size();
        u64 KH=ipow(B,H); vector<u64> base(NL); for(ll i=0;i<NL;i++){ u64 k=0; for(int c=0;c<3;c++) k=k*KH+P[c][i]/ipow(B,L-H); base[i]=k; } sort(base.begin(),base.end());
        u64 Bj=ipow(B,j); vector<pair<u64,u64>> q(NM); u64 sdiv=ipow(B,Mm-j), cdiv=ipow(B,Mm-j-H);
        for(ll i=0;i<NM;i++){ u64 s=0,k=0; for(int c=0;c<3;c++){ s=s*Bj+Q[c][i]/sdiv; k=k*KH+(Q[c][i]%sdiv)/cdiv; } q[i]={s,k}; }
        sort(q.begin(),q.end()); ll bad=0, nblk=0;
        for(ll i=0;i<NM;){ ll k=i; while(k<NM && q[k].first==q[i].first) k++; nblk++; if(k-i!=NL) bad++; else for(ll t=0;t<NL;t++) if(q[i+t].second!=base[t]){ bad++; break; } i=k; }
        printf("freeze L=%d -> m=%d: %lld sigma-blocks (expected %lld), %lld mismatching\n",L,Mm,nblk,(ll)ipow(B,3*j),bad); return bad||nblk!=ipow(B,3*j)?2:0; }
    if(mode=="ushift" || mode=="uallc"){
        // min over ALL digital shifts. ushift: certificate v* of P (+) tau over all shifts of the top H=floor(M/2) digits
        // (only the coarse digits matter); uallc: exact c of P (+) tau over all shifts tau in F_b^{3M}.
        // P (+) tau depends only on tau modulo the image of the (coarse) generator map: enumerate tau supported on the
        // non-pivot coordinates of that image (each class exactly once).
        bool tr = mode=="ushift"; int H = tr? M/2 : M; int nd=3*H;
        vector<VI> img; for(int i=0;i<M;i++){ VI v(nd); for(int c=0;c<3;c++) for(int d=0;d<H;d++) v[c*H+d]=n.g[i][c*M+d]; img.push_back(v); }
        vector<VI> E=img; vector<int> piv; { int r=0; for(int c=0;c<nd && r<(int)E.size();c++){ int p=-1; for(int i=r;i<(int)E.size();i++) if(E[i][c]){p=i;break;} if(p<0) continue;
            swap(E[p],E[r]); int iv=inv(E[r][c]); for(auto& x:E[r]) x=md(x*iv); for(int i=0;i<(int)E.size();i++) if(i!=r&&E[i][c]){ int f=E[i][c]; for(int t=0;t<nd;t++) E[i][t]=md(E[i][t]-f*E[r][t]); } piv.push_back(c); r++; } }
        int rk=piv.size(); vector<int> freec; { vector<char> isp(nd,0); for(int c:piv) isp[c]=1; for(int c=0;c<nd;c++) if(!isp[c]) freec.push_back(c); }
        if(tr && rk<M){ printf("ushift: coarse map rank %d < %d -> some pair shares a coarse cell for EVERY shift: v*_unif=0\n",rk,M); return 0; }
        ll NC=ipow(B,freec.size()); ll N=ipow(B,M);
        // linear part (shift 0) packed per coordinate on H digits
        Net lin=n; for(auto& x:lin.sh) x=0; vector<u64> base[3]; for(int c=0;c<3;c++) base[c].resize(N);
        { vector<array<u64,3>> col(M); for(int i=0;i<M;i++) for(int c=0;c<3;c++){ col[i][c]=packDigits(&n.g[i][c*M],H); }
          u64 cur[3]={0,0,0}; VI v(M,0); for(ll idx=0;idx<N;idx++){ for(int c=0;c<3;c++) base[c][idx]=cur[c];
            for(int i=0;i<M;i++){ v[i]++; for(int c=0;c<3;c++) cur[c]=padd(cur[c],col[i][c]); if(v[i]<B) break; v[i]=0; } } }
        // witness shift class value too
        ll gbest=LLONG_MAX; ll gcls=-1; ll wit=-1;
        auto evalTau=[&](const VI& tau)->ll{ u64 tp[3]; VI dg(H); for(int c=0;c<3;c++){ for(int d=0;d<H;d++) dg[d]=tau[c*H+d]; tp[c]=packDigits(dg.data(),H); }
            vector<u64> P[3]; for(int c=0;c<3;c++){ P[c].resize(N); for(ll i=0;i<N;i++) P[c][i]=pval(padd(base[c][i],tp[c])); }
            pair<ll,ll> r={-1,-1}; for(int g=min(M/3,H); g>=0; g--){ r=gridMin(P,H,tr,g); if(r.first>=0) break; } return r.first; };
        { VI tau(nd); for(int c=0;c<3;c++) for(int d=0;d<H;d++) tau[c*H+d]=n.sh[c*M+d]; wit=evalTau(tau); }
#ifdef _OPENMP
        omp_set_max_active_levels(1);
#endif
        vector<ll> res(NC);
        #pragma omp parallel for schedule(dynamic,4)
        for(ll k=0;k<NC;k++){ VI tau(nd,0); ll x=k; for(size_t t=0;t<freec.size();t++){ tau[freec[t]]=x%B; x/=B; } res[k]=evalTau(tau); }
        map<ll,ll> hist; for(ll k=0;k<NC;k++){ hist[res[k]]++; if(res[k]<gbest){gbest=res[k];gcls=k;} }
        if(tr){ printf("ushift L=%d H=%d: %lld shift classes; witness v*=%lld; min over ALL shifts v*_unif=%lld gsep_unif=%.6f; hist:",M,H,NC,wit,gbest,pow((double)B,M-H)*sqrt((double)gbest)*pow((double)B,-2.0*M/3)); }
        else { printf("uallc M=%d: %lld shift classes; witness d2=%lld; min over ALL shifts d2=%lld c_unif=%.6f; hist(first 6):",M,NC,wit,gbest,sqrt((double)gbest)*pow((double)B,-2.0*M/3)); }
        int cnt=0; for(auto& kv:hist){ if(!tr && cnt++>=6) break; printf(" %lld:%lld",kv.first,kv.second); } printf("\n"); return 0; }
    if(mode=="setshift"){ string how=argv[3]; mt19937_64 rng(atoll(argv[4])); for(auto& x:n.sh) x = how=="zero"?0:(int)(rng()%B); writeNet(n,argv[5]); return 0; }
    if(mode=="cmpsets"){ Net m2=readNet(argv[3]); if(m2.M!=M) DIE("M differs"); vector<u64> P[3],Q[3]; materialise(n,P); materialise(m2,Q);
        vector<array<u64,3>> a(P[0].size()), b(Q[0].size()); for(size_t i=0;i<a.size();i++){ a[i]={P[0][i],P[1][i],P[2][i]}; b[i]={Q[0][i],Q[1][i],Q[2][i]}; }
        sort(a.begin(),a.end()); sort(b.begin(),b.end()); printf("cmpsets: %s\n", a==b?"SAME point set":"DIFFERENT"); return a==b?0:2; }
    DIE("unknown mode");
}
