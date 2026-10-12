// r1_gsep.cpp -- R1: fast EXACT evaluation of the G3 certificate gsep_L (and of exact c_L) at large levels L of a
// deep-shift-lift chain WITHOUT materialising the level-L net, plus SA over seed + lift freedom with gsep_L as objective.
//
// Structure used (all digital, exact): after j lifts from a level-l0 net P, the level-L net (L=l0+3j) is
//   { sigma(u)*side + [ (p (+) f(u)) , jit(u) ] : u in GF(b)^{3j}, p in P }
// where u = coefficients of the 3j lift generators, sigma(u) = top j digits (a bijection u<->sigma), f(u) = digitwise
// (GF(b)) shift of the embedded l0 block digits, jit(u) = low 2j digits (independent of p). This holds because the first
// l0 generators of the level-L net are P's generators embedded at block positions [j, j+l0) (checked at run time).
// Hence pairs inside one sigma-block depend only on f(u); pairs between adjacent blocks only on (f(u), f(u'), offset).
// We dedup these combos and scan each once with a cell grid.  Two metrics:
//   trunc (the certificate): keep the top T=floor(L/2) digits, v = sum_i max(0,|dk_i|_tor-1)^2 (integer),
//                            gsep_L = b^(L-T) * sqrt(v*) * b^(-2L/3)     (== g3audit_check's definition)
//   exact: d2 = sum_i |dx_i|_tor^2,   c_L = sqrt(d2*) * b^(-2L/3)
// Family floor for all m' >= m0 in the residue class: min(c_{m0}, c_{m0+3}, ..., c_{L-3}, gsep_L), valid when every lift
// at level >= L uses D = floor(M/2) (the canonical continuation does).  Lifts BEFORE L are free (any deep-shift lift).
//
// usage:
//   r1_gsep eval SEED PARAMS|- NL [maxpts_log2=17]      c_l and gsep_l for every level of the chain (NL lifts)
//   r1_gsep mat  SEED PARAMS|- NL OUT                   write level m+3NL net (for permnet_eval / g3audit_check)
//   r1_gsep sa   SEED PARAMS|- NL Lcert secs rng OUT [dOffMax=0] [cLevelsMax=99] [maxpts_log2=15]
//                objective = min(c_l for l < Lcert (levels <= cLevelsMax), gsep_Lcert) ; Lcert = m+3k <= m+3NL
//                state: seed (linear nested scramble row ops + shift) + per-lift params (nullspace coef, b3 RHS, dOff)
// PARAMS file: NL, then per lift: dOff, then for s=0..2: len rhs..., then for s=0..2: len coef...
// build: g++-16 -O3 -std=c++17 -o bin/r1_gsep r1_gsep.cpp
#define G3_NO_MAIN
#include "g3_lift.cpp"
#include <chrono>
#include <unordered_map>
#include <map>
#include <array>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;

static ll PB[70];
static vector<uint16_t> ADD6;
static void initB(){ PB[0]=1; for(int i=1;i<70;i++) PB[i]= (PB[i-1] > (ll)4e18/B)? PB[i-1] : PB[i-1]*B;
    if(B==3 && ADD6.empty()){ ADD6.resize(729*729); for(int x=0;x<729;x++) for(int y=0;y<729;y++){ int r=0,m=1,a=x,b=y; for(int k=0;k<6;k++){ r+=((a%3+b%3)%3)*m; a/=3;b/=3;m*=3;} ADD6[x*729+y]=r; } } }
static inline ll dadd(ll x, ll y){ if(B==2) return x^y; ll r=0,m=1; while(x||y){ r+=(ll)ADD6[(x%729)*729+(y%729)]*m; x/=729; y/=729; m*=729; } return r; }

struct LiftParam { int dOff=0; VI rhs[3]; VI coef[3]; };

static Net doLift(const Net& n, const LiftParam* lp){
    int M=n.M; int D=M/2-(lp?lp->dOff:0); if(D<0) D=0; int nd=M-D;
    vector<VI> Ls[3]={lambdas(n,1,2), lambdas(n,0,1), lambdas(n,0,2)};
    VI u[3];
    for(int s=0;s<3;s++){
        VI r(M,1); if(lp && B>2) for(int e=0;e<M && e<(int)lp->rhs[s].size();e++) r[e]=1+(lp->rhs[s][e]%(B-1));
        Sys S=deep_sys(Ls[s],M,D,r); u[s]=S.part;
        if(lp) for(size_t k=0;k<S.nulls.size() && k<lp->coef[s].size();k++){ int c=lp->coef[s][k]%B; if(c) for(size_t t=0;t<u[s].size();t++) u[s][t]=md(u[s][t]+c*S.nulls[k][t]); }
    }
    VI &uyz=u[0], &uxy=u[1], &uxz=u[2]; VI sA(3*M,0), sB(3*M,0);
    for(int j=0;j<nd;j++){ sA[1*M+D+j]=uyz[j]; sA[2*M+D+j]=uyz[nd+j]; sB[0*M+D+j]=uxy[j]; sB[1*M+D+j]=uxy[nd+j]; }
    for(int j=0;j<nd;j++){ sA[0*M+D+j]=md(sB[0*M+D+j]-uxz[j]); sB[2*M+D+j]=md(sA[2*M+D+j]+uxz[nd+j]); }
    return lift(n,sA,sB);
}

// ------------------------------------------------------------------ block evaluator
struct Grid { int n; vector<ll> x,y,z; vector<int> st; ll G; };
struct BEres { ll vmin=LLONG_MAX; double cnt=0; bool ok=false; double val=0; long nf=0, ncomb=0; };

static BEres blockEval(const Net& Ln, int l0, bool trunc){
    int L=Ln.M; int j=(L-l0)/3; BEres R;
    if(j<1 || l0+3*j!=L){ fprintf(stderr,"blockEval: bad l0\n"); exit(5); }
    for(int i=0;i<l0;i++) for(int c=0;c<3;c++) for(int d=0;d<L;d++) if((d<j||d>=j+l0) && Ln.gens[i][c*L+d]){ fprintf(stderr,"blockEval: gen %d not block-supported\n",i); exit(6);}
    int T=L/2; int nb = trunc? T-j : l0;          // block digits kept
    if(trunc && (nb<1||nb>l0)){ fprintf(stderr,"blockEval: t=%d out of range\n",nb); exit(7); }
    int se = trunc? T-j : L-j;                      // side exponent
    ll side=PB[se], Ktor=PB[j]*side, ms = trunc?1:PB[2*j];
    auto blockval=[&](const VI& g,int c){ ll v=0; for(int d=0;d<nb;d++) v=v*B+g[c*L+j+d]; return v; };
    // P0 (linear part) block values
    ll N0=PB[l0]; vector<ll> P0[3]; for(int c=0;c<3;c++) P0[c].resize(N0);
    { ll cur[3]={0,0,0}; vector<int> v(l0,0); vector<array<ll,3>> gv(l0); for(int i=0;i<l0;i++) for(int c=0;c<3;c++) gv[i][c]=blockval(Ln.gens[i],c);
      for(ll idx=0; idx<N0; idx++){ for(int c=0;c<3;c++) P0[c][idx]=cur[c];
        for(int i=0;i<l0;i++){ v[i]++; for(int c=0;c<3;c++) cur[c]=dadd(cur[c],gv[i][c]); if(v[i]<B) break; v[i]=0; } } }
    // blocks
    ll NU=PB[3*j]; ll Bj=PB[j];
    vector<ll> sig(NU), jit((size_t)NU*3); vector<int> fid(NU); vector<array<ll,3>> fvals; unordered_map<ull,int> fmap;
    vector<ll> sinv(NU,-1);
    { VI cur=Ln.shift; vector<int> v(3*j,0);
      for(ll u=0; u<NU; u++){
        ll s3[3], f3[3];
        for(int c=0;c<3;c++){ ll s=0; for(int d=0;d<j;d++) s=s*B+cur[c*L+d]; s3[c]=s; f3[c]=blockval(cur,c);
            ll jt=0; for(int d=j+l0; d<L; d++) jt=jt*B+cur[c*L+d]; jit[u*3+c]=jt; }
        ll sk=(s3[0]*Bj+s3[1])*Bj+s3[2]; sig[u]=sk; if(sinv[sk]>=0){ fprintf(stderr,"sigma not bijective\n"); exit(8);} sinv[sk]=u;
        ull key=(((ull)f3[0]*(ull)PB[nb])+(ull)f3[1])*(ull)PB[nb]+(ull)f3[2];
        auto it=fmap.find(key); if(it==fmap.end()){ int id=fvals.size(); fmap[key]=id; fvals.push_back({f3[0],f3[1],f3[2]}); fid[u]=id; } else fid[u]=it->second;
        for(int i=0;i<3*j;i++){ v[i]++; const VI& g=Ln.gens[l0+i]; for(int t=0;t<3*L;t++) cur[t]=md(cur[t]+g[t]); if(v[i]<B) break; v[i]=0; }
      } }
    int nf=fvals.size(); R.nf=nf;
    vector<double> fmult(nf,0); for(ll u=0;u<NU;u++) fmult[fid[u]]+=1;
    // cross combos
    static const int W13[13][3]={{1,0,0},{0,1,0},{0,0,1},{1,1,0},{1,-1,0},{1,0,1},{1,0,-1},{0,1,1},{0,1,-1},{1,1,1},{1,1,-1},{1,-1,1},{1,-1,-1}};
    struct CK { int a,b; ll o[3]; bool operator<(const CK& e) const { if(a!=e.a) return a<e.a; if(b!=e.b) return b<e.b; for(int c=0;c<3;c++) if(o[c]!=e.o[c]) return o[c]<e.o[c]; return false; } };
    vector<pair<CK,double>> combos;
    { struct PH { size_t operator()(const pair<ull,ull>& p) const { return p.first*0x9E3779B97F4A7C15ULL ^ (p.second+0x632BE59BD9B4E019ULL)*0xC2B2AE3D27D4EB4FULL; } };
      bool dense = trunc && (ll)nf*nf*13 <= 8000000LL;
      vector<double> dc; if(dense) dc.assign((size_t)nf*nf*13,0.0);
      unordered_map<pair<ull,ull>,double,PH> hm; if(!dense) hm.reserve(NU*4);
      for(ll u=0;u<NU;u++){ ll sk=sig[u]; ll s3[3]={sk/(Bj*Bj), (sk/Bj)%Bj, sk%Bj};
        for(int w=0;w<13;w++){ ll t3[3]; for(int c=0;c<3;c++) t3[c]=((s3[c]+W13[w][c])%Bj+Bj)%Bj;
            ll u2=sinv[(t3[0]*Bj+t3[1])*Bj+t3[2]];
            if(dense){ dc[((size_t)fid[u]*nf+fid[u2])*13+w]+=1; continue; }
            ull sec=w; for(int c=0;c<3;c++){ ll jd= trunc?0:(jit[u2*3+c]-jit[u*3+c]); if(jd<=-(1LL<<17)||jd>=(1LL<<17)){ fprintf(stderr,"jit range\n"); exit(9);} sec|=(ull)(jd+(1LL<<18))<<(4+19*c); }
            hm[{((ull)fid[u]<<32)|(ull)fid[u2], sec}]+=1; } }
      if(dense){ for(int a=0;a<nf;a++) for(int b2=0;b2<nf;b2++) for(int w=0;w<13;w++){ double m2=dc[((size_t)a*nf+b2)*13+w]; if(m2>0){ CK k; k.a=a; k.b=b2; for(int c=0;c<3;c++) k.o[c]=W13[w][c]*side; combos.push_back({k,m2}); } } }
      else for(auto& kv:hm){ CK k; k.a=kv.first.first>>32; k.b=kv.first.first&0xffffffffULL; int w=kv.first.second&15; for(int c=0;c<3;c++){ ll jd=(ll)((kv.first.second>>(4+19*c))&((1ULL<<19)-1))-(1LL<<18); k.o[c]=W13[w][c]*side+jd; } combos.push_back({k,kv.second}); }
    }
    R.ncomb=combos.size();
    // grids
    double est = 0.75*pow((double)B, 2.0*L/3.0) / (trunc? (double)PB[L-T] : 1.0) + 3;
    int ck=0; while((double)PB[ck] < est && ck<se) ck++;   // cell side C=b^ck in stored-coordinate units (stored = (p(+)f)*ms in [0,side))
    for(int attempt=0; attempt<6; attempt++){
        ll C = PB[ck]; if(C>side) C=side; ll G=side/C; if(G<1) G=1;
        if(G*G*G > 64LL*N0+1000){ ck++; continue; }
        vector<Grid> grids(nf); vector<char> built(nf,0);
        auto build=[&](int id){ Grid& g=grids[id]; if(built[id]) return; built[id]=1; g.n=N0; g.G=G;
            vector<ll> X(N0),Y(N0),Z(N0); for(ll i=0;i<N0;i++){ X[i]=dadd(P0[0][i],fvals[id][0])*ms; Y[i]=dadd(P0[1][i],fvals[id][1])*ms; Z[i]=dadd(P0[2][i],fvals[id][2])*ms; }
            ll G3=G*G*G; g.st.assign(G3+1,0); auto cell=[&](ll i){ ll cx=X[i]/C, cy=Y[i]/C, cz=Z[i]/C; if(cx>=G)cx=G-1; if(cy>=G)cy=G-1; if(cz>=G)cz=G-1; return (cx*G+cy)*G+cz; };
            for(ll i=0;i<N0;i++) g.st[cell(i)+1]++; for(ll c=0;c<G3;c++) g.st[c+1]+=g.st[c];
            vector<int> pos(g.st.begin(),g.st.end()-1); g.x.resize(N0); g.y.resize(N0); g.z.resize(N0);
            for(ll i=0;i<N0;i++){ int p=pos[cell(i)]++; g.x[p]=X[i]; g.y[p]=Y[i]; g.z[p]=Z[i]; } };
        auto gt=[&](ll d)->ll{ if(d<0) d=-d; ll e=Ktor-d; if(e<d) d=e; if(trunc){ d-=1; if(d<0) d=0; } return d*d; };
        ll best=LLONG_MAX; double cnt=0;
        auto consider=[&](ll v,double mult){ if(v<best){best=v;cnt=mult;} else if(v==best) cnt+=mult; };
        // within
        for(int id=0;id<nf;id++){ build(id); Grid& g=grids[id];
            for(ll cx=0;cx<G;cx++) for(ll cy=0;cy<G;cy++) for(ll cz=0;cz<G;cz++){ ll c0=(cx*G+cy)*G+cz;
                for(int dx=-1;dx<=1;dx++){ ll nx=cx+dx; if(nx<0||nx>=G) continue; for(int dy=-1;dy<=1;dy++){ ll ny=cy+dy; if(ny<0||ny>=G) continue; for(int dz=-1;dz<=1;dz++){ ll nz=cz+dz; if(nz<0||nz>=G) continue;
                    ll c1=(nx*G+ny)*G+nz; if(c1<c0) continue;
                    for(int a=g.st[c0];a<g.st[c0+1];a++) for(int bq=(c1==c0?a+1:g.st[c1]); bq<g.st[c1+1]; bq++){
                        ll v=gt(g.x[a]-g.x[bq]); if(v>best) continue; v+=gt(g.y[a]-g.y[bq]); if(v>best) continue; v+=gt(g.z[a]-g.z[bq]); consider(v,fmult[id]); } } } } } }
        // cross: pairs (p in A-block, q in B-block), Delta = q + o - p
        for(auto& kv: combos){ const CK& k=kv.first; double mult=kv.second; build(k.a); build(k.b); Grid& A=grids[k.a]; Grid& Bg=grids[k.b];
            // B cells whose points can land within [-C, side+C) after +o
            ll lo[3],hi[3]; for(int c=0;c<3;c++){ ll l=-C-k.o[c], h=side+C-k.o[c]; if(l<0) l=0; if(h>side) h=side; if(l>=h){ lo[c]=1; hi[c]=0; } else { lo[c]=l/C; hi[c]=min(G-1,(h-1)/C); } }
            if(lo[0]>hi[0]||lo[1]>hi[1]||lo[2]>hi[2]) continue;
            for(ll bx=lo[0];bx<=hi[0];bx++) for(ll by=lo[1];by<=hi[1];by++) for(ll bz=lo[2];bz<=hi[2];bz++){ ll cb=(bx*G+by)*G+bz;
                for(int q=Bg.st[cb]; q<Bg.st[cb+1]; q++){ ll qx=Bg.x[q]+k.o[0], qy=Bg.y[q]+k.o[1], qz=Bg.z[q]+k.o[2];
                    if(qx< -C||qx>=side+C||qy< -C||qy>=side+C||qz< -C||qz>=side+C) continue;
                    auto fl=[&](ll a){ ll r= a>=0? a/C : -((-a+C-1)/C); if(r>G) r=G; if(r<-1) r=-1; return r; };
                    ll cx=fl(qx), cy=fl(qy), cz=fl(qz);
                    for(ll ax=max(0LL,cx-1); ax<=min(G-1,cx+1); ax++) for(ll ay=max(0LL,cy-1); ay<=min(G-1,cy+1); ay++) for(ll az=max(0LL,cz-1); az<=min(G-1,cz+1); az++){
                        ll ca=(ax*G+ay)*G+az;
                        for(int p=A.st[ca]; p<A.st[ca+1]; p++){ ll v=gt(qx-A.x[p]); if(v>best) continue; v+=gt(qy-A.y[p]); if(v>best) continue; v+=gt(qz-A.z[p]); consider(v,mult); } } } } }
        // validity: every pair with value <= best has all |Delta_i| < C (scanned), and non-adjacent blocks irrelevant
        double need = trunc? sqrt((double)best)+1.0 : sqrt((double)best);
        if(best<LLONG_MAX && need < (double)C - 1e-9 && need < (double)side - 1e-9){
            R.vmin=best; R.cnt=cnt; R.ok=true;
            double sc = trunc? (double)PB[L-T] : 1.0;
            R.val = sc*sqrt((double)best)*pow((double)B,-2.0*L/3.0);
            return R; }
        ck++; if(PB[ck]>side){ break; }
    }
    R.ok=false; return R;
}

// ------------------------------------------------------------------ chain + params
static bool readParams(const char* fn, vector<LiftParam>& P){
    if(string(fn)=="-") return false; FILE* f=fopen(fn,"r"); if(!f){ perror(fn); exit(1);} int nl; if(fscanf(f,"%d",&nl)!=1) exit(1); P.resize(nl);
    for(int k=0;k<nl;k++){ if(fscanf(f,"%d",&P[k].dOff)!=1) exit(1); for(int s=0;s<3;s++){ int n; if(fscanf(f,"%d",&n)!=1) exit(1); P[k].rhs[s].resize(n); for(int i=0;i<n;i++) if(fscanf(f,"%d",&P[k].rhs[s][i])!=1) exit(1);}
        for(int s=0;s<3;s++){ int n; if(fscanf(f,"%d",&n)!=1) exit(1); P[k].coef[s].resize(n); for(int i=0;i<n;i++) if(fscanf(f,"%d",&P[k].coef[s][i])!=1) exit(1);} }
    fclose(f); return true; }
static void writeParams(const string& fn, const vector<LiftParam>& P){ FILE* f=fopen(fn.c_str(),"w"); fprintf(f,"%zu\n",P.size());
    for(auto& p:P){ fprintf(f,"%d\n",p.dOff); for(int s=0;s<3;s++){ fprintf(f,"%zu",p.rhs[s].size()); for(int v:p.rhs[s]) fprintf(f," %d",v); fprintf(f,"\n"); }
        for(int s=0;s<3;s++){ fprintf(f,"%zu",p.coef[s].size()); for(int v:p.coef[s]) fprintf(f," %d",v); fprintf(f,"\n"); } } fclose(f); }
static vector<Net> chain(const Net& seed, const vector<LiftParam>& P, int nl){
    vector<Net> v; v.push_back(seed); for(int k=0;k<nl;k++) v.push_back(doLift(v.back(), k<(int)P.size()? &P[k] : nullptr)); return v; }
static int chooseL0(int m, int l, int maxlog2){ // largest l0 = m+3k <= l with b^l0 <= 2^maxlog2 and (l-l0)>=3 ; else m
    int best=m; for(int l0=m; l0<l; l0+=3){ if(pow((double)B,l0) <= pow(2.0,maxlog2)) best=l0; } return best; }
static double seedC(const Net& n){ vector<uint32_t> X,Y,Z; points(n,X,Y,Z); long long d2=mind2(X,Y,Z,(long long)X.size()); return sqrt((double)d2)*pow((double)B,-2.0*n.M/3.0); }
static BEres levelEval(const vector<Net>& ch, int k, bool trunc, int maxlog2){ // k = lift index (level m+3k)
    int m=ch[0].M; int l=m+3*k;
    if(k==0){ BEres r; if(!trunc){ r.val=seedC(ch[0]); r.ok=true; r.cnt=1; return r; }
        // trunc at seed level: materialise
        vector<uint32_t> X,Y,Z; points(ch[0],X,Y,Z); long long d2=mind2(X,Y,Z,(long long)X.size()); r.val=gsep(X,Y,Z,(long long)X.size(),m,m/2,d2); r.ok=true; r.cnt=1; return r; }
    int l0=chooseL0(m,l,maxlog2); return blockEval(ch[k], l0, trunc); }

int main(int argc,char** argv){
    if(argc<5){ fprintf(stderr,"see header\n"); return 1; }
    string mode=argv[1]; Net seed=load(argv[2]); initB(); vector<LiftParam> P; readParams(argv[3],P); int NL=atoi(argv[4]);
    int m=seed.M;
    if(mode=="eval"){ int mx=argc>5?atoi(argv[5]):17; auto ch=chain(seed,P,NL);
        double minc=1e9;
        for(int k=0;k<=NL;k++){ auto t0=chrono::steady_clock::now();
            BEres c=levelEval(ch,k,false,mx), g=levelEval(ch,k,true,mx);
            double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
            printf("b=%d m=%d c=%.5f %s gsep=%.5f (v*=%lld, #min=%.0f) %s  floor_if_cert_here=%.5f  [nf=%ld comb=%ld %.2fs]\n",B,m+3*k,c.val,c.ok?"":"(INVALID)",g.val,g.vmin,g.cnt,g.ok?"":"(INVALID)",min(minc,g.val),g.nf,g.ncomb,el); fflush(stdout);
            minc=min(minc,c.val); }
        return 0; }
    if(mode=="time"){ int l0=atoi(argv[5]); int tr=atoi(argv[6]); auto ch=chain(seed,P,NL); auto t0=chrono::steady_clock::now(); BEres r; int rep=atoi(argv[7]);
        for(int i=0;i<rep;i++) r=blockEval(ch[NL],l0,tr); double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
        printf("L=%d l0=%d trunc=%d val=%.5f v=%lld nf=%ld comb=%ld  %.4fs/eval\n",ch[NL].M,l0,tr,r.val,r.vmin,r.nf,r.ncomb,el/rep); return 0; }
    if(mode=="mat"){ auto ch=chain(seed,P,NL); save(ch[NL],argv[5]); return 0; }
    if(mode=="sa"){
        int kc=(atoi(argv[5])-m)/3; double secs=atof(argv[6]); mt19937_64 rng(atoll(argv[7])); string out=argv[8];
        int dOffMax=argc>9?atoi(argv[9]):0; int cmax=argc>10?atoi(argv[10]):99; int mx=argc>11?atoi(argv[11]):15;
        if(kc<1||kc>NL){ fprintf(stderr,"Lcert must be m+3k, 1<=k<=NL\n"); return 1; }
        if((int)P.size()<kc) P.resize(kc);
        auto obj=[&](const Net& s,const vector<LiftParam>& pp,double* parts)->double{
            auto ch=chain(s,pp,kc); double F=1e9, cntF=1; int which=-1;
            for(int k=0;k<kc;k++){ if(m+3*k>cmax) break; BEres c=levelEval(ch,k,false,mx); if(!c.ok) return -1; if(parts) parts[k]=c.val; if(c.val<F){F=c.val;cntF=c.cnt;which=k;} }
            BEres g=levelEval(ch,kc,true,mx); if(!g.ok) return -1; if(parts) parts[kc]=g.val; if(g.val<F){F=g.val;cntF=g.cnt;which=kc;}
            return F - 1e-4*log(1.0+cntF); };
        double parts[40];
        double f=obj(seed,P,nullptr), best=f; Net bs=seed; vector<LiftParam> bp=P; Net s=seed;
        auto t0=chrono::steady_clock::now(); long it=0; double T0=0.01;
        while(true){ double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count(); if(el>secs) break; it++;
            double T=T0*(1-el/secs)+2e-4; Net t=s; vector<LiftParam> tp=P; int kind=rng()%10;
            if(kind==0){ int p=rng()%(3*m); t.shift[p]=md(t.shift[p]+1+rng()%(B-1)); }
            else if(kind<=6){ int c=rng()%3; int jj=1+rng()%(m-1); int kk=rng()%jj; int a=1+rng()%(B-1);
                for(auto& g:t.gens) g[c*m+jj]=md(g[c*m+jj]+a*g[c*m+kk]); t.shift[c*m+jj]=md(t.shift[c*m+jj]+a*t.shift[c*m+kk]); }
            else { int k=rng()%kc; LiftParam& lp=tp[k]; int Mk=m+3*k; int r=rng()%4;
                if(r==0 && dOffMax>0) lp.dOff=rng()%(dOffMax+1);
                else if(r==1 && B>2){ int s3=rng()%3; if((int)lp.rhs[s3].size()<Mk) lp.rhs[s3].resize(Mk,0); lp.rhs[s3][rng()%Mk]^=1; }
                else { int s3=rng()%3; int len=2*Mk; if((int)lp.coef[s3].size()<len) lp.coef[s3].resize(len,0); int i=rng()%len; lp.coef[s3][i]=(lp.coef[s3][i]+1+rng()%(B-1))%B; } }
            double g=obj(t,tp,nullptr); if(g<0) continue;
            if(g>=f || exp((g-f)/T) > (rng()%1000000)/1e6){ s=t; P=tp; f=g; if(f>best){best=f; bs=s; bp=P;} } }
        obj(bs,bp,parts);
        printf("SA b=%d m=%d Lcert=%d iters=%ld best=%.5f parts:",B,m,m+3*kc,it,best); for(int k=0;k<=kc;k++) printf(" %.4f",parts[k]); printf("\n");
        save(bs,out+"_seed.txt"); writeParams(out+"_params.txt",bp); return 0; }
    return 1;
}
