// g3_lift.cpp -- G3: "deep-shift tau-lift" recursion m -> m+3 for DIGITAL (0,m,3)-nets, base 2 or 3.
//
// Construction (see the research notes):  given a digital net P (affine GF(b)-space, M digits/coord),
//   Q = { (a T + b^2 (p + s_d)_x + J_x(d),  (a+d1) T + ...,  (a+d1+d2) T + ...) : a in Z/b, d=(d1,d2), p in P }
//   T = b^(M+2), s_d = d1*sA + d2*sB (digitwise GF(b) shifts supported on digits of depth > D only),
//   J(d) = T8 closed-form jitter (hi_x=d2, lo_x=d1; hi_y=d1+d2, lo_y=d1; hi_z=d1, lo_z=d2).
// Q is a (0,M+3,3)-net iff  sA is yz-good, sB is xy-good, sB-sA is xz-good for the shadows of P
// (T8 Lemma + union-of-cosets = span).  "u is ab-good" <=> lambda_e(u) != 0 for e=1..M (lambda_e = the
// functional cutting out P_ab + Z_e).  G3 PROOF: for D <= M/2 the deep restrictions of lambda_1..lambda_M are
// linearly independent, so a good deep u always exists (any RHS).  Q is again digital -> iterate.
// The top D digits of every coordinate of P are never touched again => geometry frozen at depth D.
//
// usage: g3_lift SEEDFILE LEVELS [R=64] [seed=1] [Dmode=half|halfm1] [OUTPREFIX]
//   SEEDFILE: "b m" + b^m lines "x y z" (must be an affine GF(b) digital net).
//   For each level: R random solutions (random nullspace combo; b=3 also random nonzero RHS) -> best toroidal d2.
//   Prints per level: m, D, N, d2, c, gsep (guaranteed-separation floor valid for ALL later levels).
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
using namespace std;
typedef vector<int> VI;
static int B; // base
static inline int md(int a){ a%=B; return a<0?a+B:a; }
static int inv(int a){ for(int x=1;x<B;x++) if(md(a*x)==1) return x; return 0; }

struct Net { int M; vector<VI> gens; VI shift; }; // vectors of length 3M: coord c, depth j (0=top) at c*M+j

// generate integer points
static void points(const Net& n, vector<uint32_t>& X, vector<uint32_t>& Y, vector<uint32_t>& Z){
    int M=n.M; long N=1; for(int i=0;i<M;i++) N*=B;
    X.resize(N); Y.resize(N); Z.resize(N);
    VI cur=n.shift, v(M,0);
    vector<uint32_t> pw(M); { uint32_t p=1; for(int j=M-1;j>=0;j--){ pw[j]=p; p*=B; } }
    for(long idx=0; idx<N; idx++){
        uint32_t c3[3]={0,0,0};
        for(int c=0;c<3;c++){ uint32_t s=0; for(int j=0;j<M;j++) s+=cur[c*M+j]*pw[j]; c3[c]=s; }
        X[idx]=c3[0]; Y[idx]=c3[1]; Z[idx]=c3[2];
        // increment v
        for(int i=0;i<M;i++){ v[i]++; const VI& g=n.gens[i]; for(int t=0;t<3*M;t++) cur[t]=md(cur[t]+g[t]); if(v[i]<B) break; v[i]=0; }
    }
}

// toroidal min d2 via cell grid (exact: retries until found d <= min cell width)
static long long mind2(const vector<uint32_t>& X,const vector<uint32_t>& Y,const vector<uint32_t>& Z, long long Nside, long long* pa=nullptr){
    long N=X.size();
    if(N<=6000){ long long best=LLONG_MAX; for(long i=0;i<N;i++) for(long j=i+1;j<N;j++){
        long long dx=llabs((long long)X[i]-X[j]); dx=min(dx,Nside-dx); long long dy=llabs((long long)Y[i]-Y[j]); dy=min(dy,Nside-dy);
        long long dz=llabs((long long)Z[i]-Z[j]); dz=min(dz,Nside-dz); long long d=dx*dx+dy*dy+dz*dz; if(d<best) best=d; } return best; }
    long G=(long)floor(cbrt((double)N)); if(G<3) G=3;
    while(true){
        long long wmin=Nside/G;
        vector<int> cnt(G*G*G+1,0); vector<int> ord(N);
        auto cell=[&](long i){ long cx=(long)((unsigned long long)X[i]*G/Nside), cy=(long)((unsigned long long)Y[i]*G/Nside), cz=(long)((unsigned long long)Z[i]*G/Nside); return (cx*G+cy)*G+cz; };
        for(long i=0;i<N;i++) cnt[cell(i)+1]++;
        for(long c=0;c<G*G*G;c++) cnt[c+1]+=cnt[c];
        { vector<int> pos(cnt.begin(),cnt.end()-1); for(long i=0;i<N;i++) ord[pos[cell(i)]++]=i; }
        long long best=LLONG_MAX;
        for(long cx=0;cx<G;cx++) for(long cy=0;cy<G;cy++) for(long cz=0;cz<G;cz++){
            long c0=(cx*G+cy)*G+cz;
            for(int ddx=-1;ddx<=1;ddx++) for(int ddy=-1;ddy<=1;ddy++) for(int ddz=-1;ddz<=1;ddz++){
                long nx=(cx+ddx+G)%G, ny=(cy+ddy+G)%G, nz=(cz+ddz+G)%G; long c1=(nx*G+ny)*G+nz; if(c1<c0) continue;
                for(int a=cnt[c0];a<cnt[c0+1];a++){ int i=ord[a];
                    for(int bb=(c1==c0?a+1:cnt[c1]); bb<cnt[c1+1]; bb++){ int j=ord[bb];
                        long long dx=llabs((long long)X[i]-X[j]); dx=min(dx,Nside-dx); if(dx*dx>=best) continue;
                        long long dy=llabs((long long)Y[i]-Y[j]); dy=min(dy,Nside-dy);
                        long long dz=llabs((long long)Z[i]-Z[j]); dz=min(dz,Nside-dz); long long d=dx*dx+dy*dy+dz*dz; if(d<best) best=d; } } }
        }
        if(best<=wmin*wmin) return best;
        long long L=(long long)ceil(sqrt((double)best))+1; long G2=Nside/L; if(G2<3){ // brute fallback
            long long b2=LLONG_MAX; for(long i=0;i<N;i++) for(long j=i+1;j<N;j++){ long long dx=llabs((long long)X[i]-X[j]); dx=min(dx,Nside-dx); long long dy=llabs((long long)Y[i]-Y[j]); dy=min(dy,Nside-dy); long long dz=llabs((long long)Z[i]-Z[j]); dz=min(dz,Nside-dz); long long d=dx*dx+dy*dy+dz*dz; if(d<b2) b2=d;} return b2; }
        G=G2;
    }
}

// guaranteed separation floor: truncate to top D digits (W=b^(M-D)); per-coord gap max(0,|dhat|-W)
static double gsep(const vector<uint32_t>& X,const vector<uint32_t>& Y,const vector<uint32_t>& Z,long long Nside,int M,int D,long long d2true){
    long long W=1; for(int i=0;i<M-D;i++) W*=B;
    long N=X.size();
    auto tr=[&](uint32_t v){ return (long long)(v/W)*W; };
    // candidate pairs: per-coord toroidal |dhat| <= W + sqrt(d2true)
    long long R=W+(long long)ceil(sqrt((double)d2true))+1;
    long G=Nside/R; if(G<3) G=1;
    long long best=LLONG_MAX;
    auto pairval=[&](long i,long j){ long long s=0; long long d[3]={tr(X[i])-tr(X[j]),tr(Y[i])-tr(Y[j]),tr(Z[i])-tr(Z[j])};
        for(int c=0;c<3;c++){ long long a=llabs(d[c]); a=min(a,Nside-a); long long g=max(0LL,a-W); s+=g*g; } return s; };
    if(G==1){ for(long i=0;i<N;i++) for(long j=i+1;j<N;j++){ long long v=pairval(i,j); if(v<best) best=v; } }
    else {
        vector<int> cnt(G*G*G+1,0), ord(N);
        auto cell=[&](long i){ long cx=(long)((unsigned long long)X[i]*G/Nside), cy=(long)((unsigned long long)Y[i]*G/Nside), cz=(long)((unsigned long long)Z[i]*G/Nside); if(cx>=G)cx=G-1; if(cy>=G)cy=G-1; if(cz>=G)cz=G-1; return (cx*G+cy)*G+cz; };
        for(long i=0;i<N;i++) cnt[cell(i)+1]++;
        for(long c=0;c<G*G*G;c++) cnt[c+1]+=cnt[c];
        { vector<int> pos(cnt.begin(),cnt.end()-1); for(long i=0;i<N;i++) ord[pos[cell(i)]++]=i; }
        for(long cx=0;cx<G;cx++) for(long cy=0;cy<G;cy++) for(long cz=0;cz<G;cz++){ long c0=(cx*G+cy)*G+cz;
            for(int ddx=-1;ddx<=1;ddx++) for(int ddy=-1;ddy<=1;ddy++) for(int ddz=-1;ddz<=1;ddz++){
                long c1=(((cx+ddx+G)%G)*G+((cy+ddy+G)%G))*G+((cz+ddz+G)%G); if(c1<c0) continue;
                for(int a=cnt[c0];a<cnt[c0+1];a++) for(int bb=(c1==c0?a+1:cnt[c1]); bb<cnt[c1+1]; bb++){ long long v=pairval(ord[a],ord[bb]); if(v<best) best=v; } } }
    }
    return sqrt((double)best)*pow((double)B,-2.0*M/3.0);
}

// Gaussian elimination helpers over GF(B). Solve A u = r (rows = equations). Returns particular + nullspace basis.
static bool solve(vector<VI> A, VI r, int nv, VI& part, vector<VI>& nulls){
    int ne=A.size(); vector<int> piv; int row=0;
    for(int col=0; col<nv && row<ne; col++){
        int p=-1; for(int i=row;i<ne;i++) if(A[i][col]){p=i;break;} if(p<0) continue;
        swap(A[p],A[row]); swap(r[p],r[row]); int iv=inv(A[row][col]);
        for(int t=0;t<nv;t++) A[row][t]=md(A[row][t]*iv); r[row]=md(r[row]*iv);
        for(int i=0;i<ne;i++) if(i!=row && A[i][col]){ int f=A[i][col]; for(int t=0;t<nv;t++) A[i][t]=md(A[i][t]-f*A[row][t]); r[i]=md(r[i]-f*r[row]); }
        piv.push_back(col); row++; }
    for(int i=row;i<ne;i++) if(r[i]) return false;
    part.assign(nv,0); for(int i=0;i<row;i++) part[piv[i]]=r[i];
    nulls.clear(); vector<char> isp(nv,0); for(int c:piv) isp[c]=1;
    for(int f=0; f<nv; f++) if(!isp[f]){ VI v(nv,0); v[f]=1; for(int i=0;i<row;i++) v[piv[i]]=md(-A[i][f]); nulls.push_back(v); }
    return true;
}

// lambda_e for projection (ca,cb) of net n: returns vector over 2M coords (a-depth j -> j, b-depth j -> M+j)
static vector<VI> lambdas(const Net& n, int ca, int cb){
    int M=n.M; vector<VI> L;
    for(int e=1;e<=M;e++){
        // unknowns: a depths 0..e-1, b depths 0..M-e  (M+1 unknowns); constraints: orth to each generator
        int nv=M+1; vector<VI> A; VI r;
        for(int i=0;i<M;i++){ VI row(nv); for(int j=0;j<e;j++) row[j]=n.gens[i][ca*M+j]; for(int j=0;j<=M-e;j++) row[e+j]=n.gens[i][cb*M+j]; A.push_back(row); r.push_back(0); }
        VI part; vector<VI> nulls; solve(A,r,nv,part,nulls);
        if(nulls.size()!=1){ fprintf(stderr,"lambda nullity %zu at e=%d (shadow not (0,M,2)?)\n",nulls.size(),e); exit(1); }
        VI lam(2*M,0); for(int j=0;j<e;j++) lam[j]=nulls[0][j]; for(int j=0;j<=M-e;j++) lam[M+j]=nulls[0][e+j];
        L.push_back(lam);
    }
    return L;
}

// deep system for one projection: unknown u over deep a-digits (depth>=D) and deep b-digits; lambda_e(u)=r_e
struct Sys { VI part; vector<VI> nulls; int D,M; };
static Sys deep_sys(const vector<VI>& L,int M,int D,const VI& rhs){
    int nd=M-D; int nv=2*nd; vector<VI> A; VI r;
    for(int e=0;e<M;e++){ VI row(nv); for(int j=0;j<nd;j++){ row[j]=L[e][D+j]; row[nd+j]=L[e][M+D+j]; } A.push_back(row); r.push_back(rhs[e]); }
    Sys s; s.D=D; s.M=M; if(!solve(A,r,nv,s.part,s.nulls)){ fprintf(stderr,"deep system inconsistent M=%d D=%d\n",M,D); exit(2);} return s;
}
static VI sample(const Sys& s, mt19937_64& rng){ VI u=s.part; for(auto& v:s.nulls){ int c=rng()%B; if(c) for(size_t t=0;t<u.size();t++) u[t]=md(u[t]+c*v[t]); } return u; }

static Net lift(const Net& n, const VI& sA, const VI& sB){ // sA,sB: 3M digit vectors
    int M=n.M, M2=M+3; Net q; q.M=M2;
    auto emb=[&](const VI& g){ VI h(3*M2,0); for(int c=0;c<3;c++) for(int j=0;j<M;j++) h[c*M2+1+j]=g[c*M+j]; return h; };
    for(auto& g:n.gens) q.gens.push_back(emb(g));
    VI ga(3*M2,0); for(int c=0;c<3;c++) ga[c*M2]=1; q.gens.push_back(ga);
    VI g1=emb(sA); g1[0*M2]=0; g1[1*M2]=1; g1[2*M2]=1; // top digits (a, a+d1, a+d1+d2)
    // J(d1=1,d2=0): x (hi=d2=0, lo=d1=1); y (hi=d1+d2=1, lo=d1=1); z (hi=d1=1, lo=d2=0)
    g1[0*M2+M+1]=0; g1[0*M2+M+2]=1; g1[1*M2+M+1]=1; g1[1*M2+M+2]=1; g1[2*M2+M+1]=1; g1[2*M2+M+2]=0;
    VI g2=emb(sB); g2[0*M2]=0; g2[1*M2]=0; g2[2*M2]=1;
    // J(d1=0,d2=1): x (1,0); y (1,0); z (0,1)
    g2[0*M2+M+1]=1; g2[0*M2+M+2]=0; g2[1*M2+M+1]=1; g2[1*M2+M+2]=0; g2[2*M2+M+1]=0; g2[2*M2+M+2]=1;
    q.gens.push_back(g1); q.gens.push_back(g2);
    q.shift=emb(n.shift);
    return q;
}

static Net load(const char* fn){
    FILE* f=fopen(fn,"r"); if(!f){perror(fn);exit(1);} int b,m; if(fscanf(f,"%d %d",&b,&m)!=2) exit(1); B=b;
    long N=1; for(int i=0;i<m;i++) N*=b; vector<VI> P(N,VI(3*m));
    for(long i=0;i<N;i++){ for(int c=0;c<3;c++){ long v; if(fscanf(f,"%ld",&v)!=1) exit(1); for(int j=m-1;j>=0;j--){ P[i][c*m+j]=v%b; v/=b; } } }
    fclose(f);
    Net n; n.M=m; n.shift=P[0];
    // basis of differences
    vector<VI> basis; vector<int> pc;
    for(long i=1;i<N && (int)basis.size()<m;i++){ VI d(3*m); for(int t=0;t<3*m;t++) d[t]=md(P[i][t]-P[0][t]);
        for(size_t k=0;k<basis.size();k++){ int f=d[pc[k]]; if(f) for(int t=0;t<3*m;t++) d[t]=md(d[t]-f*basis[k][t]); }
        int p=-1; for(int t=0;t<3*m;t++) if(d[t]){p=t;break;} if(p<0) continue;
        int iv=inv(d[p]); for(int t=0;t<3*m;t++) d[t]=md(d[t]*iv);
        for(size_t k=0;k<basis.size();k++){ int f=basis[k][p]; if(f) for(int t=0;t<3*m;t++) basis[k][t]=md(basis[k][t]-f*d[t]); }
        basis.push_back(d); pc.push_back(p); }
    if((int)basis.size()!=m){ fprintf(stderr,"not affine: rank %zu\n",basis.size()); exit(3); }
    n.gens=basis;
    // verify affine closure: regenerate and compare as sets
    vector<uint32_t> X,Y,Z; points(n,X,Y,Z); vector<uint64_t> A,Bv;
    auto key=[&](const VI& p){ uint64_t k=0; for(int t=0;t<3*m;t++) k=k*b+p[t]; return k; };
    for(long i=0;i<N;i++) A.push_back(key(P[i]));
    for(long i=0;i<N;i++){ uint64_t k=0; uint32_t c3[3]={X[i],Y[i],Z[i]}; for(int c=0;c<3;c++){ VI dg(m); uint32_t v=c3[c]; for(int j=m-1;j>=0;j--){dg[j]=v%b; v/=b;} for(int j=0;j<m;j++) k=k*b+dg[j]; } Bv.push_back(k); }
    sort(A.begin(),A.end()); sort(Bv.begin(),Bv.end()); if(A!=Bv){ fprintf(stderr,"not affine (closure fails)\n"); exit(3); }
    return n;
}

static void save(const Net& n,const string& fn){
    vector<uint32_t> X,Y,Z; points(n,X,Y,Z); FILE* f=fopen(fn.c_str(),"w"); fprintf(f,"%d %d\n",B,n.M);
    for(size_t i=0;i<X.size();i++) fprintf(f,"%u %u %u\n",X[i],Y[i],Z[i]); fclose(f);
}

#ifndef G3_NO_MAIN
int main(int argc,char** argv){
    if(argc<3){ fprintf(stderr,"usage: g3_lift SEED LEVELS [R] [seed] [Dmode] [outprefix]\n"); return 1; }
    Net n=load(argv[1]); int levels=atoi(argv[2]); string Rs=argc>3?argv[3]:"64"; vector<int> Rl; { string t; for(char ch:Rs){ if(ch==','){Rl.push_back(atoi(t.c_str()));t="";} else t+=ch; } Rl.push_back(atoi(t.c_str())); } uint64_t sd=argc>4?atoll(argv[4]):1;
    string Dmode=argc>5?argv[5]:"half"; string outp=argc>6?argv[6]:"";
    mt19937_64 rng(sd);
    auto report=[&](const Net& q,const char* tag,int Dnext){
        vector<uint32_t> X,Y,Z; points(q,X,Y,Z); long long Ns=X.size(); long long d2=mind2(X,Y,Z,Ns);
        double c=sqrt((double)d2)*pow((double)B,-2.0*q.M/3.0);
        double g=gsep(X,Y,Z,Ns,q.M,Dnext,d2);
        printf("%s b=%d m=%d N=%lld d2=%lld c=%.4f gsep(D=%d)=%.4f\n",tag,B,q.M,Ns,d2,c,Dnext,g); fflush(stdout);
    };
    // Dmode: comma list per level; 'h' = floor(M/2), integer k>=0 -> D=k, negative -k -> floor(M/2)-k; last entry repeats
    vector<string> Dl; { string t; for(char ch:Dmode){ if(ch==','){Dl.push_back(t);t="";} else t+=ch; } Dl.push_back(t); }
    auto Dlev=[&](int lv,int M){ string t=Dl[min((size_t)lv,Dl.size()-1)]; if(t=="h"||t=="half") return M/2; int k=atoi(t.c_str()); return k<0? max(0,M/2+k) : min(k,M/2); };
    auto Dof=[&](int M){ return M/2; };
    report(n,"seed",Dof(n.M));
    for(int lv=1; lv<=levels; lv++){
        int M=n.M, D=Dlev(lv-1,M), nd=M-D;
        vector<VI> Lyz=lambdas(n,1,2), Lxy=lambdas(n,0,1), Lxz=lambdas(n,0,2);
        long long bestd2=-1; Net best;
        int R=Rl[min((size_t)(lv-1),Rl.size()-1)]; bool canon=(R==0); if(canon) R=1;
        for(int trial=0; trial<R; trial++){
            auto rhs=[&](){ VI r(M); for(int e=0;e<M;e++) r[e]=(B==2||canon)?1:1+rng()%(B-1); return r; };
            Sys syz=deep_sys(Lyz,M,D,rhs()), sxy=deep_sys(Lxy,M,D,rhs()), sxz=deep_sys(Lxz,M,D,rhs());
            VI uyz=canon?syz.part:sample(syz,rng), uxy=canon?sxy.part:sample(sxy,rng), uxz=canon?sxz.part:sample(sxz,rng);
            // sA: (xa, ya, za) with (ya,za)=uyz; sB: (xb,yb,zb) with (xb,yb)=uxy; (xb-xa, zb-za)=uxz
            VI sA(3*M,0), sB(3*M,0);
            for(int j=0;j<nd;j++){ sA[1*M+D+j]=uyz[j]; sA[2*M+D+j]=uyz[nd+j]; sB[0*M+D+j]=uxy[j]; sB[1*M+D+j]=uxy[nd+j]; }
            for(int j=0;j<nd;j++){ sA[0*M+D+j]=md(sB[0*M+D+j]-uxz[j]); sB[2*M+D+j]=md(sA[2*M+D+j]+uxz[nd+j]); }
            Net q=lift(n,sA,sB);
            vector<uint32_t> X,Y,Z; points(q,X,Y,Z); long long d2=mind2(X,Y,Z,(long long)X.size());
            if(d2>bestd2){ bestd2=d2; best=q; }
        }
        n=best; char tag[32]; snprintf(tag,32,"lvl%d(D=%d)",lv,D); report(n,tag,Dof(n.M));
        if(!outp.empty()) save(n,outp+"_m"+to_string(n.M)+".txt");
    }
}
#endif
