// codesaudit_e2cert.cpp -- Proposition prop:s5r2 / Table tab:s5r2: the fault-aware
// relaxation certificate for s=5, r=2 skeleton digits
//   S_{z_i} = sum_d kap_id x_{d,k} + bet_id x_{d,k-1} + eta_id x_{d,k-2} + sum_j G_ij z_{j,k-1} + H_ij z_{j,k-2}
// (G_ii = own term o_i, H_ii = 0).  For every pair of distinct points with all |a_c| <= (p-1)/2 (centred fine
// differences), Lemma skelred(ii) gives a_z == kap a_x + bet xi1_x + eta xi2_x + G xi1_z + H xi2_z (mod p) with
// (xi1,xi2) in {(0,0),(s,0),(s,s)}, s = sgn a_c, and a_z centred.  Pairs with some |a_c| >= (p+1)/2 have
// |a|_inf >= (p+1)/2 and jitter norm >= (p-1)/2.  Output: Minf = min |a|_inf, J2 = min sum (|a_c|-1)_+^2 over
// all nonzero relaxation solutions (capped by the far case), plus lambda_inf(Lambda_A) for A = kap.
// Written from the statement of Prop. t3s4 / Lemma skelred, not from codes_s5r2.cpp.
// input (stdin): p, then 6 kap (row-major 3x2), 6 bet, 6 eta, 9 G, 9 H.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cmath>
typedef long long ll;
int main(){
  ll p; if(scanf("%lld",&p)!=1) return 1;
  ll kap[3][2],bet[3][2],eta[3][2],G[3][3],H[3][3];
  for(int i=0;i<3;i++)for(int d=0;d<2;d++)scanf("%lld",&kap[i][d]);
  for(int i=0;i<3;i++)for(int d=0;d<2;d++)scanf("%lld",&bet[i][d]);
  for(int i=0;i<3;i++)for(int d=0;d<2;d++)scanf("%lld",&eta[i][d]);
  for(int i=0;i<3;i++)for(int j=0;j<3;j++)scanf("%lld",&G[i][j]);
  for(int i=0;i<3;i++)for(int j=0;j<3;j++)scanf("%lld",&H[i][j]);
  const ll h=(p-1)/2;
  auto cen=[&](ll v){ v%=p; if(v<0) v+=p; return v>h? v-p : v; };
  // the 5 admissible (xi1,xi2) patterns for a coordinate of sign s: index 0=(0,0),1=(s,0),2=(s,s)
  ll Minf=(p+1)/2, J2=h*h;  // far case
  ll lamInf=p;              // lambda_inf(Lambda_A): x=0 forces z==0 mod p -> |z|>=p
  // z-fault contributions for all 5^3 sign/pattern choices of the three skeleton coordinates
  int pat[5][2]={{0,0},{1,0},{1,1},{-1,0},{-1,-1}};
  std::vector<ll> zc(125*3); std::vector<int> zsg(125*3);
  for(int q=0;q<125;q++){ int t=q,pp[3]; for(int i=0;i<3;i++){pp[i]=t%5;t/=5;}
    for(int i=0;i<3;i++){ ll v=0; for(int j=0;j<3;j++) v+=G[i][j]*pat[pp[j]][0]+H[i][j]*pat[pp[j]][1];
      zc[q*3+i]=v; zsg[q*3+i]=pat[pp[i]][0]; } }
  for(ll x1=-h;x1<=h;x1++) for(ll x2=-h;x2<=h;x2++){
    ll ax=std::max(llabs(x1),llabs(x2));
    ll jx=(llabs(x1)>1?(llabs(x1)-1)*(llabs(x1)-1):0)+(llabs(x2)>1?(llabs(x2)-1)*(llabs(x2)-1):0);
    if(x1||x2){ ll mm=ax; for(int i=0;i<3;i++){ ll z=llabs(cen(kap[i][0]*x1+kap[i][1]*x2)); if(z>mm) mm=z;} if(mm<lamInf) lamInf=mm; }
    int s1=(x1>0)-(x1<0), s2=(x2>0)-(x2<0);
    for(int u1=0;u1<(x1?3:1);u1++) for(int u2=0;u2<(x2?3:1);u2++){
      ll a1=(u1>=1)*s1, b1=(u1==2)*s1, a2=(u2>=1)*s2, b2=(u2==2)*s2;
      ll base[3]; for(int i=0;i<3;i++) base[i]=kap[i][0]*x1+kap[i][1]*x2+bet[i][0]*a1+bet[i][1]*a2+eta[i][0]*b1+eta[i][1]*b2;
      for(int q=0;q<125;q++){
        ll az[3]; bool ok=true;
        for(int i=0;i<3&&ok;i++){ az[i]=cen(base[i]+zc[q*3+i]); int sg=zsg[q*3+i];
          if(sg>0 && az[i]<=0) ok=false; if(sg<0 && az[i]>=0) ok=false; }
        if(!ok) continue;
        if(!x1&&!x2&&!az[0]&&!az[1]&&!az[2]) continue;
        ll mm=ax, jj=jx; for(int i=0;i<3;i++){ ll a=llabs(az[i]); if(a>mm) mm=a; if(a>1) jj+=(a-1)*(a-1); }
        if(mm<Minf) Minf=mm; if(jj<J2) J2=jj;
      }
    }
  }
  double sc=pow((double)p,-0.6);
  printf("p=%lld lamInf=%lld Minf=%lld c_inf=%.4f J=%.4f (J2=%lld) c_jit=%.4f pig=%.2f\n",p,lamInf,Minf,(Minf-1)*sc,sqrt((double)J2),J2,sqrt((double)J2)*sc,pow((double)p,0.6));
}
