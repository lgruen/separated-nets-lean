// Independent exact toroidal min-distance oracle for digital (0,3,3)-nets in graph form
// coordinate c digits: (n_c, B_c.n mod p, R_c.n mod p). One point per cell n in (Z/p)^3.
// Pairs with toroidal cell difference |E|_inf>=3 are >=2 cells apart (>= 2p^2 in integer units).
// For each E in {-2..2}^3\0, a rigorous per-E lower bound (coordinatewise, all wrap options, jitter |.|<p)
// is used ONLY to skip E's that cannot beat the current best; surviving E's are scanned over all p^3 cells.
// Output: d2 (integer units, X in [0,p^3)), c = sqrt(d2)/p^2, argmin.
#include <cstdio>
#include <cmath>
#include <vector>
#include <algorithm>
#include <cstdlib>
typedef long long ll;
int main(int argc,char**argv){
  ll p; ll B[3][3],R[3][3];
  if(scanf("%lld",&p)!=1) return 1;
  for(int i=0;i<3;i++)for(int j=0;j<3;j++){scanf("%lld",&B[i][j]);B[i][j]=((B[i][j]%p)+p)%p;}
  for(int i=0;i<3;i++)for(int j=0;j<3;j++){scanf("%lld",&R[i][j]);R[i][j]=((R[i][j]%p)+p)%p;}
  ll N=p*p*p, p2=p*p;
  struct EE{int e[3]; double lb;}; std::vector<EE> Es;
  for(int a=-2;a<=2;a++)for(int b=-2;b<=2;b++)for(int c=-2;c<=2;c++){ if(!a&&!b&&!c) continue;
    int e[3]={a,b,c}; double lb=0;
    for(int k=0;k<3;k++){ ll beta=((B[k][0]*a+B[k][1]*b+B[k][2]*c)%p+p)%p; double best=1e300;
      for(int kap=0;kap<=1;kap++){ if(kap&&beta==0) continue; double L=fabs((double)(e[k]*p2+(beta-kap*p)*p)); double v=std::max(0.0,L-(double)(p-1)); best=std::min(best,v*v);} lb+=best; }
    EE x; x.e[0]=a;x.e[1]=b;x.e[2]=c;x.lb=lb; Es.push_back(x);}
  std::sort(Es.begin(),Es.end(),[](const EE&x,const EE&y){return x.lb<y.lb;});
  ll best=4*p2*p2; int lo=argc>1?atoi(argv[1]):0, hi=argc>2?atoi(argv[2]):1000; if(argc>3) best=atoll(argv[3]); int bestE[3]={0,0,0}; ll bestn[3]={0,0,0}; int scanned=0; int idx=-1;
  auto tor=[&](ll d)->ll{ d%=N; if(d<0)d+=N; if(d>N-d) d=N-d; return d;};
  for(auto&E:Es){ idx++; if(E.lb>=(double)best) break; if(idx<lo||idx>=hi) continue; scanned++;
    for(ll n0=0;n0<p;n0++)for(ll n1=0;n1<p;n1++){
      ll m0=(n0+E.e[0]+p)%p, m1=(n1+E.e[1]+p)%p;
      for(ll n2=0;n2<p;n2++){ ll m2=(n2+E.e[2]+p)%p; ll n[3]={n0,n1,n2}, m[3]={m0,m1,m2}; ll s=0;
        for(int k=0;k<3;k++){ ll yb=(B[k][0]*n0+B[k][1]*n1+B[k][2]*n2)%p, zb=(R[k][0]*n0+R[k][1]*n1+R[k][2]*n2)%p;
          ll ym=(B[k][0]*m0+B[k][1]*m1+B[k][2]*m2)%p, zm=(R[k][0]*m0+R[k][1]*m1+R[k][2]*m2)%p;
          ll X=n[k]*p2+yb*p+zb, Y=m[k]*p2+ym*p+zm; ll d=tor(Y-X); s+=d*d; if(s>=best) break; }
        if(s<best){best=s;bestE[0]=E.e[0];bestE[1]=E.e[1];bestE[2]=E.e[2];bestn[0]=n0;bestn[1]=n1;bestn[2]=n2;}
      }}
  }
  printf("%lld %.6f E=(%d,%d,%d) n=(%lld,%lld,%lld) scannedE=%d\n",best,sqrt((double)best)/(double)p2,bestE[0],bestE[1],bestE[2],bestn[0],bestn[1],bestn[2],scanned);
}
