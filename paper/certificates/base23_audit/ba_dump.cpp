// ba_dump.cpp -- DATA GENERATION ONLY: replays R1's witness chains (seed + params) with R1's own code and writes every
// level as a NET file (generator matrices + shift). All VERIFICATION of these nets is done by ba.cpp (independent code).
// build: g++-16 -O3 -std=c++17 -o ba_dump ba_dump.cpp     usage: ba_dump SEED PARAMS NL OUTPREFIX
#define main r1_main_unused
#include "../r1_gsep.cpp"
#undef main
int main(int argc,char** argv){
    Net seed=load(argv[1]); initB(); vector<LiftParam> P; readParams(argv[2],P); int NL=atoi(argv[3]);
    auto ch=chain(seed,P,NL);
    for(int k=0;k<=NL;k++){ const Net& n=ch[k]; string fn=string(argv[4])+"_m"+to_string(n.M)+".net"; FILE* f=fopen(fn.c_str(),"w");
        fprintf(f,"NET %d %d\n",B,n.M); for(auto& g:n.gens){ for(int t=0;t<3*n.M;t++) fprintf(f,"%d%c",g[t],t+1<3*n.M?' ':'\n'); }
        for(int t=0;t<3*n.M;t++) fprintf(f,"%d%c",n.shift[t],t+1<3*n.M?' ':'\n'); fclose(f);
        int dOff = k<NL && k<(int)P.size()? P[k].dOff : 0; printf("%s  (next lift dOff=%d)\n",fn.c_str(),dOff); }
}
