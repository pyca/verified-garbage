// Search for AES S-box circuits, forward and inverse.
// Method (Boyar & Peralta, SEA 2010, NIST pub 902701): write the S-box as
//   top linear map U, a nonlinear middle, bottom linear map B,
// with the GF(2^4) inversion of the paper's Fig. 2 (5 AND, 11 XOR), and find short
// linear programs for U and B with the paper's distance heuristic, ties random.
// The tower bases are enumerated here from FIPS 197's field, not taken from anywhere.
#include <bits/stdc++.h>
using namespace std; typedef unsigned u; typedef uint8_t b;
static mt19937 rng;
b mulf(b x,b y){u r=0,a=x;while(y){if(y&1)r^=a;a<<=1;if(a&256)a^=0x11b;y>>=1;}return r;}
b M[256][256],INV[256];
b pw(b x,int n){b r=1;while(n--)r=M[r][x];return r;}
b affl(b x){b r=0;for(int i=0;i<8;i++){int t=(x>>i)^(x>>((i+4)&7))^(x>>((i+5)&7))^(x>>((i+6)&7))^(x>>((i+7)&7));r|=(t&1)<<i;}return r;}
// Fig.2: in x1..x4 (bit0=x1), out y1..y4
int F(int v){int x1=v&1,x2=v>>1&1,x3=v>>2&1,x4=v>>3&1;int t1=x1^x2,t2=x1&x3,t3=x4^t2,t4=t1&t3,y4=x2^t4,t5=x3^x4,t6=x2^t2,t7=t6&t5,y2=x4^t7,t8=x3^y2,t9=t3^y2,t10=x4&t9,y1=t10^t8,t11=t3^t10,t12=y4&t11,y3=t12^t1;return y1|y2<<1|y3<<2|y4<<3;}
// linear program heuristic. n vars (bits), targets. Returns ops (dst form as list)
struct Op{int a,c;u f;};
// U: BFS distances over GF(2)^8 (exact)
int lin8(const vector<u>&T0,int lim,vector<Op>&out){
  vector<u> S;for(int i=0;i<8;i++)S.push_back(1u<<i);out.clear();
  set<u> T;for(u t:T0)if(__builtin_popcount(t)>1)T.insert(t);
  auto dist=[&](const vector<u>&S,vector<int>&d){d.assign(256,99);d[0]=0;vector<u>cur={0};int k=0;while(cur.size()){vector<u>nx;k++;for(u c:cur)for(u s:S)if(d[c^s]>k){d[c^s]=k;nx.push_back(c^s);}cur=nx;}};
  while(T.size()){
    if((int)out.size()+(int)T.size()>lim)return 99;
    u pick=0;vector<u> e;set<u> seen(S.begin(),S.end());set<u> cand;
    for(size_t i=0;i<S.size();i++)for(size_t j=0;j<i;j++){u f=S[i]^S[j];if(f&&!seen.count(f))cand.insert(f);}
    vector<u> im;for(u f:cand)if(T.count(f))im.push_back(f);
    if(im.size())pick=im[rng()%im.size()];
    else{int bs=1e9,bn=-1;vector<u>bb;for(u f:cand){S.push_back(f);vector<int>d;dist(S,d);S.pop_back();int s=0,n=0;for(u t:T){int x=d[t]-1;s+=x;n+=x*x;}
      if(s<bs||(s==bs&&n>bn)){bs=s;bn=n;bb={f};}else if(s==bs&&n==bn)bb.push_back(f);}
      pick=bb[rng()%bb.size()];}
    int pa=-1,pc=-1;for(size_t i=0;i<S.size()&&pa<0;i++)for(size_t j=0;j<i;j++)if((S[i]^S[j])==pick){pa=i;pc=j;break;}
    out.push_back({pa,pc,pick});S.push_back(pick);T.erase(pick);
  }
  return out.size();
}
// general n<=18: distance by exhaustive combos
bool reach(const vector<u>&S,u t,int k,size_t st){ // t as sum of exactly k elements from S[st..]
  if(k==0)return t==0; if(k==1){for(size_t i=st;i<S.size();i++)if(S[i]==t)return true;return false;}
  for(size_t i=st;i+k<=S.size()+0;i++)if(reach(S,t^S[i],k-1,i+1))return true;return false;}
int linN(int n,const vector<u>&T,int lim,vector<Op>&out){
  vector<u>S;for(int i=0;i<n;i++)S.push_back(1u<<i);out.clear();
  vector<int>D;int m=T.size();for(u t:T)D.push_back(__builtin_popcount(t)-1);
  while(true){
    int rem=0;for(int d:D)rem+=d;if(!rem)break;int nz=0;for(int d:D)nz+=d>0; if((int)out.size()+nz>lim)return 99;
    int bi=-1,bj=-1;u bf=0;
    for(size_t i=0;i<S.size()&&bi<0;i++)for(size_t j=0;j<i;j++){u f=S[i]^S[j];for(int k=0;k<m;k++)if(D[k]==1&&T[k]==f){bi=i;bj=j;bf=f;break;}if(bi>=0)break;}
    vector<int>bd;
    if(bi<0){int bs=1e9,bn=-1,cnt=0;set<u> seen(S.begin(),S.end());
      for(size_t i=0;i<S.size();i++)for(size_t j=0;j<i;j++){u f=S[i]^S[j];if(seen.count(f))continue;seen.insert(f);
        int s=0,nn=0;vector<int>nd(D);for(int k=0;k<m;k++){if(D[k]>0){if(reach(S,T[k]^f,D[k]-1,0))nd[k]=D[k]-1;}s+=nd[k];nn+=nd[k]*nd[k];}
        if(s<bs||(s==bs&&nn>bn)){bs=s;bn=nn;cnt=1;bi=i;bj=j;bf=f;bd=nd;}
        else if(s==bs&&nn==bn){cnt++;if(rng()%cnt==0){bi=i;bj=j;bf=f;bd=nd;}}}}
    else{bd=D;for(int k=0;k<m;k++)if(D[k]>0&&reach(S,T[k]^bf,D[k]-1,0))bd[k]=D[k]-1;}
    out.push_back({bi,bj,bf});S.push_back(bf);D=bd;
  }
  return out.size();
}
int main(int argc,char**argv){
  rng.seed(atoi(argv[1]));int secs=atoi(argv[2]);bool inverse=argc>3&&argv[3][0]=='i';
  for(int i=0;i<256;i++)for(int j=0;j<256;j++)M[i][j]=mulf(i,j);
  for(int i=1;i<256;i++)INV[i]=pw(i,254);
  vector<b>g16,g4;for(int i=0;i<256;i++){if(pw(i,16)==i)g16.push_back(i);if(pw(i,4)==i)g4.push_back(i);}
  // (P,Q): inv(sum x_i P_i) = sum y_i Q_i with y=F(x)
  struct PQ{b p[4],q[4];};vector<PQ>pqs;
  for(b p0:g16)for(b p1:g16)for(b p2:g16)for(b p3:g16){b p[4]={p0,p1,p2,p3};set<b>sp;for(int v=0;v<16;v++){b s=0;for(int k=0;k<4;k++)if(v>>k&1)s^=p[k];sp.insert(s);}if(sp.size()!=16)continue;
    b at[16];for(int v=0;v<16;v++){b s=0;for(int k=0;k<4;k++)if(v>>k&1)s^=p[k];at[F(v)]=INV[s];}
    b q[4]={at[1],at[2],at[4],at[8]};bool ok=true;for(int v=0;v<16&&ok;v++){b s=0;for(int k=0;k<4;k++)if(v>>k&1)s^=q[k];if(s!=at[v])ok=false;}
    if(ok){PQ z;memcpy(z.p,p,4);memcpy(z.q,q,4);pqs.push_back(z);}}
  fprintf(stderr,"pq %zu\n",pqs.size());
  struct C{PQ z;int o[4];};vector<C>cs;
  for(auto&z:pqs){int o[4]={0,1,2,3};do{b q[4];for(int k=0;k<4;k++)q[k]=z.q[o[k]];if(M[q[0]][q[3]]!=M[q[1]][q[2]])continue;b r=M[q[0]][INV[q[1]]];if(pw(r,4)!=r)continue;C c;c.z=z;memcpy(c.o,o,16);cs.push_back(c);}while(next_permutation(o,o+4));}
  fprintf(stderr,"configs %zu\n",cs.size());
  auto coord=[&](vector<b> bas){vector<u> inv(256,0);int n=bas.size();vector<u> r(256,~0u);for(u v=0;v<(1u<<n);v++){b s=0;for(int k=0;k<n;k++)if(v>>k&1)s^=bas[k];r[s]=v;}return r;};
  b affi[256];for(int i=0;i<256;i++)affi[affl(i)]=i;
  int best=1e9;time_t t0=time(0);map<string,int> tried;
  while(time(0)-t0<secs){
    C c=cs[rng()%cs.size()];b q[4];for(int k=0;k<4;k++)q[k]=c.z.q[c.o[k]];
    // q[0]=f1e1,q[1]=f1e2,q[2]=f2e1,q[3]=f2e2; normalise e1=1?  f1=q0/e1
    b e1=1,e2=M[q[1]][INV[q[0]]],f1=q[0],f2=q[2];
    // a, b coordinates also use a basis f',e' : any scaling of f by g16, independent
    b Y1=1+rng()%255,Y2=1+rng()%255;bool bad=false;b r=M[Y1][INV[Y2]];if(pw(r,16)==r)continue;
    // a,b in basis (f,e) scaled absorbed into Y1,Y2
    vector<b> bas;b qq[4]={M[f1][e1],M[f1][e2],M[f2][e1],M[f2][e2]};
    for(int k=0;k<4;k++)bas.push_back(M[Y1][qq[k]]);for(int k=0;k<4;k++)bas.push_back(M[Y2][qq[k]]);
    auto co=coord(bas);
    // input bit forms: coordinate k as mask over input bits
    auto pre=[&](int i)->b{b x=1<<i;return inverse?affi[x]:x;};
    u cf[8]={0};for(int i=0;i<8;i++){u v=co[pre(i)];for(int k=0;k<8;k++)if(v>>k&1)cf[k]|=1u<<i;}
    auto forms=[&](u*a,u*o){u A[3][2]={{a[0],a[1]},{a[2],a[3]},{a[0]^a[2],a[1]^a[3]}};for(int i=0;i<3;i++){o[3*i]=A[i][0];o[3*i+1]=A[i][1];o[3*i+2]=A[i][0]^A[i][1];}};
    u fa[9],fb[9];forms(cf,fa);forms(cf+4,fb);
    b Cf[3]={(b)(M[f1][f1]^M[f1][f2]),(b)(M[f2][f2]^M[f1][f2]),M[f1][f2]},Ce[3]={(b)(M[e1][e1]^M[e1][e2]),(b)(M[e2][e2]^M[e1][e2]),M[e1][e2]};
    b cc[9];for(int i=0;i<3;i++)for(int j=0;j<3;j++)cc[3*i+j]=M[Cf[i]][Ce[j]];
    auto conj=[&](b x){return pw(x,16);};
    b tr=M[Y1][conj(Y2)]^M[Y2][conj(Y1)];
    auto cp=coord(vector<b>(c.z.p,c.z.p+4));
    u pt[4]={0};for(int k=0;k<9;k++){u v=cp[M[cc[k]][tr]];for(int l=0;l<4;l++)if(v>>l&1)pt[l]|=1u<<k;}
    u lt[4]={0};for(int i=0;i<8;i++){u v=co[pre(i)];b x=0;b aa=0,bb=0;for(int k=0;k<4;k++){if(v>>k&1)aa^=qq[k];if(v>>(k+4)&1)bb^=qq[k];}
      b n=M[M[aa][aa]][M[Y1][conj(Y1)]]^M[M[bb][bb]][M[Y2][conj(Y2)]];u w=cp[n];for(int l=0;l<4;l++)if(w>>l&1)lt[l]|=1u<<i;}
    vector<u>UT(fa,fa+9);UT.insert(UT.end(),fb,fb+9);UT.insert(UT.end(),lt,lt+4);
    u bt[8]={0};for(int k=0;k<18;k++){b v=M[cc[k%9]][conj(k<9?Y1:Y2)];if(!inverse)v=affl(v);for(int l=0;l<8;l++)if(v>>l&1)bt[l]|=1u<<k;}
    vector<Op>ou,ob,op;int cu=99;for(int it=0;it<2;it++){vector<Op>o;int x=lin8(UT,inverse?26:25,o);if(x<cu){cu=x;ou=o;}}
    if(cu>(inverse?24:24))continue;
    int cpn=99;for(int it=0;it<6;it++){vector<Op>o;int x=linN(9,vector<u>(pt,pt+4),14,o);if(x<cpn){cpn=x;op=o;}}
    if(cpn>11)continue;
    int cb=99;for(int it=0;it<4;it++){vector<Op>o;int x=linN(18,vector<u>(bt,bt+8),33,o);if(x<cb){cb=x;ob=o;}}
    int tot=cu+cpn+4+16+5+27+cb;
    if(tot<best){best=tot;printf("total %d U %d P %d B %d\n",tot,cu,cpn,cb);
      printf("seedinfo inverse=%d Y1=%02x Y2=%02x f1=%02x f2=%02x e2=%02x o=%d%d%d%d\n",inverse,Y1,Y2,f1,f2,e2,c.o[0],c.o[1],c.o[2],c.o[3]);
      auto pr=[&](const char*n,vector<u>t){printf("%s",n);for(u x:t)printf(" %x",x);puts("");};
      pr("UT",UT);pr("PT",vector<u>(pt,pt+4));pr("BT",vector<u>(bt,bt+8));
      auto po=[&](const char*n,vector<Op>&o){printf("%s",n);for(auto&x:o)printf(" %d+%d",x.a,x.c);puts("");};
      po("U",ou);po("P",op);po("B",ob);fflush(stdout);}
  }
}
