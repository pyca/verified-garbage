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

int main(int argc,char**argv){rng.seed(atoi(argv[1]));int secs=atoi(argv[2]);int limU=atoi(argv[3]),limB=atoi(argv[4]);
 for(int i=0;i<256;i++)for(int j=0;j<256;j++)M[i][j]=mulf(i,j);
 vector<u> UT,BT;u x;for(int i=0;i<22;i++){cin>>hex>>x;UT.push_back(x);}for(int i=0;i<8;i++){cin>>hex>>x;BT.push_back(x);}
 time_t t0=time(0);set<string> seen;map<int,int> hu,hb;
 while(time(0)-t0<secs){
  for(int k=0;k<200;k++){vector<Op>o;int c=lin8(UT,limU,o);if(c<99){hu[c]++;if(c<=limU){string s="U";for(auto&y:o)s+=" "+to_string(y.a)+"+"+to_string(y.c);if(seen.insert(s).second)puts(s.c_str());}}}
  for(int k=0;k<20;k++){vector<Op>o;int c=linN(18,BT,limB,o);if(c<99){hb[c]++;if(c<=limB){string s="B";for(auto&y:o)s+=" "+to_string(y.a)+"+"+to_string(y.c);if(seen.insert(s).second)puts(s.c_str());}}}
  fflush(stdout);}
 for(auto&p:hu)fprintf(stderr,"U %d: %d\n",p.first,p.second);for(auto&p:hb)fprintf(stderr,"B %d: %d\n",p.first,p.second);}
