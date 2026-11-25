// As sched3, with every XOR identity between the circuit's values: an XOR gate may use any two
// registers whose sum it is, a value needed again may be recomputed from two registers rather than
// loaded, and moves change a gate's operands to another pair with the same sum.
// stdin: gates "op dst a b" (0 xor, 1 and; inputs < 8, outputs 200..207). args: R seed secs inv
#include <bits/stdc++.h>
using namespace std;struct G{int op,d,a,b;};int R;mt19937 rng;typedef vector<G> C;typedef unsigned long long u64;
static u64 tt[256];static bool known[256];static u64 inp[8];
static int usesA[256][64],nu[256],ptr_[256];
static unordered_map<u64,int> byt;
struct Ev{int k,d,a,b;};// k 0 xor 1 and 2 store 3 load
static vector<Ev> evs;static bool rec=false;
int cost(const C&g0){static C g;g.clear();
 // live gates
 {static bool need[256];memset(need,0,sizeof need);for(int j=0;j<8;j++)need[200+j]=1;for(int i=(int)g0.size()-1;i>=0;i--)if(need[g0[i].d]){need[g0[i].a]=need[g0[i].b]=1;g.push_back(g0[i]);}reverse(g.begin(),g.end());}
 int n=g.size();memset(nu,0,sizeof nu);memset(ptr_,0,sizeof ptr_);
 for(int i=0;i<n;i++){usesA[g[i].a][nu[g[i].a]++]=i;usesA[g[i].b][nu[g[i].b]++]=i;if(nu[g[i].a]>60||nu[g[i].b]>60)return 9999;}
 for(int j=0;j<8;j++)usesA[200+j][nu[200+j]++]=10000;
 int reg[32],nr=0;bool in[256]={},sl[256]={},ev[256]={};int c=n;for(int i=0;i<8;i++){reg[nr++]=i;in[i]=1;}
 if(rec)evs.clear();
 auto nx=[&](int v,int i){while(ptr_[v]<nu[v]&&usesA[v][ptr_[v]]<=i)ptr_[v]++;return ptr_[v]<nu[v]?usesA[v][ptr_[v]]:20000;};
 auto rm=[&](int v){for(int k=0;k<nr;k++)if(reg[k]==v){reg[k]=reg[--nr];break;}in[v]=0;};
 static int evictAt[256];
 auto room=[&](int i,int a,int b){if(nr<R)return;int bv=-1,bn=-1;for(int k=0;k<nr;k++){int v=reg[k];if(v==a||v==b)continue;int x=nx(v,i);x=2*x+(sl[v]?1:0);if(x>bn){bn=x;bv=v;}}
   if(rec)evs.push_back({4,bv,0,0});rm(bv);ev[bv]=1;};
 auto findpair=[&](int v,int&x,int&y){u64 t=tt[v];for(int p=0;p<nr;p++)for(int q=0;q<p;q++)if((tt[reg[p]]^tt[reg[q]])==t){x=reg[p];y=reg[q];return true;}return false;};
 auto bring=[&](int v,int i,int a,int b){// make v available
   int x,y;
   if(findpair(v,x,y)){if(nr>=R){ // need room, keep x,y if evicted fine since op reads first
       int px=x,py=y;room(i-1,a,b);(void)px;(void)py;}
     if(rec)evs.push_back({0,v,x,y});c++;}
   else{if(!sl[v]){sl[v]=1;c++;}room(i-1,a,b);c++;if(rec)evs.push_back({3,v,0,0});}
   in[v]=1;reg[nr++]=v;};
 for(int i=0;i<n;i++){const G&e=g[i];
  int x,y;bool done=false;
  if(e.op!=1&&(!in[e.a]||!in[e.b])&&findpair(e.d,x,y)){
    if(nx(e.a,i)>=20000&&in[e.a])rm(e.a);if(nx(e.b,i)>=20000&&in[e.b])rm(e.b);
    room(i,-1,-1);if(rec)evs.push_back({0,e.d,x,y});in[e.d]=1;reg[nr++]=e.d;done=true;}
  if(done)continue;
  for(int v:{e.a,e.b})if(!in[v])bring(v,i,e.a,e.b);
  if(nx(e.a,i)>=20000)rm(e.a);if(nx(e.b,i)>=20000&&in[e.b])rm(e.b);
  room(i,e.a,e.b);if(rec)evs.push_back({e.op==1?1:0,e.d,e.a,e.b});in[e.d]=1;reg[nr++]=e.d;}
 for(int j=0;j<8;j++)if(!in[200+j])c+=2;
 return c;}
int main(int argc,char**v){R=atoi(v[1]);rng.seed(atoi(v[2]));double secs=atof(v[3]);C g;int op,d,a,b;char line[200];while(fgets(line,200,stdin)){if(line[0]=='#')continue;if(sscanf(line,"%d %d %d %d",&op,&d,&a,&b)==4)g.push_back({op,d,a,b});}
 mt19937_64 r64(12345);int pos[64];{vector<int>p(256);iota(p.begin(),p.end(),0);shuffle(p.begin(),p.end(),r64);for(int i=0;i<64;i++)pos[i]=p[i];}
 for(int j=0;j<8;j++){tt[j]=0;for(int i=0;i<64;i++)if(pos[i]>>j&1)tt[j]|=1ull<<i;}
 for(auto&e:g)tt[e.d]=e.op==1?(tt[e.a]&tt[e.b]):(tt[e.a]^tt[e.b]);
 vector<int> sig;for(int i=0;i<8;i++)sig.push_back(i);for(auto&e:g)sig.push_back(e.d);
 unordered_map<u64,vector<int>> by;for(int s:sig)by[tt[s]].push_back(s);
 // alternatives for each xor gate
 map<int,vector<pair<int,int>>> alt;for(auto&e:g)if(e.op!=1)for(size_t i=0;i<sig.size();i++)for(size_t j=0;j<i;j++)if(sig[i]!=e.d&&sig[j]!=e.d&&(tt[sig[i]]^tt[sig[j]])==tt[e.d])alt[e.d].push_back({sig[i],sig[j]});
 size_t na=0;for(auto&x:alt)na+=x.second.size();fprintf(stderr,"alternatives %zu\n",na);
 int cur=cost(g),bc=cur;C best=g;auto t0=chrono::steady_clock::now();double T=3;long it=0;
 while(true){if((++it&63)==0){double f=chrono::duration<double>(chrono::steady_clock::now()-t0).count()/secs;if(f>1)break;T=1.2*(1-f)*(1-f)+0.1;}
  C p=g;int n=p.size();int m=rng()%8;
  if(m<6){int i=rng()%n;G e=p[i];int lo=0,hi=n-1;
   for(int k=i-1;k>=0;k--)if(p[k].d==e.a||p[k].d==e.b){lo=k+1;break;}
   for(int k=i+1;k<n;k++)if(p[k].a==e.d||p[k].b==e.d){hi=k-1;break;}
   if(hi<=lo)continue;int j=lo+rng()%(hi-lo+1);if(j==i)continue;
   if(j>i)rotate(p.begin()+i,p.begin()+i+1,p.begin()+j+1);else rotate(p.begin()+j,p.begin()+i,p.begin()+i+1);
  }else{int i=rng()%n;if(p[i].op==1)continue;auto&al=alt[p[i].d];if(al.size()<2)continue;auto q=al[rng()%al.size()];
   if(q.first==p[i].a&&q.second==p[i].b)continue;
   // operands must come earlier; if later but not dependent on d, move them: only accept if earlier or can toposort
   p[i].a=q.first;p[i].b=q.second;
   // stable toposort
   vector<int> where(256,-1);for(int k=0;k<n;k++)where[p[k].d]=k;vector<char> st(n,0);C o;o.reserve(n);bool cyc=false;
   function<void(int)> vis=[&](int k){if(st[k]==2||cyc)return;if(st[k]==1){cyc=true;return;}st[k]=1;for(int x:{p[k].a,p[k].b})if(where[x]>=0)vis(where[x]);st[k]=2;o.push_back(p[k]);};
   for(int k=0;k<n&&!cyc;k++)vis(k);if(cyc)continue;p=o;}
  int nc=cost(p);if(nc<=cur||exp((cur-nc)/T)*4294967296.0>rng()){g=p;cur=nc;if(nc<bc){bc=nc;best=g;}}}
 rec=true;int fc=cost(best);
 fprintf(stderr,"R=%d total %d its %ld\n",R,fc,it);printf("# %d\n",fc);for(auto&x:evs)printf("%d %d %d %d\n",x.k,x.d,x.a,x.b);}
