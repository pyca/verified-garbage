// Order a circuit's gates to make the two-operand register allocation (Belady, as Alloc.lean's) short.
// stdin: gates "op dst a b" (ints; inputs <8, outputs 200..207). args: registers seed seconds
#include <bits/stdc++.h>
using namespace std;struct G{int op,d,a,b;};vector<G> g;int R;mt19937 rng;
int cost(const vector<int>&o,int memop){int n=o.size();static vector<int> uses[256];for(auto&u:uses)u.clear();
 for(int i=0;i<n;i++){uses[g[o[i]].a].push_back(i);uses[g[o[i]].b].push_back(i);}for(int j=0;j<8;j++)uses[200+j].push_back(10000);
 int reg[256],slot[256];memset(reg,0,sizeof reg);memset(slot,0,sizeof slot);int used=8,c=0;vector<int> live;for(int i=0;i<8;i++){reg[i]=1;live.push_back(i);}
 static int ptr[256];memset(ptr,0,sizeof ptr);
 auto nx=[&](int v,int i){auto&u=uses[v];while(ptr[v]<(int)u.size()&&u[ptr[v]]<=i)ptr[v]++;return ptr[v]<(int)u.size()?u[ptr[v]]:20000;};
 auto need=[&](int i,int a,int b){if(used<R){used++;return;}int bv=-1,bn=-1;for(int v:live)if(reg[v]&&v!=a&&v!=b){int x=nx(v,i);if(x>bn){bn=x;bv=v;}}
   reg[bv]=0;if(!slot[bv]){slot[bv]=1;c++;}};
 for(int i=0;i<n;i++){G&e=g[o[i]];int a=e.a,b=e.b;bool ad=nx(a,i)==20000,bd=nx(b,i)==20000;
  if(!memop){for(int v:{a,b})if(!reg[v]){need(i-1,a,b);reg[v]=1;c++;}}
  int p=a,q=b;bool in=false;if(ad&&reg[a])in=true;else if(bd&&reg[b]){p=b;q=a;in=true;}
  if(in){c++;reg[p]=0;used--;}else{need(i,a,b);used--; c+=2;}
  if(e.op==2)c++;
  if(ad&&reg[a]){reg[a]=0;used--;}if(bd&&reg[b]){reg[b]=0;used--;}
  reg[e.d]=1;used++;live.push_back(e.d);}
 for(int j=0;j<8;j++)if(!reg[200+j])c++;
 return c;}
int main(int c,char**v){R=atoi(v[1]);rng.seed(atoi(v[2]));int secs=atoi(v[3]);int memop=atoi(v[4]);int op,d,a,b;while(scanf("%d %d %d %d",&op,&d,&a,&b)==4)g.push_back({op,d,a,b});
 int n=g.size();vector<int>o(n),best;iota(o.begin(),o.end(),0);int cur=cost(o,memop),bc=cur;best=o;auto t0=chrono::steady_clock::now();double T=3;long it=0;
 vector<int>pos(256,-1);
 while(true){if((++it&1023)==0){double f=chrono::duration<double>(chrono::steady_clock::now()-t0).count()/secs;if(f>1)break;T=3*(1-f)*(1-f)+0.05;}
  auto p=o;int i=rng()%n;int e=p[i];int lo=0,hi=n-1;
  for(int k=0;k<n;k++){if(k<i&&(g[p[k]].d==g[e].a||g[p[k]].d==g[e].b))lo=k+1;}
  for(int k=n-1;k>i;k--)if(g[p[k]].a==g[e].d||g[p[k]].b==g[e].d)hi=k-1;
  if(hi<=lo)continue;int j=lo+rng()%(hi-lo+1);if(j==i)continue;p.erase(p.begin()+i);p.insert(p.begin()+j,e);
  int nc=cost(p,memop);if(nc<=cur||exp((cur-nc)/T)*4294967296.0>rng()){o=p;cur=nc;if(nc<bc){bc=nc;best=o;}}}
 fprintf(stderr,"R=%d cost %d (from start %d)\n",R,bc,0);for(int x:best)printf("%d %d %d %d\n",g[x].op,g[x].d,g[x].a,g[x].b);}
