// Order (and re-associate) a circuit's gates for few loads and stores on a three-operand machine.
// stdin: gates "op dst a b" (0/2 xor, 1 and; inputs < 8, outputs 200..207). args: R seed secs
#include <bits/stdc++.h>
using namespace std;struct G{int op,d,a,b;};int R;mt19937 rng;typedef vector<G> C;
static int usesA[256][64],nu[256],ptr_[256];
int cost(const C&g){int n=g.size();memset(nu,0,sizeof nu);memset(ptr_,0,sizeof ptr_);
 for(int i=0;i<n;i++){usesA[g[i].a][nu[g[i].a]++]=i;usesA[g[i].b][nu[g[i].b]++]=i;}
 for(int j=0;j<8;j++)usesA[200+j][nu[200+j]++]=10000;
 int reg[32],nr=0;bool in[256]={},sl[256]={};int c=0;for(int i=0;i<8;i++){reg[nr++]=i;in[i]=1;}
 auto nx=[&](int v,int i){while(ptr_[v]<nu[v]&&usesA[v][ptr_[v]]<=i)ptr_[v]++;return ptr_[v]<nu[v]?usesA[v][ptr_[v]]:20000;};
 auto rm=[&](int v){for(int k=0;k<nr;k++)if(reg[k]==v){reg[k]=reg[--nr];break;}in[v]=0;};
 auto room=[&](int i,int a,int b){if(nr<R)return;int bv=-1,bn=-1;for(int k=0;k<nr;k++){int v=reg[k];if(v==a||v==b)continue;int x=nx(v,i);x=2*x+(sl[v]?1:0);if(x>bn){bn=x;bv=v;}}
   rm(bv);if(!sl[bv]&&bn/2<20000){sl[bv]=1;c++;}};
 for(int i=0;i<n;i++){const G&e=g[i];
  for(int v:{e.a,e.b})if(!in[v]){room(i-1,e.a,e.b);in[v]=1;reg[nr++]=v;c++;}
  if(nx(e.a,i)>=20000)rm(e.a);if(nx(e.b,i)>=20000&&in[e.b])rm(e.b);
  room(i,e.a,e.b);in[e.d]=1;reg[nr++]=e.d;}
 for(int j=0;j<8;j++)if(!in[200+j])c++;
 return c;}
int main(int c,char**v){R=atoi(v[1]);rng.seed(atoi(v[2]));double secs=atof(v[3]);C g;int op,d,a,b;while(scanf("%d %d %d %d",&op,&d,&a,&b)==4)g.push_back({op,d,a,b});
 int n=g.size();int cur=cost(g),bc=cur;C best=g;auto t0=chrono::steady_clock::now();double T=3;long it=0;
 while(true){if((++it&255)==0){double f=chrono::duration<double>(chrono::steady_clock::now()-t0).count()/secs;if(f>1)break;T=1.5*(1-f)*(1-f)+0.08;}
  C p=g;
  if(rng()%5){int i=rng()%n;G e=p[i];int lo=0,hi=n-1;
   for(int k=i-1;k>=0;k--)if(p[k].d==e.a||p[k].d==e.b){lo=k+1;break;}
   for(int k=i+1;k<n;k++)if(p[k].a==e.d||p[k].b==e.d){hi=k-1;break;}
   if(hi<=lo)continue;int j=lo+rng()%(hi-lo+1);if(j==i)continue;
   if(j>i)rotate(p.begin()+i,p.begin()+i+1,p.begin()+j+1);else rotate(p.begin()+j,p.begin()+i,p.begin()+i+1);
  }else{ // re-associate: d = x^y, x = p^q used once -> x' = p^y, d = x'^q
   int i=rng()%n;if(p[i].op==1)continue;bool sw=rng()&1;int x=sw?p[i].b:p[i].a,y=sw?p[i].a:p[i].b;if(x<8||x>=200)continue;
   int k=-1;for(int m=0;m<n;m++)if(p[m].d==x)k=m;if(k<0||p[k].op==1)continue;int cnt=0;for(auto&e:p)cnt+=(e.a==x)+(e.b==x);if(cnt!=1)continue;
   bool s2=rng()&1;int P=s2?p[k].b:p[k].a,Q=s2?p[k].a:p[k].b;
   if(P==y)continue;
   // y must be available at k: else move gate k to just before i
   G gk={0,x,P,y};G gi={0,p[i].d,x,Q};p[i]=gi;p.erase(p.begin()+k);p.insert(p.begin()+(i-1),gk);
  }
  int nc=cost(p);if(nc<=cur||exp((cur-nc)/T)*4294967296.0>rng()){g=p;cur=nc;if(nc<bc){bc=nc;best=g;}}}
 fprintf(stderr,"R=%d cost %d its %ld\n",R,bc,it);printf("# %d\n",bc);for(auto&x:best)printf("%d %d %d %d\n",x.op,x.d,x.a,x.b);}
