// Orders and allocates a straight-line program to R two-operand registers with separate loads and
// stores (no memory operands), by annealing over the order and over "destroy" hints, with a
// farthest-next-use allocator. Input (stdin): lines
//  i v r|m      initial value v in a register / in memory (a slot)
//  o v r|m|a    output v wanted in a register / in memory / anywhere
//  g op d a b   gate: X xor, A and, U d=f(a) non-destructive, D d=f(a) in place (b = -1)
#include <bits/stdc++.h>
using namespace std;
struct G{char op;int d,a,b;};
static vector<G> g;static int R;static mt19937 rng;
static vector<pair<int,char>> ins,outs;
static int dirtyPen;
struct Ev{int cost;};
static bool tr=false;static vector<string> code;
const int INF=100000;
static int eval(const vector<int>&o,const vector<uint8_t>&h,const vector<uint8_t>&ev){
  int n=o.size();static int usesBuf[512][24];static int cnt[512],ptr[512];
  static bool mem[512];static int regOf[512];int holder[16];
  memset(cnt,0,sizeof cnt);memset(ptr,0,sizeof ptr);memset(mem,0,sizeof mem);memset(regOf,-1,sizeof regOf);
  for(int i=0;i<n;i++){auto&e=g[o[i]];usesBuf[e.a][cnt[e.a]++]=i;if(e.b>=0&&e.b!=e.a)usesBuf[e.b][cnt[e.b]++]=i;}
  static char ow[512];memset(ow,0,sizeof ow);
  for(auto&p:outs){ow[p.first]=p.second;if(p.second!='m')usesBuf[p.first][cnt[p.first]++]=p.second=='r'?INF:INF+1000;else usesBuf[p.first][cnt[p.first]++]=INF+500;}
  for(int r=0;r<16;r++)holder[r]=-1;
  int nr=0;for(auto&p:ins){if(p.second=='r'){holder[nr]=p.first;regOf[p.first]=nr++;}else mem[p.first]=true;}
  int c=0;
  auto nx=[&](int v,int i){while(ptr[v]<cnt[v]&&usesBuf[v][ptr[v]]<i)ptr[v]++;return ptr[v]<cnt[v]?usesBuf[v][ptr[v]]:(INF*10);};
  auto E=[&](const char*s,int a,int b){if(tr){char t[64];snprintf(t,64,"%s %d %d",s,a,b);code.push_back(t);}};
  for(int i=0;i<n;i++){
    auto&e=g[o[i]];
    int hint=h[o[i]];
    auto freeReg=[&](int k1,int k2)->int{
      for(int r=0;r<R;r++)if(holder[r]<0)return r;
      // dead (no future use)
      int br=-1;double bs=-1;
      for(int r=0;r<R;r++){int v=holder[r];if(v==k1||v==k2)continue;int x=nx(v,i);
        double s;
        if(x>=INF*10)s=1e9;
        else if(x==INF+1000) s=mem[v]?5e8:4e5; // output anywhere
        else if(x==INF+500) s=mem[v]?5e8:4e5;
        else {s=x-i+ (mem[v]?dirtyPen*0.25*(1):0);s+=ev[v%256]*0.5;}
        if(s>bs){bs=s;br=r;}}
      int v=holder[br];
      if(bs<1e9&&!mem[v]){mem[v]=true;c++;E("st",v,br);}
      regOf[v]=-1;holder[br]=-1;return br;};
    auto ensure=[&](int v,int k)->int{ if(regOf[v]>=0)return regOf[v];
      int r=freeReg(v,k);holder[r]=v;regOf[v]=r;c++;E("ld",r,v);return r;};
    auto deadAfter=[&](int v){return nx(v,i+1);};
    if(e.op=='U'){
      int ra=ensure(e.a,-1);
      // ptr moves forward only, so compute next use after i last
      int na;{int p=ptr[e.a];while(p<cnt[e.a]&&usesBuf[e.a][p]<i+1)p++;na=p<cnt[e.a]?usesBuf[e.a][p]:INF*10;}
      int rd;
      bool dead=na>=INF*10||(na>=INF&&mem[e.a]&&na!=INF);
      if(dead){rd=ra;holder[ra]=-1;regOf[e.a]=-1;}
      else rd=freeReg(e.a,-1);
      holder[rd]=e.d;regOf[e.d]=rd;c++;E(("U"+to_string(o[i])).c_str(),rd,ra);
    } else {
      auto na=[&](int v){int p=ptr[v];while(p<cnt[v]&&usesBuf[v][p]<i+1)p++;return p<cnt[v]?usesBuf[v][p]:INF*10;};
      int A=e.a,B=e.b;
      // choose operand to destroy
      auto deadv=[&](int v){int x=na(v);return x>=INF*10||(x>INF&&mem[v]);};
      int p=-1;
      if(e.op=='D'){
        if(deadv(A)){int ra=ensure(A,-1);p=A;(void)ra;}
        else if(mem[A]&&(hint&1)){ensure(A,-1);p=A;}
        else if(regOf[A]<0){ensure(A,-1);p=A;}
        else {int ra=regOf[A];int rd=freeReg(A,-1);c++;E("mv",rd,ra);holder[rd]=e.d;regOf[e.d]=rd;c++;E(("D"+to_string(o[i])).c_str(),rd,rd);continue;}
        int ra=regOf[A];holder[ra]=e.d;regOf[A]=-1;regOf[e.d]=ra;c++;E(("D"+to_string(o[i])).c_str(),ra,ra);continue;
      }
      bool da=deadv(A),db=deadv(B);
      // ensure operands; an operand only in memory can be loaded as the destroyed copy
      bool ia=regOf[A]>=0,ib=regOf[B]>=0;
      if(da&&db){p=(hint&2)?B:A;}
      else if(da)p=A;else if(db)p=B;
      else if(!ia&&!ib)p=(hint&1)?A:B;
      else if(!ia)p=A;else if(!ib)p=B;
      else { // both in registers, both live
        bool ma=mem[A],mb=mem[B];
        if((hint&1)&&(ma||mb)){ if(ma&&mb)p=na(A)>na(B)?A:B; else p=ma?A:B;}
      }
      int q=p==A?B:A;
      if(p>=0){
        // dead but in memory only and other dead in register: prefer in-register
        if(da&&db&&p==A&&!ia&&ib)swap(p,q);
        else if(da&&db&&p==B&&!ib&&ia)swap(p,q);
        else if(da!=db){ // dead one in memory while live one in reg etc: still fine
        }
        ensure(q,p);int rp=ensure(p,q);int rq=regOf[q];
        holder[rp]=e.d;regOf[p]=-1;
        c++;E(e.op=='X'?"px":"an",rp,rq);
        if(deadv(q)){holder[rq]=-1;regOf[q]=-1;}
        regOf[e.d]=rp;
      } else {
        int ra=regOf[A],rb=regOf[B];int rd=freeReg(A,B);
        c+=2;E("mv",rd,ra);E(e.op=='X'?"px":"an",rd,rb);holder[rd]=e.d;regOf[e.d]=rd;
      }
      continue;
    }
  }
  for(auto&p:outs){int v=p.first;if(p.second=='m'&&!mem[v]){c++;E("st",v,regOf[v]);}
    if(p.second=='r'&&regOf[v]<0){c++;E("ldout",v,v);}}
  if(tr)for(auto&p:outs)if(regOf[p.first]>=0)E("at",p.first,regOf[p.first]);
  return c;}
int main(int ac,char**av){
  string fn=av[1];R=atoi(av[2]);rng.seed(atoi(av[3]));double secs=atof(av[4]);string outfn=av[5];
  ifstream f(fn);string t;while(f>>t){if(t=="i"){int v;char c;f>>v>>c;ins.push_back({v,c});}else if(t=="o"){int v;char c;f>>v>>c;outs.push_back({v,c});}
    else if(t=="g"){G e;string op;f>>op>>e.d>>e.a>>e.b;e.op=op[0];g.push_back(e);}}
  int n=g.size();vector<int>o(n);iota(o.begin(),o.end(),0);
  {// random topological restart
    vector<int> oo;vector<char> done(512,0);for(auto&p:ins)done[p.first]=1;vector<int> rem=o;
    while(rem.size()){vector<int> rdy;for(int x:rem)if(done[g[x].a]&&(g[x].b<0||done[g[x].b]))rdy.push_back(x);
      int x=rdy[rng()%rdy.size()];oo.push_back(x);done[g[x].d]=1;rem.erase(find(rem.begin(),rem.end(),x));}
    if(ac>6&&av[6][0]=='r')o=oo;}
  vector<uint8_t>h(n,0);vector<uint8_t>ev(256,0);dirtyPen=8;
  int cur=eval(o,h,ev),bc=cur;auto bo=o;auto bh=h;auto bev=ev;int bdp=dirtyPen;
  auto t0=chrono::steady_clock::now();double T=4;long it=0;
  while(true){
    if((++it&511)==0){double fr=chrono::duration<double>(chrono::steady_clock::now()-t0).count()/secs;if(fr>1)break;T=3.0*pow(1-fr,1.5)+0.12;}
    int k=rng()%16;
    if(k<11){
      int i=rng()%n;int e=o[i];int lo=i,hi=i;int span=1+rng()%40;
      while(lo>0&&i-lo<span&&g[o[lo-1]].d!=g[e].a&&g[o[lo-1]].d!=g[e].b)lo--;
      while(hi<n-1&&hi-i<span&&g[o[hi+1]].a!=g[e].d&&g[o[hi+1]].b!=g[e].d)hi++;
      if(lo==hi)continue;int j=lo+rng()%(hi-lo+1);if(i==j)continue;
      if(j<i)rotate(o.begin()+j,o.begin()+i,o.begin()+i+1);else rotate(o.begin()+i,o.begin()+i+1,o.begin()+j+1);
      int nc=eval(o,h,ev);
      if(nc<=cur||exp((cur-nc)/T)*4294967296.0>rng()){cur=nc;}
      else{ if(j<i)rotate(o.begin()+j,o.begin()+j+1,o.begin()+i+1);else rotate(o.begin()+i,o.begin()+j,o.begin()+j+1);}
    } else if(k<14){int i=rng()%n;uint8_t old=h[i];h[i]=rng()&3;int nc=eval(o,h,ev);if(nc<=cur||exp((cur-nc)/T)*4294967296.0>rng())cur=nc;else h[i]=old;}
    else if(k==14){int v=rng()%256;uint8_t old=ev[v];ev[v]=rng()%40;if(rng()&1)ev[v]=0;int nc=eval(o,h,ev);if(nc<=cur||exp((cur-nc)/T)*4294967296.0>rng())cur=nc;else ev[v]=old;}
    else {int old=dirtyPen;dirtyPen=rng()%80;int nc=eval(o,h,ev);if(nc<=cur||exp((cur-nc)/T)*4294967296.0>rng())cur=nc;else dirtyPen=old;}
    if(cur<bc){bc=cur;bo=o;bh=h;bev=ev;bdp=dirtyPen;}
  }
  dirtyPen=bdp;tr=true;int fc=eval(bo,bh,bev);ofstream of(outfn+"."+to_string(fc));for(auto&s:code)of<<s<<"\n";
  int ld=0,st=0,mv=0;for(auto&s:code){ld+=s.substr(0,2)=="ld";st+=s.substr(0,2)=="st";mv+=s.substr(0,2)=="mv";}
  printf("%s R=%d seed=%s cost %d (check %d) ld %d st %d mv %d its %ld\n",fn.c_str(),R,av[3],bc,fc,ld,st,mv,it);
}
