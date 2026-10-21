/* Unproven prototypes only. Differential random cases; timings require native i686. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef OPENSSL_REF
#include <openssl/bn.h>
#endif
#define MODES 10
#define DECL(i) extern void proto_mont##i(uint64_t*,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned); \
extern unsigned proto_recover##i(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned)
DECL(0);DECL(1);DECL(2);DECL(3);DECL(4);DECL(5);DECL(6);DECL(7);DECL(8);DECL(9);DECL(10);DECL(11);DECL(12);DECL(13);
typedef void (*montfn)(uint64_t*,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned);
static montfn ms[]={proto_mont0,proto_mont1,proto_mont2,proto_mont3,proto_mont4,proto_mont5,proto_mont6,proto_mont7,proto_mont8,proto_mont9};
typedef unsigned (*recfn)(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
static recfn rs[]={proto_recover0,proto_recover1,proto_recover2,proto_recover3,proto_recover4,proto_recover5,proto_recover6,proto_recover7,proto_recover8,proto_recover9,proto_recover10,proto_recover11,proto_recover12,proto_recover13};
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
static uint32_t rng=1;
static uint32_t rnd(void){rng^=rng<<13;rng^=rng>>17;rng^=rng<<5;return rng;}
static void setup(uint64_t*w,unsigned N,unsigned iv,unsigned a,unsigned b,unsigned adverse){
 uint32_t*p=(uint32_t*)w;
 for(unsigned j=0;j<N;j++){p[j]=rnd();p[a/4+j]=rnd();p[b/4+j]=rnd();}
 p[0]|=1;p[N-1]|=0x80000000u;p[a/4+N-1]&=0x7fffffffu;p[b/4+N-1]&=0x7fffffffu;
 if(adverse<3){for(unsigned j=0;j<N;j++){p[j]=~0u;p[a/4+j]=adverse?~0u:0;p[b/4+j]=adverse?~0u:0;}if(adverse){p[a/4]--;p[b/4]-=2;}}
 uint32_t inv=1;for(unsigned j=0;j<5;j++)inv*=2-p[0]*inv;p[iv/4]=0-inv;
}
static int differential(void){
 unsigned ns[]={1,2,3,4,5,8,16,32,48,64,128},cases=0;
 for(unsigned z=0;z<sizeof(ns)/sizeof(*ns);z++){
  unsigned n=ns[z],N=2*n,iv=4*N+8,a=4*N+32,b=8*N+32,o=12*N+32,s=16*N+64,L=s+12*N+64,wl=L/8;
  uint64_t*w=calloc(wl,8),*ref=calloc(wl,8),*test=calloc(wl,8);
  for(unsigned t=0;t<50;t++){
   for(unsigned j=0;j<wl;j++)w[j]=(uint64_t)rnd()<<32|rnd();setup(w,N,iv,a,b,t);
   for(unsigned alias=0;alias<5;alias++){
    unsigned dest=alias==1||alias==3?a:alias==4?b:o,op=alias<2?a:b;
    memcpy(ref,w,L);ms[0](ref,wl,n,0,iv,s,dest,a,op);
    for(unsigned mode=1;mode<MODES;mode++){
     memcpy(test,w,L);ms[mode](test,wl,n,0,iv,s,dest,a,op);
     if(memcmp((char*)ref+dest,(char*)test+dest,4*N)){printf("DIFF FAIL n=%u case=%u alias=%u mode=%u\n",n,t,alias,mode);return 1;}cases++;
    }
   }
  }free(w);free(ref);free(test);
 }printf("differential_passed=%u\n",cases);return 0;
}
#ifdef OPENSSL_REF
static int kernels(void){
 for(unsigned bits=512;bits<=4096;bits*=2){
  unsigned N=bits/32,n=N/2,iv=4*N+8,a=4*N+32,b=8*N+32,o=12*N+32,s=16*N+64,L=s+12*N+64,wl=L/8;
  uint64_t*w=calloc(wl,8);setup(w,N,iv,a,b,9);
  BN_CTX*ctx=BN_CTX_new();BN_MONT_CTX*mc=BN_MONT_CTX_new();BIGNUM*M=BN_lebin2bn((void*)w,4*N,0),*A=BN_lebin2bn((char*)w+a,4*N,0),*B=BN_lebin2bn((char*)w+b,4*N,0),*O=BN_new();
  if(!BN_MONT_CTX_set(mc,M,ctx))return 2;
  for(unsigned sq=0;sq<2;sq++){
   unsigned op=sq?a:b;unsigned char expect[1024];
   if(!BN_mod_mul_montgomery(O,A,sq?A:B,mc,ctx))return 3;BN_bn2lebinpad(O,expect,4*N);
   for(unsigned round=0;round<3;round++){
    for(unsigned seq=0;seq<MODES+1;seq++){
     unsigned mode=(seq+round)%(MODES+1);double start=now();unsigned reps=0;
     do {for(unsigned j=0;j<32;j++){if(mode<MODES)ms[mode](w,wl,n,0,iv,s,o,a,op);else if(!BN_mod_mul_montgomery(O,A,sq?A:B,mc,ctx))return 3;}reps+=32;}while(now()-start<0.08);
     double ns=(now()-start)*1e9/reps;
     if(mode<MODES&&memcmp(expect,(char*)w+o,4*N)){printf("OPENSSL DIFF bits=%u mode=%u square=%u\n",bits,mode,sq);return 4;}
     printf("kernel,bits=%u,square=%u,round=%u,mode=%u,ns=%.3f,reps=%u\n",bits,sq,round,mode,ns,reps);fflush(stdout);
    }
   }
  }BN_free(M);BN_free(A);BN_free(B);BN_free(O);BN_MONT_CTX_free(mc);BN_CTX_free(ctx);free(w);
 }return 0;
}
#endif
static unsigned readhex(FILE*f,unsigned char*out){char line[4096];if(!fgets(line,sizeof(line),f))exit(2);unsigned len=strcspn(line,"\r\n")/2;for(unsigned j=0;j<len;j++){unsigned x;if(sscanf(line+2*j,"%2x",&x)!=1)exit(2);out[j]=x;}return len;}
static int recoveries(const char*dir){
 unsigned sizes[]={512,1024,2048,3072,4096};
 for(unsigned z=0;z<5;z++){
  unsigned bits=sizes[z];char path[512];snprintf(path,sizeof(path),"%s/key%u.txt",dir,bits);FILE*f=fopen(path,"r");if(!f)return 2;
  unsigned char nb[1024],eb[1024],db[1024],p[MODES][1024],q[MODES][1024];unsigned k=readhex(f,nb),el=readhex(f,eb),dl=readhex(f,db);fclose(f);
  unsigned wl=16*k+32;uint64_t*w=calloc(wl,8);
  for(unsigned round=0;round<3;round++){
   for(unsigned seq=0;seq<MODES;seq++){
    unsigned mode=(seq+round)%MODES;double start=now();unsigned ok=0;
    for(unsigned j=0;j<3;j++)ok=rs[mode](p[mode],k,q[mode],k,nb,k,eb,el,db,dl,w,wl);
    printf("recovery,bits=%u,round=%u,mode=%u,ms=%.4f,ok=%u\n",bits,round,mode,(now()-start)*1000/3,ok);fflush(stdout);if(ok!=1)return 3;
   }
   for(unsigned mode=1;mode<MODES;mode++)if(memcmp(p[0],p[mode],k)||memcmp(q[0],q[mode],k)){printf("RECOVERY DIFF bits=%u mode=%u\n",bits,mode);return 4;}
  }free(w);
 }return 0;
}
/* Unproven constant-schedule 30-divstep batches, matching Proof.Divstep.W32. */
#define BW 260
static void add_row(uint32_t*out,unsigned outn,const uint32_t*a,unsigned n,uint32_t c){
 uint64_t carry=0;for(unsigned i=0;i<n;i++){uint64_t v=(uint64_t)a[i]*c+out[i]+carry;out[i]=(uint32_t)v;carry=v>>32;}
 for(unsigned i=n;i<outn;i++){uint64_t v=(uint64_t)out[i]+carry;out[i]=(uint32_t)v;carry=v>>32;}
}
static void subtract_shifted(uint32_t*out,unsigned outn,const uint32_t*a,unsigned n,uint32_t mask){
 uint64_t borrow=0;for(unsigned i=1;i<outn;i++){uint32_t x=i-1<n?a[i-1]&mask:0;uint64_t v=(uint64_t)out[i]-x-borrow;out[i]=(uint32_t)v;borrow=v>>63;}
}
static void lin(uint32_t*out,unsigned outn,const uint32_t*a,const uint32_t*b,unsigned n,uint32_t u,uint32_t v){
 memset(out,0,4*outn);add_row(out,outn,a,n,u);add_row(out,outn,b,n,v);subtract_shifted(out,outn,a,n,0-(u>>31));subtract_shifted(out,outn,b,n,0-(v>>31));
}
static void shift30(uint32_t*out,const uint32_t*a,unsigned n){
 for(unsigned i=0;i+1<n;i++)out[i]=(a[i]>>30)|(a[i+1]<<2);
 out[n-1]=(a[n-1]>>30)|((0-(a[n-1]>>31))<<2);
}
static void norm(uint32_t*out,const uint32_t*a,const uint32_t*m,unsigned n){
 uint32_t v[BW],t[BW];uint32_t mask=0-(a[n]>>31);uint64_t carry=0,borrow=0;
 for(unsigned i=0;i<=n;i++){uint64_t z=(uint64_t)a[i]+(i<n?(m[i]&mask):0)+carry;v[i]=(uint32_t)z;carry=z>>32;}
 for(unsigned i=0;i<=n;i++){uint64_t z=(uint64_t)v[i]-(i<n?m[i]:0)-borrow;t[i]=(uint32_t)z;borrow=z>>63;}
 mask=0-(uint32_t)borrow;for(unsigned i=0;i<n;i++)out[i]=(v[i]&mask)|(t[i]&~mask);
}
static void mred(uint32_t*out,uint32_t*a,const uint32_t*m,unsigned n,uint32_t minv){
 uint32_t k=a[0]*minv;add_row(a,n+2,m,n,k);norm(out,a+1,m,n);
}
static void mod_input(uint32_t*out,const uint32_t*a,const uint32_t*m,unsigned n){
 uint32_t v[BW],t[BW];memset(v,0,4*(n+1));
 for(unsigned k=n*32;k-->0;){uint32_t c=(a[k/32]>>(k%32))&1;for(unsigned j=0;j<=n;j++){uint32_t nc=v[j]>>31;v[j]=(v[j]<<1)|c;c=nc;}
  uint64_t borrow=0;for(unsigned j=0;j<=n;j++){uint64_t z=(uint64_t)v[j]-(j<n?m[j]:0)-borrow;t[j]=(uint32_t)z;borrow=z>>63;}
  uint32_t mask=0-(uint32_t)borrow;for(unsigned j=0;j<=n;j++)v[j]=(v[j]&mask)|(t[j]&~mask);
 }memcpy(out,v,n*4);
}
static void twice(uint32_t*a,const uint32_t*m,unsigned n){
 uint32_t v[BW],t[BW];uint64_t carry=0,borrow=0;
 for(unsigned j=0;j<n;j++){uint64_t z=(uint64_t)a[j]*2+carry;v[j]=(uint32_t)z;carry=z>>32;}v[n]=(uint32_t)carry;
 for(unsigned j=0;j<=n;j++){uint64_t z=(uint64_t)v[j]-(j<n?m[j]:0)-borrow;t[j]=(uint32_t)z;borrow=z>>63;}
 uint32_t mask=0-(uint32_t)borrow;for(unsigned j=0;j<n;j++)a[j]=(v[j]&mask)|(t[j]&~mask);
}
static void batch_inverse_ws(uint64_t*ws,unsigned fulln,unsigned n){
 unsigned stride=4*(fulln+2);unsigned char*base=(unsigned char*)ws+160;
 uint32_t *input=(uint32_t*)base,*mod=(uint32_t*)(base+8*stride);
 uint32_t m[BW],f[BW],g[BW],a[BW],b[BW],nf[BW],ng[BW],na[BW],nb[BW],t[BW];
 memcpy(m,mod,n*4);memset(f,0,4*(n+1));memset(g,0,4*(n+1));memcpy(f,m,n*4);
 uint64_t oddcarry=0;uint32_t oddmask=0-((input[0]&1)^1);for(unsigned j=0;j<n;j++){uint64_t z=(uint64_t)input[j]+(m[j]&oddmask)+oddcarry;g[j]=(uint32_t)z;oddcarry=z>>32;}g[n]=(uint32_t)oddcarry;memset(a,0,n*4);memset(b,0,n*4);
 uint32_t nz=m[0]^1;for(unsigned j=1;j<n;j++)nz|=m[j];b[0]=(nz|(0-nz))>>31;
 uint32_t minv=1;for(unsigned i=0;i<5;i++)minv*=2-m[0]*minv;minv=0-minv;
 unsigned batches=3*(n+1);uint32_t delta=1;
 for(unsigned batch=0;batch<batches;batch++){
  uint32_t F=f[0],G=g[0],U=1,V=0,Q=0,R=1,D=delta;
  for(unsigned step=0;step<30;step++){
   uint32_t B=0-(G&1),S=((D>>31)-1)&B;
   uint32_t G1=G+(((F^S)-S)&B),Q1=Q+(((U^S)-S)&B),R1=R+(((V^S)-S)&B);
   D=((D^S)-S)+2;F=F+(G1&S);G=G1>>1;U=(U+(Q1&S))<<1;V=(V+(R1&S))<<1;Q=Q1;R=R1;
  }delta=D;
  lin(t,n+1,f,g,n+1,U,V);shift30(nf,t,n+1);lin(t,n+1,f,g,n+1,Q,R);shift30(ng,t,n+1);
  lin(t,n+2,a,b,n,U,V);mred(na,t,m,n,minv);lin(t,n+2,a,b,n,Q,R);mred(nb,t,m,n,minv);
  memcpy(f,nf,4*(n+1));memcpy(g,ng,4*(n+1));memcpy(a,na,4*n);memcpy(b,nb,4*n);
 }
 uint32_t sign=0-(f[n]>>31),nz_a=0;for(unsigned j=0;j<n;j++)nz_a|=a[j];uint32_t negmask=sign&(0-((nz_a|(0-nz_a))>>31));
 uint64_t borrow=0;for(unsigned j=0;j<n;j++){uint64_t z=(uint64_t)m[j]-a[j]-borrow;na[j]=(uint32_t)z;borrow=z>>63;a[j]=(a[j]&~negmask)|(na[j]&negmask);}
 for(unsigned j=0;j<2*batches;j++)twice(a,m,n);
 for(unsigned j=0;j<4;j++)memset(base+j*stride,0,fulln*4);
 uint64_t carry=sign&1;uint32_t*vgcd=(uint32_t*)(base+stride),*vinv=(uint32_t*)(base+3*stride);
 for(unsigned j=0;j<n;j++){uint64_t z=(uint64_t)(f[j]^sign)+carry;vgcd[j]=(uint32_t)z;carry=z>>32;vinv[j]=a[j];}
 uint32_t bad=0;for(unsigned j=0;j<=n;j++)bad|=g[j];if(bad){fprintf(stderr,"DIVSTEP DID NOT CONVERGE n=%u\n",n);exit(20);}
}
__attribute__((force_align_arg_pointer)) void proto_inv_C(uint64_t*ws,unsigned n,unsigned pl,unsigned ql){(void)pl;(void)ql;batch_inverse_ws(ws,n,n);}
__attribute__((force_align_arg_pointer)) void proto_inv_active_C(uint64_t*ws,unsigned n,unsigned pl,unsigned ql){unsigned active=((pl>ql?pl:ql)+3)/4;batch_inverse_ws(ws,n,active);}

/* Odd adjustment preserves gcd and avoids preliminary division. */
__attribute__((force_align_arg_pointer)) void proto_gcd_C(uint64_t*ws,unsigned n){
 unsigned stride=4*(n+2);unsigned char*base=(unsigned char*)ws+160;
 uint32_t *input=(uint32_t*)base,*m=(uint32_t*)(base+8*stride);
 uint32_t f[BW],g[BW],nf[BW],ng[BW],t[BW];
 memset(f,0,4*(n+1));memset(g,0,4*(n+1));memcpy(f,m,n*4);
 uint32_t mask=0-((input[0]&1)^1);uint64_t carry=0;
 for(unsigned j=0;j<n;j++){uint64_t z=(uint64_t)input[j]+(m[j]&mask)+carry;g[j]=(uint32_t)z;carry=z>>32;}g[n]=(uint32_t)carry;
 uint32_t D=1;
 for(unsigned batch=0;batch<3*(n+1);batch++){
  uint32_t F=f[0],G=g[0],U=1,V=0,Q=0,R=1;
  for(unsigned step=0;step<30;step++){
   uint32_t B=0-(G&1),S=((D>>31)-1)&B;
   uint32_t G1=G+(((F^S)-S)&B),Q1=Q+(((U^S)-S)&B),R1=R+(((V^S)-S)&B);
   D=((D^S)-S)+2;F=F+(G1&S);G=G1>>1;U=(U+(Q1&S))<<1;V=(V+(R1&S))<<1;Q=Q1;R=R1;
  }
  lin(t,n+1,f,g,n+1,U,V);shift30(nf,t,n+1);lin(t,n+1,f,g,n+1,Q,R);shift30(ng,t,n+1);
  memcpy(f,nf,4*(n+1));memcpy(g,ng,4*(n+1));
 }
 uint32_t sign=0-(f[n]>>31);carry=sign&1;uint32_t*out=(uint32_t*)(base+stride);
 for(unsigned j=0;j<n;j++){uint64_t z=(uint64_t)(f[j]^sign)+carry;out[j]=(uint32_t)z;carry=z>>32;}
 for(unsigned j=0;j<=n;j++)if(g[j]){fprintf(stderr,"GCD DID NOT CONVERGE\n");exit(25);}
}

static uint64_t euclid64(uint64_t a,uint64_t b){while(b){uint64_t r=a%b;a=b;b=r;}return a;}
static uint64_t oracle_add(uint64_t a,uint64_t b,uint64_t m){return a>=m-b?a-(m-b):a+b;}
static uint64_t oracle_mul(uint64_t a,uint64_t b,uint64_t m){uint64_t r=0;a%=m;while(b){if(b&1)r=oracle_add(r,a,m);a=oracle_add(a,a,m);b>>=1;}return r;}
static int batch_selftest(void){
 for(unsigned t=0;t<1000;t++){
  uint64_t w[128]={0},m=((uint64_t)rnd()<<32|rnd())|1,q=(uint64_t)rnd()<<32|rnd();
  if(t==0)m=1;if(t==1)m=~(uint64_t)0;if(t==2)q=0;if(t==3)q=m-1;
  memcpy((char*)w+160,&q,8);memcpy((char*)w+160+8*16,&m,8);
  proto_inv_C(w,2,8,8);uint64_t g,inv;memcpy(&g,(char*)w+160+16,8);memcpy(&inv,(char*)w+160+3*16,8);
  if(g!=euclid64(m,q)||inv>=m||oracle_mul(q,inv,m)!=g%m){printf("BATCH SELFTEST FAIL case=%u\n",t);return 1;}
 memcpy((char*)w+160,&q,8);proto_gcd_C(w,2);memcpy(&g,(char*)w+176,8);
  if(g!=euclid64(m,q)){printf("GCD SELFTEST FAIL case=%u\n",t);return 1;}
 }puts("batch_selftest_passed=1000");return 0;
}

#ifdef OPENSSL_REF
extern unsigned proto_crt0(unsigned char*,unsigned,unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_crt2(unsigned char*,unsigned,unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_crt3(unsigned char*,unsigned,unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
typedef unsigned (*checkfn)(const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_check0(const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_check1(const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
static unsigned trimlen(const unsigned char**p,unsigned n){while(n&&**p==0){(*p)++;n--;}return n;}
static int openssl_import(const unsigned char*nb,unsigned k,const unsigned char*eb,unsigned el,const unsigned char*db,unsigned dl){
 BN_CTX*c=BN_CTX_new();BIGNUM*n=BN_bin2bn(nb,k,0),*e=BN_bin2bn(eb,el,0),*d=BN_bin2bn(db,dl,0),*r=BN_new(),*g=BN_new(),*y=BN_new(),*x=BN_new(),*n1=BN_dup(n),*p=BN_new(),*q=BN_new(),*p1=BN_new(),*q1=BN_new(),*dp=BN_new(),*dq=BN_new(),*qi=BN_new();
 BN_mul(r,d,e,c);BN_sub_word(r,1);unsigned t=0;while(!BN_is_odd(r)){BN_rshift1(r,r);t++;}BN_sub_word(n1,1);int found=0;
 for(unsigned cand=2;cand<102&&!found;cand++){
  BN_set_word(g,cand);BN_mod_exp(y,g,r,n,c);if(BN_is_one(y)||BN_cmp(y,n1)==0)continue;
  for(unsigned j=0;j<t;j++){
   BN_mod_sqr(x,y,n,c);if(BN_is_one(x)){found=1;break;}if(BN_cmp(x,n1)==0||j+1==t)break;BN_copy(y,x);
  }
 }
 if(found){BN_sub_word(y,1);BN_gcd(p,y,n,c);BN_div(q,0,n,p,c);BN_copy(p1,p);BN_sub_word(p1,1);BN_copy(q1,q);BN_sub_word(q1,1);BN_nnmod(dp,d,p1,c);BN_nnmod(dq,d,q1,c);if(!BN_mod_inverse(qi,q,p,c))found=0;}
 BN_free(n);BN_free(e);BN_free(d);BN_free(r);BN_free(g);BN_free(y);BN_free(x);BN_free(n1);BN_free(p);BN_free(q);BN_free(p1);BN_free(q1);BN_free(dp);BN_free(dq);BN_free(qi);BN_CTX_free(c);return found;
}
static __attribute__((always_inline)) inline int full_apis(const char*dir,int justdiff){
 for(unsigned bits=2048;bits<=4096;bits+=1024){
  char path[512];snprintf(path,sizeof(path),"%s/key%u.txt",dir,bits);FILE*f=fopen(path,"r");if(!f)return 2;
  unsigned char nb[1024],eb[1024],db[1024],pp[1024],qq[1024],dp[1024],dq[1024],qi[1024];unsigned k=readhex(f,nb),el=readhex(f,eb),dl=readhex(f,db);fclose(f);
  unsigned wl=16*k+32;uint64_t*w=calloc(wl,8);if(rs[0](pp,k,qq,k,nb,k,eb,el,db,dl,w,wl)!=1)return 3;
  const unsigned char*p=pp,*q=qq;unsigned pl=trimlen(&p,k),ql=trimlen(&q,k);
  if(proto_crt0(dp,pl,dq,ql,qi,pl,nb,k,p,pl,q,ql,db,dl,w,wl)!=1)return 4;
  for(unsigned which=0;which<2;which++){
   unsigned char xdp[1024],xdq[1024],xqi[1024];
   unsigned ok=which?proto_crt3(xdp,pl,xdq,ql,xqi,pl,nb,k,p,pl,q,ql,db,dl,w,wl):proto_crt2(xdp,pl,xdq,ql,xqi,pl,nb,k,p,pl,q,ql,db,dl,w,wl);
   if(ok!=1||memcmp(dp,xdp,pl)||memcmp(dq,xdq,ql)||memcmp(qi,xqi,pl)){printf("BATCH CRT DIFF bits=%u active=%u ok=%u\n",bits,which,ok);return 15;}
  }
  for(unsigned t=0;t<12;t++){
   unsigned char pm[1024],qm[1024],im[1024],dm[1024],em[1024];memcpy(pm,p,pl);memcpy(qm,q,ql);memcpy(im,qi,pl);memcpy(dm,dp,pl);memcpy(em,dq,ql);
   if(t==1)im[pl-1]^=1;if(t==2)memset(im,255,pl);if(t==3)pm[pl-1]&=254;if(t==4){memset(pm,0,pl);pm[pl-1]=1;memset(im,0,pl);}if(t==5)memset(pm,0,pl);if(t==6)dm[pl-1]^=1;if(t==7)qm[ql-1]^=2;if(t>7)im[(t-8)%pl]^=(unsigned char)(1u<<(t-8));
   unsigned a=proto_check0(nb,k,eb,el,pm,pl,qm,ql,dm,pl,em,ql,im,pl,w,wl),b=proto_check1(nb,k,eb,el,pm,pl,qm,ql,dm,pl,em,ql,im,pl,w,wl);
   if(a!=b){printf("CHECK DIFFERENTIAL FAIL bits=%u case=%u base=%u new=%u\n",bits,t,a,b);return 5;}
  }
  for(unsigned mode=10;mode<14;mode++){unsigned char xp[1024],xq[1024];unsigned ok=rs[mode](xp,k,xq,k,nb,k,eb,el,db,dl,w,wl);if(ok!=1||memcmp(xp,pp,k)||memcmp(xq,qq,k)){printf("GCD RECOVER DIFF bits=%u mode=%u\n",bits,mode);return 26;}}
  printf("check_differential_passed,bits=%u,cases=12\n",bits);fflush(stdout);if(justdiff){free(w);continue;}
  for(unsigned rr=0;rr<3;rr++)for(unsigned seq=0;seq<13;seq++){
   unsigned mode=(seq+rr)%13;double start=now();unsigned ok=0;
   for(unsigned rep=0;rep<3;rep++){
    if(mode==12)ok=openssl_import(nb,k,eb,el,db,dl);
    else{unsigned recmode=mode==10?12:mode==11?13:mode==8?10:mode==9?11:mode==6?7:mode==7?8:(mode==1||mode>=3)?3:0;ok=rs[recmode](pp,k,qq,k,nb,k,eb,el,db,dl,w,wl);if(ok!=1)return 6;p=pp;q=qq;pl=trimlen(&p,k);ql=trimlen(&q,k);
     ok=mode==4?proto_crt2(dp,pl,dq,ql,qi,pl,nb,k,p,pl,q,ql,db,dl,w,wl):mode>=5?proto_crt3(dp,pl,dq,ql,qi,pl,nb,k,p,pl,q,ql,db,dl,w,wl):proto_crt0(dp,pl,dq,ql,qi,pl,nb,k,p,pl,q,ql,db,dl,w,wl);if(ok!=1)return 7;
     checkfn check=mode<2?proto_check0:proto_check1;ok=check(nb,k,eb,el,p,pl,q,ql,dp,pl,dq,ql,qi,pl,w,wl);
    }if(ok!=1)return 8;
   }
   printf("full_import,bits=%u,round=%u,mode=%u,ms=%.4f,ok=%u\n",bits,rr,mode,(now()-start)*1000/3,ok);fflush(stdout);
  }
  for(unsigned rr=0;rr<3;rr++)for(unsigned mode=0;mode<5;mode++){
   double start=now();unsigned ok=0;for(unsigned rep=0;rep<5;rep++){
    if(mode==3)ok=proto_crt2(dp,pl,dq,ql,qi,pl,nb,k,p,pl,q,ql,db,dl,w,wl);
    else if(mode==4)ok=proto_crt3(dp,pl,dq,ql,qi,pl,nb,k,p,pl,q,ql,db,dl,w,wl);
    else if(mode==0)ok=proto_crt0(dp,pl,dq,ql,qi,pl,nb,k,p,pl,q,ql,db,dl,w,wl);
    else{checkfn check=mode==1?proto_check0:proto_check1;ok=check(nb,k,eb,el,p,pl,q,ql,dp,pl,dq,ql,qi,pl,w,wl);}
    if(ok!=1)return 9;
   }printf("validation,bits=%u,round=%u,mode=%u,ms=%.4f\n",bits,rr,mode,(now()-start)*1000/5);fflush(stdout);
  }
  free(w);
 }return 0;
}
#endif
int main(int argc,char**argv){if(batch_selftest()||differential())return 1;
#ifdef LOCAL_DIFF
 return full_apis(argc>1?argv[1]:"keys",1);
#else
 if(argc>1&&!strcmp(argv[1],"--diff"))return 0;
#ifdef OPENSSL_REF
 if(argc>1&&!strcmp(argv[1],"--check-diff"))return full_apis(argc>2?argv[2]:"keys",1);
 if(kernels())return 2;
 if(full_apis(argc>1?argv[1]:"keys",0))return 3;
#endif
 return recoveries(argc>1?argv[1]:"keys");
#endif
}
