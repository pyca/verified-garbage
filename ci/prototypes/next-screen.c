/* Unproven prototypes only. Differential random cases; timings require native i686. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef OPENSSL_REF
#include <openssl/bn.h>
#endif
#define DECL(i) extern void proto_mont##i(uint64_t*,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned); \
extern unsigned proto_recover##i(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned)
DECL(0);DECL(1);DECL(2);DECL(3);DECL(4);DECL(5);
typedef void (*montfn)(uint64_t*,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned);
static montfn ms[]={proto_mont0,proto_mont1,proto_mont2,proto_mont3,proto_mont4,proto_mont5};
typedef unsigned (*recfn)(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
static recfn rs[]={proto_recover0,proto_recover1,proto_recover2,proto_recover3,proto_recover4,proto_recover5};
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
    for(unsigned mode=1;mode<6;mode++){
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
    for(unsigned seq=0;seq<7;seq++){
     unsigned mode=(seq+round)%7;double start=now();unsigned reps=0;
     do {for(unsigned j=0;j<32;j++){if(mode<6)ms[mode](w,wl,n,0,iv,s,o,a,op);else if(!BN_mod_mul_montgomery(O,A,sq?A:B,mc,ctx))return 3;}reps+=32;}while(now()-start<0.08);
     double ns=(now()-start)*1e9/reps;
     if(mode<6&&memcmp(expect,(char*)w+o,4*N)){printf("OPENSSL DIFF bits=%u mode=%u square=%u\n",bits,mode,sq);return 4;}
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
  unsigned char nb[1024],eb[1024],db[1024],p[6][1024],q[6][1024];unsigned k=readhex(f,nb),el=readhex(f,eb),dl=readhex(f,db);fclose(f);
  unsigned wl=16*k+32;uint64_t*w=calloc(wl,8);
  for(unsigned round=0;round<3;round++){
   for(unsigned seq=0;seq<6;seq++){
    unsigned mode=(seq+round)%6;double start=now();unsigned ok=0;
    for(unsigned j=0;j<3;j++)ok=rs[mode](p[mode],k,q[mode],k,nb,k,eb,el,db,dl,w,wl);
    printf("recovery,bits=%u,round=%u,mode=%u,ms=%.4f,ok=%u\n",bits,round,mode,(now()-start)*1000/3,ok);fflush(stdout);if(ok!=1)return 3;
   }
   for(unsigned mode=1;mode<6;mode++)if(memcmp(p[0],p[mode],k)||memcmp(q[0],q[mode],k)){printf("RECOVERY DIFF bits=%u mode=%u\n",bits,mode);return 4;}
  }free(w);
 }return 0;
}
int main(int argc,char**argv){if(differential())return 1;if(argc>1&&!strcmp(argv[1],"--diff"))return 0;
#ifdef OPENSSL_REF
 if(kernels())return 2;
#endif
 return recoveries(argc>1?argv[1]:"keys");}
