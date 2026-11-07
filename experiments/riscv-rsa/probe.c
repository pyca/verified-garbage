#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <openssl/bn.h>
#include <openssl/crypto.h>
typedef uint64_t U;
typedef void (*kernel)(U*,const U*,const U*,const U*,size_t,U,U*,U*);
void c_one(U*,const U*,const U*,const U*,size_t,U,U*,U*);
void c_two(U*,const U*,const U*,const U*,size_t,U,U*,U*);
void c_column(U*,const U*,const U*,const U*,size_t,U,U*,U*);
#ifndef PORTABLE
#define KDECL(n) void n(U*,const U*,const U*,const U*,size_t,U,U*,U*);
KDECL(base_mont) KDECL(pair_mont) KDECL(base_square) KDECL(pair_square)
#endif
#define CHECK(x) do{if(!(x)){fprintf(stderr,"FAIL %s:%d: %s\n",__FILE__,__LINE__,#x);exit(1);}}while(0)
static U rng=0x1a2b3c4d5e6f7081ULL;
static U rnd(void){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
static U inverse(U m){U x=1;for(int i=0;i<6;i++)x*=2-m*x;return -x;}
static double now(void){struct timespec t;CHECK(clock_gettime(CLOCK_MONOTONIC,&t)==0);return t.tv_sec+t.tv_nsec*1e-9;}
static volatile U sink;
static const char *names[]={"base","pair","one","two","column"};
static kernel mults[]={
#ifndef PORTABLE
base_mont,pair_mont,
#endif
c_one,c_two};
static kernel squares[]={
#ifndef PORTABLE
base_square,pair_square,
#endif
c_column};
static void arithmetic_check(void){
    size_t widths[]={2,3,4,5,8,16,24,32,48,64,128};
    BN_CTX *ctx=BN_CTX_new();BIGNUM *m=BN_new(),*a=BN_new(),*b=BN_new(),*r=BN_new(),*ri=BN_new(),*want=BN_new();
    U mw[8*132],aw[130],bw[130],o[130];unsigned char expected[1040];
    size_t cases=0;
    for(size_t wi=0;wi<sizeof(widths)/sizeof(*widths);wi++)for(int trial=0;trial<24;trial++){
        size_t n=widths[wi];U *t=mw+2*(n+2),*tmp=mw+5*(n+2);for(size_t j=0;j<n;j++){mw[j]=rnd();aw[j]=rnd();bw[j]=rnd();}
        mw[0]|=1;mw[n-1]|=1ULL<<63;aw[n-1]>>=1;bw[n-1]>>=1;
        if(trial==0)memset(aw,0,n*8);
        if(trial==1){memcpy(aw,mw,n*8);aw[0]--;memcpy(bw,aw,n*8);}
        if(trial==2){for(size_t j=0;j<n;j++)mw[j]=UINT64_MAX;memcpy(aw,mw,n*8);aw[0]--;memcpy(bw,aw,n*8);}
        CHECK(BN_lebin2bn((void*)mw,n*8,m));CHECK(BN_lebin2bn((void*)aw,n*8,a));CHECK(BN_lebin2bn((void*)bw,n*8,b));
        CHECK(BN_one(r));CHECK(BN_lshift(r,r,n*64));CHECK(BN_mod_inverse(ri,r,m,ctx));
        for(int square=0;square<2;square++){
            CHECK(BN_mod_mul(want,a,square?a:b,m,ctx));CHECK(BN_mod_mul(want,want,ri,m,ctx));CHECK(BN_bn2lebinpad(want,expected,n*8)==(int)n*8);
            kernel *ks=square?squares:mults;size_t count=square?sizeof(squares)/sizeof(kernel):sizeof(mults)/sizeof(kernel);
            for(size_t k=0;k<count;k++){
                memset(t,0xa5,(2*n+2)*8);memset(tmp,0xa5,n*8);
                ks[k](o,aw,square?aw:bw,mw,n,inverse(mw[0]),t,tmp);
                if(memcmp(o,expected,n*8)){fprintf(stderr,"arithmetic n=%zu trial=%d square=%d kernel=%zu\n",n,trial,square,k);CHECK(0);}
                /* Real exponentiation aliases its output with the accumulator operand. */
                U alias[130];memcpy(alias,aw,n*8);ks[k](alias,alias,square?alias:bw,mw,n,inverse(mw[0]),t,tmp);CHECK(!memcmp(alias,expected,n*8));cases+=2;
            }
        }
    }
    fprintf(stderr,"PASS arithmetic: %zu checks against OpenSSL, including output aliasing\n",cases);
    BN_free(m);BN_free(a);BN_free(b);BN_free(r);BN_free(ri);BN_free(want);BN_CTX_free(ctx);
}
#ifndef PORTABLE
typedef U (*private_fn)(unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,U*,size_t);
#define DECL(n) U n(unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,U*,size_t);
DECL(base_vg_rsa_private_checked) DECL(pair_vg_rsa_private_checked) DECL(one_vg_rsa_private_checked) DECL(two_vg_rsa_private_checked) DECL(column_vg_rsa_private_checked)
static private_fn privs[]={base_vg_rsa_private_checked,pair_vg_rsa_private_checked,one_vg_rsa_private_checked,two_vg_rsa_private_checked,column_vg_rsa_private_checked};
struct key{int bits;const unsigned char *n;size_t nl;const unsigned char *e;size_t el;const unsigned char *d;size_t dl;const unsigned char *p;size_t pl;const unsigned char *q;size_t ql;const unsigned char *dp;size_t dpl;const unsigned char *dq;size_t dql;const unsigned char *qi;size_t qil;};
#include "out/fixtures.h"
struct work{unsigned char input[1024],out[1024];U scratch[16416];};
static U operate(size_t v,const struct key*k,struct work*w){
    return privs[v](w->out,k->nl,k->n,k->nl,k->e,k->el,w->input,k->nl,k->p,k->pl,k->q,k->ql,k->dp,k->dpl,k->dq,k->dql,k->qi,k->qil,w->scratch,16*k->nl+32);
}
static void rsa_check(void){
    BN_CTX*ctx=BN_CTX_new();BIGNUM*n=BN_new(),*d=BN_new(),*x=BN_new(),*y=BN_new();unsigned char expected[1024];
    struct work*w=calloc(1,sizeof(*w));size_t cases=0;
    for(size_t ki=0;ki<sizeof(keys)/sizeof(*keys);ki++){
        const struct key*k=keys+ki;BN_bin2bn(k->n,k->nl,n);BN_bin2bn(k->d,k->dl,d);
        for(int trial=0;trial<8;trial++){
            for(size_t j=0;j<k->nl;j++)w->input[j]=rnd();w->input[0]=0;
            if(trial<2){memset(w->input,0,k->nl);w->input[k->nl-1]=trial;}
            if(trial==2){memcpy(w->input,k->n,k->nl);w->input[k->nl-1]--;}
            if(trial>=6){memcpy(w->input,k->n,k->nl);if(trial==7)memset(w->input,255,k->nl);}
            if(trial<6){BN_bin2bn(w->input,k->nl,x);CHECK(BN_mod_exp(y,x,d,n,ctx));CHECK(BN_bn2binpad(y,expected,k->nl)==(int)k->nl);}
            else memset(expected,0,k->nl);
            for(size_t v=0;v<5;v++){
                U status=operate(v,k,w);
                if(status!=(U)(trial<6)||memcmp(w->out,expected,k->nl)){fprintf(stderr,"RSA key=%zu trial=%d variant=%s status=%llu\n",ki,trial,names[v],(unsigned long long)status);CHECK(0);}cases++;
            }
        }
    }
    fprintf(stderr,"PASS RSA: %zu checked private operations against OpenSSL, including rejected inputs\n",cases);
    free(w);BN_free(n);BN_free(d);BN_free(x);BN_free(y);BN_CTX_free(ctx);
}
struct threaded{size_t v;const struct key*k;size_t count;unsigned char expected[1024];};
static void*worker(void*arg){struct threaded*s=arg;struct work*w=calloc(1,sizeof(*w));memset(w->input,0x42,s->k->nl);w->input[0]=0;for(size_t i=0;i<s->count;i++){CHECK(operate(s->v,s->k,w)==1);CHECK(!memcmp(w->out,s->expected,s->k->nl));}free(w);return NULL;}
static void rsa_bench(void){
    for(size_t ki=0;ki<sizeof(keys)/sizeof(*keys);ki+=2){
        const struct key*k=keys+ki;struct work*w=calloc(1,sizeof(*w));memset(w->input,0x42,k->nl);w->input[0]=0;CHECK(operate(0,k,w)==1);
        unsigned char expected[1024];memcpy(expected,w->out,k->nl);
        for(int threads=1;threads<=4;threads*=4){
            size_t iters=threads==1?8:4;
            for(int round=0;round<7;round++)for(size_t step=0;step<5;step++){
                size_t v=round%2?4-step:step;double start=now();
                if(threads==1)for(size_t i=0;i<iters;i++){CHECK(operate(v,k,w)==1);CHECK(!memcmp(w->out,expected,k->nl));}
                else {pthread_t ids[4];struct threaded args[4];for(int t=0;t<4;t++){args[t]=(struct threaded){.v=v,.k=k,.count=iters};memcpy(args[t].expected,expected,k->nl);CHECK(!pthread_create(ids+t,NULL,worker,args+t));}for(int t=0;t<4;t++)CHECK(!pthread_join(ids[t],NULL));}
                double elapsed=now()-start;printf("rsa,%s,%d,%d,%d,%zu,%.9f\n",names[v],k->bits,threads,round,iters*threads,elapsed);fflush(stdout);
            }
        }free(w);
    }
}
static void micro_bench(void){
    for(size_t n=16;n<=32;n+=8){
        U m[8*132],a[130],b[130],o[130];U *t=m+2*(n+2),*tmp=m+5*(n+2);for(size_t j=0;j<n;j++){m[j]=rnd();a[j]=rnd();b[j]=rnd();}m[0]|=1;m[n-1]|=1ULL<<63;a[n-1]>>=1;b[n-1]>>=1;
        kernel ks[]={base_mont,pair_mont,c_one,c_two,base_square,pair_square,c_column};const char*kn[]={"base_mont","pair_mont","one_mont","two_mont","base_square","pair_square","column_square"};
        for(int r=0;r<7;r++)for(size_t step=0;step<7;step++){
            size_t v=r%2?6-step:step;size_t iters=5000;for(int warm=0;warm<100;warm++)ks[v](o,a,v>=4?a:b,m,n,inverse(m[0]),t,tmp);
            double start=now();for(size_t i=0;i<iters;i++){ks[v](o,a,v>=4?a:b,m,n,inverse(m[0]),t,tmp);sink^=o[0];}
            printf("micro,%s,%zu,1,%d,%zu,%.9f\n",kn[v],n*64,r,iters,now()-start);fflush(stdout);
        }
    }
}
#endif
int main(void){fprintf(stderr,"OpenSSL %s\n",OpenSSL_version(OPENSSL_VERSION));arithmetic_check();
#ifndef PORTABLE
rsa_check();puts("workload,variant,bits,threads,round,iterations,seconds");micro_bench();rsa_bench();
#endif
return 0;}
