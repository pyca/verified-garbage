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
KDECL(base_mont) KDECL(pair_mont) KDECL(base_square) KDECL(pair_square) KDECL(pipeline_square)
#endif
#define CHECK(x) do{if(!(x)){fprintf(stderr,"FAIL %s:%d: %s\n",__FILE__,__LINE__,#x);exit(1);}}while(0)
static U rng=0x1a2b3c4d5e6f7081ULL;
static U rnd(void){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
static U inverse(U m){U x=1;for(int i=0;i<6;i++)x*=2-m*x;return -x;}
static double cpu_now(void){struct timespec t;CHECK(clock_gettime(CLOCK_THREAD_CPUTIME_ID,&t)==0);return t.tv_sec+t.tv_nsec*1e-9;}
static double now(void){struct timespec t;CHECK(clock_gettime(CLOCK_MONOTONIC,&t)==0);return t.tv_sec+t.tv_nsec*1e-9;}
static volatile U sink;
static const char *names[]={"base","pair","one","two","column","montpair","pipeline","select","combined","pubsquare"};
static kernel mults[]={
#ifndef PORTABLE
base_mont,pair_mont,
#endif
c_one,c_two};
static kernel squares[]={
#ifndef PORTABLE
base_square,pair_square,
#endif
c_column
#ifndef PORTABLE
,pipeline_square
#endif
};
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
DECL(base_vg_rsa_private_checked) DECL(pair_vg_rsa_private_checked) DECL(one_vg_rsa_private_checked) DECL(two_vg_rsa_private_checked) DECL(column_vg_rsa_private_checked) DECL(montpair_vg_rsa_private_checked) DECL(pipeline_vg_rsa_private_checked) DECL(select_vg_rsa_private_checked) DECL(combined_vg_rsa_private_checked) DECL(pubsquare_vg_rsa_private_checked)
static private_fn privs[]={base_vg_rsa_private_checked,pair_vg_rsa_private_checked,one_vg_rsa_private_checked,two_vg_rsa_private_checked,column_vg_rsa_private_checked,montpair_vg_rsa_private_checked,pipeline_vg_rsa_private_checked,select_vg_rsa_private_checked,combined_vg_rsa_private_checked,pubsquare_vg_rsa_private_checked};
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
            for(size_t v=0;v<sizeof(privs)/sizeof(*privs);v++){
                fprintf(stderr,"check key=%zu trial=%d variant=%s\n",ki,trial,names[v]);
                U status=operate(v,k,w);
                if(status!=(U)(trial<6)||memcmp(w->out,expected,k->nl)){fprintf(stderr,"RSA key=%zu trial=%d variant=%s status=%llu\n",ki,trial,names[v],(unsigned long long)status);CHECK(0);}cases++;
            }
        }
    }
    fprintf(stderr,"PASS RSA: %zu checked private operations against OpenSSL, including rejected inputs\n",cases);
    free(w);BN_free(n);BN_free(d);BN_free(x);BN_free(y);BN_CTX_free(ctx);
}

typedef U (*public_fn)(unsigned char*,size_t,const U*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,U*,size_t);
#define PDE(n) U n(unsigned char*,size_t,const U*,size_t,const unsigned char*,size_t,const unsigned char*,size_t,U*,size_t);
PDE(base_vg_rsa_public_precomputed_checked) PDE(pair_vg_rsa_public_precomputed_checked) PDE(one_vg_rsa_public_precomputed_checked) PDE(two_vg_rsa_public_precomputed_checked) PDE(column_vg_rsa_public_precomputed_checked) PDE(montpair_vg_rsa_public_precomputed_checked) PDE(pipeline_vg_rsa_public_precomputed_checked) PDE(select_vg_rsa_public_precomputed_checked) PDE(combined_vg_rsa_public_precomputed_checked) PDE(pubsquare_vg_rsa_public_precomputed_checked)
static public_fn pubs[]={base_vg_rsa_public_precomputed_checked,pair_vg_rsa_public_precomputed_checked,one_vg_rsa_public_precomputed_checked,two_vg_rsa_public_precomputed_checked,column_vg_rsa_public_precomputed_checked,montpair_vg_rsa_public_precomputed_checked,pipeline_vg_rsa_public_precomputed_checked,select_vg_rsa_public_precomputed_checked,combined_vg_rsa_public_precomputed_checked,pubsquare_vg_rsa_public_precomputed_checked};
U base_vg_rsa_public_precompute(U*,size_t,const unsigned char*,size_t,U*,size_t);
static U public_op(size_t v,const struct key*k,struct work*w,const U*pre){return pubs[v](w->out,k->nl,pre,2*((k->nl+7)/8),k->e,k->el,w->input,k->nl,w->scratch,16*k->nl+32);}
static void public_check(void){
    struct work*w=calloc(1,sizeof(*w));U pre[256];BN_CTX*ctx=BN_CTX_new();BIGNUM*n=BN_new(),*e=BN_new(),*x=BN_new(),*y=BN_new();unsigned char expected[1024];size_t count=0;
    for(size_t ki=0;ki<sizeof(keys)/sizeof(*keys);ki++){
        const struct key*k=keys+ki;CHECK(base_vg_rsa_public_precompute(pre,2*((k->nl+7)/8),k->n,k->nl,w->scratch,16*k->nl+32)==1);
        BN_bin2bn(k->n,k->nl,n);BN_bin2bn(k->e,k->el,e);
        for(int trial=0;trial<8;trial++){
            for(size_t j=0;j<k->nl;j++)w->input[j]=rnd();w->input[0]=0;
            if(trial<2){memset(w->input,0,k->nl);w->input[k->nl-1]=trial;}
            if(trial==2){memcpy(w->input,k->n,k->nl);w->input[k->nl-1]--;}
            if(trial>=6){memcpy(w->input,k->n,k->nl);if(trial==7)memset(w->input,255,k->nl);}
            if(trial<6){BN_bin2bn(w->input,k->nl,x);CHECK(BN_mod_exp(y,x,e,n,ctx));CHECK(BN_bn2binpad(y,expected,k->nl)==(int)k->nl);}else memset(expected,0,k->nl);
            for(size_t v=0;v<sizeof(pubs)/sizeof(*pubs);v++){CHECK(public_op(v,k,w,pre)==(U)(trial<6));CHECK(!memcmp(w->out,expected,k->nl));count++;}
        }
    }
    fprintf(stderr,"PASS public RSA: %zu operations against OpenSSL\n",count);free(w);BN_free(n);BN_free(e);BN_free(x);BN_free(y);BN_CTX_free(ctx);
}
static void public_bench(void){
    struct work*w=calloc(1,sizeof(*w));U pre[256];unsigned char expected[1024];
    for(size_t ki=0;ki<sizeof(keys)/sizeof(*keys);ki++){
        const struct key*k=keys+ki;CHECK(base_vg_rsa_public_precompute(pre,2*((k->nl+7)/8),k->n,k->nl,w->scratch,16*k->nl+32)==1);memset(w->input,0x42,k->nl);w->input[0]=0;
        CHECK(public_op(0,k,w,pre)==1);memcpy(expected,w->out,k->nl);
        for(int r=0;r<7;r++)for(int step=0;step<3;step++){
            const size_t active[]={0,9,8};size_t v=active[r%2?2-step:step];size_t iters=k->bits==2048?1000:k->bits==3072?500:250;
            double start=now();for(size_t i=0;i<iters;i++){CHECK(public_op(v,k,w,pre)==1);CHECK(!memcmp(w->out,expected,k->nl));}
            printf("public,%s,%d,1,%d,%zu,%.9f,0\n",names[v],k->bits,r,iters,now()-start);fflush(stdout);
        }
    }free(w);
}
struct threaded{size_t v;const struct key*k;size_t count;double cpu;unsigned char expected[1024];};
static void*worker(void*arg){struct threaded*s=arg;struct work*w=calloc(1,sizeof(*w));memset(w->input,0x42,s->k->nl);w->input[0]=0;double start_cpu=cpu_now();for(size_t i=0;i<s->count;i++){CHECK(operate(s->v,s->k,w)==1);CHECK(!memcmp(w->out,s->expected,s->k->nl));}s->cpu=cpu_now()-start_cpu;free(w);return NULL;}
static void rsa_bench(void){
    int diagnostic=getenv("RSA_DIAGNOSTIC") && *getenv("RSA_DIAGNOSTIC");
    for(size_t ki=0;ki<sizeof(keys)/sizeof(*keys);ki++){
        const struct key*k=keys+ki;if(diagnostic && k->bits!=4096)continue;struct work*w=calloc(1,sizeof(*w));memset(w->input,0x42,k->nl);w->input[0]=0;CHECK(operate(0,k,w)==1);
        unsigned char expected[1024];memcpy(expected,w->out,k->nl);
        for(int threads=1;threads<=4;threads*=4){
            size_t iters=diagnostic?(threads==1?32:128):k->bits==2048?64:k->bits==3072?24:12;
            for(int round=0;round<7;round++)for(size_t step=0;step<(diagnostic?3:5);step++){
                static const size_t active[]={0,6,7,9,8},diag[]={0,9,8};size_t v=diagnostic?diag[round%2?2-step:step]:active[round%2?4-step:step];double start=now(),start_cpu=cpu_now(),cpu=0;
                if(threads==1){for(size_t i=0;i<iters;i++){CHECK(operate(v,k,w)==1);CHECK(!memcmp(w->out,expected,k->nl));}cpu=cpu_now()-start_cpu;}
                else {pthread_t ids[4];struct threaded args[4];for(int t=0;t<4;t++){args[t]=(struct threaded){.v=v,.k=k,.count=iters};memcpy(args[t].expected,expected,k->nl);CHECK(!pthread_create(ids+t,NULL,worker,args+t));}for(int t=0;t<4;t++){CHECK(!pthread_join(ids[t],NULL));cpu+=args[t].cpu;}}
                double elapsed=now()-start;printf("rsa,%s,%d,%d,%d,%zu,%.9f,%.9f\n",names[v],k->bits,threads,round,iters*threads,elapsed,cpu);fflush(stdout);
            }
        }free(w);
    }
}
static __attribute__((unused)) void micro_bench(void){
    for(size_t n=16;n<=32;n+=8){
        U m[8*132],a[130],b[130],o[130];U *t=m+2*(n+2),*tmp=m+5*(n+2);for(size_t j=0;j<n;j++){m[j]=rnd();a[j]=rnd();b[j]=rnd();}m[0]|=1;m[n-1]|=1ULL<<63;a[n-1]>>=1;b[n-1]>>=1;
        kernel ks[]={base_mont,pair_mont,c_one,c_two,base_square,pair_square,c_column
#ifndef PORTABLE
,pipeline_square
#endif
};const char*kn[]={"base_mont","pair_mont","one_mont","two_mont","base_square","pair_square","column_square","pipeline_square"};
        for(int r=0;r<7;r++)for(size_t step=0;step<8;step++){
            size_t v=r%2?7-step:step;size_t iters=5000;for(int warm=0;warm<100;warm++)ks[v](o,a,v>=4?a:b,m,n,inverse(m[0]),t,tmp);
            double start=now();for(size_t i=0;i<iters;i++){ks[v](o,a,v>=4?a:b,m,n,inverse(m[0]),t,tmp);sink^=o[0];}
            printf("micro,%s,%zu,1,%d,%zu,%.9f\n",kn[v],n*64,r,iters,now()-start);fflush(stdout);
        }
    }
}
#endif
int main(void){fprintf(stderr,"OpenSSL %s\n",OpenSSL_version(OPENSSL_VERSION));arithmetic_check();
#ifndef PORTABLE
rsa_check();public_check();puts("workload,variant,bits,threads,round,iterations,seconds,cpu_seconds");rsa_bench();if(!getenv("RSA_DIAGNOSTIC") || !*getenv("RSA_DIAGNOSTIC"))public_bench();
#endif
return 0;}
