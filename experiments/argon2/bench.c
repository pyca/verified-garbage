#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef void (*fn)(const uint64_t*,const uint64_t*,uint64_t*,uint64_t*);
#define X(n) void n(const uint64_t*,const uint64_t*,uint64_t*,uint64_t*);
#include "variants.h"
#undef X
struct entry {const char *name; fn f;} entries[]={
#define X(n) {#n,n},
#include "variants.h"
#undef X
};
static uint64_t rng=123;
static uint64_t random64(void){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
static uint64_t rr(uint64_t x,int n){return (x>>n)|(x<<(64-n));}
static uint64_t bm(uint64_t a,uint64_t b){return a+b+2*(uint64_t)(uint32_t)a*(uint32_t)b;}
#define G(a,b,c,d) do{a=bm(a,b);d=rr(d^a,32);c=bm(c,d);b=rr(b^c,24);a=bm(a,b);d=rr(d^a,16);c=bm(c,d);b=rr(b^c,63);}while(0)
static void perm(uint64_t*v){G(v[0],v[4],v[8],v[12]);G(v[1],v[5],v[9],v[13]);G(v[2],v[6],v[10],v[14]);G(v[3],v[7],v[11],v[15]);G(v[0],v[5],v[10],v[15]);G(v[1],v[6],v[11],v[12]);G(v[2],v[7],v[8],v[13]);G(v[3],v[4],v[9],v[14]);}
static void ref(const uint64_t*x,const uint64_t*y,uint64_t*z){uint64_t r[128],v[16];for(int i=0;i<128;i++)r[i]=x[i]^y[i];for(int i=0;i<8;i++)perm(r+16*i);for(int i=0;i<8;i++){for(int j=0;j<8;j++){v[2*j]=r[16*j+2*i];v[2*j+1]=r[16*j+2*i+1];}perm(v);for(int j=0;j<8;j++){r[16*j+2*i]=v[2*j];r[16*j+2*i+1]=v[2*j+1];}}for(int i=0;i<128;i++)z[i]=r[i]^x[i]^y[i];}
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(int argc,char**argv){_Alignas(64) uint64_t x[128],y[128],z[128],r[128],scratch[512];int n=sizeof(entries)/sizeof(entries[0]);
for(int t=0;t<1000;t++){for(int i=0;i<128;i++){x[i]=t==0?0:t==1?~0ull:random64();y[i]=t==0?~0ull:t==1?0:random64();}ref(x,y,r);for(int j=0;j<n;j++){entries[j].f(x,y,z,scratch);if(memcmp(z,r,1024)){fprintf(stderr,"BAD %s t%d\n",entries[j].name,t);return 1;}memcpy(z,x,1024);entries[j].f(z,y,z,scratch);if(memcmp(z,r,1024))return 2;memcpy(z,y,1024);entries[j].f(x,z,z,scratch);if(memcmp(z,r,1024))return 3;}}
fprintf(stderr,"PASS 1000 random/max/zero cases per candidate, disjoint and output aliases x/y\n");
for(int round=0;round<8;round++)for(int k=0;k<n;k++){int j=(k*7+round)%n;int it=50000;double t=now();for(int i=0;i<it;i++){entries[j].f(x,y,z,scratch);x[0]^=z[0];}t=now()-t;printf("%d,%s,%.3f\n",round,entries[j].name,t*1e9/it);fflush(stdout);}return 0;}
