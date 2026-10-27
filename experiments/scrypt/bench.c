#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef void(*sf)(uint32_t*,uint32_t*);
typedef void(*bf)(const void*,size_t,void*,size_t,void*);
typedef void(*rf)(void*,size_t,void*,size_t,void*,size_t);
#define S(n) void trial_##n(uint32_t*,uint32_t*);
S(scalar) S(neon) S(neon_loop)
#define B(n) void trial_bm_##n(const void*,size_t,void*,size_t,void*);void trial_rm_##n(void*,size_t,void*,size_t,void*,size_t);
B(scalar) B(neon) B(neon_loop) B(fused) B(fused_loop)
struct se{const char*n;sf f;}ss[]={{"scalar",trial_scalar},{"neon",trial_neon},{"neon_loop",trial_neon_loop}};
struct be{const char*n;bf f;rf rm;}bs[]={
#define X(n) {#n,trial_bm_##n,trial_rm_##n},
X(scalar) X(neon) X(neon_loop) X(fused) X(fused_loop)
};
static uint64_t random_state=123;
static uint64_t rnd(void){random_state^=random_state<<13;random_state^=random_state>>7;random_state^=random_state<<17;return random_state;}
static uint32_t rot(uint32_t x,unsigned n){return(x<<n)|(x>>(32-n));}
#define L(i,j,k,n) x[i]^=rot(x[j]+x[k],n)
static void ref(uint32_t*b){uint32_t x[16];memcpy(x,b,64);for(int i=0;i<4;i++){
L(4,0,12,7);L(8,4,0,9);L(12,8,4,13);L(0,12,8,18);
L(9,5,1,7);L(13,9,5,9);L(1,13,9,13);L(5,1,13,18);
L(14,10,6,7);L(2,14,10,9);L(6,2,14,13);L(10,6,2,18);
L(3,15,11,7);L(7,3,15,9);L(11,7,3,13);L(15,11,7,18);
L(1,0,3,7);L(2,1,0,9);L(3,2,1,13);L(0,3,2,18);
L(6,5,4,7);L(7,6,5,9);L(4,7,6,13);L(5,4,7,18);
L(11,10,9,7);L(8,11,10,9);L(9,8,11,13);L(10,9,8,18);
L(12,15,14,7);L(13,12,15,9);L(14,13,12,13);L(15,14,13,18);
}for(int i=0;i<16;i++)b[i]+=x[i];}
static void bmref(const uint32_t*b,size_t r,uint32_t*y){uint32_t x[16];memcpy(x,b+(2*r-1)*16,64);for(size_t j=0;j<2*r;j++){for(int k=0;k<16;k++)x[k]^=b[j*16+k];ref(x);memcpy(y+(j/2+(j%2)*r)*16,x,64);}}
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
static unsigned char *alloc(size_t n){unsigned char*p=malloc(n);if(!p)exit(90);return p;}
static volatile uint64_t sink;
int main(int argc,char**argv){uint32_t x[16],a[16],b[16],scratch[32];
for(int t=0;t<2000;t++){for(int k=0;k<16;k++)x[k]=t==0?0:t==1?~0u:rnd();memcpy(a,x,64);ref(a);for(int j=0;j<3;j++){memcpy(b,x,64);ss[j].f(b,scratch);if(memcmp(a,b,64)){fprintf(stderr,"BAD SALSA %s %d\n",ss[j].n,t);return 1;}}}
fprintf(stderr,"PASS Salsa:2000 zero/max/random cases per variant\n");
size_t rs[]={1,2,3,8,13,17,32};
for(int ri=0;ri<7;ri++){size_t r=rs[ri],len=r*128;uint32_t*in=(uint32_t*)alloc(len),*expected=(uint32_t*)alloc(len);unsigned char*out=alloc(len+128);for(int t=0;t<100;t++){for(size_t k=0;k<len/4;k++)in[k]=rnd();bmref(in,r,expected);for(int j=0;j<5;j++){memset(out,0xaa,len+128);bs[j].f(in,r,out+64,r,scratch);if(memcmp(expected,out+64,len)){fprintf(stderr,"BAD BM %s r%zu t%d\n",bs[j].n,r,t);return 2;}for(int k=0;k<64;k++)if(out[k]!=0xaa||out[len+64+k]!=0xaa)return 3;}}free(in);free(expected);free(out);}
fprintf(stderr,"PASS BlockMix:100 random cases x7 r sizes x5 variants and output guards\n");
if(argc>1)return 0;
for(int ro=0;ro<8;ro++)for(int k=0;k<3;k++){int j=(k+ro)%3;for(int i=0;i<16;i++)b[i]=rnd();int n=200000;double t=now();for(int i=0;i<n;i++)ss[j].f(b,scratch);t=now()-t;sink^=b[0];printf("salsa,%d,%s,1,%.3f\n",ro,ss[j].n,t*1e9/n);}
size_t r=8,len=128*r;uint32_t*in=(uint32_t*)alloc(len),*out=(uint32_t*)alloc(len);for(size_t k=0;k<len/4;k++)in[k]=rnd();
for(int ro=0;ro<8;ro++)for(int k=0;k<5;k++){int j=(k+ro)%5;int n=10000;double t=now();for(int i=0;i<n;i++){bs[j].f(in,r,out,r,scratch);in[0]^=out[0];}t=now()-t;printf("blockmix,%d,%s,8,%.3f\n",ro,bs[j].n,t*1e9/n);}
for(int ni=0;ni<2;ni++){size_t N=ni?16384:1024;void*v=alloc(len*N),*ws=alloc((r+2)*128);uint32_t*expected=(uint32_t*)alloc(len);for(int ro=0;ro<3;ro++){for(size_t k=0;k<len/4;k++)in[k]=rnd();for(int k=0;k<5;k++){int j=(k+ro)%5;memcpy(out,in,len);double t=now();bs[j].rm(out,r,v,N*r,ws,r+2);t=now()-t;if(j==0)memcpy(expected,out,len);else{uint32_t*check=(uint32_t*)alloc(len);memcpy(check,in,len);bs[0].rm(check,r,v,N*r,ws,r+2);if(memcmp(out,check,len)){fprintf(stderr,"BAD ROMIX %s N%zu\n",bs[j].n,N);return 4;}free(check);}printf("romix,%d,%s,%zu,%.3f\n",ro,bs[j].n,N,t*1e9);fflush(stdout);}}free(expected);free(v);free(ws);}
fprintf(stderr,"PASS ROMix all variants at N1024/16384,r8\n");free(in);free(out);return 0;}
