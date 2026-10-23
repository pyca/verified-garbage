#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "cases.h"
typedef uint32_t(*fn)(const uint8_t*,const uint8_t*,const uint8_t*,uint64_t*);
#define DECL(n) extern uint32_t ed448_trial_##n(const uint8_t*,const uint8_t*,const uint8_t*,uint64_t*);
DECL(0) DECL(1) DECL(2) DECL(3) DECL(4) DECL(5) DECL(6) DECL(7) DECL(8) DECL(9) DECL(10) DECL(11) DECL(12) DECL(13) DECL(14) DECL(15)
static fn fs[]={ed448_trial_0,ed448_trial_1,ed448_trial_2,ed448_trial_3,ed448_trial_4,ed448_trial_5,ed448_trial_6,ed448_trial_7,ed448_trial_8,ed448_trial_9,ed448_trial_10,ed448_trial_11,ed448_trial_12,ed448_trial_13,ed448_trial_14,ed448_trial_15};
static const char *names[]={"base","direct4","skip4","sparse3","sparse4","sparse5","trim5","odd5","odd6","joint5","joint-trim5","joint-trim6","joint-trim7","joint-trim8","joint8-key6","joint7-key6"};
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(void){
 uint64_t space[1026];unsigned cases=0,valid=0;uint8_t pk[80],sig[140],k[80];
 for(unsigned i=0;i<sizeof(samples)/sizeof(samples[0]);i++)for(int off=0;off<2;off++){
  const struct sample *s=&samples[i];memcpy(pk+off,s->pk,57);memcpy(sig+off,s->sig,114);memcpy(k+off,s->k,57);
  for(int v=0;v<16;v++){
   memset(space,0xa5,sizeof space);unsigned r=fs[v](pk+off,sig+off,k+off,space+1);
   if(r!=s->valid||space[0]!=0xa5a5a5a5a5a5a5a5ULL||space[1025]!=0xa5a5a5a5a5a5a5a5ULL){fprintf(stderr,"FAIL vector%d v%s got%u expected%d guards%llx,%llx\n",s->id,names[v],r,s->valid,space[0],space[1025]);return 1;}
   cases++;
  }
  if(s->valid)valid++;
 }
 fprintf(stderr,"PASS %u cases, %u valid inputs\n",cases,valid);
 // Raw 456-bit challenges, including values above L, and changed signatures.
 uint64_t rng=0x123456789abcdefULL;
 for(int i=0;i<128;i++){
  const struct sample *s=&samples[i%(sizeof(samples)/sizeof(samples[0]))];memcpy(sig,s->sig,114);
  for(int b=0;b<57;b++){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;k[b]=i==0?0:i==1?255:rng;}
  if(i&1)sig[i%114]^=1;
  unsigned want=fs[0](s->pk,sig,k,space+1);
  for(int v=1;v<16;v++)if(fs[v](s->pk,sig,k,space+1)!=want){fprintf(stderr,"FAIL differential%d v%s\n",i,names[v]);return 1;}
 }
 fprintf(stderr,"PASS arbitrary challenge differentials\n");
 puts("round,variant,us");fflush(stdout);
 for(int r=0;r<7;r++)for(int j=0;j<16;j++){
  int v=r%2?15-j:j;double start=now();unsigned sum=0;
  for(int i=0;i<1000;i++){const struct sample*s=&samples[i%8];sum+=fs[v](s->pk,s->sig,s->k,space+1);}
  printf("%d,%s,%.6f\n",r,names[v],(now()-start)*1e6/1000);fflush(stdout);if(sum==999999)abort();
 }
}
