#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define X(n) extern void n(uint64_t *,uint64_t *);
#include "lazy-variants.h"
#undef X
struct entry {const char *name; void (*f)(uint64_t *,uint64_t *);};
#define X(n) {#n,n},
static struct entry entries[]={
#include "lazy-variants.h"
};
#undef X
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(void){
 uint64_t expected[25],state[25],scratch[64];
 size_t count=sizeof(entries)/sizeof(*entries);
 for(int test=0;test<32;test++){
  for(int j=0;j<25;j++)expected[j]=UINT64_C(0x9e3779b97f4a7c15)*(j+1)*(test+1);
  uint64_t initial[25];memcpy(initial,expected,sizeof initial);
  entries[0].f(expected,scratch);
  for(size_t i=1;i<count;i++){memcpy(state,initial,sizeof state);entries[i].f(state,scratch);
   if(memcmp(expected,state,sizeof state)){fprintf(stderr,"FAIL %s %d\n",entries[i].name,test);return 1;}}
 }
 fprintf(stderr,"All %zu variants match scalar on 32 states\n",count);
 for(int round=0;round<7;round++)for(size_t j=0;j<count;j++){
  size_t i=(j+round)%count; memset(state,0,sizeof state);
  double start=now();for(int k=0;k<60000;k++)entries[i].f(state,scratch);
  double ns=(now()-start)*1e9/60000;printf("%d,%s,%.4f,%llu\n",round,entries[i].name,ns,(unsigned long long)state[0]);
 }
}
