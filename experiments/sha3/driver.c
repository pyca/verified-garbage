#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define B(n) extern void n(uint64_t *,uint64_t *,uint64_t,const uint8_t *,size_t,uint64_t *,size_t);
#include "bulks.h"
#undef B
struct entry {const char *name; void (*f)(uint64_t *,uint64_t *,uint64_t,const uint8_t *,size_t,uint64_t *,size_t);};
#define B(n) {#n,n},
static struct entry entries[]={
#include "bulks.h"
};
#undef B
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(void){
 uint64_t expected[25],state[25],scratch[80];uint8_t data[168*128];
 for(size_t i=0;i<sizeof data;i++)data[i]=(uint8_t)(i*37+9);
 size_t count=sizeof(entries)/sizeof(*entries);size_t rates[]={72,104,136,144,168};
 for(int r=0;r<5;r++)for(int blocks=1;blocks<20;blocks++){
  memset(expected,0,sizeof expected);entries[0].f(expected,scratch,0,data,rates[r]*blocks,scratch,rates[r]);
  for(size_t i=1;i<count;i++){memset(state,0,sizeof state);entries[i].f(state,scratch,0,data,rates[r]*blocks,scratch,rates[r]);
   if(memcmp(expected,state,sizeof state)){fprintf(stderr,"FAIL %s rate=%zu blocks=%d\n",entries[i].name,rates[r],blocks);return 1;}}
 }
 fprintf(stderr,"All %zu bulk variants match across all 5 rates and 1..19 blocks\n",count);
 for(int round=0;round<9;round++)for(int r=0;r<5;r++)for(size_t j=0;j<count;j++){
  size_t i=(j+round)%count;memset(state,0,sizeof state);
  double start=now();for(int k=0;k<1000;k++)entries[i].f(state,scratch,0,data,rates[r]*128,scratch,rates[r]);
  printf("%d,%zu,%s,%.4f,%llu\n",round,rates[r],entries[i].name,(now()-start)*1e9/1000,(unsigned long long)state[0]);
 }
}
