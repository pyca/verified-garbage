#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
extern void ctr_base(const void*,uint64_t,void*,void*,uint64_t,void*);
extern void ctr_wide(const void*,uint64_t,void*,void*,uint64_t,void*);
typedef void (*fn)(const void*,uint64_t,void*,void*,uint64_t,void*);
static const fn fs[]={ctr_base,ctr_wide};
static uint8_t w[240],cb[16],initial[16],data[16384],original[16384],scratch[2048];
static volatile uint8_t checksum;
static uint64_t now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
static double measure(unsigned v,unsigned nr,unsigned n,unsigned reps){
 uint64_t t=now();
 for(unsigned i=0;i<reps;i++){memcpy(cb,initial,16);fs[v](w,nr,cb,data,n,scratch);}
 uint64_t dt=now()-t;checksum^=data[0];return (double)dt/reps;
}
int main(int argc,char **argv){(void)argv;
 if(argc==1){uint64_t n,nr;while(fread(&n,8,1,stdin)==1){
  if(n>32||fread(&nr,8,1,stdin)!=1||fread(w,240,1,stdin)!=1||fread(initial,16,1,stdin)!=1)return 2;
  if(n&&fread(original,16*n,1,stdin)!=1)return 3;
  for(unsigned v=0;v<2;v++){memcpy(cb,initial,16);memcpy(data,original,16*n);fs[v](w,nr,cb,data,n,scratch);fwrite(cb,16,1,stdout);if(n)fwrite(data,16*n,1,stdout);}
 }return 0;}
 for(unsigned i=0;i<sizeof w;i++)w[i]=(uint8_t)(7*i+31);
 for(unsigned i=0;i<sizeof original;i++)original[i]=(uint8_t)(17*i+49);
 memset(initial,0xff,16);initial[15]=0xfc;
 const unsigned sizes[]={4,64,1024};
 for(unsigned nr=10;nr<=14;nr+=2)for(unsigned k=0;k<3;k++){
  unsigned n=sizes[k],reps=16384/n;uint8_t want[16384],wantcb[16];
  memcpy(data,original,16*n);memcpy(cb,initial,16);fs[0](w,nr,cb,data,n,scratch);memcpy(want,data,16*n);memcpy(wantcb,cb,16);
  memcpy(data,original,16*n);memcpy(cb,initial,16);fs[1](w,nr,cb,data,n,scratch);
  if(memcmp(data,want,16*n)||memcmp(cb,wantcb,16))return 4;
  for(unsigned v=0;v<2;v++){uint64_t end=now()+50000000;do{measure(v,nr,n,reps);}while(now()<end);}
  for(unsigned s=0;s<25;s++)for(unsigned i=0;i<2;i++){unsigned v=(s+i)%2;printf("%u,%u,%u,%u,%.3f\n",nr,n,s,v,measure(v,nr,n,reps));}
 }
 return checksum==0x37?5:0;
}
