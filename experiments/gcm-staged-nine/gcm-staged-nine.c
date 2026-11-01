#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
extern void ctr_base(const void*,uint64_t,void*,void*,uint64_t,void*);
extern void ctr_wide(const void*,uint64_t,void*,void*,uint64_t,void*);
extern void gh_packed(const void*,void*,const void*,uint64_t);
#define ARGS const void*w,uint64_t nr,void*cb,void*d,uint64_t n,const void*h,void*y,void*s
extern void gcm_staged8_nine(ARGS);
extern void gcm_staged8(ARGS);
extern void gcm_staged8_counter(ARGS);
static void separate8(ARGS){ctr_base(w,nr,cb,d,n,s);gh_packed(h,y,d,n);}
static void separate16(ARGS){ctr_wide(w,nr,cb,d,n,s);gh_packed(h,y,d,n);}
typedef void (*fn)(ARGS);
static const fn fs[]={separate8,separate16,gcm_staged8_counter,gcm_staged8_nine};
static uint8_t w[240],cb[16],initial[16],h[16],y[16],yinitial[16],data[16384],original[16384],scratch[2048];
static volatile uint8_t checksum;
static uint64_t now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
static void reset(unsigned n){memcpy(cb,initial,16);memcpy(y,yinitial,16);memcpy(data,original,16*n);}
static double measure(unsigned v,unsigned nr,unsigned n,unsigned reps){
 uint64_t t=now();
 for(unsigned i=0;i<reps;i++){memcpy(cb,initial,16);memcpy(y,yinitial,16);fs[v](w,nr,cb,data,n,h,y,scratch);}
 uint64_t dt=now()-t;checksum^=data[0]^y[0];return (double)dt/reps;
}
int main(int argc,char **argv){(void)argv;
 if(argc==1){uint64_t n,nr;while(fread(&n,8,1,stdin)==1){
  if(n>1024||n%24||fread(&nr,8,1,stdin)!=1||fread(w,240,1,stdin)!=1||fread(initial,16,1,stdin)!=1||fread(h,16,1,stdin)!=1||fread(yinitial,16,1,stdin)!=1)return 2;
  if(n&&fread(original,16*n,1,stdin)!=1)return 3;
  for(unsigned v=0;v<4;v++){reset(n);fs[v](w,nr,cb,data,n,h,y,scratch);fwrite(cb,16,1,stdout);fwrite(y,16,1,stdout);if(n)fwrite(data,16*n,1,stdout);}
 }return 0;}
 for(unsigned i=0;i<sizeof w;i++)w[i]=(uint8_t)(7*i+31);
 for(unsigned i=0;i<sizeof original;i++)original[i]=(uint8_t)(17*i+49);
 for(unsigned i=0;i<16;i++){h[i]=(uint8_t)(7*i+31);yinitial[i]=(uint8_t)(3*i+29);}
 memset(initial,0xff,16);initial[15]=0xfc;
 const unsigned sizes[]={48,96,1008};
 for(unsigned nr=10;nr<=14;nr+=2)for(unsigned k=0;k<3;k++){
  unsigned n=sizes[k],reps=16384/n;uint8_t want[16384],wantcb[16],wanty[16];
  reset(n);fs[0](w,nr,cb,data,n,h,y,scratch);memcpy(want,data,16*n);memcpy(wantcb,cb,16);memcpy(wanty,y,16);
  for(unsigned v=0;v<4;v++){reset(n);fs[v](w,nr,cb,data,n,h,y,scratch);
   if(memcmp(data,want,16*n)||memcmp(cb,wantcb,16)||memcmp(y,wanty,16)){fprintf(stderr,"mismatch nr=%u n=%u variant=%u\n",nr,n,v);return 4;}}
  for(unsigned v=0;v<4;v++){reset(n);uint64_t end=now()+50000000;do{measure(v,nr,n,reps);}while(now()<end);}
  for(unsigned s=0;s<25;s++)for(unsigned i=0;i<4;i++){unsigned v=(s+i)%4;printf("%u,%u,%u,%u,%.3f\n",nr,n,s,v,measure(v,nr,n,reps));}
 }
 fprintf(stderr,"checksum=%u\n",(unsigned)checksum);return 0;
}
