#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
extern void gh_base(const void*,void*,const void*,uint64_t);
extern void gh_fold4(const void*,void*,const void*,uint64_t);
extern void gh_fold8(const void*,void*,const void*,uint64_t);
extern void gh_packed(const void*,void*,const void*,uint64_t);
typedef void (*fn)(const void*,void*,const void*,uint64_t);
static const fn fs[]={gh_base,gh_fold4,gh_fold8,gh_packed};
static uint8_t key[16],y[16],initial[16],data[16384];
static volatile uint8_t checksum;
static uint64_t now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
static double measure(unsigned v,unsigned n,unsigned reps){uint64_t t=now();for(unsigned i=0;i<reps;i++){memcpy(y,initial,16);fs[v](key,y,data,n);}uint64_t dt=now()-t;checksum^=y[0];return (double)dt/reps;}
int main(int argc,char **argv){(void)argv;
 if(argc==1){uint64_t n;while(fread(&n,8,1,stdin)==1){if(n>1024||fread(key,16,1,stdin)!=1||fread(initial,16,1,stdin)!=1)return 2;if(n&&fread(data,16*n,1,stdin)!=1)return 3;for(unsigned v=0;v<4;v++){memcpy(y,initial,16);fs[v](key,y,data,n);fwrite(y,16,1,stdout);}}return 0;}
 for(unsigned i=0;i<16;i++){key[i]=(uint8_t)(7*i+31);initial[i]=(uint8_t)(3*i+29);}
 for(unsigned i=0;i<sizeof data;i++)data[i]=(uint8_t)(17*i+49);
 const unsigned sizes[]={1,4,8,16,17,31,64,1024};
 for(unsigned k=0;k<8;k++){unsigned n=sizes[k],reps=16384/n;uint8_t want[16];memcpy(y,initial,16);fs[0](key,y,data,n);memcpy(want,y,16);
 for(unsigned v=0;v<4;v++){memcpy(y,initial,16);fs[v](key,y,data,n);if(memcmp(y,want,16))return 4;uint64_t end=now()+50000000;do{measure(v,n,reps);}while(now()<end);}
 for(unsigned s=0;s<25;s++)for(unsigned i=0;i<4;i++){unsigned v=(s+i)%4;printf("%u,%u,%u,%.3f\n",n,s,v,measure(v,n,reps));}}
 return checksum==0x37?5:0;}
