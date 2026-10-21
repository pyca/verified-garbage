#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
extern void proto_mont(uint64_t*,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned);
extern void proto_comba_mont(uint64_t*,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned);
void profile_mont(uint64_t*w,unsigned l,unsigned n,unsigned m,unsigned inv,unsigned s,unsigned o,unsigned a,unsigned b){proto_mont(w,l,n,m,inv,s,o,a,b);}
static uint32_t seed=1;
static uint32_t random32(void){seed^=seed<<13;seed^=seed>>17;seed^=seed<<5;return seed;}
int main(void){unsigned widths[]={1,2,4,8,16,32,48,64,128};unsigned total=0;
 for(unsigned z=0;z<9;z++){unsigned n=widths[z],N=2*n;unsigned mo=0,iv=4*N+8,a=4*N+32,b=8*N+32,o=12*N+32,s=16*N+64,L=s+12*N+64,wl=L/8;uint64_t*x=calloc(wl,8),*y=calloc(wl,8);uint32_t*p=(uint32_t*)x;
  for(unsigned t=0;t<100;t++){for(unsigned i=0;i<wl*2;i++)p[i]=random32();p[0]|=1;p[N-1]|=0x80000000u;for(unsigned i=0;i<N;i++){p[a/4+i]=random32();p[b/4+i]=random32();}p[a/4+N-1]&=0x7fffffffu;p[b/4+N-1]&=0x7fffffffu;if(t<3){for(unsigned i=0;i<N;i++){p[i]=0xffffffffu;p[a/4+i]=t==0?0:0xffffffffu;p[b/4+i]=t==0?0:0xffffffffu;}p[a/4]--;}uint32_t inv=1;for(unsigned j=0;j<5;j++)inv*=2-p[0]*inv;p[iv/4]=0-inv;
   for(unsigned mode=0;mode<3;mode++){unsigned dest=mode==0?o:a,operand=mode==2?b:a;memcpy(y,x,L);proto_mont(x,wl,n,mo,iv,s,dest,a,operand);proto_comba_mont(y,wl,n,mo,iv,s,dest,a,operand);if(memcmp((char*)x+dest,(char*)y+dest,4*N)){printf("FAIL n=%u case=%u mode=%u\n",n,t,mode);return 1;}total++;}
  }free(x);free(y);
 }printf("differential cases passed: %u\n",total);return 0;
}
