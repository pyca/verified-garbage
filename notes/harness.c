#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
// call kern with registers set: r3=y r4=2w r5=o r6=a r7=b r8=T r9=tmp r10=m r14=magic
static uint64_t call(uint64_t y, uint64_t w2, uint64_t *o, uint64_t *a, uint64_t *b, uint64_t *T, uint64_t *tmp, uint64_t *m){
  register uint64_t r3 asm("r3")=y, r4 asm("r4")=w2, r5 asm("r5")=(uint64_t)o, r6 asm("r6")=(uint64_t)a,
    r7 asm("r7")=(uint64_t)b, r8 asm("r8")=(uint64_t)T, r9 asm("r9")=(uint64_t)tmp, r10 asm("r10")=(uint64_t)m;
  register uint64_t r14 asm("r14")=0x1234;
  asm volatile("bl kern" : "+r"(r3),"+r"(r4),"+r"(r5),"+r"(r6),"+r"(r7),"+r"(r8),"+r"(r9),"+r"(r10),"+r"(r14)
    : : "r0","r11","r12","r15","r16","r17","r18","r19","r20","r22","lr","ctr","cr0","xer","memory");
  return r14;
}
static uint64_t rnd(){ return ((uint64_t)rand()<<62)^((uint64_t)rand()<<31)^rand(); }
int main(){
  for(int w=2; w<=40; w++) for(int it=0; it<40; it++){ int sq = it&1;
    uint64_t m[64]={0},a[64]={0},b[64]={0},o[64]={0}; static uint64_t TT[200]; uint64_t *T=TT, *tmp=TT+w+2;
    for(int i=0;i<w;i++){m[i]=rnd();a[i]=rnd();b[i]=rnd();}
    m[0]|=1; m[w-1]|=1ULL<<63;
    // reduce a,b below m: clear top bit
    a[w-1]&=~(1ULL<<63); b[w-1]&=~(1ULL<<63); if(sq) for(int i=0;i<w;i++) b[i]=a[i];
    uint64_t y=1; for(int k=0;k<6;k++) y*= 2 - m[0]*y; y=(uint64_t)(-y)&0xffffffffULL;
    uint64_t mp=(uint64_t)0-( (uint64_t)1 ); // compute m' = -m^-1 mod 2^64
    uint64_t inv=1; for(int k=0;k<7;k++) inv*=2-m[0]*inv; mp=-inv;
    // reference FIOS single row
    uint64_t R[66]={0};
    for(int i=0;i<w;i++){
      u128 c=0; uint64_t t2[66];
      for(int j=0;j<=w;j++) t2[j]=R[j];
      // t += a_i*b
      u128 carry=0; for(int j=0;j<w;j++){ u128 s=(u128)a[i]*b[j]+t2[j]+carry; t2[j]=(uint64_t)s; carry=s>>64;}
      u128 s=(u128)t2[w]+carry; t2[w]=(uint64_t)s; uint64_t top=(uint64_t)(s>>64);
      uint64_t u=t2[0]*mp; carry=0;
      for(int j=0;j<w;j++){ u128 s2=(u128)u*m[j]+t2[j]+carry; t2[j]=(uint64_t)s2; carry=s2>>64;}
      s=(u128)t2[w]+carry; t2[w]=(uint64_t)s; top+=(uint64_t)(s>>64);
      for(int j=0;j<w;j++) R[j]=t2[j+1]; R[w]=top;
    }
    // final conditional subtract
    uint64_t D[66]; u128 br=0; for(int j=0;j<w;j++){ u128 d=(u128)R[j]-m[j]-br; D[j]=(uint64_t)d; br=(d>>64)&1;} 
    int useR = (R[w] < br);
    uint64_t *ref = useR? R : D;
    uint64_t r14 = call(y, 2*w, o, a, sq? a : b, T, tmp, m);
    if(r14!=0x1234 || memcmp(o, ref, 8*w)){ printf("MISMATCH w=%d it=%d r14=%lx\n", w, it, r14); return 1; }
  }
  printf("ok\n"); return 0;
}
