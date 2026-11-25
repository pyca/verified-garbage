/* Throwaway speed prototypes for README.md: one GHASH block each, 64-bit. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <emmintrin.h>
#include <x86intrin.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
#define L static inline __attribute__((always_inline))
static u64 H0, H1;           /* H*x^-1, words of the reflected block */
L u128 ref_cl(u64 a, u64 b){u128 r=0;for(int i=0;i<64;i++)if(a>>i&1)r^=(u128)b<<i;return r;}
/* z3:z2:z1:z0 -> fold: two words at the bottom up two words */
L void fold(u64 z[4], u64*y1, u64*y0){
  z[1]^=(z[0]<<63)^(z[0]<<62)^(z[0]<<57); z[2]^=z[0]^(z[0]>>1)^(z[0]>>2)^(z[0]>>7);
  z[2]^=(z[1]<<63)^(z[1]<<62)^(z[1]<<57); z[3]^=z[1]^(z[1]>>1)^(z[1]>>2)^(z[1]>>7);
  *y1=z[3];*y0=z[2];}
L void join(u128 l,u128 h,u128 m,u64*y1,u64*y0){
  m^=l^h; u64 z[4]={(u64)l,(u64)(l>>64)^(u64)m,(u64)h^(u64)(m>>64),(u64)(h>>64)}; fold(z,y1,y0);}
/* A: five classes, 64x64->128 */
#define M5 0x1084210842108421ULL
static u64 ka[3][5]; static const u64 msk5[5]={0x1084210842108421ULL,0x2108421084210842ULL,0x4210842108421084ULL,0x8421084210842108ULL,0x0842108421084210ULL};
L u128 clA(u64 a,const u64*k){
  u64 A[5];for(int i=0;i<5;i++)A[i]=a&msk5[i];
  u64 ms=0; (void)ms; u128 z=0;
  u128 m=((u128)M5<<65|(u128)M5); m|=(u128)M5<<65;
  for(int r=0;r<5;r++){u128 s=0;for(int i=0;i<5;i++)s^=(u128)A[i]*k[(r+5-i)%5];z|=s&(m<<r);}return z;}
static u64 msk(int i){u64 r=0;for(int j=i;j<64;j+=5)r|=1ULL<<j;return r;}
static void initA(void){u64 w[3]={H0,H1,H0^H1};for(int t=0;t<3;t++)for(int i=0;i<5;i++)ka[t][i]=w[t]&msk(i);}
__attribute__((noinline)) void blkA(u64*y1,u64*y0){u128 l=clA(*y0,ka[0]),h=clA(*y1,ka[1]),m=clA(*y0^*y1,ka[2]);join(l,h,m,y1,y0);}
/* B: four classes, 32x32->64, all sixteen products */
#define M4 0x1111111111111111ULL
static u64 kb[9][4];
L u64 cl32B(u64 a,const u64*k){u64 A[4];for(int i=0;i<4;i++)A[i]=a&(M4<<i);u64 z=0;
  for(int r=0;r<4;r++){u64 s=0;for(int i=0;i<4;i++)s^=A[i]*k[(r-i)&3];z|=s&(M4<<r);}return z;}
/* C: four classes, Karatsuba over the classes */
static u64 kc[9][9];
L void spread(u64 a,u64*s){for(int i=0;i<4;i++)s[i]=(a>>i)&0x11111111;s[4]=s[0]^s[1];s[5]=s[2]^s[3];s[6]=s[0]^s[2];s[7]=s[1]^s[3];s[8]=s[4]^s[5];}
L u64 cl32C(u64 a,const u64*k){u64 s[9],p[9];spread(a,s);for(int i=0;i<9;i++)p[i]=s[i]*k[i];
  u64 l1=p[4]^p[0]^p[1],h1=p[5]^p[2]^p[3],m1=p[8]^p[6]^p[7];
  u64 c2=p[1]^p[6]^p[0]^p[2],c3=m1^l1^h1,c4=p[2]^p[7]^p[1]^p[3];
  return ((p[0]&M4))^((c4&M4)<<4)^(((l1&M4)^((h1&M4)<<4))<<1)^(((c2&M4)^((p[3]&M4)<<4))<<2)^((c3&M4)<<3);}
static void w9(u64 y1,u64 y0,u64*w){uint32_t a=y0,b=y0>>32,c=y1,d=y1>>32;u64 v[9]={a,b,a^b,c,d,c^d,a^c,b^d,a^b^c^d};memcpy(w,v,72);}
static void initBC(void){u64 w[9];w9(H1,H0,w);for(int i=0;i<9;i++){for(int j=0;j<4;j++)kb[i][j]=w[i]&(M4<<j);spread(w[i],kc[i]);}}
L u128 k2(u64 l,u64 h,u64 m){m^=l^h;return (u128)l^((u128)m<<32)^((u128)h<<64);}
__attribute__((noinline)) void blkB(u64*y1,u64*y0){u64 w[9],p[9];w9(*y1,*y0,w);for(int i=0;i<9;i++)p[i]=cl32B(w[i],kb[i]);
  join(k2(p[0],p[1],p[2]),k2(p[3],p[4],p[5]),k2(p[6],p[7],p[8]),y1,y0);}
__attribute__((noinline)) void blkC(u64*y1,u64*y0){u64 w[9],p[9];w9(*y1,*y0,w);for(int i=0;i<9;i++)p[i]=cl32C(w[i],kc[i]);
  join(k2(p[0],p[1],p[2]),k2(p[3],p[4],p[5]),k2(p[6],p[7],p[8]),y1,y0);}
/* D: B in SSE2, two products at a time */
static __m128i kd[5][4];
static void initD(void){u64 w[10];w9(H1,H0,w);w[9]=0;for(int i=0;i<5;i++)for(int j=0;j<4;j++)kd[i][j]=_mm_set_epi64x(w[2*i+1]&(M4<<j),w[2*i]&(M4<<j));}
__attribute__((noinline)) void blkD(u64*y1,u64*y0){u64 w[10],p[10];w9(*y1,*y0,w);w[9]=0;
  for(int i=0;i<5;i++){__m128i a=_mm_loadu_si128((void*)(w+2*i)),z=_mm_setzero_si128(),A[4];
    for(int j=0;j<4;j++)A[j]=_mm_and_si128(a,_mm_set1_epi64x(M4<<j));
    for(int r=0;r<4;r++){__m128i s=_mm_setzero_si128();for(int j=0;j<4;j++)s=_mm_xor_si128(s,_mm_mul_epu32(A[j],kd[i][(r-j)&3]));
      z=_mm_or_si128(z,_mm_and_si128(s,_mm_set1_epi64x(M4<<r)));}
    _mm_storeu_si128((void*)(p+2*i),z);}
  join(k2(p[0],p[1],p[2]),k2(p[3],p[4],p[5]),k2(p[6],p[7],p[8]),y1,y0);}
/* E: four classes of 64-bit words, Karatsuba over the classes, the top
   class bit of Y (bits 60..63 of each word) apart */
static u64 ke[3][9]; static u64 top[8][2];
L void spread64(u64 a,u64*s){for(int i=0;i<4;i++)s[i]=(a>>i)&M4;s[4]=s[0]^s[1];s[5]=s[2]^s[3];s[6]=s[0]^s[2];s[7]=s[1]^s[3];s[8]=s[4]^s[5];}
L u128 clE(u64 a,const u64*k){u64 s[9];u128 p[9],M=((u128)M4<<64)|M4;spread64(a,s);for(int i=0;i<9;i++)p[i]=(u128)s[i]*k[i];
  u128 l1=p[4]^p[0]^p[1],h1=p[5]^p[2]^p[3],m1=p[8]^p[6]^p[7];
  u128 c2=p[1]^p[6]^p[0]^p[2],c3=m1^l1^h1,c4=p[2]^p[7]^p[1]^p[3];
  return ((p[0]^(c4<<4))&M)^(((l1^(h1<<4))&M)<<1)^(((c2^(p[3]<<4))&M)<<2)^((c3&M)<<3);}
static void mulref(u64 a1,u64 a0,u64*y1,u64*y0){join(ref_cl(a0,H0),ref_cl(a1,H1),ref_cl(a0^a1,H0^H1),y1,y0);(void)0;}
static void initE(void){spread64(H0,ke[0]);spread64(H1,ke[1]);spread64(H0^H1,ke[2]);
  for(int j=0;j<4;j++){mulref(0,1ULL<<(60+j),&top[j][1],&top[j][0]);mulref(1ULL<<(60+j),0,&top[4+j][1],&top[4+j][0]);}}
__attribute__((noinline)) void blkE(u64*y1,u64*y0){u64 a=*y0,b=*y1,t1=0,t0=0;
  for(int j=0;j<4;j++){u64 m=-((a>>(60+j))&1);t0^=m&top[j][0];t1^=m&top[j][1];m=-((b>>(60+j))&1);t0^=m&top[4+j][0];t1^=m&top[4+j][1];}
  a=a<<4>>4;b=b<<4>>4;join(clE(a,ke[0]),clE(b,ke[1]),clE(a^b,ke[2]),y1,y0);*y0^=t0;*y1^=t1;}
__attribute__((noinline)) void blkR(u64*y1,u64*y0){mulref(*y1,*y0,y1,y0);}
int main(){H0=0x0123456789abcdefULL*0x9e3779b97f4a7c15ULL;H1=H0*0xd1342543de82ef95ULL+12345;initA();initBC();initD();initE();
  struct{const char*n;void(*f)(u64*,u64*);}t[]={{"A k5 64x64 25x3 mul",blkA},{"B k4 32x32 144 imul",blkB},{"C k4 32x32 81 imul",blkC},{"D B with pmuludq",blkD},{"E k4 64x64 27 mul",blkE}};
  for(int i=0;i<5;i++){int bad=0;u64 y1=~0ULL,y0=~0ULL,r1=y1,r0=y0;for(int j=0;j<20000;j++){t[i].f(&y1,&y0);blkR(&r1,&r0);bad+=(y1!=r1||y0!=r0);}
    double best=1e9;for(int q=0;q<200;q++){u64 c=__rdtsc();for(int j=0;j<2000;j++)t[i].f(&y1,&y0);double d=(__rdtsc()-c)/2000.;if(d<best)best=d;}
    printf("%-22s bad=%d  %.0f TSC cycles/block\n",t[i].n,bad,best);}}
