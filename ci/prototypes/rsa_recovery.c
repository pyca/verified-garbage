/* UNPROVEN screening harness. No production code. Inputs: Wycheproof keys. */
#include <openssl/bn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define MAX 260
static unsigned N; static uint32_t M[MAX], inv, one[MAX], neg[MAX];
static unsigned long long muls, adds;
static void subsel(uint32_t *o,const uint32_t *a,uint32_t high) {
 uint32_t t[MAX]; uint64_t borrow=0;
 for(unsigned j=0;j<N;j++){uint64_t z=(uint64_t)a[j]-M[j]-borrow;t[j]=z;borrow=z>>63;}
 uint32_t mask=0-(uint32_t)(high>=borrow);
 for(unsigned j=0;j<N;j++)o[j]=(t[j]&mask)|(a[j]&~mask);
}
static void mont(uint32_t *o,const uint32_t *a,const uint32_t *b) {
 uint32_t t[2*MAX+2]={0};muls++;
 for(unsigned i=0;i<N;i++){
  uint64_t c=0;for(unsigned j=0;j<N;j++){uint64_t z=(uint64_t)a[i]*b[j]+t[i+j]+c;t[i+j]=z;c=z>>32;}
  uint64_t z=(uint64_t)t[i+N]+c;t[i+N]=z;t[i+N+1]+=z>>32;
  uint32_t q=t[i]*inv;c=0;
  for(unsigned j=0;j<N;j++){z=(uint64_t)q*M[j]+t[i+j]+c;t[i+j]=z;c=z>>32;}
  z=(uint64_t)t[i+N]+c;t[i+N]=z;t[i+N+1]+=z>>32;
 }
 subsel(o,t+N,t[2*N]);
}
static void addmod(uint32_t *o,const uint32_t *a,const uint32_t *b){
 uint32_t t[MAX];uint64_t c=0;adds++;
 for(unsigned j=0;j<N;j++){uint64_t z=(uint64_t)a[j]+b[j]+c;t[j]=z;c=z>>32;}subsel(o,t,c);
}
static void small(uint32_t *o,const uint32_t *a,unsigned g,int mode){
 uint32_t t[MAX]={0},v[MAX];
 if(mode==1){ /* public candidate, binary expansion */
  unsigned top=31-__builtin_clz(g);memcpy(t,a,N*4);
  while(top--){addmod(t,t,t);if((g>>top)&1)addmod(t,t,a);}
 }else{ /* fixed schedule, masked add; 7 bits covers all 100 candidates */
  for(int k=6;k>=0;k--){addmod(t,t,t);uint32_t mask=0-((g>>k)&1);for(unsigned j=0;j<N;j++)v[j]=a[j]&mask;addmod(t,t,v);}
 }
 memcpy(o,t,N*4);
}
static unsigned eq(const uint32_t *a,const uint32_t*b){uint32_t x=0;for(unsigned j=0;j<N;j++)x|=a[j]^b[j];return x==0;}
static void sel(uint32_t *o,const uint32_t*a,const uint32_t*b,unsigned bit){uint32_t mask=0-bit;for(unsigned j=0;j<N;j++)o[j]=(a[j]&~mask)|(b[j]&mask);}
static int baseline(uint32_t *out,const BIGNUM*r,unsigned t,unsigned c,unsigned g){
 uint32_t tab[16][MAX],y[MAX],x[MAX],v[MAX];memcpy(tab[0],one,N*4);small(tab[1],one,g,1);
 for(unsigned j=2;j<16;j++){mont(tab[j],tab[j-1],tab[1]);}
 memcpy(y,one,N*4);
 for(int k=c-4;k>=0;k-=4){for(int j=0;j<4;j++)mont(y,y,y);unsigned w=0;for(int j=3;j>=0;j--)w=w*2+BN_is_bit_set(r,k+j);memcpy(v,tab[0],N*4);for(unsigned j=1;j<16;j++)sel(v,v,tab[j],w==j);mont(y,y,v);}
 unsigned done=eq(y,one)|eq(y,neg),ok=0;
 for(unsigned k=0;k<c;k++){mont(x,y,y);unsigned e1=eq(x,one),e2=eq(x,neg),live=!done & (k<t);ok|=live&e1;done|=live&(e1|e2|(k+1==t));sel(y,y,x,live&!e1&!e2&(k+1!=t));}
 memcpy(out,y,N*4);return ok;
}
static int fused(uint32_t*out,const BIGNUM*m,unsigned c,unsigned g,int mode){
 uint32_t y[MAX],x[MAX],v[MAX],found[MAX]={0};memcpy(y,one,N*4);unsigned done=1,ok=0;
 for(int k=c-1;k>=0;k--){unsigned bit=BN_is_bit_set(m,k);mont(x,y,y);unsigned e1=eq(x,one),e2=eq(x,neg),hit=(!done)&e1&(!bit);
  sel(found,found,y,hit);ok=(ok|hit)&!bit;done=(done|e1|e2)&!bit;
  small(v,x,g,mode);sel(y,x,v,bit);done|=bit&(eq(y,one)|eq(y,neg));
 }
 memcpy(out,found,N*4);return ok;
}
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
static void words(uint32_t *o,const BIGNUM*b){unsigned char bytes[MAX*4];BN_bn2lebinpad(b,bytes,N*4);for(unsigned j=0;j<N;j++)o[j]=(uint32_t)bytes[j*4]|(uint32_t)bytes[j*4+1]<<8|(uint32_t)bytes[j*4+2]<<16|(uint32_t)bytes[j*4+3]<<24;}
int main(int argc,char**argv){
 for(unsigned bits=2048;bits<=4096;bits+=1024){char path[256],line[4096];snprintf(path,sizeof(path),"%s/key%u.txt",argc>1?argv[1]:"/workspace/scratch/evidence",bits);FILE*f=fopen(path,"r");if(!f)return 2;BIGNUM*n=NULL,*e=NULL,*d=NULL;fgets(line,sizeof(line),f);BN_hex2bn(&n,line);fgets(line,sizeof(line),f);BN_hex2bn(&e,line);fgets(line,sizeof(line),f);BN_hex2bn(&d,line);fclose(f);BN_CTX*ctx=BN_CTX_new();BIGNUM*m=BN_new(),*r=BN_new(),*R=BN_new(),*nm=BN_new();BN_mul(m,e,d,ctx);BN_sub_word(m,1);BN_copy(r,m);unsigned t=0;while(!BN_is_odd(r)){BN_rshift1(r,r);t++;}unsigned c=8*(BN_num_bytes(e)+BN_num_bytes(d));N=(bits+31)/32;words(M,n);uint32_t iv=1;for(int j=0;j<5;j++)iv*=2-M[0]*iv;inv=0-iv;BN_one(R);BN_lshift(R,R,N*32);BN_nnmod(R,R,n,ctx);words(one,R);BN_sub(nm,n,R);words(neg,nm);
  for(unsigned g=2;g<=3;g++){uint32_t out[3][MAX];int ok[3];for(int mode=0;mode<3;mode++){muls=adds=0;double start=now();for(int rep=0;rep<3;rep++)ok[mode]=mode?fused(out[mode],m,c,g,mode):baseline(out[mode],r,t,c,g);printf("%u,g=%u,mode=%d,ms=%.3f,mont=%llu,adds=%llu,ok=%d\n",bits,g,mode,(now()-start)*1000/3,muls/3,adds/3,ok[mode]);}if(ok[0]!=ok[1]||ok[0]!=ok[2]||(ok[0]&&(!eq(out[0],out[1])||!eq(out[0],out[2])))){fprintf(stderr,"MISMATCH\n");return 1;}}
 }
}
