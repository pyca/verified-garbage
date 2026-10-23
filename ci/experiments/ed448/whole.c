#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <openssl/evp.h>
typedef uint32_t(*fn)(const uint8_t*,const uint8_t*,uint64_t,const uint8_t*,uint64_t,const uint8_t*,uint64_t*);
#define DECL(n) extern uint32_t ed448_whole_trial##n(const uint8_t*,const uint8_t*,uint64_t,const uint8_t*,uint64_t,const uint8_t*,uint64_t*);
DECL(0) DECL(14) DECL(0_sha3) DECL(14_sha3)
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(int argc,char**argv){
 int sha3=argc>1; fn fs[2]={sha3?ed448_whole_trial0_sha3:ed448_whole_trial0,sha3?ed448_whole_trial14_sha3:ed448_whole_trial14};
 uint8_t seed[57],pk[57],sig[114],message[16384];uint64_t ws[1024];memset(seed,0x42,57);memset(message,0x5a,sizeof message);
 EVP_PKEY *key=EVP_PKEY_new_raw_private_key(EVP_PKEY_ED448,0,seed,57);size_t pks=57;if(!key||!EVP_PKEY_get_raw_public_key(key,pk,&pks))abort();
 EVP_PKEY *pub=EVP_PKEY_new_raw_public_key(EVP_PKEY_ED448,0,pk,57);const int sizes[]={64,1024,16384};
 puts("round,bytes,variant,us");
 for(int z=0;z<3;z++){
  int n=sizes[z];size_t sl=114;EVP_MD_CTX *s=EVP_MD_CTX_new();if(!EVP_DigestSignInit(s,0,0,0,key)||!EVP_DigestSign(s,sig,&sl,message,n))abort();EVP_MD_CTX_free(s);
  for(int v=0;v<2;v++){
   memset(ws,0,sizeof ws);if(fs[v](pk,0,0,message,n,sig,ws)!=1){fprintf(stderr,"FAIL whole good v%d n%d\n",v,n);return 1;}
   sig[0]^=1;if(fs[v](pk,0,0,message,n,sig,ws)!=0){fprintf(stderr,"FAIL whole bad v%d n%d\n",v,n);return 1;}sig[0]^=1;
  }
  for(int r=0;r<7;r++)for(int j=0;j<3;j++){
   int v=r%2?2-j:j;double start=now();unsigned sum=0;
   for(int i=0;i<1000;i++){
    if(v<2){memset(ws,0,sizeof ws);sum+=fs[v](pk,0,0,message,n,sig,ws);OPENSSL_cleanse(ws,sizeof ws);}
    else {EVP_MD_CTX *c=EVP_MD_CTX_new();if(!EVP_DigestVerifyInit(c,0,0,0,pub))abort();sum+=EVP_DigestVerify(c,sig,114,message,n);EVP_MD_CTX_free(c);}
   }
   if(sum!=1000)abort();printf("%d,%d,%s,%.6f\n",r,n,v==0?"base":v==1?"joint8-key6":"openssl",(now()-start)*1e6/1000);fflush(stdout);
  }
 }
 EVP_PKEY_free(pub);EVP_PKEY_free(key);
}
