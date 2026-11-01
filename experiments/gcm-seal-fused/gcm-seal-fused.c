#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#ifdef WITH_OPENSSL
#include <openssl/evp.h>
#include <openssl/crypto.h>
#endif
extern void seal_base(const void*,uint64_t,const void*,uint64_t,const void*,uint64_t,void*,uint64_t,void*,void*);
extern void seal_fused(const void*,uint64_t,const void*,uint64_t,const void*,uint64_t,void*,uint64_t,void*,void*);
static _Alignas(16) uint8_t ctx[256],nonce[64],aad[128],data[32768],original[32768],tag[16],scratch[2560];
static uint64_t now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
static volatile uint8_t checksum;
#ifdef WITH_OPENSSL
static EVP_CIPHER_CTX *ssl;
static void ssl_seal(unsigned n,int outplace){int used=0,last=0;
 if(!EVP_EncryptInit_ex(ssl,NULL,NULL,NULL,nonce)||!EVP_EncryptUpdate(ssl,NULL,&used,aad,13)||
    !EVP_EncryptUpdate(ssl,data,&used,outplace?original:data,(int)n)||!EVP_EncryptFinal_ex(ssl,data+used,&last)||
    !EVP_CIPHER_CTX_ctrl(ssl,EVP_CTRL_GCM_GET_TAG,16,tag)){fprintf(stderr,"OpenSSL failed\n");__builtin_abort();}}
#endif
static void invoke(unsigned v,unsigned nr,unsigned n){
 unsigned which=v%3,outplace=v/3;
 if(which<2){if(outplace)memcpy(data,original,n);
  (which?seal_fused:seal_base)(ctx,nr,nonce,12,aad,13,data,n,tag,scratch);
 }else{
#ifdef WITH_OPENSSL
 ssl_seal(n,(int)outplace);
#else
 (void)nr;__builtin_abort();
#endif
 }}
static double measure(unsigned v,unsigned nr,unsigned n,unsigned reps){uint64_t t=now();
 for(unsigned i=0;i<reps;i++)invoke(v,nr,n);
 uint64_t dt=now()-t;checksum^=data[0]^tag[0];return (double)dt/reps;}
int main(int argc,char**argv){(void)argv;
 if(argc==1){uint64_t nr,nl,al,n;while(fread(&nr,8,1,stdin)==1){
  if(fread(&nl,8,1,stdin)!=1||fread(&al,8,1,stdin)!=1||fread(&n,8,1,stdin)!=1||nl>64||al>128||n>sizeof data||fread(ctx,256,1,stdin)!=1)return 2;
  if((nl&&fread(nonce,nl,1,stdin)!=1)||(al&&fread(aad,al,1,stdin)!=1)||(n&&fread(original,n,1,stdin)!=1))return 3;
  for(unsigned v=0;v<2;v++){memcpy(data,original,n);(v?seal_fused:seal_base)(ctx,nr,nonce,nl,aad,al,data,n,tag,scratch);
   if(n)fwrite(data,n,1,stdout);fwrite(tag,16,1,stdout);}
 }return 0;}
#ifdef WITH_OPENSSL
 printf("# OpenSSL %s\n",OpenSSL_version(OPENSSL_VERSION));
 uint8_t key[32];memset(key,0x24,sizeof key);
 for(unsigned i=0;i<12;i++)nonce[i]=(uint8_t)(7*i+11);
 for(unsigned i=0;i<13;i++)aad[i]=(uint8_t)(17*i+37);
 for(unsigned i=0;i<sizeof original;i++)original[i]=(uint8_t)(29*i+13);
 FILE *f=fopen("gcm-seal-bench-ctx.bin","rb");if(!f)return 4;
 const unsigned sizes[]={63,511,512,513,1024,16384};
 for(unsigned nr=10;nr<=14;nr+=2){if(fread(ctx,256,1,f)!=1)return 5;
  ssl=EVP_CIPHER_CTX_new();const EVP_CIPHER *cipher=nr==10?EVP_aes_128_gcm():nr==12?EVP_aes_192_gcm():EVP_aes_256_gcm();
  if(!ssl||!EVP_EncryptInit_ex(ssl,cipher,NULL,key,nonce))return 6;
  for(unsigned k=0;k<sizeof sizes/sizeof sizes[0];k++){unsigned n=sizes[k],reps=65536/n;uint8_t want[32768],wanttag[16];
   memcpy(data,original,n);invoke(0,nr,n);memcpy(want,data,n);memcpy(wanttag,tag,16);
   for(unsigned v=1;v<6;v++){memcpy(data,original,n);invoke(v,nr,n);if(memcmp(want,data,n)||memcmp(wanttag,tag,16)){fprintf(stderr,"mismatch nr=%u bytes=%u v=%u\n",nr,n,v);return 7;}}
   for(unsigned v=0;v<6;v++){memcpy(data,original,n);uint64_t end=now()+50000000;do{measure(v,nr,n,reps);}while(now()<end);}
   for(unsigned sample=0;sample<25;sample++)for(unsigned j=0;j<6;j++){unsigned v=(sample+j)%6;printf("%u,%u,%u,%u,%.3f\n",nr,n,sample,v,measure(v,nr,n,reps));}
  }EVP_CIPHER_CTX_free(ssl);
 }fclose(f);return 0;
#else
 return 8;
#endif
}
