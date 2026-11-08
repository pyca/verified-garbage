#define _POSIX_C_SOURCE 200809L
#include "probe.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <inttypes.h>
#include <pthread.h>
#include <openssl/evp.h>

static volatile uint64_t sink, calls;
#ifdef __riscv
static int counting;
static perm_fn selected;
#endif
static const uint64_t rc[24]={1,0x8082,0x800000000000808aULL,0x8000000080008000ULL,0x808b,0x80000001,0x8000000080008081ULL,0x8000000000008009ULL,0x8a,0x88,0x80008009,0x8000000a,0x8000808b,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,0x8000000000008002ULL,0x8000000000000080ULL,0x800a,0x800000008000000aULL,0x8000000080008081ULL,0x8000000000008080ULL,0x80000001,0x8000000080008008ULL};
static uint64_t rol(uint64_t x,unsigned n){return n?(x<<n)|(x>>(64-n)):x;}
static void reference(void *state,void *scratch){
 (void)scratch; uint64_t a[25],b[25],c[5],d[5];memcpy(a,state,200);
 static const unsigned rho[25]={0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14};
 for(unsigned r=0;r<24;r++){
  for(unsigned x=0;x<5;x++)c[x]=a[x]^a[x+5]^a[x+10]^a[x+15]^a[x+20];
  for(unsigned x=0;x<5;x++)d[x]=c[(x+4)%5]^rol(c[(x+1)%5],1);
  for(unsigned y=0;y<5;y++)for(unsigned x=0;x<5;x++)b[y+5*((2*x+3*y)%5)]=rol(a[x+5*y]^d[x],rho[x+5*y]);
  for(unsigned y=0;y<5;y++)for(unsigned x=0;x<5;x++)a[x+5*y]=b[x+5*y]^((~b[(x+1)%5+5*y])&b[(x+2)%5+5*y]);
  a[0]^=rc[r];
 }memcpy(state,a,200);
}
#ifdef __riscv
extern void __real_vg_keccak_f1600(void*,void*);
static void baseline(void *s,void *w){__real_vg_keccak_f1600(s,w);}
void __wrap_vg_keccak_f1600(void *s,void *w){if(counting)calls++;selected(s,w);}
extern size_t vg_shake128_update(uint64_t*,size_t,const uint8_t*,size_t,uint64_t*);
extern void vg_shake128_finalize(uint64_t*,size_t);
extern size_t vg_shake128_squeeze(uint64_t*,size_t,uint8_t*,size_t);
extern size_t vg_sha3_256_update(uint64_t*,size_t,const uint8_t*,size_t,uint64_t*);
extern void vg_shake256_finalize(uint64_t*,size_t);
extern size_t vg_shake256_squeeze(uint64_t*,size_t,uint8_t*,size_t);
extern uint32_t vg_mlkem768_keygen(const uint8_t*,uint8_t*,uint8_t*,uint64_t*);
extern uint32_t vg_mlkem768_encaps(const uint8_t*,const uint8_t*,uint8_t*,uint8_t*,uint64_t*);
extern uint32_t vg_mlkem768_decaps(const uint8_t*,const uint8_t*,uint8_t*,uint64_t*);
extern uint32_t vg_mldsa65_keygen(const uint8_t*,uint8_t*,uint8_t*,uint64_t*);
extern uint32_t vg_mldsa65_sign(const uint8_t*,const uint8_t*,const uint8_t*,uint8_t*,uint64_t*);
extern uint32_t vg_mldsa65_verify(const uint8_t*,const uint8_t*,const uint8_t*,uint64_t*);
#else
static void baseline(void*s,void*w){reference(s,w);}
#endif
struct variant{const char *name;perm_fn fn;};
#define ENTRY(n) {#n,candidate_##n},
static const struct variant variants[]={{"verified",baseline},CANDIDATES(ENTRY)};
#undef ENTRY
#define NV (sizeof(variants)/sizeof(variants[0]))
static void fail(const char *what,const char *name){fprintf(stderr,"FAILED %s: %s\n",name,what);exit(1);}
static uint64_t random_word(uint64_t *x){*x^=*x<<13;*x^=*x>>7;*x^=*x<<17;return *x;}
#ifdef __riscv
static void bytes(uint8_t *p,size_t n,uint64_t seed){for(size_t i=0;i<n;i++)p[i]=(uint8_t)random_word(&seed);}
#endif
static void check_permutations(void){
 uint64_t gen=0x14aa3d907324b1ULL,expected[25],input[25];uint8_t storage[208];uint64_t scratch[64];unsigned count=0;
 for(unsigned n=0;n<1858;n++){
  for(unsigned i=0;i<25;i++)input[i]=(n<2)?(n?UINT64_MAX:0):n<1602?(i==(n-2)/64?1ULL<<((n-2)%64):0):random_word(&gen);
  memcpy(expected,input,200);reference(expected,scratch);
  for(unsigned v=0;v<NV;v++)for(unsigned off=0;off<(n<16?8:1);off++){
   memcpy(storage+off,input,200);variants[v].fn(storage+off,scratch);
   if(memcmp(storage+off,expected,200))fail("permutation differential",variants[v].name);
   count++;
  }
 }fprintf(stderr,"permutation checks: %u (walking bits, random states, offsets 0..7)\n",count);
}
#ifdef __riscv
static uint8_t msg[16384],out[4096];
static void shake(unsigned bits,size_t mlen,size_t olen,uint8_t *o){
 uint64_t state[25]={0},work[80];size_t pos;
 if(bits==128){pos=vg_shake128_update(state,0,msg,mlen,work);vg_shake128_finalize(state,pos);vg_shake128_squeeze(state,0,o,olen);}
 else{pos=vg_sha3_256_update(state,0,msg,mlen,work);vg_shake256_finalize(state,pos);vg_shake256_squeeze(state,0,o,olen);}
}
static void check_shake(void){
 const size_t lengths[]={0,1,33,34,64,135,136,137,167,168,169,1024,16384};
 uint8_t expected[4096];unsigned checks=0;
 bytes(msg,sizeof(msg),15114);counting=1;
 for(unsigned bits=128;bits<=256;bits+=128)for(unsigned i=0;i<sizeof(lengths)/sizeof(*lengths);i++){
  EVP_MD_CTX *ctx=EVP_MD_CTX_new();if(!ctx)abort();
  if(!EVP_DigestInit_ex(ctx,bits==128?EVP_shake128():EVP_shake256(),NULL)||!EVP_DigestUpdate(ctx,msg,lengths[i])||!EVP_DigestFinalXOF(ctx,expected,sizeof(expected)))abort();
  EVP_MD_CTX_free(ctx);
  for(unsigned v=0;v<NV;v++){
   selected=variants[v].fn;calls=0;shake(bits,lengths[i],sizeof(expected),out);
   if(!calls)fail("Keccak replacement hook was not called",variants[v].name);
   if(memcmp(out,expected,sizeof(expected)))fail("OpenSSL SHAKE differential",variants[v].name);
   checks++;
  }
 }counting=0;fprintf(stderr,"SHAKE/OpenSSL checks: %u; replacement hook exercised for every candidate\n",checks);
}
static uint8_t seed[64],ek[1184],dk[2400],pk[1952],sk[4032],ct[1088],key[32],mu[64],rnd[32],sig[3309];
static uint64_t ws[13056];
static void check_clients(void){
 uint8_t ek2[1184],dk2[2400],pk2[1952],sk2[4032],ct2[1088],key2[32],sig2[3309];unsigned checks=0;
 for(unsigned f=0;f<4;f++){
  bytes(seed,sizeof(seed),4514+f);bytes(mu,sizeof(mu),900+f);bytes(rnd,sizeof(rnd),125+f);
  selected=baseline;counting=1;calls=0;
  if(!vg_mlkem768_keygen(seed,ek,dk,ws)||!vg_mlkem768_encaps(ek,mu,key,ct,ws)||!vg_mldsa65_keygen(seed,pk,sk,ws)||!vg_mldsa65_sign(sk,mu,rnd,sig,ws))fail("fixture construction","verified");
  if(!calls)fail("client replacement hook not called","verified");
  for(unsigned v=0;v<NV;v++){
   selected=variants[v].fn;calls=0;
   if(!vg_mlkem768_keygen(seed,ek2,dk2,ws)||memcmp(ek,ek2,sizeof(ek))||memcmp(dk,dk2,sizeof(dk)))fail("ML-KEM keygen",variants[v].name);
   if(!vg_mlkem768_encaps(ek2,mu,key2,ct2,ws)||memcmp(ct,ct2,sizeof(ct))||memcmp(key,key2,sizeof(key)))fail("ML-KEM encaps",variants[v].name);
   if(!vg_mlkem768_decaps(dk2,ct2,key2,ws)||memcmp(key,key2,sizeof(key)))fail("ML-KEM decaps",variants[v].name);
   ct2[f]^=1;selected=baseline;vg_mlkem768_decaps(dk2,ct2,key,ws);selected=variants[v].fn;vg_mlkem768_decaps(dk2,ct2,key2,ws);
   if(memcmp(key,key2,sizeof(key)))fail("ML-KEM implicit rejection",variants[v].name);
   /* Reconstruct the unmodified fixture key for the next candidate. */
   selected=baseline;vg_mlkem768_encaps(ek,mu,key,ct,ws);selected=variants[v].fn;
   if(!vg_mldsa65_keygen(seed,pk2,sk2,ws)||memcmp(pk,pk2,sizeof(pk))||memcmp(sk,sk2,sizeof(sk)))fail("ML-DSA keygen",variants[v].name);
   if(!vg_mldsa65_sign(sk2,mu,rnd,sig2,ws)||memcmp(sig,sig2,sizeof(sig)))fail("ML-DSA signing",variants[v].name);
   if(!vg_mldsa65_verify(pk2,mu,sig2,ws))fail("ML-DSA verification",variants[v].name);
   sig2[f]^=1;if(vg_mldsa65_verify(pk2,mu,sig2,ws))fail("ML-DSA bad signature accepted",variants[v].name);
   if(!calls)fail("client replacement hook not called",variants[v].name);
   checks+=8;
  }
 }counting=0;fprintf(stderr,"full ML-KEM/ML-DSA differential checks: %u\n",checks);
}
static double now(clockid_t clock){struct timespec t;if(clock_gettime(clock,&t))abort();return (double)t.tv_sec+1e-9*t.tv_nsec;}
static void work(unsigned kind,unsigned count){
 uint64_t st[25]={0},scratch[64];uint32_t ok=0;
 for(unsigned i=0;i<count;i++)switch(kind){
 case 0:selected(st,scratch);break;
 case 1:shake(128,34,504,out);break;
 case 2:shake(256,64,1024,out);break;
 case 3:shake(256,1024,1024,out);break;
 case 4:shake(256,16384,4096,out);break;
 case 5:ok+=vg_mlkem768_keygen(seed,ek,dk,ws);break;
 case 6:ok+=vg_mlkem768_encaps(ek,mu,key,ct,ws);break;
 case 7:ok+=vg_mlkem768_decaps(dk,ct,key,ws);break;
 case 8:ok+=vg_mldsa65_keygen(seed,pk,sk,ws);break;
 case 9:ok+=vg_mldsa65_sign(sk,mu,rnd,sig,ws);break;
 case 10:ok+=vg_mldsa65_verify(pk,mu,sig,ws);break;
 default:abort();
 }
 sink^=st[0]^out[0]^ok;
}
static const char *names[]={"keccak_f1600","shake128_34_504","shake256_64_1024","shake256_1024_1024","shake256_16384_4096","mlkem768_keygen","mlkem768_encaps","mlkem768_decaps","mldsa65_keygen","mldsa65_sign_mu","mldsa65_verify_mu"};
static unsigned calibrate(unsigned kind){
 unsigned n=kind<5?100:3;selected=baseline;double t=now(CLOCK_MONOTONIC);work(kind,n);t=now(CLOCK_MONOTONIC)-t;
 double target=.08;unsigned result=(unsigned)(n*target/(t>1e-7?t:1e-7));if(result<3)result=3;if(result>500000)result=500000;return result;
}
static unsigned variant_index(const char *name){for(unsigned v=0;v<NV;v++)if(!strcmp(name,variants[v].name))return v;fail("unknown candidate",name);return 0;}
static void timings(int clients,int argc,char **argv){
 unsigned ids[NV],nids=0;
 if(clients){ids[nids++]=0;for(int i=2;i<argc;i++)ids[nids++]=variant_index(argv[i]);if(nids==1)fail("no selected candidate","clients");}
 else for(unsigned i=0;i<NV;i++)ids[nids++]=i;
 unsigned begin=clients?5:0,end=clients?11:5;
 puts("workload,round,variant,iterations,wall_ns,cpu_ns");
 for(unsigned kind=begin;kind<end;kind++){
  unsigned n=calibrate(kind);fprintf(stderr,"timing %s: %u iterations per sample\n",names[kind],n);
  for(unsigned round=0;round<7;round++)for(unsigned j=0;j<nids;j++){
   unsigned v=ids[(round&1)?(nids-1-j+round)%nids:(j+round)%nids];selected=variants[v].fn;work(kind,kind<5?30:1);
   double c=now(CLOCK_THREAD_CPUTIME_ID),t=now(CLOCK_MONOTONIC);work(kind,n);t=now(CLOCK_MONOTONIC)-t;c=now(CLOCK_THREAD_CPUTIME_ID)-c;
   printf("%s,%u,%s,%u,%.3f,%.3f\n",names[kind],round,variants[v].name,n,t*1e9/n,c*1e9/n);fflush(stdout);
  }
 }
 fprintf(stderr,"checksum: %" PRIu64 "\n",sink);
}
struct thread_task {perm_fn fn;unsigned count,index;double cpu;uint64_t result;};
static void *thread_worker(void *arg){
 struct thread_task *t=arg;uint64_t state[25]={0},scratch[64];state[0]=t->index+1;
 for(unsigned i=0;i<32;i++)t->fn(state,scratch);
 double c=now(CLOCK_THREAD_CPUTIME_ID);
 for(unsigned i=0;i<t->count;i++)t->fn(state,scratch);
 t->cpu=now(CLOCK_THREAD_CPUTIME_ID)-c;t->result=state[0];return NULL;
}
static void thread_timings(int argc,char **argv){
 unsigned ids[NV],nids=1;ids[0]=0;for(int i=2;i<argc;i++)ids[nids++]=variant_index(argv[i]);
 if(nids==1)fail("no selected candidate","threads");
 puts("workload,round,variant,iterations,wall_ns,cpu_ns");
 for(unsigned workers=1;workers<=4;workers*=4)for(unsigned round=0;round<7;round++)for(unsigned j=0;j<nids;j++){
  unsigned v=ids[(j+round)%nids],n=25000;struct thread_task tasks[4];pthread_t threads[4];
  double wall=now(CLOCK_MONOTONIC),cpu=0;
  for(unsigned i=0;i<workers;i++){tasks[i]=(struct thread_task){variants[v].fn,n,i,0,0};if(pthread_create(&threads[i],NULL,thread_worker,&tasks[i]))abort();}
  for(unsigned i=0;i<workers;i++){if(pthread_join(threads[i],NULL))abort();cpu+=tasks[i].cpu;sink^=tasks[i].result;}
  wall=now(CLOCK_MONOTONIC)-wall;
  printf("keccak_threads%u,%u,%s,%u,%.3f,%.3f\n",workers,round,variants[v].name,n*workers,wall*1e9/(n*workers),cpu*1e9/(n*workers));fflush(stdout);
 }
}

#endif
int main(int argc,char **argv){
 check_permutations();
#ifdef __riscv
 check_shake();check_clients();
 if(argc>1&&!strcmp(argv[1],"--check"))return 0;
 if(argc>1&&!strcmp(argv[1],"--threads"))thread_timings(argc,argv);
 else timings(argc>1&&!strcmp(argv[1],"--clients"),argc,argv);
#else
 (void)argc;(void)argv;fprintf(stderr,"host correctness only; timings require real RISC-V\n");
#endif
 return 0;
}
