#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
extern unsigned proto_baseline(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_recover(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_fixed(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_baseline_late(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_recover_late(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_fixed_late(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
typedef unsigned (*recovery)(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
static unsigned readhex(FILE*f,unsigned char*out){char line[4096];if(!fgets(line,sizeof(line),f))exit(2);unsigned len=strcspn(line,"\r\n")/2;for(unsigned j=0;j<len;j++){unsigned x;if(sscanf(line+2*j,"%2x",&x)!=1)exit(2);out[j]=x;}return len;}
int main(int argc,char**argv){
 unsigned sizes[]={512,1024,2048,3072,4096};
 for(unsigned idx=0;idx<5;idx++){unsigned bits=sizes[idx];char path[256],line[4096];snprintf(path,sizeof(path),"%s/key%u.txt",argc>1?argv[1]:"/workspace/scratch/evidence",bits);FILE*f=fopen(path,"r");if(!f)return 2;unsigned char nb[1024],eb[1024],db[1024],p[6][1024],q[6][1024];unsigned k=readhex(f,nb),el=readhex(f,eb),dl=readhex(f,db);fclose(f);unsigned wl=16*k+32;uint64_t*ws=calloc(wl,sizeof(uint64_t));
 recovery modes[]={proto_baseline,proto_recover,proto_fixed,proto_baseline_late,proto_recover_late,proto_fixed_late};
 for(unsigned round=0;round<3;round++){for(unsigned seq=0;seq<6;seq++){unsigned mode=(seq+round)%6;double start=now();unsigned ok=0;for(unsigned rep=0;rep<3;rep++)ok=modes[mode](p[mode],k,q[mode],k,nb,k,eb,el,db,dl,ws,wl);printf("machine,bits=%u,round=%u,mode=%u,ms=%.3f,ok=%u\n",bits,round,mode,(now()-start)*1000/3,ok);fflush(stdout);if(ok!=1)return 3;}
 for(unsigned mode=1;mode<6;mode++){if(memcmp(p[0],p[mode],k)||memcmp(q[0],q[mode],k)){fprintf(stderr,"MISMATCH\n");return 1;}}}
 free(ws);
 }
}
