#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
extern unsigned proto_recover(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
extern unsigned proto_baseline(unsigned char*,unsigned,unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,const unsigned char*,unsigned,uint64_t*,unsigned);
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
static unsigned readhex(FILE*f,unsigned char*out){char line[4096];if(!fgets(line,sizeof(line),f))exit(2);unsigned len=strcspn(line,"\r\n")/2;for(unsigned j=0;j<len;j++){unsigned x;if(sscanf(line+2*j,"%2x",&x)!=1)exit(2);out[j]=x;}return len;}
int main(int argc,char**argv){
 for(unsigned bits=2048;bits<=4096;bits+=1024){char path[256],line[4096];snprintf(path,sizeof(path),"%s/key%u.txt",argc>1?argv[1]:"/workspace/scratch/evidence",bits);FILE*f=fopen(path,"r");if(!f)return 2;unsigned char nb[1024],eb[1024],db[1024],p[2][1024],q[2][1024];unsigned k=readhex(f,nb),el=readhex(f,eb),dl=readhex(f,db);fclose(f);unsigned wl=16*k+32;uint64_t*ws=calloc(wl,sizeof(uint64_t));
 for(unsigned round=0;round<3;round++){for(unsigned seq=0;seq<2;seq++){unsigned mode=seq^(round%2);double start=now();unsigned ok=0;for(unsigned rep=0;rep<3;rep++)ok=mode?proto_recover(p[mode],k,q[mode],k,nb,k,eb,el,db,dl,ws,wl):proto_baseline(p[mode],k,q[mode],k,nb,k,eb,el,db,dl,ws,wl);printf("machine,bits=%u,round=%u,fused=%u,ms=%.3f,ok=%u\n",bits,round,mode,(now()-start)*1000/3,ok);fflush(stdout);if(ok!=1)return 3;}
 if(memcmp(p[0],p[1],k)||memcmp(q[0],q[1],k)){fprintf(stderr,"MISMATCH\n");return 1;}}
 free(ws);
 }
}
