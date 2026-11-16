#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
void x_new(uint8_t*, const uint8_t*, const uint8_t*, uint64_t*);
static uint64_t scratch[512];
int main(int argc,char**argv){
  int n=atoi(argv[1]); srand(7); uint8_t s[32],p[32],o[32];
  for(int t=0;t<n;t++){
    for(int i=0;i<32;i++){s[i]=rand();p[i]=rand();}
    if(t==1) memset(p,0xff,32); if(t==2){memset(p,0,32);} if(t==3){memset(s,0xff,32);memset(p,0xff,32);p[31]=0x7f;p[0]=0xec;}
    if(t==4){memset(p,0xff,32);p[31]=0x7f;p[0]=0xed;} if(t==5){memset(p,0,32);p[0]=9;}
    x_new(o,s,p,scratch);
    for(int i=0;i<32;i++)printf("%02x",s[i]); printf(" ");
    for(int i=0;i<32;i++)printf("%02x",p[i]); printf(" ");
    for(int i=0;i<32;i++)printf("%02x",o[i]); printf("\n");
  }
}
