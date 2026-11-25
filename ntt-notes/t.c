#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
void my_fwd(int16_t*); void my_inv(int16_t*);
#define Q 3329
static int Z[128];
static int br(int k){int r=0;for(int i=0;i<7;i++)r|=((k>>i)&1)<<(6-i);return r;}
static void ntt(int*f){int i=1;for(int l=128;l>=2;l/=2)for(int s=0;s<256;s+=2*l){int z=Z[i++];for(int j=s;j<s+l;j++){int t=z*f[j+l]%Q;f[j+l]=(f[j]-t+Q)%Q;f[j]=(f[j]+t)%Q;}}}
static void intt(int*f){int i=127;for(int l=2;l<=128;l*=2)for(int s=0;s<256;s+=2*l){int z=Z[i--];for(int j=s;j<s+l;j++){int t=f[j];f[j]=(t+f[j+l])%Q;f[j+l]=z*(f[j+l]-t+Q)%Q;}}for(int j=0;j<256;j++)f[j]=f[j]*3303%Q;}
int main(){for(int k=0;k<128;k++){int e=br(k),z=1;while(e--)z=z*17%Q;Z[k]=z;}
int bad=0;for(int it=0;it<3000;it++){int16_t a[256]__attribute__((aligned(16))),b[256];int r[256],r2[256];
for(int i=0;i<256;i++){int v=rand()%Q; if(it%5==0)v=rand()%2?0:Q-1; if(it%5==1)v=Q-1; if(it%5==2)v=rand()%3?Q-1:0; if(it==3)v=0; a[i]=b[i]=r[i]=r2[i]=v;}
my_fwd(a);ntt(r);for(int i=0;i<256;i++)if(a[i]!=r[i]){if(!bad)printf("fwd %d %d: %d %d\n",it,i,a[i],r[i]);bad++;}
my_inv(b);intt(r2);for(int i=0;i<256;i++)if(b[i]!=r2[i]){if(bad<5)printf("inv %d %d: %d %d\n",it,i,b[i],r2[i]);bad++;}}
printf("bad %d\n",bad);}
