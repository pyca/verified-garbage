/* UNPROVEN prototypes, linked only into the standalone experiment. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
typedef uint64_t U;
typedef __uint128_t W;
static void finish(U *o, U *t, U *tmp, const U *m, size_t n) {
    U borrow=0;
    for(size_t j=0;j<n;j++){U x=t[j]-m[j], b=t[j]<m[j];tmp[j]=x-borrow;borrow=b|(x<borrow);}
    U mask=-(U)(t[n]<borrow);
    for(size_t j=0;j<n;j++)o[j]=tmp[j]^((tmp[j]^t[j])&mask);
}
static inline void row(U *t,const U *b,const U *m,size_t n,U ai,U inv){
    W z=(W)ai*b[0]+t[0]; U c=z>>64, q=(U)z*inv;
    z=(W)q*m[0]+(U)z; U d=z>>64;
    for(size_t j=1;j<n;j++){
        z=(W)ai*b[j]+t[j]+c;c=z>>64;
        z=(W)q*m[j]+(U)z+d;d=z>>64;t[j-1]=z;
    }
    z=(W)t[n]+c+d;t[n-1]=z;t[n]=z>>64;
}
void c_one(U *o,const U *a,const U *b,const U *m,size_t n,U inv,U *t,U *tmp){
    memset(t,0,(n+1)*8);
    for(size_t i=0;i<n;i++)row(t,b,m,n,a[i],inv);
    finish(o,t,tmp,m,n);
}
void c_two(U *o,const U *a,const U *b,const U *m,size_t n,U inv,U *t,U *tmp){
    memset(t,0,(n+1)*8);size_t i=0;
    for(;i+1<n;i+=2){
        U a0=a[i],a1=a[i+1];W z=(W)a0*b[0]+t[0];U c0=z>>64,q0=(U)z*inv;
        z=(W)q0*m[0]+(U)z;U d0=z>>64,c1=0,d1=0,q1=0;
        for(size_t j=1;j<n;j++){
            z=(W)a0*b[j]+t[j]+c0;c0=z>>64;
            z=(W)q0*m[j]+(U)z+d0;d0=z>>64;U v=z;
            z=(W)a1*b[j-1]+v+c1;c1=z>>64;
            if(j==1){q1=(U)z*inv;z=(W)q1*m[0]+(U)z;d1=z>>64;}
            else {z=(W)q1*m[j-1]+(U)z+d1;d1=z>>64;t[j-2]=z;}
        }
        z=(W)t[n]+c0+d0;U v=z,top=z>>64;
        z=(W)a1*b[n-1]+v+c1;c1=z>>64;
        z=(W)q1*m[n-1]+(U)z+d1;d1=z>>64;t[n-2]=z;
        z=(W)top+c1+d1;t[n-1]=z;t[n]=z>>64;
    }
    if(i<n)row(t,b,m,n,a[i],inv);
    finish(o,t,tmp,m,n);
}
static inline void acc(U s[3], U x,U y){
    W p=(W)x*y,z=(W)s[0]+(U)p;s[0]=z;
    z=(W)s[1]+(U)(p>>64)+(U)(z>>64);s[1]=z;s[2]+=z>>64;
}
void c_column(U *o,const U *a,const U *b,const U *m,size_t n,U inv,U *t,U *tmp){
    (void)b;U s[3]={0,0,0};
    for(size_t k=0;k<2*n;k++){
        size_t lo=k<n?0:k-n+1,hi=k<n?k:n-1;
        if(k<2*n-1)for(size_t j=lo;j<=hi && j<=k-j;j++){
            acc(s,a[j],a[k-j]);if(j!=k-j)acc(s,a[j],a[k-j]);
        }
        for(size_t j=lo;j<n && j<k;j++)acc(s,t[j],m[k-j]);
        if(k<n){t[k]=s[0]*inv;acc(s,t[k],m[0]);}
        else t[k]=s[0];
        s[0]=s[1];s[1]=s[2];s[2]=0;
    }
    t[2*n]=s[0];finish(o,t+n,tmp,m,n);
}
