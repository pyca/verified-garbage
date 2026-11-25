
import re,subprocess,sys,random
S=sys.argv[1]; txt=open(S+'/proto/pieces.txt').read()
parts={}
for b in txt.split('@')[1:]:
    h,_,body=b.partition('\n'); parts[h.strip()]=body.rstrip('\n')
def whole(n,order):
    w=parts['whole '+n]; i=[m.start() for m in re.finditer(r'(?m)^\.Lx', w)][1]; lab=w[i:w.index(':',i)]
    j=w.index('jne '+lab,i); head=w[:i]+lab+':\n'; tail='sub rbx, 1\n'+w[j:]
    return head+'\n'.join(parts[n+' '+o] for o in order)+'\n'+tail
def build(orders):
    out='.intel_syntax noprefix\n.text\n'+parts['inv']+'\n'
    for k,(n,o) in enumerate(orders):
        out+=re.sub(r'\.Lx',f'.Lv{k}_',whole(n,o).replace('x_'+n,f'f{k}'))+'\n'
    open(S+'/proto/o.s','w').write(out)
    N=len(orders)
    c='#include <stdio.h>\n#include <string.h>\n#include <stdint.h>\n#include <x86intrin.h>\ntypedef void fn(uint8_t*,const uint8_t*,const uint8_t*,uint64_t*);\n'
    c+='fn '+','.join(f'f{k}' for k in range(N))+';\nfn*F[]={'+','.join(f'f{k}' for k in range(N))+'};static uint64_t sc[512]__attribute__((aligned(64)));\n'
    c+='int main(){uint8_t o[32],k[32],u[32];double best[%d];memset(k,0x42,32);for(int j=0;j<%d;j++)best[j]=1e18;for(int r=0;r<150;r++)for(int j=0;j<%d;j++){memset(u,9,32);uint64_t t=__rdtsc();for(int i=0;i<12;i++){F[j](o,k,u,sc);memcpy(u,o,32);}double d=(__rdtsc()-t)/12.0;if(d<best[j])best[j]=d;}for(int j=0;j<%d;j++){printf("%%.0f %%02x%%02x\\n",best[j],o[0],o[1]);}}'%(N,N,N,N)
    open(S+'/proto/o.c','w').write(c)
    subprocess.check_call(['gcc','-O2','-z','noexecstack','-o',S+'/proto/o',S+'/proto/o.c',S+'/proto/o.s'])
    return [l.split()[0] for l in subprocess.run([S+'/proto/o'],stdout=subprocess.PIPE,text=True).stdout.split('\n') if l]
if __name__=='__main__':
    O={'chosen':'A D B C UV P AA BB Q E s x2 d w dd z2 x3 z3','rfc':'A B C D UV AA BB E P Q s d x3 dd z3 x2 w z2',
     'v1':'D A B C UV P AA BB Q s E d x2 dd w x3 z2 z3','v2':'A B C D UV P Q AA BB s d E x2 x3 dd w z3 z2','v3':'C D A B UV AA P BB Q E d w x2 dd s z2 z3 x3',
     'v4':'A D B C UV P AA BB Q E d w dd x2 s z2 z3 x3','v5':'A D B C UV P Q AA BB d E dd w s z2 z3 x2 x3','v6':'A D C B UV Q AA P BB E d s w dd x2 z2 z3 x3'}
    L=[(n,o.split()) for n in ('base','adx') for o in O.values()]
    r=build(L); names=list(O)
    for i,(n,o) in enumerate(L): print(n,names[i%len(O)],r[i])
