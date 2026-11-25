import random,subprocess,sys
exec(open('gen.py').read().split("def dbl():")[0])
exec("""
def cp(o,a): pass
""")
# symbolic dag, one value per op; slots assigned greedily afterwards
OPS={ # name:(kind,args)
 'd':('mul','Z','Z'),'tm':('sub','X','d'),'tp':('add','X','d'),'g':('mul','H','H'),
 'z3':('mul','H','Z'),'m0':('mul','tm','tp'),'S':('mul','X','g'),'m':('tri','m0'),
 'mm':('mul','m','m'),'g2':('mul','g','g'),'x3':('x3','mm','S'),'w':('sub','S','x3'),
 'm2':('add','m','m'),'q':('mul','m2','w'),'h3':('subf','q','g2')}
def order(rnd):
    done=set('XHZ');left=set(OPS);o=[]
    while left:
        r=[k for k in sorted(left) if all(a in done for a in OPS[k][1:])]
        k=rnd.choice(r);o.append(k);left.remove(k);done.add(k)
    return o
def valid(o):
    done=set('XHZ')
    for k in o:
        if not all(a in done for a in OPS[k][1:]): return False
        done.add(k)
    return True
def assign(o):
    # final slots: x3->X, h3->H, z3->Z ; temps from pool of T0.. (6 more)
    last={}
    for i,k in enumerate(o):
        for a in OPS[k][1:]: last[a]=i
    slot={'X':0,'H':72,'Z':144}; free=[216+72*i for i in range(6)]; final={'x3':'X','h3':'H','z3':'Z'}
    prog=[]
    for i,k in enumerate(o):
        kind,*args=OPS[k]
        a=[slot[x] for x in args]
        for x in set(args):
            if last[x]==i and slot[x] not in (0,72,144): free.append(slot[x])
        if k in final:
            v=final[k]
            if last.get(v,-1)>i: return None
            s=slot[v]
        else:
            if not free: return None
            s=free.pop(0) if False else free.pop()
        slot[k]=s; prog.append((kind,s,a))
    return prog
def emit(prog):
    for kind,s,a in prog:
        if kind=='mul': call(s,*a)
        else: globals()[kind](s,*a)
def build(progs,fname):
    out.clear(); e(".intel_syntax noprefix"); e(".text")
    for i,p in enumerate(progs): fn(f"d{i}",lambda p=p: emit(p))
    open(fname,'w').write("\n".join(out)+"\n")
exec("def fn"+open('gen.py').read().split("def fn")[1].split("fn(\"p_dbl\"")[0])
def measure(progs):
    build(progs,'s.s'); n=len(progs)
    c='#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n#include <x86intrin.h>\ntypedef void F(uint64_t*,uint64_t);\n'+''.join(f'F d{i};' for i in range(n))+'static uint64_t ws[1024] __attribute__((aligned(64)));F*fs[]={'+','.join(f'd{i}' for i in range(n))+'};int main(){for(int i=0;i<'+str(n)+';i++){for(int j=0;j<1024;j++)ws[j]=rand()*0x100000001ull;for(int j=8;j<81;j+=9)ws[j]&=255;uint64_t b=-1;for(int k=0;k<150;k++){uint64_t t=__rdtsc();fs[i](ws,100);t=__rdtsc()-t;if(t<b)b=t;}printf("%.1f\\n",b/100.0);}}'
    open('s.c','w').write(c)
    subprocess.check_call("gcc -O1 s.c s.s mul.s -o s.out 2>/dev/null",shell=True)
    best=[1e9]*n
    for _ in range(2):
        for i,v in enumerate(subprocess.check_output("./s.out").split()): best[i]=min(best[i],float(v))
    return best
if __name__=="__main__":
    rnd=random.Random(int(sys.argv[1])); pool=[]
    for rounds in range(int(sys.argv[2])):
        cand=[]
        while len(cand)<40:
            if rounds==0 or rnd.random()<.2: o=order(rnd)
            else:
                o=list(rnd.choice(pool)[1])
                for _ in range(rnd.randint(1,3)):
                    i=rnd.randrange(len(o)); k=o.pop(i); o.insert(rnd.randrange(len(o)+1),k)
                if not valid(o): continue
            p=assign(o)
            if p: cand.append((o,p))
        t=measure([p for _,p in cand])
        pool=sorted(pool+[(x,o,p) for x,(o,p) in zip(t,cand)],key=lambda z:z[0])[:8]
        print(rounds,[round(x[0],1) for x in pool[:4]],min(t),max(t),flush=True)
    for x,o,p in pool[:3]: print(x,' '.join(o)); print(p)
