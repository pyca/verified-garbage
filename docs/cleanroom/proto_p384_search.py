import re,random,subprocess,sys,json
ops={};cur=None
for l in open('ops.txt'):
    if l.startswith('@@slots'): slots=json.loads(l[8:]);continue
    if l.startswith('@@'): cur=l[2:].strip();ops[cur]=[];continue
    if l.strip() not in('ret',''): ops[cur].append(re.sub('[{}]','',l.rstrip()))
X,Y,Z=slots[:3];POOL=slots[3:]
def em(k,o,a,b):
    key='dbl' if k=='add' and a==b else 'sqr' if k=='mul' and a==b else k
    def r(m):
        v=int(m.group(0)); return str((o if v<2000000 else a if v<3000000 else b)+v%1000000)
    return '\n'.join(re.sub(r'\b[123]0000\d\d\b',r,l) for l in ops[key])
A={'d':('mul','Z','Z'),'g0':('mul','Y','Y'),'g':('add','g0','g0'),'b':('mul','X','g'),'tm':('sub','X','d'),'tp':('add','X','d'),
'm0':('mul','tm','tp'),'m1':('add','m0','m0'),'m':('add','m1','m0'),'S':('add','b','b'),'z0':('mul','Y','Z'),'z3':('add','z0','z0'),
'mm':('mul','m','m'),'x1':('sub','mm','S'),'x3':('sub','x1','S'),'w':('sub','S','x3'),'q':('mul','m','w'),'u':('mul','g','g'),'u2':('add','u','u'),'y3':('sub','q','u2')}
B=dict(A); 
for k in('z0','g','b','S','u','u2'):B.pop(k)
B.update({'yz':('add','Y','Z'),'z0':('mul','yz','yz'),'z1':('sub','z0','g0'),'z3':('sub','z1','d'),'b':('mul','X','g0'),'b2':('add','b','b'),'S':('add','b2','b2'),
'u':('mul','g0','g0'),'u1':('add','u','u'),'u2':('add','u1','u1'),'u3':('add','u2','u2'),'y3':('sub','q','u3')})
FIN={'x3':'X','y3':'Y','z3':'Z'}; EARLY={'x3':['x1'],'z3':['z0','z1'],'y3':['q']}
def order(O,rnd):
    done=set('XYZ');left=set(O);o=[]
    while left:
        k=rnd.choice([k for k in sorted(left) if all(a in done for a in O[k][1:])]);o.append(k);left.remove(k);done.add(k)
    return o
def valid(O,o):
    done=set('XYZ')
    for k in o:
        if not all(a in done for a in O[k][1:]):return False
        done.add(k)
    return True
def assign(O,o):
    last={}
    for i,k in enumerate(o):
        for a in O[k][1:]:last[a]=i
    sl={'X':X,'Y':Y,'Z':Z};free=POOL[::-1];prog=[]
    for i,k in enumerate(o):
        kind,*a=O[k];s=[sl[x] for x in a]
        for x in set(a):
            if last[x]==i and sl[x] not in (X,Y,Z):free.append(sl[x])
        if k in FIN:
            v=FIN[k]
            if last[v]>i:return None
            t=sl[v]
        else:
            if not free:return None
            t=free.pop()
        sl[k]=t;prog.append((kind,t,*s))
    return prog
core=open('s3.s').read();core=core[core.index('.globl vg_p384_mul'):core.index('.globl p_old')]
def meas(ps):
    t='.intel_syntax noprefix\n.text\n'+core
    for i,p in enumerate(ps):
        t+=f'\n.globl d{i}\nd{i}:\n'+''.join(f'push {r}\n' for r in 'rbx rbp r12 r13 r14 r15'.split())+'sub rsp,8\nmov rbx,rsi\n1:\n'+'\n'.join(em(*x) for x in p)+'\nsub rbx,1\njnz 1b\nadd rsp,8\n'+''.join(f'pop {r}\n' for r in 'r15 r14 r13 r12 rbp rbx'.split())+'ret\n'
    open('z.s','w').write(t);n=len(ps)
    c=open('m3.c').read();c=re.sub(r'F p_old.*?;',''.join(f'F d{i};' for i in range(n)),c,1)
    c=c[:c.index('int main')]+'int main(){'+''.join(f'T(d{i})' for i in range(n))+'}'
    open('z.c','w').write(c);subprocess.check_call('gcc -O1 z.c z.s -o z 2>/dev/null',shell=True)
    b=[1e9]*n
    for _ in range(2):
        for i,v in enumerate(subprocess.check_output('./z').split()[1::2]):b[i]=min(b[i],float(v))
    return b
for nm,O in(('A',A),('B',B)):
    rnd=random.Random(5);pool=[]
    for R in range(int(sys.argv[1])):
        c=[]
        while len(c)<40:
            if R==0 or rnd.random()<.2:o=order(O,rnd)
            else:
                o=list(rnd.choice(pool)[1])
                for _ in range(rnd.randint(1,3)):
                    k=o.pop(rnd.randrange(len(o)));o.insert(rnd.randrange(len(o)+1),k)
                if not valid(O,o):continue
            p=assign(O,o)
            if p:c.append((o,p))
        t=meas([p for _,p in c]);pool=sorted(pool+[(x,o,p) for x,(o,p) in zip(t,c)],key=lambda z:z[0])[:8]
        print(nm,R,[x[0] for x in pool[:3]],max(t),flush=True)
    for x,o,p in pool[:3]:print(x,' '.join(o));print(p)
