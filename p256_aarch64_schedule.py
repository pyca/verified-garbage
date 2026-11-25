#!/usr/bin/env python3
"""The allocated P-256 field programs on AArch64, from the raw ones.

`Impl/P256/VerifyAllocatedCode.lean` and `Impl/P256/EcdhAllocatedCode.lean`
hold literal instructions: the straight-line field programs of
`VerifyAllocated.raw`, `EcdhDouble.raw` and `EcdhTable.raw`, and the inversions'
update of `(f, g, a, b)`, scheduled and with their registers allocated. This
writes them. It is untrusted: Lean checks each against its raw program.

    python3 ci/p256_aarch64_schedule.py [--tries 700] [name ...]

needs the built Lean modules, with their private parts
(`ci/lean_cache.py fill-private lean <Impl modules>`), and `llvm-mca` (LLVM
18), whose Neoverse N2 model ranks the schedules tried. The search is
deterministic for a given `--tries` and LLVM.

How it works: the program is value-numbered into a graph, with loads of slots
as leaves and only the slots the caller observes as roots. A list scheduler
takes the operation that can start first, the one with the longest path to
the end among equals, unless `P` values are live, when it takes one that
frees a register, and never looks further than `K` instructions past the
oldest one left. An operation that sets the flags starts only when no other
chain of carries is open. Registers are then allocated in order, spilling the
value whose next use is furthest (one that can be loaded again at no cost
first). `P`, `K`, the width and a tie-breaking noise are searched at random.
"""

import collections, multiprocessing, os, random, re, subprocess, sys, tempfile
FS={'adds','adcs','subs','sbcs'}; FU={'adcs','sbcs','adc','sbc','csel'}
LEAF=('ldr','movz','in') # values that no instruction of the schedule computes
LAT={'mul':2,'umulh':3,'extr':3,'ldr':4,'madd':2}
REGS=[f'x{i}' for i in list(range(1,18))+list(range(20,29))+[30]]
SPILL=list(range(7104,7680,8))
class N:
    __slots__=('op','imm','a','f','raw','users','fu','id','h','slot')
def parse(text):
    out=[]
    for l in text.splitlines():
        t=re.sub(r'VG\.AArch64\.\w+\.','',l); t=re.sub(r'[()]','',t).split()
        op=t[0]; t=t[1:]
        if op=='logic': op,t=t[0],t[1:]; assert op=='and',l
        if op!='umulh': assert t[0]=='x',l; t=t[1:]
        out.append((op,t))
    return out
def build(raw,observe,inputs=()):
    nodes=[]; cse={}; reg={}; slot={}; fl=None
    def mk(op,imm=None,a=(),f=None,i=0):
        k=(op,imm,tuple(a),f)
        if op not in FS and k in cse: return cse[k]
        n=N(); n.op=op;n.imm=imm;n.a=tuple(a);n.f=f;n.raw=i;n.id=len(nodes);n.slot=None;nodes.append(n)
        cse[k]=n.id; return n.id
    for r in inputs: reg[r]=mk('in',r)
    for i,(op,t) in enumerate(raw):
        if op=='ldr':
            o=int(t[2])
            if o not in slot: slot[o]=mk('ldr',o,i=i)
            reg[t[0]]=slot[o]
        elif op=='str': 
            o=int(t[2])
            if o not in slot: slot[o]=None
            slot[o]=reg[t[0]]
        elif op=='movz': reg[t[0]]=mk('movz',(int(t[1].split('#')[0],16),int(t[2])),i=i)
        elif op=='movk': reg[t[0]]=mk('movk',(int(t[1].split('#')[0],16),int(t[2])),(reg[t[0]],),i=i)
        elif op in('lsl','lsr'): reg[t[0]]=mk(op,int(t[2]),(reg[t[1]],),i=i)
        elif op=='extr': reg[t[0]]=mk(op,int(t[3]),(reg[t[1]],reg[t[2]]),i=i)
        else:
            n=mk(op,None,[reg[x] for x in t[1:]],fl if op in FU else None,i)
            reg[t[0]]=n
            if op in FS: fl=n
    stores=[(o,v) for o,v in slot.items() if v is not None and observe(o) and not(nodes[v].op=='ldr' and nodes[v].imm==o)]
    return nodes,stores
def prune(nodes,stores):
    live=set(); st=[v for _,v in stores]
    while st:
        v=st.pop()
        if v in live: continue
        live.add(v); n=nodes[v]; st+=list(n.a)+([n.f] if n.f is not None else [])
    return live
def schedule(nodes,stores,P,K,width,seed=0,full=True,lat=LAT,noise=0):
    rnd=random.Random(seed)
    live=prune(nodes,stores)
    L=lambda n: lat.get(n.op,1)
    # ops: node ids that are real (not ldr/movz), plus stores
    ops=[v for v in live if nodes[v].op not in LEAF]
    S=len(nodes); items=ops+[S+i for i in range(len(stores))]
    deps={}; succ=collections.defaultdict(list)
    uses=collections.Counter()
    for v in ops:
        n=nodes[v]; deps[v]=set(n.a)|({n.f} if n.f is not None else set())
        for a in set(n.a): uses[a]+=1
    inuse=collections.defaultdict(list)
    for v in ops:
        for a in nodes[v].a:
            if nodes[a].op=='ldr': inuse[nodes[a].imm].append(v)
    for i,(o,v) in enumerate(stores):
        deps[S+i]={v}|set(inuse[o]); uses[v]+=1
        for j,(o2,v2) in enumerate(stores):
            if nodes[v2].op=='ldr' and nodes[v2].imm==o and j!=i: deps[S+i].add(S+j)
    rem={}
    for x in items:
        d={y for y in deps[x] if y>=S or nodes[y].op not in LEAF}
        rem[x]=len(d)
        for y in d: succ[y].append(x)
    raw=lambda x: nodes[x].raw if x<S else nodes[stores[x-S][1]].raw
    order=sorted(items,key=raw)
    # heights
    H={}
    topo=sorted(ops,key=lambda v:v)
    for v in reversed(topo):
        H[v]=L(nodes[v])+max([H[s] for s in succ[v] if s<S],default=0)
    for x in items:
        if x>=S: H[x]=0
        H[x]+=rnd.random()*noise
    # chains
    ch={}
    def root(v):
        r=v
        while nodes[r].f is not None: r=nodes[r].f
        return r
    mem=collections.defaultdict(list)
    for v in ops:
        if nodes[v].op in FS or nodes[v].f is not None: ch[v]=root(v); mem[ch[v]].append(v)
    # external ancestors for chain start
    need={}
    for r,ms in mem.items():
        s=set(ms); seen=set()
        stack=[a for m in ms for a in nodes[m].a]
        while stack:
            a=stack.pop()
            if a in seen or a in s or nodes[a].op in LEAF: continue
            seen.add(a)
            stack+=[b for b in deps[a]]
        # which of seen depend on s?
        dd={}
        for a in sorted(seen):
            dd[a]=any((b in s) or dd.get(b,False) for b in deps[a])
        if full: need[r]={a for a in seen if not dd[a]}
        else: need[r]={a for a in seen if not dd[a] and nodes[a].op in FS or (not dd[a] and nodes[a].f is not None)}
    done=set(); t=0.0; fin={}; res=[]
    avail={x for x in items if rem[x]==0}
    openr=None; chrem={r:set(ms) for r,ms in mem.items()}
    fremain=collections.Counter()
    for v in ops:
        if nodes[v].f is not None: fremain[nodes[v].f]+=1
    curf=None
    u=dict(uses); pressure=0; ploaded=set()
    ptr=0
    def delta(x):
        d=0
        if x<S:
            for a in set(nodes[x].a):
                if u[a]==1 and (nodes[a].op not in('ldr','movz') or a in ploaded): d-=1
                elif nodes[a].op=='ldr' and a not in ploaded and u[a]>1: d+=1
            if uses[x]>0: d+=1
        else:
            v=stores[x-S][1]
            if u[v]==1: d-=1
        return d
    while len(done)<len(items):
        while ptr<len(order) and order[ptr] in done: ptr+=1
        base=raw(order[ptr])
        cand=[]
        for x in avail:
            if x<S and (nodes[x].op in FS or nodes[x].f is not None):
                r=ch[x]
                if openr is not None and r!=openr: continue
                if openr is None and not need[r]<=done: continue
                if nodes[x].op in FS and nodes[x].f is not None:
                    # must be the last consumer of its flags
                    if fremain[nodes[x].f]>1: continue
            if raw(x)-base>K and not (x<S and openr is not None and ch.get(x)==openr): continue
            cand.append(x)
        if not cand:
            cand=[x for x in avail if not(x<S and (nodes[x].op in FS or nodes[x].f is not None) and ((openr is not None and ch[x]!=openr) or (openr is None and not need[ch[x]]<=done) or (nodes[x].op in FS and nodes[x].f is not None and fremain[nodes[x].f]>1)))]
            cand=[min(cand,key=raw)]
        est=lambda x: max([t]+[fin.get(d,0) for d in deps[x]])
        if pressure>=P:
            m=min(delta(x) for x in cand)
            if m<=0:
                c2=[x for x in cand if delta(x)==m]
            else: c2=[min(cand,key=lambda x:(raw(x)))]
            x=min(c2,key=lambda x:(est(x),-H[x]))
        else:
            x=min(cand,key=lambda x:(max(est(x),t),-H[x]))
        pressure+=delta(x)
        if x<S:
            for a in set(nodes[x].a):
                u[a]-=1
                if nodes[a].op=='ldr':
                    ploaded.add(a)
                    if u[a]==0: ploaded.discard(a)
        else: u[stores[x-S][1]]-=1
        e=est(x); fin[x]=e+(L(nodes[x]) if x<S else 1)
        t+=1.0/width
        done.add(x); res.append(x); avail.discard(x)
        if x<S and x in ch:
            r=ch[x]
            if nodes[x].f is not None: fremain[nodes[x].f]-=1
            chrem[r].discard(x); openr=r if chrem[r] else None
        for y in succ[x]:
            rem[y]-=1
            if rem[y]==0: avail.add(y)
    return res
def allocate(nodes,stores,sched,regs=REGS):
    S=len(nodes)
    nu=collections.defaultdict(list)
    for i,x in enumerate(sched):
        for a in (nodes[x].a if x<S else (stores[x-S][1],)):
            if not nu[a] or nu[a][-1]!=i: nu[a].append(i)
    for a in nu: nu[a].reverse()
    loc={}; home={}; free=list(regs); out=[]; last={}
    spill=list(SPILL); spilled={}; maxsp=0
    def remat(v):
        n=nodes[v]
        if n.op=='movz': return ('movz',)
        if v in home: return ('ldr',home[v])
        return None
    for v,n in enumerate(nodes):
        if n.op=='ldr': home[v]=n.imm
        if n.op=='in' and nu[v]: loc[v]=n.imm; free.remove(n.imm)
    def get(protect,avoid=()):
        if free:
            # least recently freed
            return free.pop(0)
        best=None
        for v,r in loc.items():
            if v in protect: continue
            nx=nu[v][-1] if nu[v] else 10**9
            # cost: distance discounted when a spill store is needed
            d=nx-i
            if remat(v) is None: d*=0.6
            if best is None or d>best[0]: best=(d,v)
        v=best[1]; r=loc[v]
        if nu[v] and remat(v) is None:
            s=spill.pop(0); home[v]=s; spilled[v]=s
            out.append(('str',r,s))
        del loc[v]; return r
    def ensure(v,protect):
        if v in loc: return loc[v]
        n=nodes[v]; r=get(protect)
        if n.op=='movz': out.append(('movz',r,n.imm))
        else: out.append(('ldr',r,home[v]))
        loc[v]=r; return r
    for i,x in enumerate(sched):
        args=nodes[x].a if x<S else (stores[x-S][1],)
        prot=set(args); ars=[]
        for a in args: ars.append(ensure(a,prot))
        for a in set(args):
            nu[a].pop() if nu[a] and nu[a][-1]==i else None
        if x>=S:
            o,v=stores[x-S]; out.append(('str',ars[0],o)); 
            if v not in home: home[v]=o
            # inputs whose home is overwritten
            for w in [w for w in home if home[w]==o and w!=v]: del home[w]
        dead=[a for a in set(args) if not nu[a]]
        if x<S:
            n=nodes[x]
            if n.op=='movk' and dead: r=ars[0]; del loc[args[0]]; out.append(('movk',r,n.imm)); 
            else:
                for a in dead:
                    free.append(loc.pop(a))
                    if a in spilled: spill.insert(0,spilled.pop(a)); home.pop(a,None)
                if dead and len(free)>0: r=free.pop(-1)
                else: r=get(prot)
                if n.op=='movk': out.append(('mov',r,ars[0])); out.append(('movk',r,n.imm))
                else: out.append((n.op,r,*ars,*( [n.imm] if n.imm is not None else [])))
            if nu[x]: loc[x]=r
            else: free.append(r)
        else:
            for a in dead:
                free.append(loc.pop(a))
                if a in spilled: spill.insert(0,spilled.pop(a)); home.pop(a,None)
    return out
def asm(out):
    L=[]
    for o in out:
        if o[0]=='ldr': L.append(f'ldr {o[1]}, [x0, #{o[2]}]')
        elif o[0]=='str': L.append(f'str {o[1]}, [x0, #{o[2]}]')
        elif o[0] in('movz','movk'): L.append(f'{o[0]} {o[1]}, #{o[2][0]}, lsl #{16*o[2][1]}')
        elif o[0]=='mov': L.append(f'mov {o[1]}, {o[2]}')
        elif o[0]=='csel': L.append(f'csel {o[1]}, {o[2]}, {o[3]}, hs')
        elif o[0] in('lsl','lsr'): L.append(f'{o[0]} {o[1]}, {o[2]}, #{o[3]}')
        elif o[0]=='extr': L.append(f'extr {o[1]}, {o[2]}, {o[3]}, #{o[4]}')
        else: L.append(f'{o[0]} '+', '.join(o[1:]))
    return '\n'.join(L)+'\n'
def lean(out):
    L=[]
    for o in out:
        if o[0] in('ldr','str'): L.append(f'.{o[0]} .x .{o[1]} .x0 {o[2]}')
        elif o[0] in('movz','movk'): L.append(f'.{o[0]} .x .{o[1]} {o[2][0]} {o[2][1]}')
        elif o[0]=='mov': L.append(f'.logic .orr .x .{o[1]} .{o[2]} .{o[2]}')
        elif o[0]=='and': L.append('.logic .and .x '+' '.join('.'+r for r in o[1:]))
        elif o[0]=='umulh': L.append('.umulh '+' '.join('.'+r for r in o[1:]))
        else: L.append(f'.{o[0]} .x '+' '.join('.'+r if isinstance(r,str) else str(r) for r in o[1:]))
    return L
M64=2**64-1
def simulate(out,mem,regs={}):
    r=dict(regs); mem=dict(mem); c=0
    for o in out:
        op=o[0]
        if op=='ldr': r[o[1]]=mem[o[2]]
        elif op=='str': mem[o[2]]=r[o[1]]
        elif op=='movz': r[o[1]]=o[2][0]<<16*o[2][1]
        elif op=='movk': r[o[1]]=r[o[1]]&~(0xffff<<16*o[2][1])|o[2][0]<<16*o[2][1]
        elif op=='mov': r[o[1]]=r[o[2]]
        else:
            v=[r[y] for y in o[2:] if isinstance(y,str)]
            if op=='mul':x=v[0]*v[1]
            elif op=='umulh':x=v[0]*v[1]>>64
            elif op=='and':x=v[0]&v[1]
            elif op=='add':x=v[0]+v[1]
            elif op=='sub':x=v[0]-v[1]
            elif op in('adds','adcs','adc'):
                x=v[0]+v[1]+(0 if op=='adds' else c)
                if op!='adc':c=x>>64
            elif op in('subs','sbcs','sbc'):
                x=v[0]+(M64^v[1])+(1 if op=='subs' else c)
                if op!='sbc':c=x>>64
            elif op=='csel':x=v[0] if c else v[1]
            elif op=='lsl':x=v[0]<<o[3]
            elif op=='lsr':x=v[0]>>o[3]
            elif op=='extr':x=(v[0]<<64|v[1])>>o[4]
            else: raise Exception(op)
            r[o[1]]=x&M64
    return mem
def rawout(raw):
    o=[]
    for op,t in raw:
        if op in('ldr','str'): o.append((op,t[0],int(t[2])))
        elif op in('movz','movk'): o.append((op,t[0],(int(t[1].split('#')[0],16),int(t[2]))))
        elif op in('lsl','lsr'): o.append((op,t[0],t[1],int(t[2])))
        elif op=='extr': o.append((op,t[0],t[1],t[2],int(t[3])))
        else: o.append((op,*t))
    return o

def spillless(o):
    return o < 7104 or o >= 7680

# The slots observed, as in each block's certificate (`observe`).
OBSERVED = {
    'double': lambda o: (o < 800 or o >= 992) and spillless(o),
    'dblu': lambda o: (o < 800 or o >= 992 or 864 <= o < 928) and spillless(o),
    'zaddu': lambda o: (o < 800 or o >= 992) and spillless(o),
    'fieldUpdate': lambda o: 2272 <= o < 2416, 'orderUpdate': lambda o: 2272 <= o < 2416,
    'mixedHead': spillless, 'mixedTail': spillless, 'jacTail': spillless, 'cachedHead': spillless,
}
FILES = {'VerifyAllocatedCode': ['orderUpdate', 'mixedHead', 'mixedTail', 'jacTail', 'cachedHead'],
         'EcdhAllocatedCode': ['fieldUpdate', 'double', 'dblu', 'zaddu']}
# The inversions' updates: the divsteps' matrix in its registers, d and the batches' counter (and,
# for ECDH, the output's pointer) kept.
DEFS = {'orderUpdate': 'inverseUpdate', 'fieldUpdate': 'inverseUpdate'}
INPUTS = {'orderUpdate': ['x4','x5','x6','x7'], 'fieldUpdate': ['x4','x5','x6','x7']}
KEEP = {'orderUpdate': ['x1'], 'fieldUpdate': ['x1','x20']}
DUMP = """import Lean
import VerifiedGarbage.Impl.P256.VerifyAllocated
import VerifiedGarbage.Impl.P256.EcdhDouble
import VerifiedGarbage.Impl.P256.EcdhTable
import VerifiedGarbage.Impl.P256.EcdhInverse
open VG.AArch64 VG.Impl.P256
deriving instance Repr for Instr
run_cmd do
  let out (n : String) (l : List Instr) : IO Unit :=
    IO.FS.writeFile ("DIR/" ++ n) ("\\n".intercalate (l.map fun i => (toString (repr i)).replace "\\n" " "))
  out "double" EcdhDouble.raw
  out "fieldUpdate" EcdhInverse.updateRaw
  out "orderUpdate" (.movz .x .x12 0 0 :: VG.Impl.Ecdsa.AArch64.p256.invN.fgUpdate ++ VG.Impl.Ecdsa.AArch64.p256.invN.abUpdate)
  out "dblu" (EcdhTable.raw true)
  out "zaddu" (EcdhTable.raw false)
  out "mixedHead" (VerifyAllocated.raw .mixedHead)
  out "mixedTail" (VerifyAllocated.raw .mixedTail)
  out "jacTail" (VerifyAllocated.raw .jacTail)
  out "cachedHead" (VerifyAllocated.raw .cachedHead)
"""

def check(name, raw, out):
    """The slots observed, on random words (Lean proves it)."""
    mem = {o: random.getrandbits(64) for o in range(0, 8192, 8)}
    regs = {r: random.getrandbits(64) for r in INPUTS.get(name, [])}
    a = simulate(rawout(raw), mem, regs)
    b = simulate(out, mem, regs)
    assert all(a[o] == b[o] for o in a if OBSERVED[name](o)), name

def cycles(out):
    r = subprocess.run(['llvm-mca-18', '-march=aarch64', '-mcpu=neoverse-n2', '-dispatch=5', '-iterations=1',
                        '-instruction-info=0', '-resource-pressure=0', '-'],
                       input=asm(out), capture_output=True, text=True, check=True)
    return int(re.search(r'Total Cycles:\s+(\d+)', r.stdout).group(1))

def work(job):
    name, raw, tries, seed = job
    nodes, stores = build(raw, OBSERVED[name], INPUTS.get(name, []))
    regs = [r for r in REGS if r not in KEEP.get(name, [])]
    rnd = random.Random(seed)
    best = None
    for _ in range(tries):
        P = rnd.choice([16, 18, 19, 20, 21, 22, 23, 24, 10**6])
        K = rnd.choice([0, 0, 10, 20, 40, 60, 80, 100, 130, 160, 200, 250])
        w = rnd.choice([3, 4, 5, 6])
        full = rnd.random() < .6
        nz = rnd.choice([0, 0, 1, 3, 8])
        try:
            out = allocate(nodes, stores, schedule(nodes, stores, P, K, w, seed=rnd.random(), full=full, noise=nz), regs)
        except IndexError:  # no spill slot left
            continue
        score = cycles(out) + 0.06 * len(out)
        if best is None or score < best[0]:
            best = (score, (P, K, w, full, nz), out)
    return best

def write(root, blocks):
    for f, names in FILES.items():
        names = [n for n in names if n in blocks]
        path = os.path.join(root, 'lean/VerifiedGarbage/Impl/P256', f + '.lean')
        lines = open(path).read().split('\n')
        end = max(i for i, l in enumerate(lines) if l.startswith('end '))
        keep, skip = [], False
        for l in lines[:end]:
            m = re.match(r'^def (\w+) ', l)
            if m:
                skip = m.group(1) in names or m.group(1) in [DEFS.get(n) for n in names]
            if not skip:
                keep.append(l)
        while keep and keep[-1] == '':
            keep.pop()
        out = []
        for n in names:
            c = lean(blocks[n])
            out += ['', f'def {DEFS.get(n, n)} : List Instr :=', '  aarch64_instrs%', '   [' + c[0] + ',']
            out += ['    ' + x + ',' for x in c[1:-1]] + ['    ' + c[-1] + ']']
        open(path, 'w').write('\n'.join(keep + out + [''] + lines[end:]))

def main():
    args = sys.argv[1:]
    tries = int(args[1]) if args[:1] == ['--tries'] else 700
    only = args[2:] if args[:1] == ['--tries'] else args
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    blocks = {}
    with tempfile.TemporaryDirectory() as d:
        dump = os.path.join(root, 'lean', 'ScratchP256Dump.lean')
        open(dump, 'w').write(DUMP.replace('DIR', d))
        try:
            subprocess.run(['lake', 'env', 'lean', dump], cwd=os.path.join(root, 'lean'), check=True)
        finally:
            os.remove(dump)
        raws = {n: parse(open(os.path.join(d, n)).read()) for n in OBSERVED}
    for n, raw in raws.items():
        if only and n not in only:
            continue
        with multiprocessing.Pool(4) as pool:
            found = pool.map(work, [(n, raw, tries, s) for s in range(4)])
        best = min((b for b in found if b), key=lambda b: b[0])
        check(n, raw, best[2])
        print(n, 'raw', len(raw), cycles(rawout(raw)), 'now', len(best[2]), cycles(best[2]), best[1], flush=True)
        blocks[n] = best[2]
    write(root, blocks)

if __name__ == '__main__':
    main()
