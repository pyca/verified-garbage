"""Registers for sched4's event list: stores at the first eviction of a value loaded later, then a
colouring of the instances' live ranges. usage: alloc4.py file fwd|inv out-regs(comma) regs(comma)"""
import sys,random,os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__))+'/..')
from sbox_check import sboxes
fn,kind,OUT,NAMES=sys.argv[1],sys.argv[2],[int(x) for x in sys.argv[3].split(',')],[int(x) for x in sys.argv[4].split(',')]
EV=[tuple(map(int,l.split())) for l in open(fn) if l[0]!='#']
# instructions: (kind,dst,srcs)
ins=[];cur={v:('in',v) for v in range(8)};stored=set()
loads={d:[t for t,e in enumerate(EV) if e[0]==3 and e[1]==d] for d in {e[1] for e in EV if e[0]==3}}
inst={}  # instance id -> [start,lastuse,value]
for v in range(8): inst[('in',v)]=[-1,-1]
def use(v): i=cur[v];inst[i][1]=len(ins);return i
for t,(k,d,a,b) in enumerate(EV):
    if k in(0,1):
        x,y=use(a),use(b);i=('op',len(ins));inst[i]=[len(ins),len(ins)];cur[d]=i;ins.append((k,i,x,y))
    elif k==3:
        i=('op',len(ins));inst[i]=[len(ins),len(ins)];cur[d]=i;ins.append((3,i,d,None))
    elif k==4:
        if d in loads and d not in stored and any(x>t for x in loads[d]):
            stored.add(d);x=use(d);ins.append((2,None,x,d))
outs=[cur[200+j] for j in range(8)]
for o in outs: inst[o][1]=len(ins)+1
# slots
last={d:max(i for i,x in enumerate(ins) if x[0]==3 and x[2]==d) for d in stored}
slot={};free=[];ns=0
for i,x in enumerate(ins):
    if x[0]==2:
        if free: slot[x[3]]=free.pop(0)
        else: slot[x[3]]=ns;ns+=1
    if x[0]==3 and last[x[2]]==i: free.append(slot[x[2]])
def color(rng):
    fixed={('in',v):v for v in range(8)}
    for j,o in enumerate(outs):
        if o in fixed and fixed[o]!=OUT[j]: return None
        fixed[o]=OUT[j]
    busy={r:[] for r in NAMES}
    for i,r in fixed.items(): busy[r].append(tuple(inst[i]))
    for r in NAMES:
        b=sorted(busy[r])
        for x,y in zip(b,b[1:]):
            if x[1]>y[0]: return None
    col=dict(fixed)
    for i in sorted((i for i in inst if i not in fixed),key=lambda i:inst[i][0]):
        s,e=inst[i]
        c=[r for r in NAMES if all(e<=x or y<=s for x,y in busy[r])]
        if not c: return None
        c.sort(key=lambda r:(min([x for x,y in busy[r] if x>=e] or [10**6])-e)+rng.random()*25)
        col[i]=c[0];busy[c[0]].append((s,e))
    return col
rng=random.Random(1);col=None
for tr in range(30000):
    col=color(rng)
    if col: break
if not col: print('no colouring');sys.exit(1)
R=lambda i:'.lr' if col[i]==14 else f'.r{col[i]}'
code=[]
for x in ins:
    if x[0]==2: code.append(f'stS {slot[x[3]]} {R(x[2])}')
    elif x[0]==3: code.append(f'ldS {R(x[1])} {slot[x[2]]}')
    else: code.append(f"{'andR' if x[0]==1 else 'eorR'} {R(x[1])} {R(x[2])} {R(x[3])}")
reg={('.r%d'%j):sum(1<<x for x in range(256) if x>>j&1) for j in range(8)};sl={}
for c in code:
    q=c.split()
    if q[0]=='stS': sl[q[1]]=reg[q[2]]
    elif q[0]=='ldS': reg[q[1]]=sl[q[2]]
    elif q[0]=='andR': reg[q[1]]=reg[q[2]]&reg[q[3]]
    else: reg[q[1]]=reg[q[2]]^reg[q[3]]
o=[reg['.lr' if r==14 else f'.r{r}'] for r in OUT];S_,SI=sboxes()
t=[sum((o[j]>>x&1)<<j for j in range(8)) for x in range(256)]
if kind=='inv': assert [t[x^0x63] for x in range(256)]==SI
else: assert [v^0x63 for v in t]==S_
print('--',len(code),'instructions',ns,'slots',sum(c[0:2]=='st' for c in code),'stores',sum(c[:3]=='ldS' for c in code),'loads tries',tr)
line='  '
for i,c in enumerate(code):
    it=c+(',' if i<len(code)-1 else ']')
    if len(line)+len(it)>98: print(line.rstrip());line='  '
    line+=it+' '
print(line.rstrip())
