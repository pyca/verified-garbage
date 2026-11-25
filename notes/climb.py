import sys,random
S=sys.argv[1]; seed=int(sys.argv[2]); rounds=int(sys.argv[3]); var=sys.argv[4]
src=open(S+'/proto/lim.py').read(); pre=src.split("ch='A D")[0].replace("sys.argv=['x',sys.argv[1]]","").replace("sys.argv[1]",repr(S))
exec(pre)
dep={'A':[],'B':[],'C':[],'D':[],'UV':['A','B','C','D'],'M':['C','D'],'P':['D','A'],'Q':['C','B'],'AA':['UV'],'BB':['UV'],'s':['P','Q'],'d':['P','Q'],'E':['AA','BB'],'x3':['s'],'dd':['d'],'z3':['dd'],'x2':['AA','BB'],'w':['AA','E'],'z2':['E','w']}
if var=='M':
    for k in dep: dep[k]=['M' if x in('A','B','UV') else x for x in dep[k]]
    dep['M']=['C','D']
# writers of state after its readers
dep['x2']+=['M'] if var=='M' else ['A','B']; dep['z2']+=['M'] if var=='M' else ['A','B']
def ok(o):
    s=set()
    for x in o:
        if any(d not in s for d in dep[x]): return False
        s.add(x)
    # x3,z3 after C,D (always, through P,Q)
    return True
rng=random.Random(seed)
cur=('D C M P AA BB Q E d w x2 dd s z2 z3 x3' if var=='M' else 'A D B C UV P AA BB Q E s x2 d w dd z2 x3 z3').split()
def mut(o):
    while 1:
        n=o[:]
        for _ in range(rng.choice([1,1,2,3])):
            x=n.pop(rng.randrange(len(n))); n.insert(rng.randrange(len(n)+1),x)
        if n!=o and ok(n): return n
for r in range(rounds):
    c=[cur]+[mut(cur) for _ in range(9)]
    res=list(map(float,build([('base',o) for o in c]+[('adx',o) for o in c])))
    sc=[res[i]/res[0]+res[i+len(c)]/res[len(c)] for i in range(len(c))]
    b=min(range(len(c)),key=lambda i:sc[i])
    if sc[b]<1.998: cur=c[b]
    if r%5==4: print(r,round(sc[b],4),' '.join(cur),flush=True)
