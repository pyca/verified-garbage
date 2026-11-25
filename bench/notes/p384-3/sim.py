"""A small out-of-order model: 5-wide, window 160, 4 integer pipes of which 2 multiply,
flag setting 2.2 a cycle, 3 loads, 1.5 stores."""
def uses(i):
    op=i[0];a=i[1:]
    if op=='ldr': return [('m',)+tuple(a[1])],[a[0]]
    if op=='str': return [a[0]],[('m',)+tuple(a[1])]
    if op=='movz': return [],[a[0]]
    rd=[x for x in a[1:]] 
    if op in('lsl','lsr','subImm'): rd=[a[1]]
    if op=='extr': rd=[a[1],a[2]]
    wr=[a[0]]
    if op in('adc','adcs','sbc','sbcs','csel'): rd=rd+['C']
    if op in('adds','adcs','subs','sbcs'): wr=wr+['C']
    return rd,wr
LAT={'mul':2,'umulh':3,'ldr':4,'str':1}
def sim(code,rob=160,width=5,verbose=False):
    n=len(code); ready=[0]*n; last={}; deps=[]
    for k,i in enumerate(code):
        rd,wr=uses(i); deps.append([last[x] for x in rd if x in last])
        for x in wr: last[x]=k
    done=[None]*n; issued=[False]*n; head=0; disp=0; t=0; fl=0.0; st=0.0
    inwin=[]
    while head<n:
        while head<n and done[head] is not None and done[head]<=t: head+=1
        c=0
        while disp<n and c<width and disp-head<rob: inwin.append(disp);disp+=1;c+=1
        alu=4;m=2;l=3;fl=min(fl+2.2,3);st=min(st+1.2,2)
        rest=[]
        for k in inwin:
            op=code[k][0]; ok=all(done[d] is not None and done[d]<=t for d in deps[k])
            if ok:
                if op=='ldr':
                    if l: l-=1
                    else: ok=False
                elif op=='str':
                    if st>=1: st-=1
                    else: ok=False
                elif op in('mul','umulh','extr'):
                    if m and alu: m-=1;alu-=1
                    else: ok=False
                elif op in('adds','adcs','subs','sbcs'):
                    if alu and fl>=1: alu-=1;fl-=1
                    else: ok=False
                else:
                    if alu: alu-=1
                    else: ok=False
            if ok: done[k]=t+LAT.get(op,1)
            else: rest.append(k)
        inwin=rest; t+=1
    return max(done)
def rename(code,k,dep):
    out=[]
    for i in code:
        if i[0] in('ldr','str'):
            b,o=i[2]
            if b=='o': b=f'o{k}' if not dep else 'a'
            out.append((i[0],i[1],(b,o)))
        else: out.append(i)
    return out
def both(code,n=8):
    L=[];I=[]
    for k in range(n): L+=rename(code,k,True); I+=rename(code,k,False)
    return sim(L)/n,sim(I)/n
if __name__=='__main__':
    import gen,gen2
    for nm,c in [('K',gen.build('K')),('S',gen.build('S')),('Q',gen.build('Q')),('K2',gen2.build2('K')),('Q2',gen2.build2('Q'))]:
        print(nm,len(c),both(c), 'depth',sim(c,rob=10**6,width=10**6))
