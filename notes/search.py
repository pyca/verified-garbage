from alloc import *
import alloc,sys,json,multiprocessing as mp,random
def mca5(out,cpu='neoverse-n2'):
    r=subprocess.run(['llvm-mca-18','-march=aarch64','-mcpu='+cpu,'-dispatch=5','-iterations=1','-instruction-info=0','-resource-pressure=0','-'],input=asm(out),capture_output=True,text=True)
    return int(re.search(r'Total Cycles:\s+(\d+)',r.stdout).group(1))
def work(a):
    name,n,seed=a
    raw=parse(f'/tmp/sp/{name}.raw'); nodes,stores=build(raw,OBS[name])
    rnd=random.Random(seed); best=None
    for j in range(n):
        P=rnd.choice([16,18,19,20,21,22,23,24,10**6]); K=rnd.choice([0,0,10,20,40,60,80,100,130,160,200,250]); w=rnd.choice([3,4,5,6]); full=rnd.random()<.6; nz=rnd.choice([0,0,1,3,8])
        try: out=allocate(nodes,stores,schedule(nodes,stores,P,K,w,seed=rnd.random(),full=full,noise=nz))
        except IndexError: continue
        c=mca5(out); score=c+0.06*len(out)
        if best is None or score<best[0]: best=(score,c,len(out),(P,K,w,full,nz),out)
    return name,best
if __name__=='__main__':
    n=int(sys.argv[1]); names=sys.argv[2:] or list(OBS)
    for name in names:
        ro=rawout(parse(f'/tmp/sp/{name}.raw'))
        with mp.Pool(4) as p: rs=p.map(work,[(name,n,s) for s in range(4)])
        b=min((r[1] for r in rs),key=lambda b:b[0]); check(name,b[4])
        print(name,'raw',len(ro),mca5(ro),'best',b[:4],[ (c,mca5(b[4],c)) for c in('neoverse-v1','neoverse-v2','apple-m1')],flush=True)
        open(f'/tmp/sp/{name}.best','w').write(json.dumps(b[4]))
