import sys
# full round DAG: S-box (file), then linear layer 'A','B' (enc) ; key mems
def lin(kind,S,nv,K):
    """S: value ids of 8 slices after S-box; returns gates, outs"""
    g=[];c=[nv]
    def nw(op,a,b=-1):
        c[0]+=1;g.append((op,c[0],a,b));return c[0]
    X=lambda a,b:nw('X',a,b)
    U=lambda a:nw('U',a)
    D=lambda a:nw('D',a)
    b=[0]*8;r=[0]*8;h=[0]*8
    for j in range(8):
        s=S[j]
        if kind=='B':
            s=U(U(s)); d=U(s); b[j]=X(s,d); t=U(b[j])
        else:
            v=U(s); d=X(D(v),D(v)); b[j]=X(s,d); t=U(U(U(b[j])))
        h[j]=X(d,t)
    outs=[]
    for j in range(8):
        terms=[h[j]]
        o=X(h[j],b[(j+7)%8])
        if j in(1,3,4): o=X(o,b[7])
        o=X(o,K[j]); outs.append(o)
    return g,outs,c[0]
def main():
    sb,kind,I,O,fn=sys.argv[1:6]
    G=[tuple(map(int,l.split())) for l in open('../n/notes/results/'+sb) if l.strip()]
    K=list(range(260,268))
    g,outs,_=lin(kind,[200+j for j in range(8)],270,K)
    with open(fn,'w') as f:
        for j in range(8): f.write(f'i {j} {I[j]}\n')
        for k in K: f.write(f'i {k} m\n')
        for o,j in zip(outs,range(8)): f.write(f'o {o} {O[j]}\n')
        for o,d,a,b in G: f.write(f'g {"XA"[o]} {d} {a} {b}\n')
        for q in g: f.write('g %s %d %d %d\n'%q)
main()
