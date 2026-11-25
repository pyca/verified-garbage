"""Emit the Lean circuit files from the search results (variables renumbered in gate order)."""
import sys
from sbox_check import *
def load(fn):
    L=open(fn).read().split('total'); return ('total'+L[-1]).strip().split('\n')
def circ(fn,inverse):
    gates,outs=build(load(fn),inverse)
    # constants: every signal has a parity (stored = true ^ parity); an xor gate becomes an
    # xnor where its operands' parities and its own wanted parity differ; ANDs need parity 0
    par={f'x{i}':(0x63>>i)&1 if inverse else 0 for i in range(8)}
    want={} if inverse else {outs[j]:1 for j in range(8) if 0x63>>j&1}
    G=[]
    for op,t,a,b in gates:
        if op=='and': assert par[a]==0 and par[b]==0,(a,b); w=0; o='and'
        else: w=want.get(t,0); o='xnor' if par[a]^par[b]^w else 'xor'
        par[t]=w; G.append((o,t,a,b))
    return G,outs
def check(G,outs,table):
    v={f'x{i}':sum(1<<x for x in range(256) if x>>i&1) for i in range(8)};M=(1<<256)-1
    for op,t,a,b in G:
        v[t]= v[a]&v[b] if op=='and' else v[a]^v[b]^(M if op=='xnor' else 0)
    assert [sum((v[outs[j]]>>x&1)<<j for j in range(8)) for x in range(256)]==table
if __name__=='__main__':
    S,SI=sboxes()
    for fn,inv,T in (('results/fwd-112.txt',False,S),('results/inv-115.txt',True,SI)):
        G,outs=circ(fn,inv); check(G,outs,T)
        num={f'x{i}':i for i in range(8)};k=8
        for g in G:
            if g[1] in outs: num[g[1]]=200+outs.index(g[1])
            else: num[g[1]]=k;k+=1
        print(fn,len(G)); line='  '
        for i,(op,t,a,b) in enumerate(G):
            it=f'⟨{num[t]}, .{op}, {num[a]}, {num[b]}⟩'+(',' if i<len(G)-1 else ']')
            if len(line)+len(it)>98: print(line.rstrip());line='  '
            line+=it+' '
        print(line.rstrip())
