from alloc import *
import sys
raw=rawout(parse('/tmp/sp/double.raw'))
# first op is square: up to first 4 strs
def upto(raw,k):
    c=0
    for i,o in enumerate(raw):
        if o[0]=='str':
            c+=1
            if c==4*k: return i+1
i1=upto(raw,1); sq=raw[:i1]
print('square',len(sq),[ (c,mca(sq,c)) for c in('neoverse-n2','neoverse-v1','neoverse-v2','apple-m1')])
# mul: 5th field op : t2=t1*t2 (after sq,sq,sub,weakAdd)
i4=upto(raw,4); i5=upto(raw,5); mu=raw[i4:i5]
print('mul',len(mu),[ (c,mca(mu,c)) for c in('neoverse-n2','neoverse-v1','neoverse-v2','apple-m1')])
open('sq.s','w').write(asm(sq));open('mu.s','w').write(asm(mu))
