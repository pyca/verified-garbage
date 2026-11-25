from alloc import *
name='double'
raw=parse(f'/tmp/sp/{name}.raw'); nodes,stores=build(raw,OBS[name])
out=allocate(nodes,stores,schedule(nodes,stores,10**6,0,4)); open('o.s','w').write(asm(out))
import collections; print(collections.Counter(o[0] for o in out))
