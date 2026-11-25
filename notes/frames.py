# rho from FIPS 202
import itertools
def rho():
    R={(0,0):0}; x,y=1,0
    for t in range(24):
        R[(x,y)]=(t+1)*(t+2)//2%64
        x,y=y,(2*x+3*y)%5
    return R
R=rho()
src=lambda x,y:((x+3*y)%5,x)     # B(x,y)=rol(A'[src],R[src])
# frame p(l): register holds ror(value, p) meaning value = rol(reg,p).
# out(x,y) may take the frame of B_x or B_{x+2} in row y. frame of B(x,y) = p(src)+R[src]
# want p_out=p: choose pred for each lane; only cycle may have zero sum mod 64
edges={}
for x in range(5):
    for y in range(5):
        edges[(x,y)]=[(src(x,y),R[src(x,y)],0),(src((x+2)%5,y),R[src((x+2)%5,y)],2)]
# tree rooted at (0,0)
tree={(0,0):0}; order=[(0,0)]; depth={(0,0):0}; pick={(0,0):0}
ch=True
while ch:
    ch=False
    for l in edges:
        if l in tree: continue
        for (s,r,k) in edges[l]:
            if s in tree:
                tree[l]=(tree[s]+r)%64; pick[l]=k; depth[l]=depth[s]+1; ch=True;break


import math
