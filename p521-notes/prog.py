from sat import *
import sat
from sqr import sqr
# inline version regs: x0 base; mul with b0..7 regs, b8 loaded
br=["x3","x4","x5","x6","x16","x17","x24","x25"]
def mulI(o,a,b):
    c=[f"ldr {br[j]},[x0,#{b+8*j}]" for j in range(8)]+["mov x7,#0"]
    body=sat.mul(ra='x0',oa=a,b=br+['B8'],ro='x0',oo=o)
    out=[]
    for l in body:
        if 'B8' in l:
            out.append(f"ldr x2,[x0,#{b+64}]"); l=l.replace('B8','x2')
        out.append(l)
    return c+out
def sqrI(o,a): return sqr('x0',a,'x0',o)
w=ACC[:9]
def addI(o,a,b):
    c=[f"ldr {w[k]},[x0,#{a+8*k}]" for k in range(9)]+["mov x7,#0","subs x1,x7,x7"]
    for k in range(9): c+=[f"ldr x2,[x0,#{b+8*k}]",f"adcs {w[k]},{w[k]},x2"]
    c+=["mov x2,#512",f"subs x1,{w[8]},x2"]+[f"sbcs {w[k]},{w[k]},x7" for k in range(9)]+["mov x2,#511",f"and {w[8]},{w[8]},x2"]
    return c+[f"str {w[k]},[x0,#{o+8*k}]" for k in range(9)]
def subI(o,a,b):
    c=[f"ldr {w[k]},[x0,#{a+8*k}]" for k in range(9)]+["mov x7,#0"]
    for k in range(9): c+=[f"ldr x2,[x0,#{b+8*k}]",f"{'subs' if k==0 else 'sbcs'} {w[k]},{w[k]},x2"]
    c+=[f"sbcs {w[k]},{w[k]},x7" for k in range(9)]+["mov x2,#511",f"and {w[8]},{w[8]},x2"]
    return c+[f"str {w[k]},[x0,#{o+8*k}]" for k in range(9)]
S=lambda i:72*i
px,py,pz,ox,oy,oz,t0,t1,t2,t3=[S(i) for i in range(10)]
M=lambda o,a,b: sqrI(o,a) if a==b else mulI(o,a,b)
A,B=addI,subI
def dbl():
    c=[]
    for f,*r in [(M,t0,pz,pz),(M,t1,py,py),(A,oz,py,pz),(B,t3,px,t0),(A,ox,px,t0),(M,t2,px,t1),(M,oz,oz,oz),(M,t3,t3,ox),
      (B,oz,oz,t1),(B,oz,oz,t0),(M,t1,t1,t1),(A,ox,t3,t3),(A,t3,ox,t3),(A,t2,t2,t2),(A,t2,t2,t2),(M,ox,t3,t3),(A,t1,t1,t1),(A,t1,t1,t1),(A,t1,t1,t1),
      (B,ox,ox,t2),(B,ox,ox,t2),(B,oy,t2,ox),(M,oy,t3,oy),(B,oy,oy,t1)]: c+=f(*r)
    return c
if __name__=='__main__':
    for n,c in [('mul',mulI(0,72,144)),('sqr',sqrI(0,72)),('add',addI(0,72,144)),('sub',subI(0,72,144)),('dbl',dbl())]: print(n,mca(c))
