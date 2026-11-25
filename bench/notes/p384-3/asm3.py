import gen,gen2,gen3,gen4
from asm import txt,fn
def noextr(code):
    out=[]
    for i in code:
        if i[0]=='extr':
            d,hi,lo,n=i[1:]
            # d may equal lo/hi; use x26 as scratch
            out+=[('lsr',26,lo,n),('lsl',d,hi,64-n),('add',d,d,26)]
        else: out.append(i)
    return out
V={'S':gen.build('S'),'Sx':noextr(gen.build('S')),'I':gen4.build4('I'),'Ix':noextr(gen4.build4('I')),'Q':gen.build('Q'),'Qx':noextr(gen.build('Q')),'K':gen2.build2('K')}
for k,c in V.items(): gen3.check(c,'Q' if k[0]=='Q' else 'C',500)
def lat(c,n=8): return ["add x26,x0,#64","add x27,x0,#128","add x28,x0,#64"],n
F={}
def base(ops):
    # x26 is scratch: use x0 based addressing through fixed offsets instead
    return ops
def tx(code,off):
    o=[]
    for l in txt(code): o.append(l.replace('[x26, #','[x0, #A').replace('[x27, #','[x0, #B').replace('[x28, #','[x0, #O').replace('[x0, #A','[x0, #%d+'%off['a']).replace('[x0, #B','[x0, #%d+'%off['b']).replace('[x0, #O','[x0, #%d+'%off['o']))
    return o
for k,c in V.items():
    F[k+'_lat']=tx(c,{'a':64,'b':128,'o':64})*8
    F[k+'_ind']=sum([tx(c,{'a':64,'b':128,'o':192+64*i}) for i in range(8)],[])
print("".join(fn("r_"+n,b) for n,b in F.items()).replace('\nextern "C"','\nunsafe extern "C"'))
print("pub static PROTOS: &[(&str, unsafe extern \"C\" fn(*mut u64))] = &[")
for n in F: print(f'("{n}", r_{n}),')
print("];")
