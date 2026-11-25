from asm import fn
def rep(f,n=256): 
    b=["mov x1,x0","mov x2,x0"]+[f"mov x{r},x0" for r in range(3,16)]
    i=0
    while i<n:
        ls=f(i); b+=ls; i+=len(ls)
    return b
d=lambda i:3+i%12
F={
'clock':rep(lambda i:["add x3,x3,x2"]),
'adds':rep(lambda i:[f"adds x{d(i)},x1,x2"]),
'addsadc':rep(lambda i:[f"adds x{d(i)},x1,x2",f"adc x{d(i+1)},x1,x2"]),
'adds3':rep(lambda i:[f"adds x{d(i)},x1,x2",f"adcs x{d(i+1)},x1,x2",f"adcs x{d(i+2)},x1,x2",f"adc x{d(i+3)},x1,x2"]),
'mulchain':rep(lambda i:[f"mul x{d(i)},x1,x2",f"adds x{d(i+1)},x1,x2",f"umulh x{d(i+2)},x1,x2",f"adcs x{d(i+3)},x1,x2"]),
'adc':rep(lambda i:[f"adc x{d(i)},x1,x2"]),
'csel':rep(lambda i:[f"csel x{d(i)},x1,x2,cs"]),
'subs_csel':rep(lambda i:[f"subs x{d(i)},x1,x2",f"csel x{d(i+1)},x1,x2,cs"]),
'madd':rep(lambda i:[f"madd x{d(i)},x1,x2,x3"]),
'maddacc':rep(lambda i:[f"madd x{d(i)},x1,x2,x{d(i)}"]),
'addsh':rep(lambda i:[f"add x{d(i)},x1,x2,lsl #32"]),
'lsl':rep(lambda i:[f"lsl x{d(i)},x1,#32"]),
'extr':rep(lambda i:[f"extr x{d(i)},x1,x2,#32"]),
'mul':rep(lambda i:[f"mul x{d(i)},x1,x2"]),
'umulh':rep(lambda i:[f"umulh x{d(i)},x1,x2"]),
'mullat':rep(lambda i:["mul x3,x3,x2"]),
'umulhlat':rep(lambda i:["umulh x3,x3,x2"]),
'mul_add':rep(lambda i:[f"mul x{d(i)},x1,x2",f"add x{d(i+1)},x1,x2"]),
'ldr':rep(lambda i:[f"ldr x{d(i)},[x0,#{8*(i%8)}]"]),
'ldp':rep(lambda i:[f"ldp x{d(i)},x{d(i+1)},[x0,#{16*(i%4)}]"]),
'str':rep(lambda i:[f"str x{d(i)},[x0,#{8*(i%8)}]"]),
'stp':rep(lambda i:[f"stp x{d(i)},x{d(i+1)},[x0,#{16*(i%4)}]"]),
'logic':rep(lambda i:[f"and x{d(i)},x1,x2"]),
}
print("".join(fn("q_"+n,b) for n,b in F.items()).replace('\nextern "C"','\nunsafe extern "C"'))
print("pub static PROTOS: &[(&str, unsafe extern \"C\" fn(*mut u64))] = &[")
for n in F: print(f'("{n}", q_{n}),')
print("];")
