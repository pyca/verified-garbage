import subprocess,re,sys
from alloc import *
def asm(code,m=lambda o:o):
    R=lambda n:f"x{n}"; out=[]
    for op,a in code:
        if op in('ldr','str'): out.append(f"{op} x{a[0]}, [x0, #{m(a[2])}]")
        elif op=='movz': out.append(f"movz x{a[0]}, #{a[1]}, lsl #{16*a[2]}" if a[2] else f"movz x{a[0]}, #{a[1]}")
        elif op in('lsl','lsr'): out.append(f"{op} x{a[0]}, x{a[1]}, #{a[2]}")
        elif op=='extr': out.append(f"extr x{a[0]}, x{a[1]}, x{a[2]}, #{a[3]}")
        elif op=='csel': out.append(f"csel x{a[0]}, x{a[1]}, x{a[2]}, cs")
        else: out.append(f"{op.replace('logic','')} "+", ".join(R(x) for x in a))
    open('z.s','w').write("\n".join(out)+"\n")
    subprocess.check_call(['aarch64-linux-gnu-as','-o','z.o','z.s'])
    subprocess.check_call(['aarch64-linux-gnu-objcopy','-O','binary','-j','.text','z.o','z.bin'])
    b=open('z.bin','rb').read()
    return [int.from_bytes(b[i:i+4],'little') for i in range(0,len(b),4)]
def swapRD(o):
    for a,b in((736,880),(784,928),(832,976)):
        if a<=o<a+48: return o-a+b
        if b<=o<b+48: return o-b+a
    return o
def patch(f,pairs):
    s=open(f).read()
    for rw,nw in pairs:
        toks=list(re.finditer(r'0x[0-9a-f]{8}',s)); vals=[int(t.group(),16) for t in toks]
        i=0;n=0
        first=rw[0]
        while True:
            try: i=vals.index(first,i)
            except ValueError: break
            if vals[i:i+len(rw)]==rw:
                a=toks[i].start();e=toks[i+len(rw)-1].end()
                s=s[:a]+",".join('0x%08x'%w for w in nw)+s[e:]
                n+=1
                toks=list(re.finditer(r'0x[0-9a-f]{8}',s)); vals=[int(t.group(),16) for t in toks]
                i+=len(nw)
            else: i+=1
        print(f,'replaced',n)
    open(f,'w').write(s)
if __name__=='__main__':
    raw,al=main()
    pairs=[(asm(raw),asm(al)),(asm(raw,swapRD),asm(al,swapRD))]
    for f in sys.argv[1:]: patch(f,pairs)
