"""Unverified parity-carry assembly, checked by the C differential harness."""
import generate as g

def reg(r): return r.lstrip('.')
def ld(r,s,i):
    return [f'addi {r}, s{7+i-20}, 0'] if i>=20 else [f'ld {r}, {8*i}({s})']
def xl(r,s,i):
    return [f'xor {r}, {r}, s{7+i-20}'] if i>=20 else [f'ld t6, {8*i}({s})',f'xor {r}, {r}, t6']
def emit(ops,s,d,parity):
    lines=[]
    for op,args in ops:
        if op in ('ld','xl'):
            r,_,i=args
            lines += (ld if op=='ld' else xl)(reg(r),s,int(i))
        elif op=='st':
            _,i,r=args;i=int(i);r=reg(r)
            lines += [f'addi s{7+i-20}, {r}, 0'] if i>=20 else [f'sd {r}, {8*i}({d})']
            if parity: lines += [f'addi s{2+i}, {r}, 0'] if i<5 else [f'xor s{2+i%5}, s{2+i%5}, {r}']
        elif op=='rol':
            r,n=reg(args[0]),int(args[1]);lines += [f'slli t6, {r}, {n}',f'srli {r}, {r}, {64-n}',f'or {r}, {r}, t6']
        elif op=='nt':
            r=reg(args[0]);lines += [f'xori {r}, {r}, -1']
        else:
            r,q=map(reg,args)
            lines += [f'addi {r}, {q}, 0'] if op=='mv' else [f'{dict(xr="xor",an="and",orr="or")[op]} {r}, {r}, {q}']
    return lines

baseline=(g.ROOT/'crates/verified-garbage-asm-riscv64/assembly/internal/vg_keccak_f1600.s').read_text()
names=[];sources=[]
for carry in (False,True):
    name='asm_row4parity' if carry else 'asm_row4'
    names.append(name)
    text=baseline
    saves=[];restores=[]
    for i in range(5):
        saves += [f'sd s{2+i}, {352+8*i}(t6)',f'sd s{7+i}, {552+8*i}(t6)']
        restores += [f'ld s{2+i}, {160+8*i}(a0)',f'ld s{7+i}, {360+8*i}(a0)']
    def block(lines): return ''.join('\t'+line+'\n' for line in lines)
    text=text.replace('\tandi t0, s1, 7\n',block(saves)+'\tandi t0, s1, 7\n',1)
    for i in range(20,25):
        text=text.replace(f'\tsd a{i-18}, {192+8*i}(t6)\n',block([f'addi s{i-13}, a{i-18}, 0']))
    if carry:
        init=[]
        for x in range(5):
            init+=ld('s'+str(x+2),'a0',x)
            for y in range(1,5):init+=xl('s'+str(x+2),'a0',x+5*y)
        text=text.replace('21:\n22:\n','21:\n'+block(init)+'22:\n')
    first=text.index('22:\n')+len('22:\n')
    end=text.index('\taddi s0, s0, 16',first)
    body=[]
    for k,(s,d) in enumerate([('a0','a1'),('a1','a0')]):
        if carry:
            body+=emit(g.A[:4]+[g.A[10]],s,d,False)
            body += [f'addi a{x+2}, s{x+2}, 0' for x in range(5)]
            body+=emit([op for i,op in enumerate(g.A) if i>=22 and i not in (25,28,31)],s,d,False)
        else:body+=emit(g.A,s,d,False)
        body += [f'ld t6, {8*k}(s0)','xor t0, t0, t6']
        body += emit(g.B,s,d,carry)
    text=text[:first]+block(body)+text[end:]
    # Output copies are the only remaining reads of cached physical lanes.
    for i in range(20,25):
        text=text.replace(f'\tld t0, {8*i}(a0)\n',block(ld('t0','a0',i)))
    text=text.replace('\tld s0, 400(a0)\n',block(restores)+'\tld s0, 400(a0)\n')
    sources.append(text.replace('vg_keccak_f1600','candidate_'+name))
path=g.OUT/'parity.S'
path.write_text('.text\n'+'\n'.join('.globl candidate_'+n+'\n.type candidate_'+n+', @function\n'+s for n,s in zip(names,sources)))
with (g.OUT/'asm-files.txt').open('a') as f:f.write(str(path)+'\n')
