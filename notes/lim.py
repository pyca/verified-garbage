import sys,re; sys.argv=['x',sys.argv[1]]
exec(open(sys.argv[1]+'/proto/ord.py').read().split("if __name__")[0])
# merged A,B,U,V
def m(b,o): return f'[rdi + {b+8*o}]'
X2,Z2,A,B,C,D,U,V=96,128,224,256,288,320,352,384
R1=['r8','r9','r10','r11'];R2=['r12','r13','r14','r15']
def q(b,i): return f'QWORD PTR [rdi + {b+8*i}]'
def merged(split=False):
    L=['xor ecx, ecx','mov eax, 38','mov edx, 38']
    for i in range(4): L+=[f'mov {R1[i]}, {q(X2,i)}']
    for i in range(4): L+=[f'mov {R2[i]}, {R1[i]}']
    for i in range(4): L+=[('add' if i==0 else 'adc')+f' {R1[i]}, {q(Z2,i)}']
    L+=['cmovae rax, rcx']
    for i in range(4): L+=[('sub' if i==0 else 'sbb')+f' {R2[i]}, {q(Z2,i)}']
    L+=['cmovae rdx, rcx']
    L+=['add r8, rax','adc r9, 0','adc r10, 0','adc r11, 0','sub r12, rdx','sbb r13, 0','sbb r14, 0','sbb r15, 0']
    for i in range(4): L+=[f'mov {q(A,i)}, {R1[i]}']
    for i in range(4): L+=[f'mov {q(B,i)}, {R2[i]}']
    L+=['movzx eax, BYTE PTR [rdi + rbx + 770]','movzx ecx, BYTE PTR [rdi + rbx + 771]','xor rax, rcx']
    for i in range(4): L+=[f'cmovne {R1[i]}, {q(C,i)}']
    for i in range(4): L+=[f'cmovne {R2[i]}, {q(D,i)}']
    for i in range(4): L+=[f'mov {q(U,i)}, {R1[i]}']
    for i in range(4): L+=[f'mov {q(V,i)}, {R2[i]}']
    return '\n'.join(L)
for n in ('base','adx'): parts[n+' M']=merged()
# dependency-free: everything reads slots nothing writes (z2->z2 etc. replaced)
def nodep(n):
    for o in ('A','B','C','D','UV','P','Q','AA','BB','s','d','E','x2','w','dd','z2','x3','z3'):
        t=parts[n+' '+o]
        lines=t.split('\n'); st=[i for i,l in enumerate(lines) if re.match(r'mov QWORD PTR',l)]
        for i in st[-4:] if o!='UV' else st: lines[i]=re.sub(r'\[rdi\+(\d+)\]',lambda g:f'[rdi + {int(g[1])+2048}]',lines[i])
        parts[f'{n} nd{o}']='\n'.join(lines)
for n in ('base','adx'): nodep(n)
ch='A D B C UV P AA BB Q E s x2 d w dd z2 x3 z3'
O={'chosen':ch,'nodep':' '.join('nd'+x for x in ch.split()),'merged':'D C M P AA BB Q E s x2 d w dd z2 x3 z3','merged2':'C D M AA P BB Q E s x2 d w dd z2 x3 z3','merged3':'C D M P AA BB Q s E d x2 dd w x3 z2 z3','merged4':'C D M AA P BB Q E d w x2 dd s z2 z3 x3'}
L=[(n,o.split()) for n in ('base','adx') for o in O.values()]
for z in range(2):
    r=build(L); names=list(O)
    for i,(n,o) in enumerate(L): print(n,names[i%len(O)],r[i])
