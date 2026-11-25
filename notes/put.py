import sys,json,re; sys.path.insert(0,'/tmp/sp')
from alloc import lean
B='/home/user/verified-garbage/lean/VerifiedGarbage/Impl/P256/'
for f,names in (('VerifyAllocatedCode',['mixedHead','mixedTail','jacTail','cachedHead']),('EcdhAllocatedCode',['double','dblu','zaddu'])):
    L=open(B+f+'.lean').read().split('\n')
    end=[i for i,l in enumerate(L) if l.startswith('end ')][-1]
    # drop earlier generated defs
    body=L[:end]
    keep=[];skip=False
    for l in body:
        m=re.match(r'^def (\w+) ',l)
        if m: skip=m.group(1) in names
        if not skip: keep.append(l)
    while keep and keep[-1]=='': keep.pop()
    out=[]
    for n in names:
        c=lean(json.load(open(f'/tmp/sp/{n}.best')))
        out+=['',f'def {n} : List Instr :=','  aarch64_instrs%']
        out+=['   ['+c[0]+',']+['    '+x+',' for x in c[1:-1]]+['    '+c[-1]+']']
    open(B+f+'.lean','w').write('\n'.join(keep+out+['']+L[end:]))
