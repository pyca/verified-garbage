#!/usr/bin/env python3
"""Build out-of-tree, explicitly unproven RISC-V RSA experiments."""
import argparse, json, re, subprocess, urllib.request, hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'experiments/riscv-rsa/out'
ASM=ROOT/'crates/verified-garbage-asm-riscv64/assembly'
# Each match is an entire inlined arithmetic kernel, including its local loops.
END=r'\txor s3, s3, s2\n\tand s3, s3, s4\n\txor s3, s3, s2\n\tsd s3, 0\(a0\)\n\taddi t3, t3, 8\n\taddi t4, t4, 8\n\taddi a0, a0, 8\n\taddi t5, t5, -1\n\tbnez t5, \d+b\n'
MONT=re.compile(r'\taddi a1, t0, 0\n\taddi t3, a5, 0\n\taddi t5, t0, 1\n.*?'+END,re.S)
SQR=re.compile(r'\taddi t3, a5, 0\n\tadd t5, t0, t0\n\taddi t5, t5, 2\n.*?'+END+r'\tslli t3, t0, 3\n\tsub a5, a5, t3\n',re.S)
REGS=['ra','t0','t1','t2','t3','t4','t5','t6']+[f'a{i}' for i in range(8)]+[f's{i}' for i in range(12)]
def save():return '\taddi sp, sp, -224\n'+''.join(f'\tsd {r}, {8*i}(sp)\n' for i,r in enumerate(REGS))
def restore():return ''.join(f'\tld {r}, {8*i}(sp)\n' for i,r in enumerate(REGS))+'\taddi sp, sp, 224\n'
def ld(dst,src):return f'\tld {dst}, {REGS.index(src)*8}(sp)\n'
def call_c(name):
    return save()+''.join(ld(d,s) for d,s in zip(['a0','a1','a2','a3','a4','a5','a6','a7'],['a2','a3','a4','a7','t0','t1','a5','a6']))+f'\tcall {name}\n'+restore()
def entry(name,body):
    return f'.balign 4\n.globl {name}\n.type {name}, @function\n{name}:\n'+save()+''.join(ld(d,s) for d,s in zip(['a2','a3','a4','a7','t0','t1','a5','a6'],['a0','a1','a2','a3','a4','a5','a6','a7']))+body+restore()+'\tret\n'
def pairs(s):
    p=re.compile(r'\tmul (\w+), (\w+), (\w+)\n\tmulhu (\w+), \2, \3\n')
    count=0
    def sub(m):
        nonlocal count
        low,x,y,high=m.groups()
        if high in (x,y):return m[0]
        count+=1
        return f'\tmulhu {high}, {x}, {y}\n\tmul {low}, {x}, {y}\n'
    return p.sub(sub,s),count

def pipeline_square(body):
    # Stage the next independent product before consuming the current carry.
    step=re.compile(r"\tld s4, (\d+)\(t4\)\n\tmul s3, s0, a7\n\tmulhu s2, s0, a7\n\tld a7, (\d+)\(a0\)\n\tadd s3, s3, s4\n\tsltu s4, s3, s4\n\tadd s2, s2, s4\n\tadd s3, s3, s1\n\tsltu s4, s3, s1\n\tadd s1, s2, s4\n\tsd s3, \1\(t4\)\n")
    matches=list(step.finditer(body)); chunks=[];last=0;count=0;i=0
    while i+1<len(matches):
        a,b=matches[i:i+2];k,nxt=map(int,a.groups());k2,nxt2=map(int,b.groups())
        if a.end()!=b.start() or k2!=k+8 or nxt2!=nxt+8:i+=1;continue
        chunks.append(body[last:a.start()]);chunks.append(
            f"\tld s4, {k}(t4)\n\tmul s3, s0, a7\n\tmulhu s2, s0, a7\n\tld a7, {nxt}(a0)\n"
            f"\tmul a4, s0, a7\n\tmulhu a2, s0, a7\n\tld a7, {nxt2}(a0)\n"
            "\tadd s3, s3, s4\n\tsltu s4, s3, s4\n\tadd s2, s2, s4\n"
            "\tadd s3, s3, s1\n\tsltu s4, s3, s1\n\tadd s1, s2, s4\n"
            f"\tsd s3, {k}(t4)\n\tld s4, {k2}(t4)\n"
            "\tadd a4, a4, s4\n\tsltu s4, a4, s4\n\tadd a2, a2, s4\n"
            "\tadd a4, a4, s1\n\tsltu s4, a4, s1\n\tadd s1, a2, s4\n"
            f"\tsd a4, {k2}(t4)\n")
        last=b.end();count+=1;i+=2
    assert count==8,count
    chunks.append(body[last:]);result=''.join(chunks)
    at=result.rindex('\taddi t3, a5, 0\n\taddi t4, a6, 0\n\taddi a0, a7, 0\n')
    result=result[:at]+'\tld a2, 0(sp)\n'+result[at:]
    return '\taddi sp, sp, -16\n\tsd a2, 0(sp)\n\tsd a4, 8(sp)\n'+result+'\tld a4, 8(sp)\n\taddi sp, sp, 16\n'

SELECT=re.compile(r'\taddi s8, zero, 0\n.*?\taddi t2, s8, -16\n\tbnez t2, \d+b\n',re.S)
def select_words(_):
    text="\tslli t3, s5, 3\n\tadd t3, a7, t3\n\tslli s4, s5, 2\n\tadd s4, s4, s5\n\tadd s4, a7, s4\n\tmv t5, t0\n991:\n\tmv s1, t3\n\tli s0, 0\n\tli t6, 1\n\tsll t6, t6, a1\n"
    for j in range(16):
        text+='\tld s2, 0(s1)\n\tandi t2, t6, 1\n\tneg t2, t2\n\tand s2, s2, t2\n\tor s0, s0, s2\n'
        if j!=15:text+='\tsrli t6, t6, 1\n\tadd s1, s1, s5\n'
    return text+'\tsd s0, 0(s4)\n\taddi s4, s4, 8\n\taddi t3, t3, 8\n\taddi t5, t5, -1\n\tbnez t5, 991b\n'

def fixtures():
    keys=[];sources=[]
    for bits in (2048,3072,4096):
        name=f'rsa_oaep_{bits}_sha256_mgf1sha256_test.json'
        url=f'https://raw.githubusercontent.com/C2SP/wycheproof/main/testvectors_v1/{name}'
        data=urllib.request.urlopen(url).read(); sources.append({'url':url,'sha256':hashlib.sha256(data).hexdigest()})
        groups=json.loads(data)['testGroups']
        for group in groups[:2]:
            k=group['privateKey'];keys.append((bits,k))
    def blob(h):return bytes.fromhex(h if len(h)%2==0 else '0'+h).lstrip(b'\0') or b'\0'
    lines=['/* Published Wycheproof private keys; provenance in fixtures.json. */']
    fields=['modulus','publicExponent','privateExponent','prime1','prime2','exponent1','exponent2','coefficient']
    for i,(bits,k) in enumerate(keys):
        for j,f in enumerate(fields):
            b=blob(k[f]);b=b.rjust(len(blob(k['prime2' if f=='exponent2' else 'prime1'])),b'\0') if f in ('exponent1','exponent2','coefficient') else b;lines.append(f'static const unsigned char key_{i}_{j}[]={{'+','.join(map(str,b))+'};')
    lines.append('static const struct key keys[]={')
    for i,(bits,k) in enumerate(keys):
        lines.append('{'+str(bits)+','+','.join(f'key_{i}_{j},sizeof(key_{i}_{j})' for j in range(8))+'},')
    lines.append('};')
    (OUT/'fixtures.h').write_text('\n'.join(lines))
    (OUT/'fixtures.json').write_text(json.dumps(sources,indent=2))

def main():
    OUT.mkdir(exist_ok=True)
    crt=(ASM/'internal/vg_rsa_private_crt.s').read_text()
    public=(ASM/'rsa.s').read_text();checked=(ASM/'internal/vg_rsa_private_checked.s').read_text();pubchecked=(ASM/'internal/vg_rsa_public_precomputed_checked.s').read_text()
    alltext='\n'.join((public,crt,checked,pubchecked))
    variants={'base':alltext,'pair':pairs(alltext)[0]}
    nm=len(MONT.findall(alltext));ns=len(SQR.findall(alltext))
    assert nm>10 and ns>5,(nm,ns)
    variants['one']=MONT.sub(lambda m:call_c('c_one'),alltext)
    variants['two']=MONT.sub(lambda m:call_c('c_two'),alltext)
    variants['column']=SQR.sub(lambda m:call_c('c_column'),alltext)
    variants['montpair']=MONT.sub(lambda m:pairs(m[0])[0],alltext)
    variants['pipeline']=SQR.sub(lambda m:pipeline_square(m[0]),alltext)
    variants['select']=SELECT.sub(select_words,alltext)
    square_body=SQR.search(crt)[0]
    square_body=re.sub(r'^(\d+):',lambda m:str(int(m[1])+10000)+':',square_body,flags=re.M)
    square_body=re.sub(r'\b(\d+)([bf])\b',lambda m:str(int(m[1])+10000)+m[2],square_body)
    replacements=0
    def public_square(m):
        nonlocal replacements
        before=pubchecked[:m.start()]
        args=re.findall(r'\taddi a3, a7, 0\n((?:\tadd a3, a3, s5\n)*)\taddi a4, a7, 0\n((?:\tadd a4, a4, s5\n)*)',before)
        if args and args[-1][0].count('\n')==5 and args[-1][1].count('\n')==5:
            replacements+=1
            return '\tadd a6, a7, s5\n'+square_body
        return m[0]
    fast_public=MONT.sub(public_square,pubchecked)
    assert replacements==2,replacements
    variants['pubsquare']=alltext.replace(pubchecked,fast_public)
    combined=SQR.sub(lambda m:pipeline_square(m[0]),variants['pubsquare'])
    combined=SELECT.sub(select_words,combined)
    variants['combined']=MONT.sub(lambda m:pairs(m[0])[0],combined)
    assert len(SELECT.findall(alltext))==4
    report={'mont_sites':nm,'square_sites':ns,'reordered_pairs':pairs(alltext)[1]}
    (OUT/'transforms.json').write_text(json.dumps(report,indent=2));print(report)
    # Numeric local labels remain scoped by nearest definition; globals are namespaced.
    for name,text in variants.items():
        text=re.sub(r'\{(vg_\w+)\}',r'\1',text)
        text=re.sub(r'\b(vg_\w+)\b',lambda m:name+'_'+m[0],text)
        text=re.sub(r'^([A-Za-z_]\w*):$',r'.balign 4\n.globl \1\n\1:',text,flags=re.M)
        (OUT/f'{name}.S').write_text('.text\n'+text+'\n.section .note.GNU-stack,"",@progbits\n')
    micro='.text\n.option arch, +m, +c\n'
    mb=MONT.search(crt)[0];sb=SQR.search(crt)[0]
    for name,body in [('base_mont',mb),('pair_mont',pairs(mb)[0]),('base_square',sb),('pair_square',pairs(sb)[0]),('pipeline_square',pipeline_square(sb))]:micro+=entry(name,body)
    (OUT/'micro.S').write_text(micro+'\n.section .note.GNU-stack,"",@progbits\n')
    for name in ('fixtures.h','fixtures.json'):
        (OUT/name).write_bytes((ROOT/'experiments/riscv-rsa/fixtures'/name).read_bytes())
if __name__=='__main__':main()
