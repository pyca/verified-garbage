from gen import keccak
import random,struct,sys
from elftools.elf.elffile import ELFFile
from unicorn import *; from unicorn.arm64_const import *
e=ELFFile(open('t.elf','rb')); sy={s.name:s['st_value'] for s in e.get_section_by_name('.symtab').iter_symbols()}
from gen import RCS
mu=Uc(UC_ARCH_ARM64,UC_MODE_ARM); mu.ctl_set_cpu_model(UC_CPU_ARM64_MAX)
mu.mem_map(0,0x800000)
for s in e.iter_segments():
    if s['p_type']=='PT_LOAD': mu.mem_write(s['p_vaddr'],s.data())
mu.mem_map(0x1000000,0x10000)
mu.reg_write(UC_ARM64_REG_CPACR_EL1,3<<20)
def run(fn,bufs):
    for i,b in enumerate(bufs): mu.mem_write(0x1000000+0x1000*i,b); mu.reg_write(UC_ARM64_REG_X0+i,0x1000000+0x1000*i)
    mu.reg_write(UC_ARM64_REG_SP,0x100f000); mu.reg_write(UC_ARM64_REG_X30,0x1ff000)
    mu.emu_start(sy[fn],0x1ff000)
pk=lambda a:struct.pack('<%dQ'%len(a),*a)
def rd(i,n): return list(struct.unpack('<%dQ'%n,mu.mem_read(0x1000000+0x1000*i,8*n)))
rc=pk([v for r in RCS for v in (r,r)]); rc1=pk(RCS)
A=[random.getrandbits(64) for _ in range(25)];B=[random.getrandbits(64) for _ in range(25)];C=[random.getrandbits(64) for _ in range(25)]
for fn in sorted(k for k in sy if k.startswith('p_')):
    try:
        if fn.startswith('p_s'): run(fn,[pk(A),bytes(512),rc1]); print(fn,rd(0,25)==keccak(A))
        else:
            run(fn,[pk([v for t in zip(A,B) for v in t]),pk(C)+bytes(300),rc]); o=rd(0,50)
            print(fn,o[0::2]==keccak(A),o[1::2]==keccak(B), rd(1,25)==keccak(C) if 'x3' in fn else '')
    except Exception as ex: print(fn,ex, hex(mu.reg_read(UC_ARM64_REG_PC)))
