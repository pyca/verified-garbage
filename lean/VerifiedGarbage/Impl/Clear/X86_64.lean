import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Clearing registers before returning (x86-64)

`clear rs avx` zeroes the SSE registers, with `vpxor x, x, x` if `avx`
(VEX.128, which also zeroes the upper halves of the AVX and AVX-512
registers) and with `pxor x, x` otherwise (the baseline, which leaves them),
and then the general-purpose registers `rs` with `xor r32, r32`, which zeroes
all 64 bits and leaves CF = OF = SF = 0 and ZF = 1. At the end of a
function's code it leaves no secret residue in registers
(`X86_64.noResidue`; `Proof/Framework/X86_64/Residue.lean`).
-/

namespace VG.Impl.Clear.X86_64

open VG.X86_64

def xregs : List XReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
   .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

def zeroVec (avx : Bool) (x : XReg) : Instr :=
  if avx then .vop (.vbin .vpxor .l128 x x x) else .xop (.bin .pxor x x)

def zeroGpr (r : Reg) : Instr := .alu32 .xor r (.reg r)

def clear (rs : List Reg) (avx : Bool) : List Instr :=
  xregs.map (zeroVec avx) ++ rs.map zeroGpr

end VG.Impl.Clear.X86_64
