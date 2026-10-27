module

import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.TCB.X86.Isa

/-! # Compare an absolute difference with the RSA separation threshold

For n native words the threshold is 2^(32*n-100). The low n-4 words are
scanned once (`FrontRt.orScan`). The next word supplies its low 28 bits to
that scan and its high nibble to the comparison; the three highest words
must all be zero (`FrontRt.top`). All arithmetic and addresses are
independent of the difference's value.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Near
open VG VG.X86 VG.Impl.Mont.X86

/-- EAX becomes one exactly when the difference is at most the threshold.
ECX starts with the high nibble, EBX with the lower-part OR, and EDX with
the three highest words' OR. The nibble plus the lower nonzero bit is at
most 16, so its addition cannot wrap. -/
def finish : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .ebx (.imm 1), .alu .sbb .eax (.imm 0),
    .alu .add .ecx (.reg .eax), .mov .eax (.imm 0), .alu .sub .ecx (.imm 2), .alu .adc .eax (.imm 0),
    .mov .ecx (.imm 0), .alu .sub .edx (.imm 1), .alu .adc .ecx (.imm 0), .alu .and .eax (.reg .ecx)]

end VG.Impl.RsaKeyGen.X86.Near
