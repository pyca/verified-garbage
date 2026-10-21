module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.OrScan

/-! # Compare an absolute difference with the RSA separation threshold

For n native words the threshold is 2^(32*n-100). The low n-4 words are
scanned once. The next word supplies its low 28 bits to that scan and its
high nibble to the comparison; the three highest words must all be zero.
All arithmetic and addresses are independent of the difference's value.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Near
open VG VG.X86 VG.Impl.Mont.X86

def top (n src : Nat) : List Instr :=
  [.mov .eax (.mem (sc (src + 4 * (n - 4)))), .mov .ecx (.reg .eax), .shift .shr .ecx 28,
    .alu .and .eax (.imm 0x0fffffff), .alu .or .ebx (.reg .eax),
    .mov .edx (.mem (sc (src + 4 * (n - 4) + 4))),
    .alu .or .edx (.mem (sc (src + 4 * (n - 4) + 8))),
    .alu .or .edx (.mem (sc (src + 4 * (n - 4) + 12)))]

/-- EAX becomes one exactly when the difference is at most the threshold.
ECX starts with the high nibble, EBX with the lower-part OR, and EDX with
the three highest words' OR. The nibble plus the lower nonzero bit is at
most 16, so its addition cannot wrap. -/
def finish : List Instr :=
  [.mov .eax (.imm 1), .alu .sub .ebx (.imm 1), .alu .sbb .eax (.imm 0),
    .alu .add .ecx (.reg .eax), .mov .eax (.imm 0), .alu .sub .ecx (.imm 2), .alu .adc .eax (.imm 0),
    .mov .ecx (.imm 0), .alu .sub .edx (.imm 1), .alu .adc .ecx (.imm 0), .alu .and .eax (.reg .ecx)]

def code (n src : Nat) : Prog isa :=
  .seq (OrScan.code (n - 4) src) (.block (top n src ++ finish))

end VG.Impl.RsaKeyGen.X86.Near
