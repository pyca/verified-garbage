module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Return whether the native GCD bank contains exactly one -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Impl.Mont.X86

def result : List Instr :=
  [.mov .eax (.mem (sc 176)), .alu .sub .eax (.imm 1), .alu .or .eax (.mem (sc 180)),
    .mov .ecx (.imm 0), .alu .sub .eax (.imm 1), .alu .adc .ecx (.imm 0), .mov .eax (.reg .ecx)]

end VG.Impl.RsaKeyGen.X86.Gcd64
