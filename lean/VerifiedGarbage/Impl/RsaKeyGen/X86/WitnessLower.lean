module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.OrScan

/-! # A full native scan determines whether a witness is at least two -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.Impl.Mont.X86

def finish (src : Nat) : List Instr :=
  [.mov .eax (.mem (sc src)), .alu .or .eax (.imm 1), .alu .xor .eax (.imm 1),
    .alu .or .ebx (.reg .eax), .alu .cmp .ebx (.imm 1), .alu .sbb .ebx (.reg .ebx),
    .alu .xor .ebx (.imm (BitVec.allOnes 32))]

def code (n src : Nat) : Prog isa :=
  .seq (OrScan.code (n - 1) (src + 4)) (.block (finish src))

end VG.Impl.RsaKeyGen.X86.WitnessLower
