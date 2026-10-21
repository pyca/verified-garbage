module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Secret exponent alignment masks from the paired lowest-set-bit marker -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.SigMask
open VG VG.X86 VG.Impl.Mont.X86

def constant : Nat → BitVec 32
  | 1 => 0xDDDDDDDD
  | 2 => 0x99999999
  | _ => 0x11111111

/-- ECX is all ones when sigma > j; every read has a fixed public address. -/
def code (marker j : Nat) : List Instr :=
  [.mov .eax (.mem (sc marker)), .alu .or .eax (.mem (sc (marker + 4))),
    .alu .and .eax (.imm (constant j)), .alu .cmp .eax (.imm 1), .alu .sbb .ecx (.reg .ecx),
    .alu .xor .ecx (.imm (BitVec.allOnes 32))]

end VG.Impl.RsaKeyGen.X86.SigMask
